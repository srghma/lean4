// Lean compiler output
// Module: Lean.Compiler.LCNF.Renaming
// Imports: Lean.Compiler.LCNF.CompilerM
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::{
    l_Lean_Compiler_LCNF_LCtx_addFunDecl, l_Lean_Compiler_LCNF_LCtx_addLetDecl,
    l_Lean_Compiler_LCNF_LCtx_addParam,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::ffi::{lean_st_ref_set, lean_st_ref_take};
use crate::ffi::lean_ptr_addr;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(
    mut v_t_916_: *mut crate::leanh::LeanObject,
    mut v_k_917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: u8 = 0;
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_916_) == 0 {
                    v_k_918_ = crate::leanh::lean_ctor_get(v_t_916_, 1);
                    v_v_919_ = crate::leanh::lean_ctor_get(v_t_916_, 2);
                    v_l_920_ = crate::leanh::lean_ctor_get(v_t_916_, 3);
                    v_r_921_ = crate::leanh::lean_ctor_get(v_t_916_, 4);
                    v___x_922_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_917_, v_k_918_);
                    match v___x_922_ {
                        0 => {
                            v_t_916_ = v_l_920_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_919_);
                            v___x_924_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_924_, 0, v_v_919_);
                            return v___x_924_;
                        }
                        _ => {
                            v_t_916_ = v_r_921_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_926_ = crate::leanh::lean_box(0);
                    return v___x_926_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg___boxed(
    mut v_t_927_: *mut crate::leanh::LeanObject,
    mut v_k_928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_929_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_t_927_, v_k_928_);
    crate::leanh::lean_dec(v_k_928_);
    crate::leanh::lean_dec(v_t_927_);
    return v_res_929_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(
    mut v_pu_930_: u8,
    mut v_param_931_: *mut crate::leanh::LeanObject,
    mut v_r_932_: *mut crate::leanh::LeanObject,
    mut v_a_933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_937_: u8 = 0;
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_941_: u8 = 0;
    let mut v_val_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_945_: u8 = 0;
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_951_: u8 = 0;
    let mut v_param_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_963_: u8 = 0;
    let mut v_isSharedCheck_964_: u8 = 0;
    let mut v_isSharedCheck_965_: u8 = 0;
    let mut v_unused_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_935_ = crate::leanh::lean_ctor_get(v_param_931_, 0);
                v_type_936_ = crate::leanh::lean_ctor_get(v_param_931_, 2);
                v_borrow_937_ = crate::leanh::lean_ctor_get_uint8(
                    v_param_931_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v___x_938_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_r_932_, v_fvarId_935_);
                if crate::leanh::lean_obj_tag(v___x_938_) == 1 {
                    crate::leanh::lean_inc_ref(v_type_936_);
                    crate::leanh::lean_inc(v_fvarId_935_);
                    v_isSharedCheck_965_ = (!crate::leanh::lean_is_exclusive(v_param_931_)) as u8;
                    if v_isSharedCheck_965_ == 0 {
                        v_unused_966_ = crate::leanh::lean_ctor_get(v_param_931_, 2);
                        crate::leanh::lean_dec(v_unused_966_);
                        v_unused_967_ = crate::leanh::lean_ctor_get(v_param_931_, 1);
                        crate::leanh::lean_dec(v_unused_967_);
                        v_unused_968_ = crate::leanh::lean_ctor_get(v_param_931_, 0);
                        crate::leanh::lean_dec(v_unused_968_);
                        v___x_940_ = v_param_931_;
                        v_isShared_941_ = v_isSharedCheck_965_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_param_931_);
                        v___x_940_ = crate::leanh::lean_box(0);
                        v_isShared_941_ = v_isSharedCheck_965_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_938_);
                    v___x_969_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_969_, 0, v_param_931_);
                    return v___x_969_;
                }
            }
            1 => {
                v_val_942_ = crate::leanh::lean_ctor_get(v___x_938_, 0);
                v_isSharedCheck_964_ = (!crate::leanh::lean_is_exclusive(v___x_938_)) as u8;
                if v_isSharedCheck_964_ == 0 {
                    v___x_944_ = v___x_938_;
                    v_isShared_945_ = v_isSharedCheck_964_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_942_);
                    crate::leanh::lean_dec(v___x_938_);
                    v___x_944_ = crate::leanh::lean_box(0);
                    v_isShared_945_ = v_isSharedCheck_964_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_946_ = lean_st_ref_take(v_a_933_);
                v_lctx_947_ = crate::leanh::lean_ctor_get(v___x_946_, 0);
                v_nextIdx_948_ = crate::leanh::lean_ctor_get(v___x_946_, 1);
                v_isSharedCheck_963_ = (!crate::leanh::lean_is_exclusive(v___x_946_)) as u8;
                if v_isSharedCheck_963_ == 0 {
                    v___x_950_ = v___x_946_;
                    v_isShared_951_ = v_isSharedCheck_963_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_948_);
                    crate::leanh::lean_inc(v_lctx_947_);
                    crate::leanh::lean_dec(v___x_946_);
                    v___x_950_ = crate::leanh::lean_box(0);
                    v_isShared_951_ = v_isSharedCheck_963_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_941_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_940_, 1, v_val_942_);
                    v_param_953_ = v___x_940_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_962_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_962_, 0, v_fvarId_935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_962_, 1, v_val_942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_962_, 2, v_type_936_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_962_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_borrow_937_,
                    );
                    v_param_953_ = v_reuseFailAlloc_962_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_param_953_);
                v___x_954_ =
                    l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_930_, v_lctx_947_, v_param_953_);
                if v_isShared_951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_950_, 0, v___x_954_);
                    v___x_956_ = v___x_950_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_961_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_961_, 1, v_nextIdx_948_);
                    v___x_956_ = v_reuseFailAlloc_961_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_957_ = lean_st_ref_set(v_a_933_, v___x_956_);
                if v_isShared_945_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_944_, 0);
                    crate::leanh::lean_ctor_set(v___x_944_, 0, v_param_953_);
                    v___x_959_ = v___x_944_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_960_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_960_, 0, v_param_953_);
                    v___x_959_ = v_reuseFailAlloc_960_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_applyRenaming___redArg___boxed(
    mut v_pu_970_: *mut crate::leanh::LeanObject,
    mut v_param_971_: *mut crate::leanh::LeanObject,
    mut v_r_972_: *mut crate::leanh::LeanObject,
    mut v_a_973_: *mut crate::leanh::LeanObject,
    mut v_a_974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_975_: u8 = 0;
    let mut v_res_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_975_ = (crate::leanh::lean_unbox(v_pu_970_) as u8);
    v_res_976_ = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(
        v_pu_boxed_975_,
        v_param_971_,
        v_r_972_,
        v_a_973_,
    );
    crate::leanh::lean_dec(v_a_973_);
    crate::leanh::lean_dec(v_r_972_);
    return v_res_976_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_applyRenaming(
    mut v_pu_977_: u8,
    mut v_param_978_: *mut crate::leanh::LeanObject,
    mut v_r_979_: *mut crate::leanh::LeanObject,
    mut v_a_980_: *mut crate::leanh::LeanObject,
    mut v_a_981_: *mut crate::leanh::LeanObject,
    mut v_a_982_: *mut crate::leanh::LeanObject,
    mut v_a_983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(
        v_pu_977_,
        v_param_978_,
        v_r_979_,
        v_a_981_,
    );
    return v___x_985_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_applyRenaming___boxed(
    mut v_pu_986_: *mut crate::leanh::LeanObject,
    mut v_param_987_: *mut crate::leanh::LeanObject,
    mut v_r_988_: *mut crate::leanh::LeanObject,
    mut v_a_989_: *mut crate::leanh::LeanObject,
    mut v_a_990_: *mut crate::leanh::LeanObject,
    mut v_a_991_: *mut crate::leanh::LeanObject,
    mut v_a_992_: *mut crate::leanh::LeanObject,
    mut v_a_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_994_: u8 = 0;
    let mut v_res_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_994_ = (crate::leanh::lean_unbox(v_pu_986_) as u8);
    v_res_995_ = l_Lean_Compiler_LCNF_Param_applyRenaming(
        v_pu_boxed_994_,
        v_param_987_,
        v_r_988_,
        v_a_989_,
        v_a_990_,
        v_a_991_,
        v_a_992_,
    );
    crate::leanh::lean_dec(v_a_992_);
    crate::leanh::lean_dec_ref(v_a_991_);
    crate::leanh::lean_dec(v_a_990_);
    crate::leanh::lean_dec_ref(v_a_989_);
    crate::leanh::lean_dec(v_r_988_);
    return v_res_995_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0(
    mut v_00_u03b4_996_: *mut crate::leanh::LeanObject,
    mut v_t_997_: *mut crate::leanh::LeanObject,
    mut v_k_998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_t_997_, v_k_998_);
    return v___x_999_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___boxed(
    mut v_00_u03b4_1000_: *mut crate::leanh::LeanObject,
    mut v_t_1001_: *mut crate::leanh::LeanObject,
    mut v_k_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1003_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0(v_00_u03b4_1000_, v_t_1001_, v_k_1002_);
    crate::leanh::lean_dec(v_k_1002_);
    crate::leanh::lean_dec(v_t_1001_);
    return v_res_1003_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(
    mut v_pu_1004_: u8,
    mut v_decl_1005_: *mut crate::leanh::LeanObject,
    mut v_r_1006_: *mut crate::leanh::LeanObject,
    mut v_a_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1015_: u8 = 0;
    let mut v_val_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1019_: u8 = 0;
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1025_: u8 = 0;
    let mut v_decl_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1037_: u8 = 0;
    let mut v_isSharedCheck_1038_: u8 = 0;
    let mut v_isSharedCheck_1039_: u8 = 0;
    let mut v_unused_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_1009_ = crate::leanh::lean_ctor_get(v_decl_1005_, 0);
                v_type_1010_ = crate::leanh::lean_ctor_get(v_decl_1005_, 2);
                v_value_1011_ = crate::leanh::lean_ctor_get(v_decl_1005_, 3);
                v___x_1012_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_r_1006_, v_fvarId_1009_);
                if crate::leanh::lean_obj_tag(v___x_1012_) == 1 {
                    crate::leanh::lean_inc(v_value_1011_);
                    crate::leanh::lean_inc_ref(v_type_1010_);
                    crate::leanh::lean_inc(v_fvarId_1009_);
                    v_isSharedCheck_1039_ = (!crate::leanh::lean_is_exclusive(v_decl_1005_)) as u8;
                    if v_isSharedCheck_1039_ == 0 {
                        v_unused_1040_ = crate::leanh::lean_ctor_get(v_decl_1005_, 3);
                        crate::leanh::lean_dec(v_unused_1040_);
                        v_unused_1041_ = crate::leanh::lean_ctor_get(v_decl_1005_, 2);
                        crate::leanh::lean_dec(v_unused_1041_);
                        v_unused_1042_ = crate::leanh::lean_ctor_get(v_decl_1005_, 1);
                        crate::leanh::lean_dec(v_unused_1042_);
                        v_unused_1043_ = crate::leanh::lean_ctor_get(v_decl_1005_, 0);
                        crate::leanh::lean_dec(v_unused_1043_);
                        v___x_1014_ = v_decl_1005_;
                        v_isShared_1015_ = v_isSharedCheck_1039_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_decl_1005_);
                        v___x_1014_ = crate::leanh::lean_box(0);
                        v_isShared_1015_ = v_isSharedCheck_1039_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1012_);
                    v___x_1044_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1044_, 0, v_decl_1005_);
                    return v___x_1044_;
                }
            }
            1 => {
                v_val_1016_ = crate::leanh::lean_ctor_get(v___x_1012_, 0);
                v_isSharedCheck_1038_ = (!crate::leanh::lean_is_exclusive(v___x_1012_)) as u8;
                if v_isSharedCheck_1038_ == 0 {
                    v___x_1018_ = v___x_1012_;
                    v_isShared_1019_ = v_isSharedCheck_1038_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1016_);
                    crate::leanh::lean_dec(v___x_1012_);
                    v___x_1018_ = crate::leanh::lean_box(0);
                    v_isShared_1019_ = v_isSharedCheck_1038_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1020_ = lean_st_ref_take(v_a_1007_);
                v_lctx_1021_ = crate::leanh::lean_ctor_get(v___x_1020_, 0);
                v_nextIdx_1022_ = crate::leanh::lean_ctor_get(v___x_1020_, 1);
                v_isSharedCheck_1037_ = (!crate::leanh::lean_is_exclusive(v___x_1020_)) as u8;
                if v_isSharedCheck_1037_ == 0 {
                    v___x_1024_ = v___x_1020_;
                    v_isShared_1025_ = v_isSharedCheck_1037_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_1022_);
                    crate::leanh::lean_inc(v_lctx_1021_);
                    crate::leanh::lean_dec(v___x_1020_);
                    v___x_1024_ = crate::leanh::lean_box(0);
                    v_isShared_1025_ = v_isSharedCheck_1037_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1015_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1014_, 1, v_val_1016_);
                    v_decl_1027_ = v___x_1014_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1036_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_fvarId_1009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_val_1016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1036_, 2, v_type_1010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1036_, 3, v_value_1011_);
                    v_decl_1027_ = v_reuseFailAlloc_1036_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_decl_1027_);
                v___x_1028_ =
                    l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_1004_, v_lctx_1021_, v_decl_1027_);
                if v_isShared_1025_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1024_, 0, v___x_1028_);
                    v___x_1030_ = v___x_1024_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1035_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_nextIdx_1022_);
                    v___x_1030_ = v_reuseFailAlloc_1035_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1031_ = lean_st_ref_set(v_a_1007_, v___x_1030_);
                if v_isShared_1019_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1018_, 0);
                    crate::leanh::lean_ctor_set(v___x_1018_, 0, v_decl_1027_);
                    v___x_1033_ = v___x_1018_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1034_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_decl_1027_);
                    v___x_1033_ = v_reuseFailAlloc_1034_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg___boxed(
    mut v_pu_1045_: *mut crate::leanh::LeanObject,
    mut v_decl_1046_: *mut crate::leanh::LeanObject,
    mut v_r_1047_: *mut crate::leanh::LeanObject,
    mut v_a_1048_: *mut crate::leanh::LeanObject,
    mut v_a_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1050_: u8 = 0;
    let mut v_res_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1050_ = (crate::leanh::lean_unbox(v_pu_1045_) as u8);
    v_res_1051_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(
        v_pu_boxed_1050_,
        v_decl_1046_,
        v_r_1047_,
        v_a_1048_,
    );
    crate::leanh::lean_dec(v_a_1048_);
    crate::leanh::lean_dec(v_r_1047_);
    return v_res_1051_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_applyRenaming(
    mut v_pu_1052_: u8,
    mut v_decl_1053_: *mut crate::leanh::LeanObject,
    mut v_r_1054_: *mut crate::leanh::LeanObject,
    mut v_a_1055_: *mut crate::leanh::LeanObject,
    mut v_a_1056_: *mut crate::leanh::LeanObject,
    mut v_a_1057_: *mut crate::leanh::LeanObject,
    mut v_a_1058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1060_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(
        v_pu_1052_,
        v_decl_1053_,
        v_r_1054_,
        v_a_1056_,
    );
    return v___x_1060_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_applyRenaming___boxed(
    mut v_pu_1061_: *mut crate::leanh::LeanObject,
    mut v_decl_1062_: *mut crate::leanh::LeanObject,
    mut v_r_1063_: *mut crate::leanh::LeanObject,
    mut v_a_1064_: *mut crate::leanh::LeanObject,
    mut v_a_1065_: *mut crate::leanh::LeanObject,
    mut v_a_1066_: *mut crate::leanh::LeanObject,
    mut v_a_1067_: *mut crate::leanh::LeanObject,
    mut v_a_1068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1069_: u8 = 0;
    let mut v_res_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1069_ = (crate::leanh::lean_unbox(v_pu_1061_) as u8);
    v_res_1070_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming(
        v_pu_boxed_1069_,
        v_decl_1062_,
        v_r_1063_,
        v_a_1064_,
        v_a_1065_,
        v_a_1066_,
        v_a_1067_,
    );
    crate::leanh::lean_dec(v_a_1067_);
    crate::leanh::lean_dec_ref(v_a_1066_);
    crate::leanh::lean_dec(v_a_1065_);
    crate::leanh::lean_dec_ref(v_a_1064_);
    crate::leanh::lean_dec(v_r_1063_);
    return v_res_1070_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(
    mut v_pu_1071_: u8,
    mut v_r_1072_: *mut crate::leanh::LeanObject,
    mut v_i_1073_: *mut crate::leanh::LeanObject,
    mut v_as_1074_: *mut crate::leanh::LeanObject,
    mut v___y_1075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: u8 = 0;
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: usize = 0;
    let mut v___x_1084_: usize = 0;
    let mut v___x_1085_: u8 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1096_: u8 = 0;
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1100_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1077_ = lean_array_get_size(v_as_1074_);
                v___x_1078_ = lean_nat_dec_lt(v_i_1073_, v___x_1077_);
                if v___x_1078_ == 0 {
                    crate::leanh::lean_dec(v_i_1073_);
                    v___x_1079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1079_, 0, v_as_1074_);
                    return v___x_1079_;
                } else {
                    v_a_1080_ = lean_array_fget_borrowed(v_as_1074_, v_i_1073_);
                    crate::leanh::lean_inc(v_a_1080_);
                    v___x_1081_ = l_Lean_Compiler_LCNF_Param_applyRenaming___redArg(
                        v_pu_1071_,
                        v_a_1080_,
                        v_r_1072_,
                        v___y_1075_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1081_) == 0 {
                        v_a_1082_ = crate::leanh::lean_ctor_get(v___x_1081_, 0);
                        crate::leanh::lean_inc(v_a_1082_);
                        crate::leanh::lean_dec_ref_known(v___x_1081_, 1);
                        v___x_1083_ = lean_ptr_addr(v_a_1080_);
                        v___x_1084_ = lean_ptr_addr(v_a_1082_);
                        v___x_1085_ = lean_usize_dec_eq(v___x_1083_, v___x_1084_);
                        if v___x_1085_ == 0 {
                            v___x_1086_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1087_ = lean_nat_add(v_i_1073_, v___x_1086_);
                            v___x_1088_ = lean_array_fset(v_as_1074_, v_i_1073_, v_a_1082_);
                            crate::leanh::lean_dec(v_i_1073_);
                            v_i_1073_ = v___x_1087_;
                            v_as_1074_ = v___x_1088_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1082_);
                            v___x_1090_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1091_ = lean_nat_add(v_i_1073_, v___x_1090_);
                            crate::leanh::lean_dec(v_i_1073_);
                            v_i_1073_ = v___x_1091_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_as_1074_);
                        crate::leanh::lean_dec(v_i_1073_);
                        v_a_1093_ = crate::leanh::lean_ctor_get(v___x_1081_, 0);
                        v_isSharedCheck_1100_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1081_)) as u8;
                        if v_isSharedCheck_1100_ == 0 {
                            v___x_1095_ = v___x_1081_;
                            v_isShared_1096_ = v_isSharedCheck_1100_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1093_);
                            crate::leanh::lean_dec(v___x_1081_);
                            v___x_1095_ = crate::leanh::lean_box(0);
                            v_isShared_1096_ = v_isSharedCheck_1100_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1096_ == 0 {
                    v___x_1098_ = v___x_1095_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1099_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
                    v___x_1098_ = v_reuseFailAlloc_1099_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1098_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg___boxed(
    mut v_pu_1101_: *mut crate::leanh::LeanObject,
    mut v_r_1102_: *mut crate::leanh::LeanObject,
    mut v_i_1103_: *mut crate::leanh::LeanObject,
    mut v_as_1104_: *mut crate::leanh::LeanObject,
    mut v___y_1105_: *mut crate::leanh::LeanObject,
    mut v___y_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1107_: u8 = 0;
    let mut v_res_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1107_ = (crate::leanh::lean_unbox(v_pu_1101_) as u8);
    v_res_1108_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_boxed_1107_, v_r_1102_, v_i_1103_, v_as_1104_, v___y_1105_);
    crate::leanh::lean_dec(v___y_1105_);
    crate::leanh::lean_dec(v_r_1102_);
    return v_res_1108_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(
    mut v_pu_1109_: u8,
    mut v_r_1110_: *mut crate::leanh::LeanObject,
    mut v_i_1111_: *mut crate::leanh::LeanObject,
    mut v_as_1112_: *mut crate::leanh::LeanObject,
    mut v___y_1113_: *mut crate::leanh::LeanObject,
    mut v___y_1114_: *mut crate::leanh::LeanObject,
    mut v___y_1115_: *mut crate::leanh::LeanObject,
    mut v___y_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: u8 = 0;
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: usize = 0;
    let mut v___x_1125_: usize = 0;
    let mut v___x_1126_: u8 = 0;
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1145_: u8 = 0;
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1149_: u8 = 0;
    let mut v_a_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1153_: u8 = 0;
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1157_: u8 = 0;
    let mut v_code_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut v_code_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1118_ = lean_array_get_size(v_as_1112_);
                v___x_1119_ = lean_nat_dec_lt(v_i_1111_, v___x_1118_);
                if v___x_1119_ == 0 {
                    crate::leanh::lean_dec(v_i_1111_);
                    v___x_1120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1120_, 0, v_as_1112_);
                    return v___x_1120_;
                } else {
                    v_a_1121_ = lean_array_fget_borrowed(v_as_1112_, v_i_1111_);
                    match crate::leanh::lean_obj_tag(v_a_1121_) {
                        0 => {
                            v_params_1134_ = crate::leanh::lean_ctor_get(v_a_1121_, 1);
                            v_code_1135_ = crate::leanh::lean_ctor_get(v_a_1121_, 2);
                            v___x_1136_ = crate::leanh::lean_unsigned_to_nat(0);
                            crate::leanh::lean_inc_ref(v_params_1134_);
                            v___x_1137_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_1109_, v_r_1110_, v___x_1136_, v_params_1134_, v___y_1114_);
                            if crate::leanh::lean_obj_tag(v___x_1137_) == 0 {
                                v_a_1138_ = crate::leanh::lean_ctor_get(v___x_1137_, 0);
                                crate::leanh::lean_inc(v_a_1138_);
                                crate::leanh::lean_dec_ref_known(v___x_1137_, 1);
                                crate::leanh::lean_inc_ref(v_code_1135_);
                                v___x_1139_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                                    v_pu_1109_,
                                    v_code_1135_,
                                    v_r_1110_,
                                    v___y_1113_,
                                    v___y_1114_,
                                    v___y_1115_,
                                    v___y_1116_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1139_) == 0 {
                                    v_a_1140_ = crate::leanh::lean_ctor_get(v___x_1139_, 0);
                                    crate::leanh::lean_inc(v_a_1140_);
                                    crate::leanh::lean_dec_ref_known(v___x_1139_, 1);
                                    crate::leanh::lean_inc_ref(v_a_1121_);
                                    v___x_1141_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_1109_, v_a_1121_, v_a_1138_, v_a_1140_);
                                    v_a_1123_ = v___x_1141_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_1138_);
                                    crate::leanh::lean_dec_ref(v_as_1112_);
                                    crate::leanh::lean_dec(v_i_1111_);
                                    v_a_1142_ = crate::leanh::lean_ctor_get(v___x_1139_, 0);
                                    v_isSharedCheck_1149_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1139_)) as u8;
                                    if v_isSharedCheck_1149_ == 0 {
                                        v___x_1144_ = v___x_1139_;
                                        v_isShared_1145_ = v_isSharedCheck_1149_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1142_);
                                        crate::leanh::lean_dec(v___x_1139_);
                                        v___x_1144_ = crate::leanh::lean_box(0);
                                        v_isShared_1145_ = v_isSharedCheck_1149_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_as_1112_);
                                crate::leanh::lean_dec(v_i_1111_);
                                v_a_1150_ = crate::leanh::lean_ctor_get(v___x_1137_, 0);
                                v_isSharedCheck_1157_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1137_)) as u8;
                                if v_isSharedCheck_1157_ == 0 {
                                    v___x_1152_ = v___x_1137_;
                                    v_isShared_1153_ = v_isSharedCheck_1157_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1150_);
                                    crate::leanh::lean_dec(v___x_1137_);
                                    v___x_1152_ = crate::leanh::lean_box(0);
                                    v_isShared_1153_ = v_isSharedCheck_1157_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            v_code_1158_ = crate::leanh::lean_ctor_get(v_a_1121_, 1);
                            crate::leanh::lean_inc_ref(v_code_1158_);
                            v___x_1159_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                                v_pu_1109_,
                                v_code_1158_,
                                v_r_1110_,
                                v___y_1113_,
                                v___y_1114_,
                                v___y_1115_,
                                v___y_1116_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1159_) == 0 {
                                v_a_1160_ = crate::leanh::lean_ctor_get(v___x_1159_, 0);
                                crate::leanh::lean_inc(v_a_1160_);
                                crate::leanh::lean_dec_ref_known(v___x_1159_, 1);
                                crate::leanh::lean_inc_ref(v_a_1121_);
                                v___x_1161_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1121_, v_a_1160_);
                                v_a_1123_ = v___x_1161_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_as_1112_);
                                crate::leanh::lean_dec(v_i_1111_);
                                v_a_1162_ = crate::leanh::lean_ctor_get(v___x_1159_, 0);
                                v_isSharedCheck_1169_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1159_)) as u8;
                                if v_isSharedCheck_1169_ == 0 {
                                    v___x_1164_ = v___x_1159_;
                                    v_isShared_1165_ = v_isSharedCheck_1169_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1162_);
                                    crate::leanh::lean_dec(v___x_1159_);
                                    v___x_1164_ = crate::leanh::lean_box(0);
                                    v_isShared_1165_ = v_isSharedCheck_1169_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v_code_1170_ = crate::leanh::lean_ctor_get(v_a_1121_, 0);
                            crate::leanh::lean_inc_ref(v_code_1170_);
                            v___x_1171_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                                v_pu_1109_,
                                v_code_1170_,
                                v_r_1110_,
                                v___y_1113_,
                                v___y_1114_,
                                v___y_1115_,
                                v___y_1116_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1171_) == 0 {
                                v_a_1172_ = crate::leanh::lean_ctor_get(v___x_1171_, 0);
                                crate::leanh::lean_inc(v_a_1172_);
                                crate::leanh::lean_dec_ref_known(v___x_1171_, 1);
                                crate::leanh::lean_inc_ref(v_a_1121_);
                                v___x_1173_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1121_, v_a_1172_);
                                v_a_1123_ = v___x_1173_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_as_1112_);
                                crate::leanh::lean_dec(v_i_1111_);
                                v_a_1174_ = crate::leanh::lean_ctor_get(v___x_1171_, 0);
                                v_isSharedCheck_1181_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1171_)) as u8;
                                if v_isSharedCheck_1181_ == 0 {
                                    v___x_1176_ = v___x_1171_;
                                    v_isShared_1177_ = v_isSharedCheck_1181_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1174_);
                                    crate::leanh::lean_dec(v___x_1171_);
                                    v___x_1176_ = crate::leanh::lean_box(0);
                                    v_isShared_1177_ = v_isSharedCheck_1181_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1124_ = lean_ptr_addr(v_a_1121_);
                v___x_1125_ = lean_ptr_addr(v_a_1123_);
                v___x_1126_ = lean_usize_dec_eq(v___x_1124_, v___x_1125_);
                if v___x_1126_ == 0 {
                    v___x_1127_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1128_ = lean_nat_add(v_i_1111_, v___x_1127_);
                    v___x_1129_ = lean_array_fset(v_as_1112_, v_i_1111_, v_a_1123_);
                    crate::leanh::lean_dec(v_i_1111_);
                    v_i_1111_ = v___x_1128_;
                    v_as_1112_ = v___x_1129_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_a_1123_);
                    v___x_1131_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1132_ = lean_nat_add(v_i_1111_, v___x_1131_);
                    crate::leanh::lean_dec(v_i_1111_);
                    v_i_1111_ = v___x_1132_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v_isShared_1145_ == 0 {
                    v___x_1147_ = v___x_1144_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1148_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
                    v___x_1147_ = v_reuseFailAlloc_1148_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1147_;
            }
            4 => {
                if v_isShared_1153_ == 0 {
                    v___x_1155_ = v___x_1152_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
                    v___x_1155_ = v_reuseFailAlloc_1156_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1155_;
            }
            6 => {
                if v_isShared_1165_ == 0 {
                    v___x_1167_ = v___x_1164_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
                    v___x_1167_ = v_reuseFailAlloc_1168_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1167_;
            }
            8 => {
                if v_isShared_1177_ == 0 {
                    v___x_1179_ = v___x_1176_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
                    v___x_1179_ = v_reuseFailAlloc_1180_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_applyRenaming(
    mut v_pu_1182_: u8,
    mut v_code_1183_: *mut crate::leanh::LeanObject,
    mut v_r_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
    mut v_a_1186_: *mut crate::leanh::LeanObject,
    mut v_a_1187_: *mut crate::leanh::LeanObject,
    mut v_a_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v___y_1200_: u8 = 0;
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1203_: u8 = 0;
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1210_: u8 = 0;
    let mut v_unused_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: usize = 0;
    let mut v___x_1217_: usize = 0;
    let mut v___x_1218_: u8 = 0;
    let mut v___x_1219_: usize = 0;
    let mut v___x_1220_: usize = 0;
    let mut v___x_1221_: u8 = 0;
    let mut v_isSharedCheck_1222_: u8 = 0;
    let mut v_a_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1226_: u8 = 0;
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1230_: u8 = 0;
    let mut v_decl_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1239_: u8 = 0;
    let mut v___y_1241_: u8 = 0;
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1244_: u8 = 0;
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut v_unused_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: usize = 0;
    let mut v___x_1258_: usize = 0;
    let mut v___x_1259_: u8 = 0;
    let mut v___x_1260_: usize = 0;
    let mut v___x_1261_: usize = 0;
    let mut v___x_1262_: u8 = 0;
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut v_a_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_decl_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1280_: u8 = 0;
    let mut v___y_1282_: u8 = 0;
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1285_: u8 = 0;
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut v_unused_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: usize = 0;
    let mut v___x_1299_: usize = 0;
    let mut v___x_1300_: u8 = 0;
    let mut v___x_1301_: usize = 0;
    let mut v___x_1302_: usize = 0;
    let mut v___x_1303_: u8 = 0;
    let mut v_isSharedCheck_1304_: u8 = 0;
    let mut v_a_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1308_: u8 = 0;
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1312_: u8 = 0;
    let mut v_cases_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1320_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1327_: usize = 0;
    let mut v___x_1328_: usize = 0;
    let mut v___x_1329_: u8 = 0;
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1342_: u8 = 0;
    let mut v_unused_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1347_: u8 = 0;
    let mut v_a_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1351_: u8 = 0;
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_isSharedCheck_1356_: u8 = 0;
    let mut v_fvarId_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1365_: u8 = 0;
    let mut v___x_1366_: usize = 0;
    let mut v___x_1367_: usize = 0;
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1371_: u8 = 0;
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut v_unused_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1386_: u8 = 0;
    let mut v_fvarId_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1395_: u8 = 0;
    let mut v___x_1396_: usize = 0;
    let mut v___x_1397_: usize = 0;
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1408_: u8 = 0;
    let mut v_unused_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1416_: u8 = 0;
    let mut v_fvarId_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1427_: u8 = 0;
    let mut v___x_1428_: usize = 0;
    let mut v___x_1429_: usize = 0;
    let mut v___x_1430_: u8 = 0;
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1433_: u8 = 0;
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1440_: u8 = 0;
    let mut v_unused_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1450_: u8 = 0;
    let mut v_fvarId_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v___x_1459_: usize = 0;
    let mut v___x_1460_: usize = 0;
    let mut v___x_1461_: u8 = 0;
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1464_: u8 = 0;
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut v_unused_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1478_: u8 = 0;
    let mut v_fvarId_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1481_: u8 = 0;
    let mut v_persistent_1482_: u8 = 0;
    let mut v_k_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v___x_1489_: usize = 0;
    let mut v___x_1490_: usize = 0;
    let mut v___x_1491_: u8 = 0;
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1494_: u8 = 0;
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_unused_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut v_fvarId_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1511_: u8 = 0;
    let mut v_persistent_1512_: u8 = 0;
    let mut v_objs_x3f_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1519_: u8 = 0;
    let mut v___x_1520_: usize = 0;
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1525_: u8 = 0;
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1532_: u8 = 0;
    let mut v_unused_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1540_: u8 = 0;
    let mut v_fvarId_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1547_: u8 = 0;
    let mut v___x_1548_: usize = 0;
    let mut v___x_1549_: usize = 0;
    let mut v___x_1550_: u8 = 0;
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1553_: u8 = 0;
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_unused_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1566_: u8 = 0;
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_1183_) {
                0 => {
                    v_decl_1190_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                    v_k_1191_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                    crate::leanh::lean_inc_ref(v_decl_1190_);
                    v___x_1192_ = l_Lean_Compiler_LCNF_LetDecl_applyRenaming___redArg(
                        v_pu_1182_,
                        v_decl_1190_,
                        v_r_1184_,
                        v_a_1186_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1192_) == 0 {
                        v_a_1193_ = crate::leanh::lean_ctor_get(v___x_1192_, 0);
                        crate::leanh::lean_inc(v_a_1193_);
                        crate::leanh::lean_dec_ref_known(v___x_1192_, 1);
                        crate::leanh::lean_inc_ref(v_k_1191_);
                        v___x_1194_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                            v_pu_1182_, v_k_1191_, v_r_1184_, v_a_1185_, v_a_1186_, v_a_1187_,
                            v_a_1188_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1194_) == 0 {
                            v_a_1195_ = crate::leanh::lean_ctor_get(v___x_1194_, 0);
                            v_isSharedCheck_1222_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1194_)) as u8;
                            if v_isSharedCheck_1222_ == 0 {
                                v___x_1197_ = v___x_1194_;
                                v_isShared_1198_ = v_isSharedCheck_1222_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1195_);
                                crate::leanh::lean_dec(v___x_1194_);
                                v___x_1197_ = crate::leanh::lean_box(0);
                                v_isShared_1198_ = v_isSharedCheck_1222_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1193_);
                            crate::leanh::lean_dec_ref_known(v_code_1183_, 2);
                            return v___x_1194_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1183_, 2);
                        v_a_1223_ = crate::leanh::lean_ctor_get(v___x_1192_, 0);
                        v_isSharedCheck_1230_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1192_)) as u8;
                        if v_isSharedCheck_1230_ == 0 {
                            v___x_1225_ = v___x_1192_;
                            v_isShared_1226_ = v_isSharedCheck_1230_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1223_);
                            crate::leanh::lean_dec(v___x_1192_);
                            v___x_1225_ = crate::leanh::lean_box(0);
                            v_isShared_1226_ = v_isSharedCheck_1230_;
                            state = 7;
                            continue;
                        }
                    }
                }
                1 => {
                    v_decl_1231_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                    v_k_1232_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                    crate::leanh::lean_inc_ref(v_decl_1231_);
                    v___x_1233_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(
                        v_pu_1182_,
                        v_decl_1231_,
                        v_r_1184_,
                        v_a_1185_,
                        v_a_1186_,
                        v_a_1187_,
                        v_a_1188_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1233_) == 0 {
                        v_a_1234_ = crate::leanh::lean_ctor_get(v___x_1233_, 0);
                        crate::leanh::lean_inc(v_a_1234_);
                        crate::leanh::lean_dec_ref_known(v___x_1233_, 1);
                        crate::leanh::lean_inc_ref(v_k_1232_);
                        v___x_1235_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                            v_pu_1182_, v_k_1232_, v_r_1184_, v_a_1185_, v_a_1186_, v_a_1187_,
                            v_a_1188_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1235_) == 0 {
                            v_a_1236_ = crate::leanh::lean_ctor_get(v___x_1235_, 0);
                            v_isSharedCheck_1263_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1235_)) as u8;
                            if v_isSharedCheck_1263_ == 0 {
                                v___x_1238_ = v___x_1235_;
                                v_isShared_1239_ = v_isSharedCheck_1263_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1236_);
                                crate::leanh::lean_dec(v___x_1235_);
                                v___x_1238_ = crate::leanh::lean_box(0);
                                v_isShared_1239_ = v_isSharedCheck_1263_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1234_);
                            crate::leanh::lean_dec_ref_known(v_code_1183_, 2);
                            return v___x_1235_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1183_, 2);
                        v_a_1264_ = crate::leanh::lean_ctor_get(v___x_1233_, 0);
                        v_isSharedCheck_1271_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1233_)) as u8;
                        if v_isSharedCheck_1271_ == 0 {
                            v___x_1266_ = v___x_1233_;
                            v_isShared_1267_ = v_isSharedCheck_1271_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1264_);
                            crate::leanh::lean_dec(v___x_1233_);
                            v___x_1266_ = crate::leanh::lean_box(0);
                            v_isShared_1267_ = v_isSharedCheck_1271_;
                            state = 15;
                            continue;
                        }
                    }
                }
                2 => {
                    v_decl_1272_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                    v_k_1273_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                    crate::leanh::lean_inc_ref(v_decl_1272_);
                    v___x_1274_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(
                        v_pu_1182_,
                        v_decl_1272_,
                        v_r_1184_,
                        v_a_1185_,
                        v_a_1186_,
                        v_a_1187_,
                        v_a_1188_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1274_) == 0 {
                        v_a_1275_ = crate::leanh::lean_ctor_get(v___x_1274_, 0);
                        crate::leanh::lean_inc(v_a_1275_);
                        crate::leanh::lean_dec_ref_known(v___x_1274_, 1);
                        crate::leanh::lean_inc_ref(v_k_1273_);
                        v___x_1276_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                            v_pu_1182_, v_k_1273_, v_r_1184_, v_a_1185_, v_a_1186_, v_a_1187_,
                            v_a_1188_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1276_) == 0 {
                            v_a_1277_ = crate::leanh::lean_ctor_get(v___x_1276_, 0);
                            v_isSharedCheck_1304_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1276_)) as u8;
                            if v_isSharedCheck_1304_ == 0 {
                                v___x_1279_ = v___x_1276_;
                                v_isShared_1280_ = v_isSharedCheck_1304_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1277_);
                                crate::leanh::lean_dec(v___x_1276_);
                                v___x_1279_ = crate::leanh::lean_box(0);
                                v_isShared_1280_ = v_isSharedCheck_1304_;
                                state = 17;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1275_);
                            crate::leanh::lean_dec_ref_known(v_code_1183_, 2);
                            return v___x_1276_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1183_, 2);
                        v_a_1305_ = crate::leanh::lean_ctor_get(v___x_1274_, 0);
                        v_isSharedCheck_1312_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1274_)) as u8;
                        if v_isSharedCheck_1312_ == 0 {
                            v___x_1307_ = v___x_1274_;
                            v_isShared_1308_ = v_isSharedCheck_1312_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1305_);
                            crate::leanh::lean_dec(v___x_1274_);
                            v___x_1307_ = crate::leanh::lean_box(0);
                            v_isShared_1308_ = v_isSharedCheck_1312_;
                            state = 23;
                            continue;
                        }
                    }
                }
                4 => {
                    v_cases_1313_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                    crate::leanh::lean_inc_ref(v_cases_1313_);
                    v_typeName_1314_ = crate::leanh::lean_ctor_get(v_cases_1313_, 0);
                    v_resultType_1315_ = crate::leanh::lean_ctor_get(v_cases_1313_, 1);
                    v_discr_1316_ = crate::leanh::lean_ctor_get(v_cases_1313_, 2);
                    v_alts_1317_ = crate::leanh::lean_ctor_get(v_cases_1313_, 3);
                    v_isSharedCheck_1356_ = (!crate::leanh::lean_is_exclusive(v_cases_1313_)) as u8;
                    if v_isSharedCheck_1356_ == 0 {
                        v___x_1319_ = v_cases_1313_;
                        v_isShared_1320_ = v_isSharedCheck_1356_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_alts_1317_);
                        crate::leanh::lean_inc(v_discr_1316_);
                        crate::leanh::lean_inc(v_resultType_1315_);
                        crate::leanh::lean_inc(v_typeName_1314_);
                        crate::leanh::lean_dec(v_cases_1313_);
                        v___x_1319_ = crate::leanh::lean_box(0);
                        v_isShared_1320_ = v_isSharedCheck_1356_;
                        state = 25;
                        continue;
                    }
                }
                7 => {
                    v_fvarId_1357_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                    v_i_1358_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                    v_y_1359_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                    v_k_1360_ = crate::leanh::lean_ctor_get(v_code_1183_, 3);
                    crate::leanh::lean_inc_ref(v_k_1360_);
                    v___x_1361_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                        v_pu_1182_, v_k_1360_, v_r_1184_, v_a_1185_, v_a_1186_, v_a_1187_,
                        v_a_1188_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1361_) == 0 {
                        v_a_1362_ = crate::leanh::lean_ctor_get(v___x_1361_, 0);
                        v_isSharedCheck_1386_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1361_)) as u8;
                        if v_isSharedCheck_1386_ == 0 {
                            v___x_1364_ = v___x_1361_;
                            v_isShared_1365_ = v_isSharedCheck_1386_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1362_);
                            crate::leanh::lean_dec(v___x_1361_);
                            v___x_1364_ = crate::leanh::lean_box(0);
                            v_isShared_1365_ = v_isSharedCheck_1386_;
                            state = 34;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1183_, 4);
                        return v___x_1361_;
                    }
                }
                8 => {
                    v_fvarId_1387_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                    v_i_1388_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                    v_y_1389_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                    v_k_1390_ = crate::leanh::lean_ctor_get(v_code_1183_, 3);
                    crate::leanh::lean_inc_ref(v_k_1390_);
                    v___x_1391_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                        v_pu_1182_, v_k_1390_, v_r_1184_, v_a_1185_, v_a_1186_, v_a_1187_,
                        v_a_1188_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1391_) == 0 {
                        v_a_1392_ = crate::leanh::lean_ctor_get(v___x_1391_, 0);
                        v_isSharedCheck_1416_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1391_)) as u8;
                        if v_isSharedCheck_1416_ == 0 {
                            v___x_1394_ = v___x_1391_;
                            v_isShared_1395_ = v_isSharedCheck_1416_;
                            state = 39;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1392_);
                            crate::leanh::lean_dec(v___x_1391_);
                            v___x_1394_ = crate::leanh::lean_box(0);
                            v_isShared_1395_ = v_isSharedCheck_1416_;
                            state = 39;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1183_, 4);
                        return v___x_1391_;
                    }
                }
                9 => {
                    v_fvarId_1417_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                    v_i_1418_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                    v_offset_1419_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                    v_y_1420_ = crate::leanh::lean_ctor_get(v_code_1183_, 3);
                    v_ty_1421_ = crate::leanh::lean_ctor_get(v_code_1183_, 4);
                    v_k_1422_ = crate::leanh::lean_ctor_get(v_code_1183_, 5);
                    crate::leanh::lean_inc_ref(v_k_1422_);
                    v___x_1423_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                        v_pu_1182_, v_k_1422_, v_r_1184_, v_a_1185_, v_a_1186_, v_a_1187_,
                        v_a_1188_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1423_) == 0 {
                        v_a_1424_ = crate::leanh::lean_ctor_get(v___x_1423_, 0);
                        v_isSharedCheck_1450_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1423_)) as u8;
                        if v_isSharedCheck_1450_ == 0 {
                            v___x_1426_ = v___x_1423_;
                            v_isShared_1427_ = v_isSharedCheck_1450_;
                            state = 44;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1424_);
                            crate::leanh::lean_dec(v___x_1423_);
                            v___x_1426_ = crate::leanh::lean_box(0);
                            v_isShared_1427_ = v_isSharedCheck_1450_;
                            state = 44;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1183_, 6);
                        return v___x_1423_;
                    }
                }
                10 => {
                    v_fvarId_1451_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                    v_cidx_1452_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                    v_k_1453_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                    crate::leanh::lean_inc_ref(v_k_1453_);
                    v___x_1454_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                        v_pu_1182_, v_k_1453_, v_r_1184_, v_a_1185_, v_a_1186_, v_a_1187_,
                        v_a_1188_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1454_) == 0 {
                        v_a_1455_ = crate::leanh::lean_ctor_get(v___x_1454_, 0);
                        v_isSharedCheck_1478_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1454_)) as u8;
                        if v_isSharedCheck_1478_ == 0 {
                            v___x_1457_ = v___x_1454_;
                            v_isShared_1458_ = v_isSharedCheck_1478_;
                            state = 49;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1455_);
                            crate::leanh::lean_dec(v___x_1454_);
                            v___x_1457_ = crate::leanh::lean_box(0);
                            v_isShared_1458_ = v_isSharedCheck_1478_;
                            state = 49;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1183_, 3);
                        return v___x_1454_;
                    }
                }
                11 => {
                    v_fvarId_1479_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                    v_n_1480_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                    v_check_1481_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_1183_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_1482_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_1183_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_1483_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                    crate::leanh::lean_inc_ref(v_k_1483_);
                    v___x_1484_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                        v_pu_1182_, v_k_1483_, v_r_1184_, v_a_1185_, v_a_1186_, v_a_1187_,
                        v_a_1188_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1484_) == 0 {
                        v_a_1485_ = crate::leanh::lean_ctor_get(v___x_1484_, 0);
                        v_isSharedCheck_1508_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1484_)) as u8;
                        if v_isSharedCheck_1508_ == 0 {
                            v___x_1487_ = v___x_1484_;
                            v_isShared_1488_ = v_isSharedCheck_1508_;
                            state = 54;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1485_);
                            crate::leanh::lean_dec(v___x_1484_);
                            v___x_1487_ = crate::leanh::lean_box(0);
                            v_isShared_1488_ = v_isSharedCheck_1508_;
                            state = 54;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1183_, 3);
                        return v___x_1484_;
                    }
                }
                12 => {
                    v_fvarId_1509_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                    v_n_1510_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                    v_check_1511_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_1183_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_persistent_1512_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_1183_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_1513_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                    v_k_1514_ = crate::leanh::lean_ctor_get(v_code_1183_, 3);
                    crate::leanh::lean_inc_ref(v_k_1514_);
                    v___x_1515_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                        v_pu_1182_, v_k_1514_, v_r_1184_, v_a_1185_, v_a_1186_, v_a_1187_,
                        v_a_1188_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1515_) == 0 {
                        v_a_1516_ = crate::leanh::lean_ctor_get(v___x_1515_, 0);
                        v_isSharedCheck_1540_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1515_)) as u8;
                        if v_isSharedCheck_1540_ == 0 {
                            v___x_1518_ = v___x_1515_;
                            v_isShared_1519_ = v_isSharedCheck_1540_;
                            state = 59;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1516_);
                            crate::leanh::lean_dec(v___x_1515_);
                            v___x_1518_ = crate::leanh::lean_box(0);
                            v_isShared_1519_ = v_isSharedCheck_1540_;
                            state = 59;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1183_, 4);
                        return v___x_1515_;
                    }
                }
                13 => {
                    v_fvarId_1541_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                    v_k_1542_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                    crate::leanh::lean_inc_ref(v_k_1542_);
                    v___x_1543_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                        v_pu_1182_, v_k_1542_, v_r_1184_, v_a_1185_, v_a_1186_, v_a_1187_,
                        v_a_1188_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1543_) == 0 {
                        v_a_1544_ = crate::leanh::lean_ctor_get(v___x_1543_, 0);
                        v_isSharedCheck_1566_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1543_)) as u8;
                        if v_isSharedCheck_1566_ == 0 {
                            v___x_1546_ = v___x_1543_;
                            v_isShared_1547_ = v_isSharedCheck_1566_;
                            state = 64;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1544_);
                            crate::leanh::lean_dec(v___x_1543_);
                            v___x_1546_ = crate::leanh::lean_box(0);
                            v_isShared_1547_ = v_isSharedCheck_1566_;
                            state = 64;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1183_, 2);
                        return v___x_1543_;
                    }
                }
                _ => {
                    v___x_1567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1567_, 0, v_code_1183_);
                    return v___x_1567_;
                }
            },
            1 => {
                v___x_1216_ = lean_ptr_addr(v_k_1191_);
                v___x_1217_ = lean_ptr_addr(v_a_1195_);
                v___x_1218_ = lean_usize_dec_eq(v___x_1216_, v___x_1217_);
                if v___x_1218_ == 0 {
                    v___y_1200_ = v___x_1218_;
                    state = 2;
                    continue;
                } else {
                    v___x_1219_ = lean_ptr_addr(v_decl_1190_);
                    v___x_1220_ = lean_ptr_addr(v_a_1193_);
                    v___x_1221_ = lean_usize_dec_eq(v___x_1219_, v___x_1220_);
                    v___y_1200_ = v___x_1221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_1200_ == 0 {
                    v_isSharedCheck_1210_ = (!crate::leanh::lean_is_exclusive(v_code_1183_)) as u8;
                    if v_isSharedCheck_1210_ == 0 {
                        v_unused_1211_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                        crate::leanh::lean_dec(v_unused_1211_);
                        v_unused_1212_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                        crate::leanh::lean_dec(v_unused_1212_);
                        v___x_1202_ = v_code_1183_;
                        v_isShared_1203_ = v_isSharedCheck_1210_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1183_);
                        v___x_1202_ = crate::leanh::lean_box(0);
                        v_isShared_1203_ = v_isSharedCheck_1210_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1195_);
                    crate::leanh::lean_dec(v_a_1193_);
                    if v_isShared_1198_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1197_, 0, v_code_1183_);
                        v___x_1214_ = v___x_1197_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1215_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_code_1183_);
                        v___x_1214_ = v_reuseFailAlloc_1215_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1203_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1202_, 1, v_a_1195_);
                    crate::leanh::lean_ctor_set(v___x_1202_, 0, v_a_1193_);
                    v___x_1205_ = v___x_1202_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1209_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_a_1195_);
                    v___x_1205_ = v_reuseFailAlloc_1209_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1198_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1197_, 0, v___x_1205_);
                    v___x_1207_ = v___x_1197_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
                    v___x_1207_ = v_reuseFailAlloc_1208_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1207_;
            }
            6 => {
                return v___x_1214_;
            }
            7 => {
                if v_isShared_1226_ == 0 {
                    v___x_1228_ = v___x_1225_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1229_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
                    v___x_1228_ = v_reuseFailAlloc_1229_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1228_;
            }
            9 => {
                v___x_1257_ = lean_ptr_addr(v_k_1232_);
                v___x_1258_ = lean_ptr_addr(v_a_1236_);
                v___x_1259_ = lean_usize_dec_eq(v___x_1257_, v___x_1258_);
                if v___x_1259_ == 0 {
                    v___y_1241_ = v___x_1259_;
                    state = 10;
                    continue;
                } else {
                    v___x_1260_ = lean_ptr_addr(v_decl_1231_);
                    v___x_1261_ = lean_ptr_addr(v_a_1234_);
                    v___x_1262_ = lean_usize_dec_eq(v___x_1260_, v___x_1261_);
                    v___y_1241_ = v___x_1262_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1241_ == 0 {
                    v_isSharedCheck_1251_ = (!crate::leanh::lean_is_exclusive(v_code_1183_)) as u8;
                    if v_isSharedCheck_1251_ == 0 {
                        v_unused_1252_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                        crate::leanh::lean_dec(v_unused_1252_);
                        v_unused_1253_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                        crate::leanh::lean_dec(v_unused_1253_);
                        v___x_1243_ = v_code_1183_;
                        v_isShared_1244_ = v_isSharedCheck_1251_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1183_);
                        v___x_1243_ = crate::leanh::lean_box(0);
                        v_isShared_1244_ = v_isSharedCheck_1251_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1236_);
                    crate::leanh::lean_dec(v_a_1234_);
                    if v_isShared_1239_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1238_, 0, v_code_1183_);
                        v___x_1255_ = v___x_1238_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1256_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_code_1183_);
                        v___x_1255_ = v_reuseFailAlloc_1256_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_1244_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1243_, 1, v_a_1236_);
                    crate::leanh::lean_ctor_set(v___x_1243_, 0, v_a_1234_);
                    v___x_1246_ = v___x_1243_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1234_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_a_1236_);
                    v___x_1246_ = v_reuseFailAlloc_1250_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1239_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1238_, 0, v___x_1246_);
                    v___x_1248_ = v___x_1238_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1249_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
                    v___x_1248_ = v_reuseFailAlloc_1249_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1248_;
            }
            14 => {
                return v___x_1255_;
            }
            15 => {
                if v_isShared_1267_ == 0 {
                    v___x_1269_ = v___x_1266_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
                    v___x_1269_ = v_reuseFailAlloc_1270_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1269_;
            }
            17 => {
                v___x_1298_ = lean_ptr_addr(v_k_1273_);
                v___x_1299_ = lean_ptr_addr(v_a_1277_);
                v___x_1300_ = lean_usize_dec_eq(v___x_1298_, v___x_1299_);
                if v___x_1300_ == 0 {
                    v___y_1282_ = v___x_1300_;
                    state = 18;
                    continue;
                } else {
                    v___x_1301_ = lean_ptr_addr(v_decl_1272_);
                    v___x_1302_ = lean_ptr_addr(v_a_1275_);
                    v___x_1303_ = lean_usize_dec_eq(v___x_1301_, v___x_1302_);
                    v___y_1282_ = v___x_1303_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v___y_1282_ == 0 {
                    v_isSharedCheck_1292_ = (!crate::leanh::lean_is_exclusive(v_code_1183_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v_unused_1293_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                        crate::leanh::lean_dec(v_unused_1293_);
                        v_unused_1294_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                        crate::leanh::lean_dec(v_unused_1294_);
                        v___x_1284_ = v_code_1183_;
                        v_isShared_1285_ = v_isSharedCheck_1292_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1183_);
                        v___x_1284_ = crate::leanh::lean_box(0);
                        v_isShared_1285_ = v_isSharedCheck_1292_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1277_);
                    crate::leanh::lean_dec(v_a_1275_);
                    if v_isShared_1280_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1279_, 0, v_code_1183_);
                        v___x_1296_ = v___x_1279_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_1297_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_code_1183_);
                        v___x_1296_ = v_reuseFailAlloc_1297_;
                        state = 22;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_1285_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1284_, 1, v_a_1277_);
                    crate::leanh::lean_ctor_set(v___x_1284_, 0, v_a_1275_);
                    v___x_1287_ = v___x_1284_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_a_1277_);
                    v___x_1287_ = v_reuseFailAlloc_1291_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1280_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1279_, 0, v___x_1287_);
                    v___x_1289_ = v___x_1279_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
                    v___x_1289_ = v_reuseFailAlloc_1290_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1289_;
            }
            22 => {
                return v___x_1296_;
            }
            23 => {
                if v_isShared_1308_ == 0 {
                    v___x_1310_ = v___x_1307_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
                    v___x_1310_ = v_reuseFailAlloc_1311_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1310_;
            }
            25 => {
                v___x_1321_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_alts_1317_);
                v___x_1322_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(v_pu_1182_, v_r_1184_, v___x_1321_, v_alts_1317_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
                if crate::leanh::lean_obj_tag(v___x_1322_) == 0 {
                    v_a_1323_ = crate::leanh::lean_ctor_get(v___x_1322_, 0);
                    v_isSharedCheck_1347_ = (!crate::leanh::lean_is_exclusive(v___x_1322_)) as u8;
                    if v_isSharedCheck_1347_ == 0 {
                        v___x_1325_ = v___x_1322_;
                        v_isShared_1326_ = v_isSharedCheck_1347_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1323_);
                        crate::leanh::lean_dec(v___x_1322_);
                        v___x_1325_ = crate::leanh::lean_box(0);
                        v_isShared_1326_ = v_isSharedCheck_1347_;
                        state = 26;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1319_);
                    crate::leanh::lean_dec_ref(v_alts_1317_);
                    crate::leanh::lean_dec(v_discr_1316_);
                    crate::leanh::lean_dec_ref(v_resultType_1315_);
                    crate::leanh::lean_dec(v_typeName_1314_);
                    crate::leanh::lean_dec_ref_known(v_code_1183_, 1);
                    v_a_1348_ = crate::leanh::lean_ctor_get(v___x_1322_, 0);
                    v_isSharedCheck_1355_ = (!crate::leanh::lean_is_exclusive(v___x_1322_)) as u8;
                    if v_isSharedCheck_1355_ == 0 {
                        v___x_1350_ = v___x_1322_;
                        v_isShared_1351_ = v_isSharedCheck_1355_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1348_);
                        crate::leanh::lean_dec(v___x_1322_);
                        v___x_1350_ = crate::leanh::lean_box(0);
                        v_isShared_1351_ = v_isSharedCheck_1355_;
                        state = 32;
                        continue;
                    }
                }
            }
            26 => {
                v___x_1327_ = lean_ptr_addr(v_alts_1317_);
                crate::leanh::lean_dec_ref(v_alts_1317_);
                v___x_1328_ = lean_ptr_addr(v_a_1323_);
                v___x_1329_ = lean_usize_dec_eq(v___x_1327_, v___x_1328_);
                if v___x_1329_ == 0 {
                    v_isSharedCheck_1342_ = (!crate::leanh::lean_is_exclusive(v_code_1183_)) as u8;
                    if v_isSharedCheck_1342_ == 0 {
                        v_unused_1343_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                        crate::leanh::lean_dec(v_unused_1343_);
                        v___x_1331_ = v_code_1183_;
                        v_isShared_1332_ = v_isSharedCheck_1342_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1183_);
                        v___x_1331_ = crate::leanh::lean_box(0);
                        v_isShared_1332_ = v_isSharedCheck_1342_;
                        state = 27;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1323_);
                    crate::leanh::lean_del_object(v___x_1319_);
                    crate::leanh::lean_dec(v_discr_1316_);
                    crate::leanh::lean_dec_ref(v_resultType_1315_);
                    crate::leanh::lean_dec(v_typeName_1314_);
                    if v_isShared_1326_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1325_, 0, v_code_1183_);
                        v___x_1345_ = v___x_1325_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1346_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_code_1183_);
                        v___x_1345_ = v_reuseFailAlloc_1346_;
                        state = 31;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_1320_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1319_, 3, v_a_1323_);
                    v___x_1334_ = v___x_1319_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1341_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_typeName_1314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_resultType_1315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_discr_1316_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_a_1323_);
                    v___x_1334_ = v_reuseFailAlloc_1341_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_1332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1331_, 0, v___x_1334_);
                    v___x_1336_ = v___x_1331_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1340_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1334_);
                    v___x_1336_ = v_reuseFailAlloc_1340_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_1326_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1325_, 0, v___x_1336_);
                    v___x_1338_ = v___x_1325_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1339_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
                    v___x_1338_ = v_reuseFailAlloc_1339_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_1338_;
            }
            31 => {
                return v___x_1345_;
            }
            32 => {
                if v_isShared_1351_ == 0 {
                    v___x_1353_ = v___x_1350_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1354_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
                    v___x_1353_ = v_reuseFailAlloc_1354_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1353_;
            }
            34 => {
                v___x_1366_ = lean_ptr_addr(v_k_1360_);
                v___x_1367_ = lean_ptr_addr(v_a_1362_);
                v___x_1368_ = lean_usize_dec_eq(v___x_1366_, v___x_1367_);
                if v___x_1368_ == 0 {
                    crate::leanh::lean_inc(v_y_1359_);
                    crate::leanh::lean_inc(v_i_1358_);
                    crate::leanh::lean_inc(v_fvarId_1357_);
                    v_isSharedCheck_1378_ = (!crate::leanh::lean_is_exclusive(v_code_1183_)) as u8;
                    if v_isSharedCheck_1378_ == 0 {
                        v_unused_1379_ = crate::leanh::lean_ctor_get(v_code_1183_, 3);
                        crate::leanh::lean_dec(v_unused_1379_);
                        v_unused_1380_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                        crate::leanh::lean_dec(v_unused_1380_);
                        v_unused_1381_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                        crate::leanh::lean_dec(v_unused_1381_);
                        v_unused_1382_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                        crate::leanh::lean_dec(v_unused_1382_);
                        v___x_1370_ = v_code_1183_;
                        v_isShared_1371_ = v_isSharedCheck_1378_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1183_);
                        v___x_1370_ = crate::leanh::lean_box(0);
                        v_isShared_1371_ = v_isSharedCheck_1378_;
                        state = 35;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1362_);
                    if v_isShared_1365_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1364_, 0, v_code_1183_);
                        v___x_1384_ = v___x_1364_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_1385_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_code_1183_);
                        v___x_1384_ = v_reuseFailAlloc_1385_;
                        state = 38;
                        continue;
                    }
                }
            }
            35 => {
                if v_isShared_1371_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1370_, 3, v_a_1362_);
                    v___x_1373_ = v___x_1370_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = crate::leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_fvarId_1357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_i_1358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_y_1359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_a_1362_);
                    v___x_1373_ = v_reuseFailAlloc_1377_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_1365_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1364_, 0, v___x_1373_);
                    v___x_1375_ = v___x_1364_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
                    v___x_1375_ = v_reuseFailAlloc_1376_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1375_;
            }
            38 => {
                return v___x_1384_;
            }
            39 => {
                v___x_1396_ = lean_ptr_addr(v_k_1390_);
                v___x_1397_ = lean_ptr_addr(v_a_1392_);
                v___x_1398_ = lean_usize_dec_eq(v___x_1396_, v___x_1397_);
                if v___x_1398_ == 0 {
                    crate::leanh::lean_inc(v_y_1389_);
                    crate::leanh::lean_inc(v_i_1388_);
                    crate::leanh::lean_inc(v_fvarId_1387_);
                    v_isSharedCheck_1408_ = (!crate::leanh::lean_is_exclusive(v_code_1183_)) as u8;
                    if v_isSharedCheck_1408_ == 0 {
                        v_unused_1409_ = crate::leanh::lean_ctor_get(v_code_1183_, 3);
                        crate::leanh::lean_dec(v_unused_1409_);
                        v_unused_1410_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                        crate::leanh::lean_dec(v_unused_1410_);
                        v_unused_1411_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                        crate::leanh::lean_dec(v_unused_1411_);
                        v_unused_1412_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                        crate::leanh::lean_dec(v_unused_1412_);
                        v___x_1400_ = v_code_1183_;
                        v_isShared_1401_ = v_isSharedCheck_1408_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1183_);
                        v___x_1400_ = crate::leanh::lean_box(0);
                        v_isShared_1401_ = v_isSharedCheck_1408_;
                        state = 40;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1392_);
                    if v_isShared_1395_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1394_, 0, v_code_1183_);
                        v___x_1414_ = v___x_1394_;
                        state = 43;
                        continue;
                    } else {
                        v_reuseFailAlloc_1415_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_code_1183_);
                        v___x_1414_ = v_reuseFailAlloc_1415_;
                        state = 43;
                        continue;
                    }
                }
            }
            40 => {
                if v_isShared_1401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1400_, 3, v_a_1392_);
                    v___x_1403_ = v___x_1400_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1407_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_fvarId_1387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_i_1388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_y_1389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1407_, 3, v_a_1392_);
                    v___x_1403_ = v_reuseFailAlloc_1407_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_1395_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1394_, 0, v___x_1403_);
                    v___x_1405_ = v___x_1394_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_1406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
                    v___x_1405_ = v_reuseFailAlloc_1406_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_1405_;
            }
            43 => {
                return v___x_1414_;
            }
            44 => {
                v___x_1428_ = lean_ptr_addr(v_k_1422_);
                v___x_1429_ = lean_ptr_addr(v_a_1424_);
                v___x_1430_ = lean_usize_dec_eq(v___x_1428_, v___x_1429_);
                if v___x_1430_ == 0 {
                    crate::leanh::lean_inc_ref(v_ty_1421_);
                    crate::leanh::lean_inc(v_y_1420_);
                    crate::leanh::lean_inc(v_offset_1419_);
                    crate::leanh::lean_inc(v_i_1418_);
                    crate::leanh::lean_inc(v_fvarId_1417_);
                    v_isSharedCheck_1440_ = (!crate::leanh::lean_is_exclusive(v_code_1183_)) as u8;
                    if v_isSharedCheck_1440_ == 0 {
                        v_unused_1441_ = crate::leanh::lean_ctor_get(v_code_1183_, 5);
                        crate::leanh::lean_dec(v_unused_1441_);
                        v_unused_1442_ = crate::leanh::lean_ctor_get(v_code_1183_, 4);
                        crate::leanh::lean_dec(v_unused_1442_);
                        v_unused_1443_ = crate::leanh::lean_ctor_get(v_code_1183_, 3);
                        crate::leanh::lean_dec(v_unused_1443_);
                        v_unused_1444_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                        crate::leanh::lean_dec(v_unused_1444_);
                        v_unused_1445_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                        crate::leanh::lean_dec(v_unused_1445_);
                        v_unused_1446_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                        crate::leanh::lean_dec(v_unused_1446_);
                        v___x_1432_ = v_code_1183_;
                        v_isShared_1433_ = v_isSharedCheck_1440_;
                        state = 45;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1183_);
                        v___x_1432_ = crate::leanh::lean_box(0);
                        v_isShared_1433_ = v_isSharedCheck_1440_;
                        state = 45;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1424_);
                    if v_isShared_1427_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1426_, 0, v_code_1183_);
                        v___x_1448_ = v___x_1426_;
                        state = 48;
                        continue;
                    } else {
                        v_reuseFailAlloc_1449_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_code_1183_);
                        v___x_1448_ = v_reuseFailAlloc_1449_;
                        state = 48;
                        continue;
                    }
                }
            }
            45 => {
                if v_isShared_1433_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1432_, 5, v_a_1424_);
                    v___x_1435_ = v___x_1432_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_1439_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_fvarId_1417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_i_1418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_offset_1419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 3, v_y_1420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 4, v_ty_1421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 5, v_a_1424_);
                    v___x_1435_ = v_reuseFailAlloc_1439_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_1427_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1435_);
                    v___x_1437_ = v___x_1426_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_1438_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
                    v___x_1437_ = v_reuseFailAlloc_1438_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_1437_;
            }
            48 => {
                return v___x_1448_;
            }
            49 => {
                v___x_1459_ = lean_ptr_addr(v_k_1453_);
                v___x_1460_ = lean_ptr_addr(v_a_1455_);
                v___x_1461_ = lean_usize_dec_eq(v___x_1459_, v___x_1460_);
                if v___x_1461_ == 0 {
                    crate::leanh::lean_inc(v_cidx_1452_);
                    crate::leanh::lean_inc(v_fvarId_1451_);
                    v_isSharedCheck_1471_ = (!crate::leanh::lean_is_exclusive(v_code_1183_)) as u8;
                    if v_isSharedCheck_1471_ == 0 {
                        v_unused_1472_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                        crate::leanh::lean_dec(v_unused_1472_);
                        v_unused_1473_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                        crate::leanh::lean_dec(v_unused_1473_);
                        v_unused_1474_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                        crate::leanh::lean_dec(v_unused_1474_);
                        v___x_1463_ = v_code_1183_;
                        v_isShared_1464_ = v_isSharedCheck_1471_;
                        state = 50;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1183_);
                        v___x_1463_ = crate::leanh::lean_box(0);
                        v_isShared_1464_ = v_isSharedCheck_1471_;
                        state = 50;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1455_);
                    if v_isShared_1458_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1457_, 0, v_code_1183_);
                        v___x_1476_ = v___x_1457_;
                        state = 53;
                        continue;
                    } else {
                        v_reuseFailAlloc_1477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_code_1183_);
                        v___x_1476_ = v_reuseFailAlloc_1477_;
                        state = 53;
                        continue;
                    }
                }
            }
            50 => {
                if v_isShared_1464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1463_, 2, v_a_1455_);
                    v___x_1466_ = v___x_1463_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = crate::leanh::lean_alloc_ctor(10, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_fvarId_1451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_cidx_1452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_a_1455_);
                    v___x_1466_ = v_reuseFailAlloc_1470_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                if v_isShared_1458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1457_, 0, v___x_1466_);
                    v___x_1468_ = v___x_1457_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_1469_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
                    v___x_1468_ = v_reuseFailAlloc_1469_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_1468_;
            }
            53 => {
                return v___x_1476_;
            }
            54 => {
                v___x_1489_ = lean_ptr_addr(v_k_1483_);
                v___x_1490_ = lean_ptr_addr(v_a_1485_);
                v___x_1491_ = lean_usize_dec_eq(v___x_1489_, v___x_1490_);
                if v___x_1491_ == 0 {
                    crate::leanh::lean_inc(v_n_1480_);
                    crate::leanh::lean_inc(v_fvarId_1479_);
                    v_isSharedCheck_1501_ = (!crate::leanh::lean_is_exclusive(v_code_1183_)) as u8;
                    if v_isSharedCheck_1501_ == 0 {
                        v_unused_1502_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                        crate::leanh::lean_dec(v_unused_1502_);
                        v_unused_1503_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                        crate::leanh::lean_dec(v_unused_1503_);
                        v_unused_1504_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                        crate::leanh::lean_dec(v_unused_1504_);
                        v___x_1493_ = v_code_1183_;
                        v_isShared_1494_ = v_isSharedCheck_1501_;
                        state = 55;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1183_);
                        v___x_1493_ = crate::leanh::lean_box(0);
                        v_isShared_1494_ = v_isSharedCheck_1501_;
                        state = 55;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1485_);
                    if v_isShared_1488_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1487_, 0, v_code_1183_);
                        v___x_1506_ = v___x_1487_;
                        state = 58;
                        continue;
                    } else {
                        v_reuseFailAlloc_1507_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_code_1183_);
                        v___x_1506_ = v_reuseFailAlloc_1507_;
                        state = 58;
                        continue;
                    }
                }
            }
            55 => {
                if v_isShared_1494_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1493_, 2, v_a_1485_);
                    v___x_1496_ = v___x_1493_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = crate::leanh::lean_alloc_ctor(11, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_fvarId_1479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_n_1480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_a_1485_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1500_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_check_1481_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1500_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_persistent_1482_,
                    );
                    v___x_1496_ = v_reuseFailAlloc_1500_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                if v_isShared_1488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1487_, 0, v___x_1496_);
                    v___x_1498_ = v___x_1487_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_1499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
                    v___x_1498_ = v_reuseFailAlloc_1499_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_1498_;
            }
            58 => {
                return v___x_1506_;
            }
            59 => {
                v___x_1520_ = lean_ptr_addr(v_k_1514_);
                v___x_1521_ = lean_ptr_addr(v_a_1516_);
                v___x_1522_ = lean_usize_dec_eq(v___x_1520_, v___x_1521_);
                if v___x_1522_ == 0 {
                    crate::leanh::lean_inc(v_objs_x3f_1513_);
                    crate::leanh::lean_inc(v_n_1510_);
                    crate::leanh::lean_inc(v_fvarId_1509_);
                    v_isSharedCheck_1532_ = (!crate::leanh::lean_is_exclusive(v_code_1183_)) as u8;
                    if v_isSharedCheck_1532_ == 0 {
                        v_unused_1533_ = crate::leanh::lean_ctor_get(v_code_1183_, 3);
                        crate::leanh::lean_dec(v_unused_1533_);
                        v_unused_1534_ = crate::leanh::lean_ctor_get(v_code_1183_, 2);
                        crate::leanh::lean_dec(v_unused_1534_);
                        v_unused_1535_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                        crate::leanh::lean_dec(v_unused_1535_);
                        v_unused_1536_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                        crate::leanh::lean_dec(v_unused_1536_);
                        v___x_1524_ = v_code_1183_;
                        v_isShared_1525_ = v_isSharedCheck_1532_;
                        state = 60;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1183_);
                        v___x_1524_ = crate::leanh::lean_box(0);
                        v_isShared_1525_ = v_isSharedCheck_1532_;
                        state = 60;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1516_);
                    if v_isShared_1519_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1518_, 0, v_code_1183_);
                        v___x_1538_ = v___x_1518_;
                        state = 63;
                        continue;
                    } else {
                        v_reuseFailAlloc_1539_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_code_1183_);
                        v___x_1538_ = v_reuseFailAlloc_1539_;
                        state = 63;
                        continue;
                    }
                }
            }
            60 => {
                if v_isShared_1525_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1524_, 3, v_a_1516_);
                    v___x_1527_ = v___x_1524_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_1531_ = crate::leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_fvarId_1509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_n_1510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_objs_x3f_1513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_a_1516_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1531_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_check_1511_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1531_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_1512_,
                    );
                    v___x_1527_ = v_reuseFailAlloc_1531_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                if v_isShared_1519_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1518_, 0, v___x_1527_);
                    v___x_1529_ = v___x_1518_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_1530_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
                    v___x_1529_ = v_reuseFailAlloc_1530_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_1529_;
            }
            63 => {
                return v___x_1538_;
            }
            64 => {
                v___x_1548_ = lean_ptr_addr(v_k_1542_);
                v___x_1549_ = lean_ptr_addr(v_a_1544_);
                v___x_1550_ = lean_usize_dec_eq(v___x_1548_, v___x_1549_);
                if v___x_1550_ == 0 {
                    crate::leanh::lean_inc(v_fvarId_1541_);
                    v_isSharedCheck_1560_ = (!crate::leanh::lean_is_exclusive(v_code_1183_)) as u8;
                    if v_isSharedCheck_1560_ == 0 {
                        v_unused_1561_ = crate::leanh::lean_ctor_get(v_code_1183_, 1);
                        crate::leanh::lean_dec(v_unused_1561_);
                        v_unused_1562_ = crate::leanh::lean_ctor_get(v_code_1183_, 0);
                        crate::leanh::lean_dec(v_unused_1562_);
                        v___x_1552_ = v_code_1183_;
                        v_isShared_1553_ = v_isSharedCheck_1560_;
                        state = 65;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1183_);
                        v___x_1552_ = crate::leanh::lean_box(0);
                        v_isShared_1553_ = v_isSharedCheck_1560_;
                        state = 65;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1544_);
                    if v_isShared_1547_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1546_, 0, v_code_1183_);
                        v___x_1564_ = v___x_1546_;
                        state = 68;
                        continue;
                    } else {
                        v_reuseFailAlloc_1565_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_code_1183_);
                        v___x_1564_ = v_reuseFailAlloc_1565_;
                        state = 68;
                        continue;
                    }
                }
            }
            65 => {
                if v_isShared_1553_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1552_, 1, v_a_1544_);
                    v___x_1555_ = v___x_1552_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = crate::leanh::lean_alloc_ctor(13, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_fvarId_1541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_a_1544_);
                    v___x_1555_ = v_reuseFailAlloc_1559_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                if v_isShared_1547_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1546_, 0, v___x_1555_);
                    v___x_1557_ = v___x_1546_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
                    v___x_1557_ = v_reuseFailAlloc_1558_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_1557_;
            }
            68 => {
                return v___x_1564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_applyRenaming(
    mut v_pu_1568_: u8,
    mut v_decl_1569_: *mut crate::leanh::LeanObject,
    mut v_r_1570_: *mut crate::leanh::LeanObject,
    mut v_a_1571_: *mut crate::leanh::LeanObject,
    mut v_a_1572_: *mut crate::leanh::LeanObject,
    mut v_a_1573_: *mut crate::leanh::LeanObject,
    mut v_a_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v_val_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1590_: u8 = 0;
    let mut v_decl_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_reuseFailAlloc_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1610_: u8 = 0;
    let mut v_isSharedCheck_1611_: u8 = 0;
    let mut v_unused_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_1576_ = crate::leanh::lean_ctor_get(v_decl_1569_, 0);
                v_params_1577_ = crate::leanh::lean_ctor_get(v_decl_1569_, 2);
                crate::leanh::lean_inc_ref(v_params_1577_);
                v_type_1578_ = crate::leanh::lean_ctor_get(v_decl_1569_, 3);
                crate::leanh::lean_inc_ref(v_type_1578_);
                v_value_1579_ = crate::leanh::lean_ctor_get(v_decl_1569_, 4);
                v___x_1580_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Param_applyRenaming_spec__0___redArg(v_r_1570_, v_fvarId_1576_);
                if crate::leanh::lean_obj_tag(v___x_1580_) == 1 {
                    crate::leanh::lean_inc_ref(v_value_1579_);
                    crate::leanh::lean_inc(v_fvarId_1576_);
                    v_isSharedCheck_1611_ = (!crate::leanh::lean_is_exclusive(v_decl_1569_)) as u8;
                    if v_isSharedCheck_1611_ == 0 {
                        v_unused_1612_ = crate::leanh::lean_ctor_get(v_decl_1569_, 4);
                        crate::leanh::lean_dec(v_unused_1612_);
                        v_unused_1613_ = crate::leanh::lean_ctor_get(v_decl_1569_, 3);
                        crate::leanh::lean_dec(v_unused_1613_);
                        v_unused_1614_ = crate::leanh::lean_ctor_get(v_decl_1569_, 2);
                        crate::leanh::lean_dec(v_unused_1614_);
                        v_unused_1615_ = crate::leanh::lean_ctor_get(v_decl_1569_, 1);
                        crate::leanh::lean_dec(v_unused_1615_);
                        v_unused_1616_ = crate::leanh::lean_ctor_get(v_decl_1569_, 0);
                        crate::leanh::lean_dec(v_unused_1616_);
                        v___x_1582_ = v_decl_1569_;
                        v_isShared_1583_ = v_isSharedCheck_1611_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_decl_1569_);
                        v___x_1582_ = crate::leanh::lean_box(0);
                        v_isShared_1583_ = v_isSharedCheck_1611_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1580_);
                    crate::leanh::lean_inc_ref(v_value_1579_);
                    v___x_1617_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                        v_pu_1568_,
                        v_value_1579_,
                        v_r_1570_,
                        v_a_1571_,
                        v_a_1572_,
                        v_a_1573_,
                        v_a_1574_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1617_) == 0 {
                        v_a_1618_ = crate::leanh::lean_ctor_get(v___x_1617_, 0);
                        crate::leanh::lean_inc(v_a_1618_);
                        crate::leanh::lean_dec_ref_known(v___x_1617_, 1);
                        v___x_1619_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_1568_, v_decl_1569_, v_type_1578_, v_params_1577_, v_a_1618_, v_a_1572_);
                        return v___x_1619_;
                    } else {
                        crate::leanh::lean_dec_ref(v_type_1578_);
                        crate::leanh::lean_dec_ref(v_params_1577_);
                        crate::leanh::lean_dec_ref(v_decl_1569_);
                        v_a_1620_ = crate::leanh::lean_ctor_get(v___x_1617_, 0);
                        v_isSharedCheck_1627_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1617_)) as u8;
                        if v_isSharedCheck_1627_ == 0 {
                            v___x_1622_ = v___x_1617_;
                            v_isShared_1623_ = v_isSharedCheck_1627_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1620_);
                            crate::leanh::lean_dec(v___x_1617_);
                            v___x_1622_ = crate::leanh::lean_box(0);
                            v_isShared_1623_ = v_isSharedCheck_1627_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_val_1584_ = crate::leanh::lean_ctor_get(v___x_1580_, 0);
                crate::leanh::lean_inc(v_val_1584_);
                crate::leanh::lean_dec_ref_known(v___x_1580_, 1);
                v___x_1585_ = lean_st_ref_take(v_a_1572_);
                v_lctx_1586_ = crate::leanh::lean_ctor_get(v___x_1585_, 0);
                v_nextIdx_1587_ = crate::leanh::lean_ctor_get(v___x_1585_, 1);
                v_isSharedCheck_1610_ = (!crate::leanh::lean_is_exclusive(v___x_1585_)) as u8;
                if v_isSharedCheck_1610_ == 0 {
                    v___x_1589_ = v___x_1585_;
                    v_isShared_1590_ = v_isSharedCheck_1610_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_1587_);
                    crate::leanh::lean_inc(v_lctx_1586_);
                    crate::leanh::lean_dec(v___x_1585_);
                    v___x_1589_ = crate::leanh::lean_box(0);
                    v_isShared_1590_ = v_isSharedCheck_1610_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_value_1579_);
                crate::leanh::lean_inc_ref(v_type_1578_);
                crate::leanh::lean_inc_ref(v_params_1577_);
                if v_isShared_1583_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1582_, 1, v_val_1584_);
                    v_decl_1592_ = v___x_1582_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1609_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_fvarId_1576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_val_1584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_params_1577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_type_1578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 4, v_value_1579_);
                    v_decl_1592_ = v_reuseFailAlloc_1609_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_decl_1592_);
                v___x_1593_ =
                    l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_1568_, v_lctx_1586_, v_decl_1592_);
                if v_isShared_1590_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1589_, 0, v___x_1593_);
                    v___x_1595_ = v___x_1589_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1608_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_nextIdx_1587_);
                    v___x_1595_ = v_reuseFailAlloc_1608_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1596_ = lean_st_ref_set(v_a_1572_, v___x_1595_);
                v___x_1597_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                    v_pu_1568_,
                    v_value_1579_,
                    v_r_1570_,
                    v_a_1571_,
                    v_a_1572_,
                    v_a_1573_,
                    v_a_1574_,
                );
                if crate::leanh::lean_obj_tag(v___x_1597_) == 0 {
                    v_a_1598_ = crate::leanh::lean_ctor_get(v___x_1597_, 0);
                    crate::leanh::lean_inc(v_a_1598_);
                    crate::leanh::lean_dec_ref_known(v___x_1597_, 1);
                    v___x_1599_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_1568_, v_decl_1592_, v_type_1578_, v_params_1577_, v_a_1598_, v_a_1572_);
                    return v___x_1599_;
                } else {
                    crate::leanh::lean_dec_ref(v_decl_1592_);
                    crate::leanh::lean_dec_ref(v_type_1578_);
                    crate::leanh::lean_dec_ref(v_params_1577_);
                    v_a_1600_ = crate::leanh::lean_ctor_get(v___x_1597_, 0);
                    v_isSharedCheck_1607_ = (!crate::leanh::lean_is_exclusive(v___x_1597_)) as u8;
                    if v_isSharedCheck_1607_ == 0 {
                        v___x_1602_ = v___x_1597_;
                        v_isShared_1603_ = v_isSharedCheck_1607_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1600_);
                        crate::leanh::lean_dec(v___x_1597_);
                        v___x_1602_ = crate::leanh::lean_box(0);
                        v_isShared_1603_ = v_isSharedCheck_1607_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1603_ == 0 {
                    v___x_1605_ = v___x_1602_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
                    v___x_1605_ = v_reuseFailAlloc_1606_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1605_;
            }
            7 => {
                if v_isShared_1623_ == 0 {
                    v___x_1625_ = v___x_1622_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
                    v___x_1625_ = v_reuseFailAlloc_1626_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_applyRenaming___boxed(
    mut v_pu_1628_: *mut crate::leanh::LeanObject,
    mut v_decl_1629_: *mut crate::leanh::LeanObject,
    mut v_r_1630_: *mut crate::leanh::LeanObject,
    mut v_a_1631_: *mut crate::leanh::LeanObject,
    mut v_a_1632_: *mut crate::leanh::LeanObject,
    mut v_a_1633_: *mut crate::leanh::LeanObject,
    mut v_a_1634_: *mut crate::leanh::LeanObject,
    mut v_a_1635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1636_: u8 = 0;
    let mut v_res_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1636_ = (crate::leanh::lean_unbox(v_pu_1628_) as u8);
    v_res_1637_ = l_Lean_Compiler_LCNF_FunDecl_applyRenaming(
        v_pu_boxed_1636_,
        v_decl_1629_,
        v_r_1630_,
        v_a_1631_,
        v_a_1632_,
        v_a_1633_,
        v_a_1634_,
    );
    crate::leanh::lean_dec(v_a_1634_);
    crate::leanh::lean_dec_ref(v_a_1633_);
    crate::leanh::lean_dec(v_a_1632_);
    crate::leanh::lean_dec_ref(v_a_1631_);
    crate::leanh::lean_dec(v_r_1630_);
    return v_res_1637_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2___boxed(
    mut v_pu_1638_: *mut crate::leanh::LeanObject,
    mut v_r_1639_: *mut crate::leanh::LeanObject,
    mut v_i_1640_: *mut crate::leanh::LeanObject,
    mut v_as_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1647_: u8 = 0;
    let mut v_res_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1647_ = (crate::leanh::lean_unbox(v_pu_1638_) as u8);
    v_res_1648_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__2(v_pu_boxed_1647_, v_r_1639_, v_i_1640_, v_as_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
    crate::leanh::lean_dec(v___y_1645_);
    crate::leanh::lean_dec_ref(v___y_1644_);
    crate::leanh::lean_dec(v___y_1643_);
    crate::leanh::lean_dec_ref(v___y_1642_);
    crate::leanh::lean_dec(v_r_1639_);
    return v_res_1648_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_applyRenaming___boxed(
    mut v_pu_1649_: *mut crate::leanh::LeanObject,
    mut v_code_1650_: *mut crate::leanh::LeanObject,
    mut v_r_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
    mut v_a_1654_: *mut crate::leanh::LeanObject,
    mut v_a_1655_: *mut crate::leanh::LeanObject,
    mut v_a_1656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1657_: u8 = 0;
    let mut v_res_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1657_ = (crate::leanh::lean_unbox(v_pu_1649_) as u8);
    v_res_1658_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
        v_pu_boxed_1657_,
        v_code_1650_,
        v_r_1651_,
        v_a_1652_,
        v_a_1653_,
        v_a_1654_,
        v_a_1655_,
    );
    crate::leanh::lean_dec(v_a_1655_);
    crate::leanh::lean_dec_ref(v_a_1654_);
    crate::leanh::lean_dec(v_a_1653_);
    crate::leanh::lean_dec_ref(v_a_1652_);
    crate::leanh::lean_dec(v_r_1651_);
    return v_res_1658_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(
    mut v_pu_1659_: u8,
    mut v_r_1660_: *mut crate::leanh::LeanObject,
    mut v_i_1661_: *mut crate::leanh::LeanObject,
    mut v_as_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1668_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_1659_, v_r_1660_, v_i_1661_, v_as_1662_, v___y_1664_);
    return v___x_1668_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___boxed(
    mut v_pu_1669_: *mut crate::leanh::LeanObject,
    mut v_r_1670_: *mut crate::leanh::LeanObject,
    mut v_i_1671_: *mut crate::leanh::LeanObject,
    mut v_as_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1678_: u8 = 0;
    let mut v_res_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1678_ = (crate::leanh::lean_unbox(v_pu_1669_) as u8);
    v_res_1679_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1(v_pu_boxed_1678_, v_r_1670_, v_i_1671_, v_as_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
    crate::leanh::lean_dec(v___y_1676_);
    crate::leanh::lean_dec_ref(v___y_1675_);
    crate::leanh::lean_dec(v___y_1674_);
    crate::leanh::lean_dec_ref(v___y_1673_);
    crate::leanh::lean_dec(v_r_1670_);
    return v_res_1679_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(
    mut v_f_1680_: *mut crate::leanh::LeanObject,
    mut v_v_1681_: *mut crate::leanh::LeanObject,
    mut v___y_1682_: *mut crate::leanh::LeanObject,
    mut v___y_1683_: *mut crate::leanh::LeanObject,
    mut v___y_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1690_: u8 = 0;
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1695_: u8 = 0;
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1702_: u8 = 0;
    let mut v_a_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1706_: u8 = 0;
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1710_: u8 = 0;
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_1681_) == 0 {
                    v_code_1687_ = crate::leanh::lean_ctor_get(v_v_1681_, 0);
                    v_isSharedCheck_1711_ = (!crate::leanh::lean_is_exclusive(v_v_1681_)) as u8;
                    if v_isSharedCheck_1711_ == 0 {
                        v___x_1689_ = v_v_1681_;
                        v_isShared_1690_ = v_isSharedCheck_1711_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_1687_);
                        crate::leanh::lean_dec(v_v_1681_);
                        v___x_1689_ = crate::leanh::lean_box(0);
                        v_isShared_1690_ = v_isSharedCheck_1711_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_1680_);
                    v___x_1712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1712_, 0, v_v_1681_);
                    return v___x_1712_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_1685_);
                crate::leanh::lean_inc_ref(v___y_1684_);
                crate::leanh::lean_inc(v___y_1683_);
                crate::leanh::lean_inc_ref(v___y_1682_);
                v___x_1691_ = crate::leanh::lean_apply_6(
                    v_f_1680_,
                    v_code_1687_,
                    v___y_1682_,
                    v___y_1683_,
                    v___y_1684_,
                    v___y_1685_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1691_) == 0 {
                    v_a_1692_ = crate::leanh::lean_ctor_get(v___x_1691_, 0);
                    v_isSharedCheck_1702_ = (!crate::leanh::lean_is_exclusive(v___x_1691_)) as u8;
                    if v_isSharedCheck_1702_ == 0 {
                        v___x_1694_ = v___x_1691_;
                        v_isShared_1695_ = v_isSharedCheck_1702_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1692_);
                        crate::leanh::lean_dec(v___x_1691_);
                        v___x_1694_ = crate::leanh::lean_box(0);
                        v_isShared_1695_ = v_isSharedCheck_1702_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1689_);
                    v_a_1703_ = crate::leanh::lean_ctor_get(v___x_1691_, 0);
                    v_isSharedCheck_1710_ = (!crate::leanh::lean_is_exclusive(v___x_1691_)) as u8;
                    if v_isSharedCheck_1710_ == 0 {
                        v___x_1705_ = v___x_1691_;
                        v_isShared_1706_ = v_isSharedCheck_1710_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1703_);
                        crate::leanh::lean_dec(v___x_1691_);
                        v___x_1705_ = crate::leanh::lean_box(0);
                        v_isShared_1706_ = v_isSharedCheck_1710_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1689_, 0, v_a_1692_);
                    v___x_1697_ = v___x_1689_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1701_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1692_);
                    v___x_1697_ = v_reuseFailAlloc_1701_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1695_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1694_, 0, v___x_1697_);
                    v___x_1699_ = v___x_1694_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
                    v___x_1699_ = v_reuseFailAlloc_1700_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1699_;
            }
            5 => {
                if v_isShared_1706_ == 0 {
                    v___x_1708_ = v___x_1705_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
                    v___x_1708_ = v_reuseFailAlloc_1709_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg___boxed(
    mut v_f_1713_: *mut crate::leanh::LeanObject,
    mut v_v_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v_f_1713_, v_v_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
    crate::leanh::lean_dec(v___y_1718_);
    crate::leanh::lean_dec_ref(v___y_1717_);
    crate::leanh::lean_dec(v___y_1716_);
    crate::leanh::lean_dec_ref(v___y_1715_);
    return v_res_1720_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(
    mut v_pu_1721_: u8,
    mut v_f_1722_: *mut crate::leanh::LeanObject,
    mut v_v_1723_: *mut crate::leanh::LeanObject,
    mut v___y_1724_: *mut crate::leanh::LeanObject,
    mut v___y_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1729_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v_f_1722_, v_v_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
    return v___x_1729_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___boxed(
    mut v_pu_1730_: *mut crate::leanh::LeanObject,
    mut v_f_1731_: *mut crate::leanh::LeanObject,
    mut v_v_1732_: *mut crate::leanh::LeanObject,
    mut v___y_1733_: *mut crate::leanh::LeanObject,
    mut v___y_1734_: *mut crate::leanh::LeanObject,
    mut v___y_1735_: *mut crate::leanh::LeanObject,
    mut v___y_1736_: *mut crate::leanh::LeanObject,
    mut v___y_1737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1738_: u8 = 0;
    let mut v_res_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1738_ = (crate::leanh::lean_unbox(v_pu_1730_) as u8);
    v_res_1739_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0(v_pu_boxed_1738_, v_f_1731_, v_v_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
    crate::leanh::lean_dec(v___y_1736_);
    crate::leanh::lean_dec_ref(v___y_1735_);
    crate::leanh::lean_dec(v___y_1734_);
    crate::leanh::lean_dec_ref(v___y_1733_);
    return v_res_1739_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(
    mut v_pu_1740_: u8,
    mut v_r_1741_: *mut crate::leanh::LeanObject,
    mut v_x_1742_: *mut crate::leanh::LeanObject,
    mut v___y_1743_: *mut crate::leanh::LeanObject,
    mut v___y_1744_: *mut crate::leanh::LeanObject,
    mut v___y_1745_: *mut crate::leanh::LeanObject,
    mut v___y_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
        v_pu_1740_,
        v_x_1742_,
        v_r_1741_,
        v___y_1743_,
        v___y_1744_,
        v___y_1745_,
        v___y_1746_,
    );
    return v___x_1748_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed(
    mut v_pu_1749_: *mut crate::leanh::LeanObject,
    mut v_r_1750_: *mut crate::leanh::LeanObject,
    mut v_x_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
    mut v___y_1754_: *mut crate::leanh::LeanObject,
    mut v___y_1755_: *mut crate::leanh::LeanObject,
    mut v___y_1756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1757_: u8 = 0;
    let mut v_res_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1757_ = (crate::leanh::lean_unbox(v_pu_1749_) as u8);
    v_res_1758_ = l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0(
        v_pu_boxed_1757_,
        v_r_1750_,
        v_x_1751_,
        v___y_1752_,
        v___y_1753_,
        v___y_1754_,
        v___y_1755_,
    );
    crate::leanh::lean_dec(v___y_1755_);
    crate::leanh::lean_dec_ref(v___y_1754_);
    crate::leanh::lean_dec(v___y_1753_);
    crate::leanh::lean_dec_ref(v___y_1752_);
    crate::leanh::lean_dec(v_r_1750_);
    return v_res_1758_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_applyRenaming(
    mut v_pu_1759_: u8,
    mut v_decl_1760_: *mut crate::leanh::LeanObject,
    mut v_r_1761_: *mut crate::leanh::LeanObject,
    mut v_a_1762_: *mut crate::leanh::LeanObject,
    mut v_a_1763_: *mut crate::leanh::LeanObject,
    mut v_a_1764_: *mut crate::leanh::LeanObject,
    mut v_a_1765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_1769_: u8 = 0;
    let mut v_inlineAttr_x3f_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1773_: u8 = 0;
    let mut v_name_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_1778_: u8 = 0;
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1781_: u8 = 0;
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_a_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut v_a_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1813_: u8 = 0;
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1817_: u8 = 0;
    let mut v_isSharedCheck_1818_: u8 = 0;
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_r_1761_) == 0 {
                    v_toSignature_1767_ = crate::leanh::lean_ctor_get(v_decl_1760_, 0);
                    v_value_1768_ = crate::leanh::lean_ctor_get(v_decl_1760_, 1);
                    v_recursive_1769_ = crate::leanh::lean_ctor_get_uint8(
                        v_decl_1760_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_inlineAttr_x3f_1770_ = crate::leanh::lean_ctor_get(v_decl_1760_, 2);
                    v_isSharedCheck_1819_ = (!crate::leanh::lean_is_exclusive(v_decl_1760_)) as u8;
                    if v_isSharedCheck_1819_ == 0 {
                        v___x_1772_ = v_decl_1760_;
                        v_isShared_1773_ = v_isSharedCheck_1819_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_inlineAttr_x3f_1770_);
                        crate::leanh::lean_inc(v_value_1768_);
                        crate::leanh::lean_inc(v_toSignature_1767_);
                        crate::leanh::lean_dec(v_decl_1760_);
                        v___x_1772_ = crate::leanh::lean_box(0);
                        v_isShared_1773_ = v_isSharedCheck_1819_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1820_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1820_, 0, v_decl_1760_);
                    return v___x_1820_;
                }
            }
            1 => {
                v_name_1774_ = crate::leanh::lean_ctor_get(v_toSignature_1767_, 0);
                v_levelParams_1775_ = crate::leanh::lean_ctor_get(v_toSignature_1767_, 1);
                v_type_1776_ = crate::leanh::lean_ctor_get(v_toSignature_1767_, 2);
                v_params_1777_ = crate::leanh::lean_ctor_get(v_toSignature_1767_, 3);
                v_safe_1778_ = crate::leanh::lean_ctor_get_uint8(
                    v_toSignature_1767_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_1818_ =
                    (!crate::leanh::lean_is_exclusive(v_toSignature_1767_)) as u8;
                if v_isSharedCheck_1818_ == 0 {
                    v___x_1780_ = v_toSignature_1767_;
                    v_isShared_1781_ = v_isSharedCheck_1818_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_params_1777_);
                    crate::leanh::lean_inc(v_type_1776_);
                    crate::leanh::lean_inc(v_levelParams_1775_);
                    crate::leanh::lean_inc(v_name_1774_);
                    crate::leanh::lean_dec(v_toSignature_1767_);
                    v___x_1780_ = crate::leanh::lean_box(0);
                    v_isShared_1781_ = v_isSharedCheck_1818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1782_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1783_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Code_applyRenaming_spec__1___redArg(v_pu_1759_, v_r_1761_, v___x_1782_, v_params_1777_, v_a_1763_);
                if crate::leanh::lean_obj_tag(v___x_1783_) == 0 {
                    v_a_1784_ = crate::leanh::lean_ctor_get(v___x_1783_, 0);
                    crate::leanh::lean_inc(v_a_1784_);
                    crate::leanh::lean_dec_ref_known(v___x_1783_, 1);
                    v___x_1785_ = crate::leanh::lean_box((v_pu_1759_) as usize);
                    v___f_1786_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Compiler_LCNF_Decl_applyRenaming___lam__0___boxed
                            as *mut core::ffi::c_void,
                        8,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1786_, 0, v___x_1785_);
                    crate::leanh::lean_closure_set(v___f_1786_, 1, v_r_1761_);
                    v___x_1787_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_applyRenaming_spec__0___redArg(v___f_1786_, v_value_1768_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
                    if crate::leanh::lean_obj_tag(v___x_1787_) == 0 {
                        v_a_1788_ = crate::leanh::lean_ctor_get(v___x_1787_, 0);
                        v_isSharedCheck_1801_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1787_)) as u8;
                        if v_isSharedCheck_1801_ == 0 {
                            v___x_1790_ = v___x_1787_;
                            v_isShared_1791_ = v_isSharedCheck_1801_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1788_);
                            crate::leanh::lean_dec(v___x_1787_);
                            v___x_1790_ = crate::leanh::lean_box(0);
                            v_isShared_1791_ = v_isSharedCheck_1801_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1784_);
                        crate::leanh::lean_del_object(v___x_1780_);
                        crate::leanh::lean_dec_ref(v_type_1776_);
                        crate::leanh::lean_dec(v_levelParams_1775_);
                        crate::leanh::lean_dec(v_name_1774_);
                        crate::leanh::lean_del_object(v___x_1772_);
                        crate::leanh::lean_dec(v_inlineAttr_x3f_1770_);
                        v_a_1802_ = crate::leanh::lean_ctor_get(v___x_1787_, 0);
                        v_isSharedCheck_1809_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1787_)) as u8;
                        if v_isSharedCheck_1809_ == 0 {
                            v___x_1804_ = v___x_1787_;
                            v_isShared_1805_ = v_isSharedCheck_1809_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1802_);
                            crate::leanh::lean_dec(v___x_1787_);
                            v___x_1804_ = crate::leanh::lean_box(0);
                            v_isShared_1805_ = v_isSharedCheck_1809_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1780_);
                    crate::leanh::lean_dec_ref(v_type_1776_);
                    crate::leanh::lean_dec(v_levelParams_1775_);
                    crate::leanh::lean_dec(v_name_1774_);
                    crate::leanh::lean_del_object(v___x_1772_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_1770_);
                    crate::leanh::lean_dec_ref(v_value_1768_);
                    crate::leanh::lean_dec_ref_known(v_r_1761_, 5);
                    v_a_1810_ = crate::leanh::lean_ctor_get(v___x_1783_, 0);
                    v_isSharedCheck_1817_ = (!crate::leanh::lean_is_exclusive(v___x_1783_)) as u8;
                    if v_isSharedCheck_1817_ == 0 {
                        v___x_1812_ = v___x_1783_;
                        v_isShared_1813_ = v_isSharedCheck_1817_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1810_);
                        crate::leanh::lean_dec(v___x_1783_);
                        v___x_1812_ = crate::leanh::lean_box(0);
                        v_isShared_1813_ = v_isSharedCheck_1817_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1781_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1780_, 3, v_a_1784_);
                    v___x_1793_ = v___x_1780_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_name_1774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_levelParams_1775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 2, v_type_1776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 3, v_a_1784_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1800_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_safe_1778_,
                    );
                    v___x_1793_ = v_reuseFailAlloc_1800_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1773_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1772_, 1, v_a_1788_);
                    crate::leanh::lean_ctor_set(v___x_1772_, 0, v___x_1793_);
                    v___x_1795_ = v___x_1772_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1799_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_a_1788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_inlineAttr_x3f_1770_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1799_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_1769_,
                    );
                    v___x_1795_ = v_reuseFailAlloc_1799_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1791_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1790_, 0, v___x_1795_);
                    v___x_1797_ = v___x_1790_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1798_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
                    v___x_1797_ = v_reuseFailAlloc_1798_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1797_;
            }
            7 => {
                if v_isShared_1805_ == 0 {
                    v___x_1807_ = v___x_1804_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
                    v___x_1807_ = v_reuseFailAlloc_1808_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1807_;
            }
            9 => {
                if v_isShared_1813_ == 0 {
                    v___x_1815_ = v___x_1812_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
                    v___x_1815_ = v_reuseFailAlloc_1816_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_applyRenaming___boxed(
    mut v_pu_1821_: *mut crate::leanh::LeanObject,
    mut v_decl_1822_: *mut crate::leanh::LeanObject,
    mut v_r_1823_: *mut crate::leanh::LeanObject,
    mut v_a_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
    mut v_a_1828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1829_: u8 = 0;
    let mut v_res_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1829_ = (crate::leanh::lean_unbox(v_pu_1821_) as u8);
    v_res_1830_ = l_Lean_Compiler_LCNF_Decl_applyRenaming(
        v_pu_boxed_1829_,
        v_decl_1822_,
        v_r_1823_,
        v_a_1824_,
        v_a_1825_,
        v_a_1826_,
        v_a_1827_,
    );
    crate::leanh::lean_dec(v_a_1827_);
    crate::leanh::lean_dec_ref(v_a_1826_);
    crate::leanh::lean_dec(v_a_1825_);
    crate::leanh::lean_dec_ref(v_a_1824_);
    return v_res_1830_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Renaming(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Renaming(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Renaming(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Renaming(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Renaming(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Renaming(builtin);
}
