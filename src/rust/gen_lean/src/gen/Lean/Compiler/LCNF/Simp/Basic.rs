// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Basic
// Imports: Lean.Compiler.LCNF.CompilerM
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg,
    l_Lean_Compiler_LCNF_findLetValue_x3f___redArg,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_get_size, lean_nat_dec_eq};
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(
    mut v_pu_56_: u8,
    mut v_fvarId_57_: *mut crate::leanh::LeanObject,
    mut v_a_58_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_66_: u8 = 0;
    let mut v___x_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_77_: u8 = 0;
    let mut v_isSharedCheck_79_: u8 = 0;
    let mut v_a_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_83_: u8 = 0;
    let mut v___x_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_87_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_60_ =
                    l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_56_, v_fvarId_57_, v_a_58_);
                if crate::leanh::lean_obj_tag(v___x_60_) == 0 {
                    v_a_61_ = crate::leanh::lean_ctor_get(v___x_60_, 0);
                    crate::leanh::lean_inc(v_a_61_);
                    if crate::leanh::lean_obj_tag(v_a_61_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_a_61_, 1);
                        crate::leanh::lean_dec(v_fvarId_57_);
                        return v___x_60_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_60_, 1);
                        crate::leanh::lean_dec(v_a_61_);
                        v___x_62_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
                            v_pu_56_,
                            v_fvarId_57_,
                            v_a_58_,
                        );
                        crate::leanh::lean_dec(v_fvarId_57_);
                        if crate::leanh::lean_obj_tag(v___x_62_) == 0 {
                            v_a_63_ = crate::leanh::lean_ctor_get(v___x_62_, 0);
                            v_isSharedCheck_79_ =
                                (!crate::leanh::lean_is_exclusive(v___x_62_)) as u8;
                            if v_isSharedCheck_79_ == 0 {
                                v___x_65_ = v___x_62_;
                                v_isShared_66_ = v_isSharedCheck_79_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_63_);
                                crate::leanh::lean_dec(v___x_62_);
                                v___x_65_ = crate::leanh::lean_box(0);
                                v_isShared_66_ = v_isSharedCheck_79_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_80_ = crate::leanh::lean_ctor_get(v___x_62_, 0);
                            v_isSharedCheck_87_ =
                                (!crate::leanh::lean_is_exclusive(v___x_62_)) as u8;
                            if v_isSharedCheck_87_ == 0 {
                                v___x_82_ = v___x_62_;
                                v_isShared_83_ = v_isSharedCheck_87_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_80_);
                                crate::leanh::lean_dec(v___x_62_);
                                v___x_82_ = crate::leanh::lean_box(0);
                                v_isShared_83_ = v_isSharedCheck_87_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_57_);
                    return v___x_60_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_63_) == 1 {
                    v_val_72_ = crate::leanh::lean_ctor_get(v_a_63_, 0);
                    crate::leanh::lean_inc(v_val_72_);
                    crate::leanh::lean_dec_ref_known(v_a_63_, 1);
                    if crate::leanh::lean_obj_tag(v_val_72_) == 4 {
                        v_fvarId_73_ = crate::leanh::lean_ctor_get(v_val_72_, 0);
                        crate::leanh::lean_inc(v_fvarId_73_);
                        v_args_74_ = crate::leanh::lean_ctor_get(v_val_72_, 1);
                        crate::leanh::lean_inc_ref(v_args_74_);
                        crate::leanh::lean_dec_ref_known(v_val_72_, 2);
                        v___x_75_ = lean_array_get_size(v_args_74_);
                        crate::leanh::lean_dec_ref(v_args_74_);
                        v___x_76_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_77_ = lean_nat_dec_eq(v___x_75_, v___x_76_);
                        if v___x_77_ == 0 {
                            crate::leanh::lean_dec(v_fvarId_73_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_65_);
                            v_fvarId_57_ = v_fvarId_73_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_72_);
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_63_);
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_68_ = crate::leanh::lean_box(0);
                if v_isShared_66_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_65_, 0, v___x_68_);
                    v___x_70_ = v___x_65_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_71_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
                    v___x_70_ = v_reuseFailAlloc_71_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_70_;
            }
            4 => {
                if v_isShared_83_ == 0 {
                    v___x_85_ = v___x_82_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_86_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
                    v___x_85_ = v_reuseFailAlloc_86_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_85_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg___boxed(
    mut v_pu_88_: *mut crate::leanh::LeanObject,
    mut v_fvarId_89_: *mut crate::leanh::LeanObject,
    mut v_a_90_: *mut crate::leanh::LeanObject,
    mut v_a_91_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_92_: u8 = 0;
    let mut v_res_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_92_ = (crate::leanh::lean_unbox(v_pu_88_) as u8);
    v_res_93_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(
        v_pu_boxed_92_,
        v_fvarId_89_,
        v_a_90_,
    );
    crate::leanh::lean_dec(v_a_90_);
    return v_res_93_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f(
    mut v_pu_94_: u8,
    mut v_fvarId_95_: *mut crate::leanh::LeanObject,
    mut v_a_96_: *mut crate::leanh::LeanObject,
    mut v_a_97_: *mut crate::leanh::LeanObject,
    mut v_a_98_: *mut crate::leanh::LeanObject,
    mut v_a_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_101_ =
        l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v_pu_94_, v_fvarId_95_, v_a_97_);
    return v___x_101_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___boxed(
    mut v_pu_102_: *mut crate::leanh::LeanObject,
    mut v_fvarId_103_: *mut crate::leanh::LeanObject,
    mut v_a_104_: *mut crate::leanh::LeanObject,
    mut v_a_105_: *mut crate::leanh::LeanObject,
    mut v_a_106_: *mut crate::leanh::LeanObject,
    mut v_a_107_: *mut crate::leanh::LeanObject,
    mut v_a_108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_109_: u8 = 0;
    let mut v_res_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_109_ = (crate::leanh::lean_unbox(v_pu_102_) as u8);
    v_res_110_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f(
        v_pu_boxed_109_,
        v_fvarId_103_,
        v_a_104_,
        v_a_105_,
        v_a_106_,
        v_a_107_,
    );
    crate::leanh::lean_dec(v_a_107_);
    crate::leanh::lean_dec_ref(v_a_106_);
    crate::leanh::lean_dec(v_a_105_);
    crate::leanh::lean_dec_ref(v_a_104_);
    return v_res_110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(
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
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_Basic(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
}
