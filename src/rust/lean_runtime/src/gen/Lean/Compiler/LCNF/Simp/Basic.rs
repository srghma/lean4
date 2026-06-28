// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Basic
// Imports: Lean.Compiler.LCNF.CompilerM
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg,
    l_Lean_Compiler_LCNF_findLetValue_x3f___redArg,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_get_size, lean_nat_dec_eq};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(
    mut v_pu_56_: u8,
    mut v_fvarId_57_: *mut LeanObject,
    mut v_a_58_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_61_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_63_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_66_: u8 = 0;
    let mut v___x_68_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_71_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_72_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_73_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_74_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_77_: u8 = 0;
    let mut v_isSharedCheck_79_: u8 = 0;
    let mut v_a_80_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_83_: u8 = 0;
    let mut v___x_85_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_86_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_87_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_60_ =
                    l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_56_, v_fvarId_57_, v_a_58_);
                if lean_obj_tag(v___x_60_) == 0 {
                    v_a_61_ = lean_ctor_get(v___x_60_, 0);
                    lean_inc(v_a_61_);
                    if lean_obj_tag(v_a_61_) == 1 {
                        lean_dec_ref_known(v_a_61_, 1);
                        lean_dec(v_fvarId_57_);
                        return v___x_60_;
                    } else {
                        lean_dec_ref_known(v___x_60_, 1);
                        lean_dec(v_a_61_);
                        v___x_62_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
                            v_pu_56_,
                            v_fvarId_57_,
                            v_a_58_,
                        );
                        lean_dec(v_fvarId_57_);
                        if lean_obj_tag(v___x_62_) == 0 {
                            v_a_63_ = lean_ctor_get(v___x_62_, 0);
                            v_isSharedCheck_79_ = (!lean_is_exclusive(v___x_62_)) as u8;
                            if v_isSharedCheck_79_ == 0 {
                                v___x_65_ = v___x_62_;
                                v_isShared_66_ = v_isSharedCheck_79_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_63_);
                                lean_dec(v___x_62_);
                                v___x_65_ = lean_box(0);
                                v_isShared_66_ = v_isSharedCheck_79_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_80_ = lean_ctor_get(v___x_62_, 0);
                            v_isSharedCheck_87_ = (!lean_is_exclusive(v___x_62_)) as u8;
                            if v_isSharedCheck_87_ == 0 {
                                v___x_82_ = v___x_62_;
                                v_isShared_83_ = v_isSharedCheck_87_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_80_);
                                lean_dec(v___x_62_);
                                v___x_82_ = lean_box(0);
                                v_isShared_83_ = v_isSharedCheck_87_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_fvarId_57_);
                    return v___x_60_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_63_) == 1 {
                    v_val_72_ = lean_ctor_get(v_a_63_, 0);
                    lean_inc(v_val_72_);
                    lean_dec_ref_known(v_a_63_, 1);
                    if lean_obj_tag(v_val_72_) == 4 {
                        v_fvarId_73_ = lean_ctor_get(v_val_72_, 0);
                        lean_inc(v_fvarId_73_);
                        v_args_74_ = lean_ctor_get(v_val_72_, 1);
                        lean_inc_ref(v_args_74_);
                        lean_dec_ref_known(v_val_72_, 2);
                        v___x_75_ = lean_array_get_size(v_args_74_);
                        lean_dec_ref(v_args_74_);
                        v___x_76_ = lean_unsigned_to_nat(0);
                        v___x_77_ = lean_nat_dec_eq(v___x_75_, v___x_76_);
                        if v___x_77_ == 0 {
                            lean_dec(v_fvarId_73_);
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_65_);
                            v_fvarId_57_ = v_fvarId_73_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_72_);
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_63_);
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_68_ = lean_box(0);
                if v_isShared_66_ == 0 {
                    lean_ctor_set(v___x_65_, 0, v___x_68_);
                    v___x_70_ = v___x_65_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
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
                    v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
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
    mut v_pu_88_: *mut LeanObject,
    mut v_fvarId_89_: *mut LeanObject,
    mut v_a_90_: *mut LeanObject,
    mut v_a_91_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_92_: u8 = 0;
    let mut v_res_93_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_92_ = (lean_unbox(v_pu_88_) as u8);
    v_res_93_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(
        v_pu_boxed_92_,
        v_fvarId_89_,
        v_a_90_,
    );
    lean_dec(v_a_90_);
    return v_res_93_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f(
    mut v_pu_94_: u8,
    mut v_fvarId_95_: *mut LeanObject,
    mut v_a_96_: *mut LeanObject,
    mut v_a_97_: *mut LeanObject,
    mut v_a_98_: *mut LeanObject,
    mut v_a_99_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    v___x_101_ =
        l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v_pu_94_, v_fvarId_95_, v_a_97_);
    return v___x_101_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___boxed(
    mut v_pu_102_: *mut LeanObject,
    mut v_fvarId_103_: *mut LeanObject,
    mut v_a_104_: *mut LeanObject,
    mut v_a_105_: *mut LeanObject,
    mut v_a_106_: *mut LeanObject,
    mut v_a_107_: *mut LeanObject,
    mut v_a_108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_109_: u8 = 0;
    let mut v_res_110_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_109_ = (lean_unbox(v_pu_102_) as u8);
    v_res_110_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f(
        v_pu_boxed_109_,
        v_fvarId_103_,
        v_a_104_,
        v_a_105_,
        v_a_106_,
        v_a_107_,
    );
    lean_dec(v_a_107_);
    lean_dec_ref(v_a_106_);
    lean_dec(v_a_105_);
    lean_dec_ref(v_a_104_);
    return v_res_110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
}
