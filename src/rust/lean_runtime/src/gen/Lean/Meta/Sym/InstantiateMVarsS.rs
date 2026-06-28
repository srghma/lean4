// Lean compiler output
// Module: Lean.Meta.Sym.InstantiateMVarsS
// Imports: Lean.Meta.Sym.SymM
use crate::r#gen::Lean::Expr::l_Lean_Expr_hasMVar;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, l_Lean_Meta_Sym_shareCommon___redArg,
    runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive,
};
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___redArg(
    mut v_e_70_: *mut LeanObject,
    mut v___y_71_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_73_: u8 = 0;
    let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_76_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_78_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_79_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_80_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_81_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_82_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_83_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_84_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_87_: u8 = 0;
    let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_92_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_93_: u8 = 0;
    let mut v_unused_94_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_73_ = l_Lean_Expr_hasMVar(v_e_70_);
                if v___x_73_ == 0 {
                    v___x_74_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_74_, 0, v_e_70_);
                    return v___x_74_;
                } else {
                    v___x_75_ = lean_st_ref_get(v___y_71_);
                    v_mctx_76_ = lean_ctor_get(v___x_75_, 0);
                    lean_inc_ref(v_mctx_76_);
                    lean_dec(v___x_75_);
                    v___x_77_ = l_Lean_instantiateMVarsCore(v_mctx_76_, v_e_70_);
                    v_fst_78_ = lean_ctor_get(v___x_77_, 0);
                    lean_inc(v_fst_78_);
                    v_snd_79_ = lean_ctor_get(v___x_77_, 1);
                    lean_inc(v_snd_79_);
                    lean_dec_ref(v___x_77_);
                    v___x_80_ = lean_st_ref_take(v___y_71_);
                    v_cache_81_ = lean_ctor_get(v___x_80_, 1);
                    v_zetaDeltaFVarIds_82_ = lean_ctor_get(v___x_80_, 2);
                    v_postponed_83_ = lean_ctor_get(v___x_80_, 3);
                    v_diag_84_ = lean_ctor_get(v___x_80_, 4);
                    v_isSharedCheck_93_ = (!lean_is_exclusive(v___x_80_)) as u8;
                    if v_isSharedCheck_93_ == 0 {
                        v_unused_94_ = lean_ctor_get(v___x_80_, 0);
                        lean_dec(v_unused_94_);
                        v___x_86_ = v___x_80_;
                        v_isShared_87_ = v_isSharedCheck_93_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_84_);
                        lean_inc(v_postponed_83_);
                        lean_inc(v_zetaDeltaFVarIds_82_);
                        lean_inc(v_cache_81_);
                        lean_dec(v___x_80_);
                        v___x_86_ = lean_box(0);
                        v_isShared_87_ = v_isSharedCheck_93_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_87_ == 0 {
                    lean_ctor_set(v___x_86_, 0, v_snd_79_);
                    v___x_89_ = v___x_86_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_92_, 0, v_snd_79_);
                    lean_ctor_set(v_reuseFailAlloc_92_, 1, v_cache_81_);
                    lean_ctor_set(v_reuseFailAlloc_92_, 2, v_zetaDeltaFVarIds_82_);
                    lean_ctor_set(v_reuseFailAlloc_92_, 3, v_postponed_83_);
                    lean_ctor_set(v_reuseFailAlloc_92_, 4, v_diag_84_);
                    v___x_89_ = v_reuseFailAlloc_92_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_90_ = lean_st_ref_set(v___y_71_, v___x_89_);
                v___x_91_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_91_, 0, v_fst_78_);
                return v___x_91_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___redArg___boxed(
    mut v_e_95_: *mut LeanObject,
    mut v___y_96_: *mut LeanObject,
    mut v___y_97_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_98_: *mut LeanObject = core::ptr::null_mut();
    v_res_98_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___redArg(
        v_e_95_, v___y_96_,
    );
    lean_dec(v___y_96_);
    return v_res_98_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0(
    mut v_e_99_: *mut LeanObject,
    mut v___y_100_: *mut LeanObject,
    mut v___y_101_: *mut LeanObject,
    mut v___y_102_: *mut LeanObject,
    mut v___y_103_: *mut LeanObject,
    mut v___y_104_: *mut LeanObject,
    mut v___y_105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    v___x_107_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___redArg(
        v_e_99_, v___y_103_,
    );
    return v___x_107_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___boxed(
    mut v_e_108_: *mut LeanObject,
    mut v___y_109_: *mut LeanObject,
    mut v___y_110_: *mut LeanObject,
    mut v___y_111_: *mut LeanObject,
    mut v___y_112_: *mut LeanObject,
    mut v___y_113_: *mut LeanObject,
    mut v___y_114_: *mut LeanObject,
    mut v___y_115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_116_: *mut LeanObject = core::ptr::null_mut();
    v_res_116_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0(
        v_e_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_,
    );
    lean_dec(v___y_114_);
    lean_dec_ref(v___y_113_);
    lean_dec(v___y_112_);
    lean_dec_ref(v___y_111_);
    lean_dec(v___y_110_);
    lean_dec_ref(v___y_109_);
    return v_res_116_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateMVarsS(
    mut v_e_117_: *mut LeanObject,
    mut v_a_118_: *mut LeanObject,
    mut v_a_119_: *mut LeanObject,
    mut v_a_120_: *mut LeanObject,
    mut v_a_121_: *mut LeanObject,
    mut v_a_122_: *mut LeanObject,
    mut v_a_123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_125_: u8 = 0;
    v___x_125_ = l_Lean_Expr_hasMVar(v_e_117_);
    if v___x_125_ == 0 {
        let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
        v___x_126_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_126_, 0, v_e_117_);
        return v___x_126_;
    } else {
        let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_128_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
        v___x_127_ =
            l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___redArg(
                v_e_117_, v_a_121_,
            );
        v_a_128_ = lean_ctor_get(v___x_127_, 0);
        lean_inc(v_a_128_);
        lean_dec_ref(v___x_127_);
        v___x_129_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_128_, v_a_119_);
        return v___x_129_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_instantiateMVarsS___boxed(
    mut v_e_130_: *mut LeanObject,
    mut v_a_131_: *mut LeanObject,
    mut v_a_132_: *mut LeanObject,
    mut v_a_133_: *mut LeanObject,
    mut v_a_134_: *mut LeanObject,
    mut v_a_135_: *mut LeanObject,
    mut v_a_136_: *mut LeanObject,
    mut v_a_137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_138_: *mut LeanObject = core::ptr::null_mut();
    v_res_138_ = l_Lean_Meta_Sym_instantiateMVarsS(
        v_e_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_,
    );
    lean_dec(v_a_136_);
    lean_dec_ref(v_a_135_);
    lean_dec(v_a_134_);
    lean_dec_ref(v_a_133_);
    lean_dec(v_a_132_);
    lean_dec_ref(v_a_131_);
    return v_res_138_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
}
