// Lean compiler output
// Module: Lean.Meta.Sym.InstantiateMVarsS
// Imports: Lean.Meta.Sym.SymM
use crate::r#gen::Lean::Expr::l_Lean_Expr_hasMVar;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, l_Lean_Meta_Sym_shareCommon___redArg,
    runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___redArg(
    mut v_e_70_: *mut crate::leanh::LeanObject,
    mut v___y_71_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_73_: u8 = 0;
    let mut v___x_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_87_: u8 = 0;
    let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_93_: u8 = 0;
    let mut v_unused_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_73_ = l_Lean_Expr_hasMVar(v_e_70_);
                if v___x_73_ == 0 {
                    v___x_74_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_74_, 0, v_e_70_);
                    return v___x_74_;
                } else {
                    v___x_75_ = lean_st_ref_get(v___y_71_);
                    v_mctx_76_ = crate::leanh::lean_ctor_get(v___x_75_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_76_);
                    crate::leanh::lean_dec(v___x_75_);
                    v___x_77_ = l_Lean_instantiateMVarsCore(v_mctx_76_, v_e_70_);
                    v_fst_78_ = crate::leanh::lean_ctor_get(v___x_77_, 0);
                    crate::leanh::lean_inc(v_fst_78_);
                    v_snd_79_ = crate::leanh::lean_ctor_get(v___x_77_, 1);
                    crate::leanh::lean_inc(v_snd_79_);
                    crate::leanh::lean_dec_ref(v___x_77_);
                    v___x_80_ = lean_st_ref_take(v___y_71_);
                    v_cache_81_ = crate::leanh::lean_ctor_get(v___x_80_, 1);
                    v_zetaDeltaFVarIds_82_ = crate::leanh::lean_ctor_get(v___x_80_, 2);
                    v_postponed_83_ = crate::leanh::lean_ctor_get(v___x_80_, 3);
                    v_diag_84_ = crate::leanh::lean_ctor_get(v___x_80_, 4);
                    v_isSharedCheck_93_ = (!crate::leanh::lean_is_exclusive(v___x_80_)) as u8;
                    if v_isSharedCheck_93_ == 0 {
                        v_unused_94_ = crate::leanh::lean_ctor_get(v___x_80_, 0);
                        crate::leanh::lean_dec(v_unused_94_);
                        v___x_86_ = v___x_80_;
                        v_isShared_87_ = v_isSharedCheck_93_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_84_);
                        crate::leanh::lean_inc(v_postponed_83_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_82_);
                        crate::leanh::lean_inc(v_cache_81_);
                        crate::leanh::lean_dec(v___x_80_);
                        v___x_86_ = crate::leanh::lean_box(0);
                        v_isShared_87_ = v_isSharedCheck_93_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_87_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_86_, 0, v_snd_79_);
                    v___x_89_ = v___x_86_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_92_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_92_, 0, v_snd_79_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_92_, 1, v_cache_81_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_92_, 2, v_zetaDeltaFVarIds_82_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_92_, 3, v_postponed_83_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_92_, 4, v_diag_84_);
                    v___x_89_ = v_reuseFailAlloc_92_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_90_ = lean_st_ref_set(v___y_71_, v___x_89_);
                v___x_91_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_91_, 0, v_fst_78_);
                return v___x_91_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___redArg___boxed(
    mut v_e_95_: *mut crate::leanh::LeanObject,
    mut v___y_96_: *mut crate::leanh::LeanObject,
    mut v___y_97_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_98_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___redArg(
        v_e_95_, v___y_96_,
    );
    crate::leanh::lean_dec(v___y_96_);
    return v_res_98_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0(
    mut v_e_99_: *mut crate::leanh::LeanObject,
    mut v___y_100_: *mut crate::leanh::LeanObject,
    mut v___y_101_: *mut crate::leanh::LeanObject,
    mut v___y_102_: *mut crate::leanh::LeanObject,
    mut v___y_103_: *mut crate::leanh::LeanObject,
    mut v___y_104_: *mut crate::leanh::LeanObject,
    mut v___y_105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_107_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___redArg(
        v_e_99_, v___y_103_,
    );
    return v___x_107_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___boxed(
    mut v_e_108_: *mut crate::leanh::LeanObject,
    mut v___y_109_: *mut crate::leanh::LeanObject,
    mut v___y_110_: *mut crate::leanh::LeanObject,
    mut v___y_111_: *mut crate::leanh::LeanObject,
    mut v___y_112_: *mut crate::leanh::LeanObject,
    mut v___y_113_: *mut crate::leanh::LeanObject,
    mut v___y_114_: *mut crate::leanh::LeanObject,
    mut v___y_115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_116_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0(
        v_e_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_,
    );
    crate::leanh::lean_dec(v___y_114_);
    crate::leanh::lean_dec_ref(v___y_113_);
    crate::leanh::lean_dec(v___y_112_);
    crate::leanh::lean_dec_ref(v___y_111_);
    crate::leanh::lean_dec(v___y_110_);
    crate::leanh::lean_dec_ref(v___y_109_);
    return v_res_116_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateMVarsS(
    mut v_e_117_: *mut crate::leanh::LeanObject,
    mut v_a_118_: *mut crate::leanh::LeanObject,
    mut v_a_119_: *mut crate::leanh::LeanObject,
    mut v_a_120_: *mut crate::leanh::LeanObject,
    mut v_a_121_: *mut crate::leanh::LeanObject,
    mut v_a_122_: *mut crate::leanh::LeanObject,
    mut v_a_123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_125_: u8 = 0;
    v___x_125_ = l_Lean_Expr_hasMVar(v_e_117_);
    if v___x_125_ == 0 {
        let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_126_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_126_, 0, v_e_117_);
        return v___x_126_;
    } else {
        let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_127_ =
            l_Lean_instantiateMVars___at___00Lean_Meta_Sym_instantiateMVarsS_spec__0___redArg(
                v_e_117_, v_a_121_,
            );
        v_a_128_ = crate::leanh::lean_ctor_get(v___x_127_, 0);
        crate::leanh::lean_inc(v_a_128_);
        crate::leanh::lean_dec_ref(v___x_127_);
        v___x_129_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_128_, v_a_119_);
        return v___x_129_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_instantiateMVarsS___boxed(
    mut v_e_130_: *mut crate::leanh::LeanObject,
    mut v_a_131_: *mut crate::leanh::LeanObject,
    mut v_a_132_: *mut crate::leanh::LeanObject,
    mut v_a_133_: *mut crate::leanh::LeanObject,
    mut v_a_134_: *mut crate::leanh::LeanObject,
    mut v_a_135_: *mut crate::leanh::LeanObject,
    mut v_a_136_: *mut crate::leanh::LeanObject,
    mut v_a_137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_138_ = l_Lean_Meta_Sym_instantiateMVarsS(
        v_e_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_,
    );
    crate::leanh::lean_dec(v_a_136_);
    crate::leanh::lean_dec_ref(v_a_135_);
    crate::leanh::lean_dec(v_a_134_);
    crate::leanh::lean_dec_ref(v_a_133_);
    crate::leanh::lean_dec(v_a_132_);
    crate::leanh::lean_dec_ref(v_a_131_);
    return v_res_138_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_InstantiateMVarsS(
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
pub unsafe fn initialize_Lean_Meta_Sym_InstantiateMVarsS(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
}
