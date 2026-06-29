// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.CtorIdx
// Imports: Lean.Meta.Tactic.Simp.Simproc Init.Simproc Lean.Meta.Constructions.CtorIdx Lean.Meta.CtorRecognizer
use crate::r#gen::Init::Simproc::{initialize_Init_Simproc, runtime_initialize_Init_Simproc};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_constName_x3f, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_sort___override,
    l_Lean_instInhabitedExpr, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Meta::Constructions::CtorIdx::{
    initialize_Lean_Meta_Constructions_CtorIdx, l_isCtorIdx_x3f___redArg,
    runtime_initialize_Lean_Meta_Constructions_CtorIdx,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::{
    initialize_Lean_Meta_CtorRecognizer, l_Lean_Meta_isConstructorApp_x3f,
    runtime_initialize_Lean_Meta_CtorRecognizer,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, l_Lean_Meta_Simp_registerBuiltinDSimproc,
    runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
use crate::ffi::lean_mk_array;
use crate::ffi::lean_array_set;
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_sub,
};
pub static l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_reduceCtorIdx___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_reduceCtorIdx___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 73, 100, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value) as *mut crate::leanh::LeanObject,11681431521506135087 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value: crate::leanh::LeanArrayObject<1> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(
    mut v_x_161_: *mut crate::leanh::LeanObject,
    mut v_x_162_: *mut crate::leanh::LeanObject,
    mut v_x_163_: *mut crate::leanh::LeanObject,
    mut v___y_164_: *mut crate::leanh::LeanObject,
    mut v___y_165_: *mut crate::leanh::LeanObject,
    mut v___y_166_: *mut crate::leanh::LeanObject,
    mut v___y_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_181_: u8 = 0;
    let mut v_val_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: u8 = 0;
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_201_: u8 = 0;
    let mut v_val_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_205_: u8 = 0;
    let mut v_cidx_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_214_: u8 = 0;
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_219_: u8 = 0;
    let mut v_a_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_223_: u8 = 0;
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_227_: u8 = 0;
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_232_: u8 = 0;
    let mut v_a_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_236_: u8 = 0;
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_240_: u8 = 0;
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_161_) == 5 {
                    v_fn_169_ = crate::leanh::lean_ctor_get(v_x_161_, 0);
                    crate::leanh::lean_inc_ref(v_fn_169_);
                    v_arg_170_ = crate::leanh::lean_ctor_get(v_x_161_, 1);
                    crate::leanh::lean_inc_ref(v_arg_170_);
                    crate::leanh::lean_dec_ref_known(v_x_161_, 2);
                    v___x_171_ = lean_array_set(v_x_162_, v_x_163_, v_arg_170_);
                    v___x_172_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_173_ = lean_nat_sub(v_x_163_, v___x_172_);
                    crate::leanh::lean_dec(v_x_163_);
                    v_x_161_ = v_fn_169_;
                    v_x_162_ = v___x_171_;
                    v_x_163_ = v___x_173_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_163_);
                    v___x_175_ = l_Lean_Expr_constName_x3f(v_x_161_);
                    crate::leanh::lean_dec_ref(v_x_161_);
                    if crate::leanh::lean_obj_tag(v___x_175_) == 1 {
                        v_val_176_ = crate::leanh::lean_ctor_get(v___x_175_, 0);
                        crate::leanh::lean_inc(v_val_176_);
                        crate::leanh::lean_dec_ref_known(v___x_175_, 1);
                        v___x_177_ = l_isCtorIdx_x3f___redArg(v_val_176_, v___y_167_);
                        if crate::leanh::lean_obj_tag(v___x_177_) == 0 {
                            v_a_178_ = crate::leanh::lean_ctor_get(v___x_177_, 0);
                            v_isSharedCheck_232_ =
                                (!crate::leanh::lean_is_exclusive(v___x_177_)) as u8;
                            if v_isSharedCheck_232_ == 0 {
                                v___x_180_ = v___x_177_;
                                v_isShared_181_ = v_isSharedCheck_232_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_178_);
                                crate::leanh::lean_dec(v___x_177_);
                                v___x_180_ = crate::leanh::lean_box(0);
                                v_isShared_181_ = v_isSharedCheck_232_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_x_162_);
                            v_a_233_ = crate::leanh::lean_ctor_get(v___x_177_, 0);
                            v_isSharedCheck_240_ =
                                (!crate::leanh::lean_is_exclusive(v___x_177_)) as u8;
                            if v_isSharedCheck_240_ == 0 {
                                v___x_235_ = v___x_177_;
                                v_isShared_236_ = v_isSharedCheck_240_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_233_);
                                crate::leanh::lean_dec(v___x_177_);
                                v___x_235_ = crate::leanh::lean_box(0);
                                v_isShared_236_ = v_isSharedCheck_240_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_175_);
                        crate::leanh::lean_dec_ref(v_x_162_);
                        v___x_241_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
                        v___x_242_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_242_, 0, v___x_241_);
                        return v___x_242_;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_178_) == 1 {
                    v_val_182_ = crate::leanh::lean_ctor_get(v_a_178_, 0);
                    crate::leanh::lean_inc(v_val_182_);
                    crate::leanh::lean_dec_ref_known(v_a_178_, 1);
                    v_numParams_183_ = crate::leanh::lean_ctor_get(v_val_182_, 1);
                    crate::leanh::lean_inc(v_numParams_183_);
                    v_numIndices_184_ = crate::leanh::lean_ctor_get(v_val_182_, 2);
                    crate::leanh::lean_inc(v_numIndices_184_);
                    crate::leanh::lean_dec(v_val_182_);
                    v___x_185_ = lean_array_get_size(v_x_162_);
                    v___x_186_ = lean_nat_add(v_numParams_183_, v_numIndices_184_);
                    crate::leanh::lean_dec(v_numIndices_184_);
                    crate::leanh::lean_dec(v_numParams_183_);
                    v___x_187_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_188_ = lean_nat_add(v___x_186_, v___x_187_);
                    crate::leanh::lean_dec(v___x_186_);
                    v___x_189_ = lean_nat_dec_eq(v___x_185_, v___x_188_);
                    crate::leanh::lean_dec(v___x_188_);
                    if v___x_189_ == 0 {
                        crate::leanh::lean_dec_ref(v_x_162_);
                        v___x_190_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
                        if v_isShared_181_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_180_, 0, v___x_190_);
                            v___x_192_ = v___x_180_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
                            v___x_192_ = v_reuseFailAlloc_193_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_180_);
                        v___x_194_ = l_Lean_instInhabitedExpr;
                        v___x_195_ = lean_nat_sub(v___x_185_, v___x_187_);
                        v___x_196_ = lean_array_get(v___x_194_, v_x_162_, v___x_195_);
                        crate::leanh::lean_dec(v___x_195_);
                        crate::leanh::lean_dec_ref(v_x_162_);
                        v___x_197_ = l_Lean_Meta_isConstructorApp_x3f(
                            v___x_196_, v___y_164_, v___y_165_, v___y_166_, v___y_167_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_197_) == 0 {
                            v_a_198_ = crate::leanh::lean_ctor_get(v___x_197_, 0);
                            v_isSharedCheck_219_ =
                                (!crate::leanh::lean_is_exclusive(v___x_197_)) as u8;
                            if v_isSharedCheck_219_ == 0 {
                                v___x_200_ = v___x_197_;
                                v_isShared_201_ = v_isSharedCheck_219_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_198_);
                                crate::leanh::lean_dec(v___x_197_);
                                v___x_200_ = crate::leanh::lean_box(0);
                                v_isShared_201_ = v_isSharedCheck_219_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_220_ = crate::leanh::lean_ctor_get(v___x_197_, 0);
                            v_isSharedCheck_227_ =
                                (!crate::leanh::lean_is_exclusive(v___x_197_)) as u8;
                            if v_isSharedCheck_227_ == 0 {
                                v___x_222_ = v___x_197_;
                                v_isShared_223_ = v_isSharedCheck_227_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_220_);
                                crate::leanh::lean_dec(v___x_197_);
                                v___x_222_ = crate::leanh::lean_box(0);
                                v_isShared_223_ = v_isSharedCheck_227_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_178_);
                    crate::leanh::lean_dec_ref(v_x_162_);
                    v___x_228_ =
                        l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
                    if v_isShared_181_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_180_, 0, v___x_228_);
                        v___x_230_ = v___x_180_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_231_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
                        v___x_230_ = v_reuseFailAlloc_231_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_192_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_198_) == 1 {
                    v_val_202_ = crate::leanh::lean_ctor_get(v_a_198_, 0);
                    v_isSharedCheck_214_ = (!crate::leanh::lean_is_exclusive(v_a_198_)) as u8;
                    if v_isSharedCheck_214_ == 0 {
                        v___x_204_ = v_a_198_;
                        v_isShared_205_ = v_isSharedCheck_214_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_202_);
                        crate::leanh::lean_dec(v_a_198_);
                        v___x_204_ = crate::leanh::lean_box(0);
                        v_isShared_205_ = v_isSharedCheck_214_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_198_);
                    v___x_215_ =
                        l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
                    if v_isShared_201_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_200_, 0, v___x_215_);
                        v___x_217_ = v___x_200_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_218_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
                        v___x_217_ = v_reuseFailAlloc_218_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v_cidx_206_ = crate::leanh::lean_ctor_get(v_val_202_, 2);
                crate::leanh::lean_inc(v_cidx_206_);
                crate::leanh::lean_dec(v_val_202_);
                v___x_207_ = l_Lean_mkNatLit(v_cidx_206_);
                if v_isShared_205_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_204_, 0);
                    crate::leanh::lean_ctor_set(v___x_204_, 0, v___x_207_);
                    v___x_209_ = v___x_204_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_213_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_207_);
                    v___x_209_ = v_reuseFailAlloc_213_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_201_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_200_, 0, v___x_209_);
                    v___x_211_ = v___x_200_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_212_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
                    v___x_211_ = v_reuseFailAlloc_212_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_211_;
            }
            7 => {
                return v___x_217_;
            }
            8 => {
                if v_isShared_223_ == 0 {
                    v___x_225_ = v___x_222_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_226_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
                    v___x_225_ = v_reuseFailAlloc_226_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_225_;
            }
            10 => {
                return v___x_230_;
            }
            11 => {
                if v_isShared_236_ == 0 {
                    v___x_238_ = v___x_235_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
                    v___x_238_ = v_reuseFailAlloc_239_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___boxed(
    mut v_x_243_: *mut crate::leanh::LeanObject,
    mut v_x_244_: *mut crate::leanh::LeanObject,
    mut v_x_245_: *mut crate::leanh::LeanObject,
    mut v___y_246_: *mut crate::leanh::LeanObject,
    mut v___y_247_: *mut crate::leanh::LeanObject,
    mut v___y_248_: *mut crate::leanh::LeanObject,
    mut v___y_249_: *mut crate::leanh::LeanObject,
    mut v___y_250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_251_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(
        v_x_243_, v_x_244_, v_x_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_,
    );
    crate::leanh::lean_dec(v___y_249_);
    crate::leanh::lean_dec_ref(v___y_248_);
    crate::leanh::lean_dec(v___y_247_);
    crate::leanh::lean_dec_ref(v___y_246_);
    return v_res_251_;
}
pub unsafe fn _init_l_reduceCtorIdx___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_252_ = crate::leanh::lean_box(0);
    v_dummy_253_ = l_Lean_Expr_sort___override(v___x_252_);
    return v_dummy_253_;
}
pub unsafe fn l_reduceCtorIdx(
    mut v_e_254_: *mut crate::leanh::LeanObject,
    mut v_a_255_: *mut crate::leanh::LeanObject,
    mut v_a_256_: *mut crate::leanh::LeanObject,
    mut v_a_257_: *mut crate::leanh::LeanObject,
    mut v_a_258_: *mut crate::leanh::LeanObject,
    mut v_a_259_: *mut crate::leanh::LeanObject,
    mut v_a_260_: *mut crate::leanh::LeanObject,
    mut v_a_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dummy_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_263_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_reduceCtorIdx___closed__0),
        core::ptr::addr_of_mut!(l_reduceCtorIdx___closed__0_once),
        _init_l_reduceCtorIdx___closed__0,
    );
    v_nargs_264_ = l_Lean_Expr_getAppNumArgs(v_e_254_);
    crate::leanh::lean_inc(v_nargs_264_);
    v___x_265_ = lean_mk_array(v_nargs_264_, v_dummy_263_);
    v___x_266_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_267_ = lean_nat_sub(v_nargs_264_, v___x_266_);
    crate::leanh::lean_dec(v_nargs_264_);
    v___x_268_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(
        v_e_254_, v___x_265_, v___x_267_, v_a_258_, v_a_259_, v_a_260_, v_a_261_,
    );
    return v___x_268_;
}
pub unsafe fn l_reduceCtorIdx___boxed(
    mut v_e_269_: *mut crate::leanh::LeanObject,
    mut v_a_270_: *mut crate::leanh::LeanObject,
    mut v_a_271_: *mut crate::leanh::LeanObject,
    mut v_a_272_: *mut crate::leanh::LeanObject,
    mut v_a_273_: *mut crate::leanh::LeanObject,
    mut v_a_274_: *mut crate::leanh::LeanObject,
    mut v_a_275_: *mut crate::leanh::LeanObject,
    mut v_a_276_: *mut crate::leanh::LeanObject,
    mut v_a_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_278_ = l_reduceCtorIdx(
        v_e_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_,
    );
    crate::leanh::lean_dec(v_a_276_);
    crate::leanh::lean_dec_ref(v_a_275_);
    crate::leanh::lean_dec(v_a_274_);
    crate::leanh::lean_dec_ref(v_a_273_);
    crate::leanh::lean_dec(v_a_272_);
    crate::leanh::lean_dec_ref(v_a_271_);
    crate::leanh::lean_dec(v_a_270_);
    return v_res_278_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0(
    mut v_x_279_: *mut crate::leanh::LeanObject,
    mut v_x_280_: *mut crate::leanh::LeanObject,
    mut v_x_281_: *mut crate::leanh::LeanObject,
    mut v___y_282_: *mut crate::leanh::LeanObject,
    mut v___y_283_: *mut crate::leanh::LeanObject,
    mut v___y_284_: *mut crate::leanh::LeanObject,
    mut v___y_285_: *mut crate::leanh::LeanObject,
    mut v___y_286_: *mut crate::leanh::LeanObject,
    mut v___y_287_: *mut crate::leanh::LeanObject,
    mut v___y_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_290_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(
        v_x_279_, v_x_280_, v_x_281_, v___y_285_, v___y_286_, v___y_287_, v___y_288_,
    );
    return v___x_290_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___boxed(
    mut v_x_291_: *mut crate::leanh::LeanObject,
    mut v_x_292_: *mut crate::leanh::LeanObject,
    mut v_x_293_: *mut crate::leanh::LeanObject,
    mut v___y_294_: *mut crate::leanh::LeanObject,
    mut v___y_295_: *mut crate::leanh::LeanObject,
    mut v___y_296_: *mut crate::leanh::LeanObject,
    mut v___y_297_: *mut crate::leanh::LeanObject,
    mut v___y_298_: *mut crate::leanh::LeanObject,
    mut v___y_299_: *mut crate::leanh::LeanObject,
    mut v___y_300_: *mut crate::leanh::LeanObject,
    mut v___y_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_302_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0(
        v_x_291_, v_x_292_, v_x_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_,
        v___y_299_, v___y_300_,
    );
    crate::leanh::lean_dec(v___y_300_);
    crate::leanh::lean_dec_ref(v___y_299_);
    crate::leanh::lean_dec(v___y_298_);
    crate::leanh::lean_dec_ref(v___y_297_);
    crate::leanh::lean_dec(v___y_296_);
    crate::leanh::lean_dec_ref(v___y_295_);
    crate::leanh::lean_dec(v___y_294_);
    return v_res_302_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_311_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
    v___x_312_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
    v___x_313_ =
        crate::leanh::lean_alloc_closure(l_reduceCtorIdx___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_314_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_311_, v___x_312_, v___x_313_);
    return v___x_314_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9____boxed(
    mut v_a_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_316_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
    return v_res_316_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_CtorRecognizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(builtin);
}
