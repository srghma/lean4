// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.CtorIdx
// Imports: Lean.Meta.Tactic.Simp.Simproc Init.Simproc Lean.Meta.Constructions.CtorIdx Lean.Meta.CtorRecognizer
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0_value
) as *mut LeanObject;
static mut l_reduceCtorIdx___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_reduceCtorIdx___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 73, 100, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value) as *mut LeanObject,11681431521506135087 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value: LeanArrayObject<1> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9__value) as *mut LeanObject;
pub unsafe fn l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(
    mut v_x_161_: *mut LeanObject,
    mut v_x_162_: *mut LeanObject,
    mut v_x_163_: *mut LeanObject,
    mut v___y_164_: *mut LeanObject,
    mut v___y_165_: *mut LeanObject,
    mut v___y_166_: *mut LeanObject,
    mut v___y_167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_181_: u8 = 0;
    let mut v_val_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_189_: u8 = 0;
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_201_: u8 = 0;
    let mut v_val_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_205_: u8 = 0;
    let mut v_cidx_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_214_: u8 = 0;
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_219_: u8 = 0;
    let mut v_a_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_223_: u8 = 0;
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_227_: u8 = 0;
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_232_: u8 = 0;
    let mut v_a_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_236_: u8 = 0;
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_240_: u8 = 0;
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_161_) == 5 {
                    v_fn_169_ = lean_ctor_get(v_x_161_, 0);
                    lean_inc_ref(v_fn_169_);
                    v_arg_170_ = lean_ctor_get(v_x_161_, 1);
                    lean_inc_ref(v_arg_170_);
                    lean_dec_ref_known(v_x_161_, 2);
                    v___x_171_ = lean_array_set(v_x_162_, v_x_163_, v_arg_170_);
                    v___x_172_ = lean_unsigned_to_nat(1);
                    v___x_173_ = lean_nat_sub(v_x_163_, v___x_172_);
                    lean_dec(v_x_163_);
                    v_x_161_ = v_fn_169_;
                    v_x_162_ = v___x_171_;
                    v_x_163_ = v___x_173_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_163_);
                    v___x_175_ = l_Lean_Expr_constName_x3f(v_x_161_);
                    lean_dec_ref(v_x_161_);
                    if lean_obj_tag(v___x_175_) == 1 {
                        v_val_176_ = lean_ctor_get(v___x_175_, 0);
                        lean_inc(v_val_176_);
                        lean_dec_ref_known(v___x_175_, 1);
                        v___x_177_ = l_isCtorIdx_x3f___redArg(v_val_176_, v___y_167_);
                        if lean_obj_tag(v___x_177_) == 0 {
                            v_a_178_ = lean_ctor_get(v___x_177_, 0);
                            v_isSharedCheck_232_ = (!lean_is_exclusive(v___x_177_)) as u8;
                            if v_isSharedCheck_232_ == 0 {
                                v___x_180_ = v___x_177_;
                                v_isShared_181_ = v_isSharedCheck_232_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_178_);
                                lean_dec(v___x_177_);
                                v___x_180_ = lean_box(0);
                                v_isShared_181_ = v_isSharedCheck_232_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_x_162_);
                            v_a_233_ = lean_ctor_get(v___x_177_, 0);
                            v_isSharedCheck_240_ = (!lean_is_exclusive(v___x_177_)) as u8;
                            if v_isSharedCheck_240_ == 0 {
                                v___x_235_ = v___x_177_;
                                v_isShared_236_ = v_isSharedCheck_240_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_233_);
                                lean_dec(v___x_177_);
                                v___x_235_ = lean_box(0);
                                v_isShared_236_ = v_isSharedCheck_240_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_175_);
                        lean_dec_ref(v_x_162_);
                        v___x_241_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
                        v___x_242_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_242_, 0, v___x_241_);
                        return v___x_242_;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_178_) == 1 {
                    v_val_182_ = lean_ctor_get(v_a_178_, 0);
                    lean_inc(v_val_182_);
                    lean_dec_ref_known(v_a_178_, 1);
                    v_numParams_183_ = lean_ctor_get(v_val_182_, 1);
                    lean_inc(v_numParams_183_);
                    v_numIndices_184_ = lean_ctor_get(v_val_182_, 2);
                    lean_inc(v_numIndices_184_);
                    lean_dec(v_val_182_);
                    v___x_185_ = lean_array_get_size(v_x_162_);
                    v___x_186_ = lean_nat_add(v_numParams_183_, v_numIndices_184_);
                    lean_dec(v_numIndices_184_);
                    lean_dec(v_numParams_183_);
                    v___x_187_ = lean_unsigned_to_nat(1);
                    v___x_188_ = lean_nat_add(v___x_186_, v___x_187_);
                    lean_dec(v___x_186_);
                    v___x_189_ = lean_nat_dec_eq(v___x_185_, v___x_188_);
                    lean_dec(v___x_188_);
                    if v___x_189_ == 0 {
                        lean_dec_ref(v_x_162_);
                        v___x_190_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
                        if v_isShared_181_ == 0 {
                            lean_ctor_set(v___x_180_, 0, v___x_190_);
                            v___x_192_ = v___x_180_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
                            v___x_192_ = v_reuseFailAlloc_193_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_180_);
                        v___x_194_ = l_Lean_instInhabitedExpr;
                        v___x_195_ = lean_nat_sub(v___x_185_, v___x_187_);
                        v___x_196_ = lean_array_get(v___x_194_, v_x_162_, v___x_195_);
                        lean_dec(v___x_195_);
                        lean_dec_ref(v_x_162_);
                        v___x_197_ = l_Lean_Meta_isConstructorApp_x3f(
                            v___x_196_, v___y_164_, v___y_165_, v___y_166_, v___y_167_,
                        );
                        if lean_obj_tag(v___x_197_) == 0 {
                            v_a_198_ = lean_ctor_get(v___x_197_, 0);
                            v_isSharedCheck_219_ = (!lean_is_exclusive(v___x_197_)) as u8;
                            if v_isSharedCheck_219_ == 0 {
                                v___x_200_ = v___x_197_;
                                v_isShared_201_ = v_isSharedCheck_219_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_198_);
                                lean_dec(v___x_197_);
                                v___x_200_ = lean_box(0);
                                v_isShared_201_ = v_isSharedCheck_219_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_220_ = lean_ctor_get(v___x_197_, 0);
                            v_isSharedCheck_227_ = (!lean_is_exclusive(v___x_197_)) as u8;
                            if v_isSharedCheck_227_ == 0 {
                                v___x_222_ = v___x_197_;
                                v_isShared_223_ = v_isSharedCheck_227_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_220_);
                                lean_dec(v___x_197_);
                                v___x_222_ = lean_box(0);
                                v_isShared_223_ = v_isSharedCheck_227_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_178_);
                    lean_dec_ref(v_x_162_);
                    v___x_228_ =
                        l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
                    if v_isShared_181_ == 0 {
                        lean_ctor_set(v___x_180_, 0, v___x_228_);
                        v___x_230_ = v___x_180_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
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
                if lean_obj_tag(v_a_198_) == 1 {
                    v_val_202_ = lean_ctor_get(v_a_198_, 0);
                    v_isSharedCheck_214_ = (!lean_is_exclusive(v_a_198_)) as u8;
                    if v_isSharedCheck_214_ == 0 {
                        v___x_204_ = v_a_198_;
                        v_isShared_205_ = v_isSharedCheck_214_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_202_);
                        lean_dec(v_a_198_);
                        v___x_204_ = lean_box(0);
                        v_isShared_205_ = v_isSharedCheck_214_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_198_);
                    v___x_215_ =
                        l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
                    if v_isShared_201_ == 0 {
                        lean_ctor_set(v___x_200_, 0, v___x_215_);
                        v___x_217_ = v___x_200_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
                        v___x_217_ = v_reuseFailAlloc_218_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v_cidx_206_ = lean_ctor_get(v_val_202_, 2);
                lean_inc(v_cidx_206_);
                lean_dec(v_val_202_);
                v___x_207_ = l_Lean_mkNatLit(v_cidx_206_);
                if v_isShared_205_ == 0 {
                    lean_ctor_set_tag(v___x_204_, 0);
                    lean_ctor_set(v___x_204_, 0, v___x_207_);
                    v___x_209_ = v___x_204_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_207_);
                    v___x_209_ = v_reuseFailAlloc_213_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_201_ == 0 {
                    lean_ctor_set(v___x_200_, 0, v___x_209_);
                    v___x_211_ = v___x_200_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
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
                    v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
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
                    v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
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
    mut v_x_243_: *mut LeanObject,
    mut v_x_244_: *mut LeanObject,
    mut v_x_245_: *mut LeanObject,
    mut v___y_246_: *mut LeanObject,
    mut v___y_247_: *mut LeanObject,
    mut v___y_248_: *mut LeanObject,
    mut v___y_249_: *mut LeanObject,
    mut v___y_250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_251_: *mut LeanObject = core::ptr::null_mut();
    v_res_251_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(
        v_x_243_, v_x_244_, v_x_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_,
    );
    lean_dec(v___y_249_);
    lean_dec_ref(v___y_248_);
    lean_dec(v___y_247_);
    lean_dec_ref(v___y_246_);
    return v_res_251_;
}
pub unsafe fn _init_l_reduceCtorIdx___closed__0() -> *mut LeanObject {
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_253_: *mut LeanObject = core::ptr::null_mut();
    v___x_252_ = lean_box(0);
    v_dummy_253_ = l_Lean_Expr_sort___override(v___x_252_);
    return v_dummy_253_;
}
pub unsafe fn l_reduceCtorIdx(
    mut v_e_254_: *mut LeanObject,
    mut v_a_255_: *mut LeanObject,
    mut v_a_256_: *mut LeanObject,
    mut v_a_257_: *mut LeanObject,
    mut v_a_258_: *mut LeanObject,
    mut v_a_259_: *mut LeanObject,
    mut v_a_260_: *mut LeanObject,
    mut v_a_261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dummy_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    v_dummy_263_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_reduceCtorIdx___closed__0),
        core::ptr::addr_of_mut!(l_reduceCtorIdx___closed__0_once),
        _init_l_reduceCtorIdx___closed__0,
    );
    v_nargs_264_ = l_Lean_Expr_getAppNumArgs(v_e_254_);
    lean_inc(v_nargs_264_);
    v___x_265_ = lean_mk_array(v_nargs_264_, v_dummy_263_);
    v___x_266_ = lean_unsigned_to_nat(1);
    v___x_267_ = lean_nat_sub(v_nargs_264_, v___x_266_);
    lean_dec(v_nargs_264_);
    v___x_268_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(
        v_e_254_, v___x_265_, v___x_267_, v_a_258_, v_a_259_, v_a_260_, v_a_261_,
    );
    return v___x_268_;
}
pub unsafe fn l_reduceCtorIdx___boxed(
    mut v_e_269_: *mut LeanObject,
    mut v_a_270_: *mut LeanObject,
    mut v_a_271_: *mut LeanObject,
    mut v_a_272_: *mut LeanObject,
    mut v_a_273_: *mut LeanObject,
    mut v_a_274_: *mut LeanObject,
    mut v_a_275_: *mut LeanObject,
    mut v_a_276_: *mut LeanObject,
    mut v_a_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_278_: *mut LeanObject = core::ptr::null_mut();
    v_res_278_ = l_reduceCtorIdx(
        v_e_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_,
    );
    lean_dec(v_a_276_);
    lean_dec_ref(v_a_275_);
    lean_dec(v_a_274_);
    lean_dec_ref(v_a_273_);
    lean_dec(v_a_272_);
    lean_dec_ref(v_a_271_);
    lean_dec(v_a_270_);
    return v_res_278_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0(
    mut v_x_279_: *mut LeanObject,
    mut v_x_280_: *mut LeanObject,
    mut v_x_281_: *mut LeanObject,
    mut v___y_282_: *mut LeanObject,
    mut v___y_283_: *mut LeanObject,
    mut v___y_284_: *mut LeanObject,
    mut v___y_285_: *mut LeanObject,
    mut v___y_286_: *mut LeanObject,
    mut v___y_287_: *mut LeanObject,
    mut v___y_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    v___x_290_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(
        v_x_279_, v_x_280_, v_x_281_, v___y_285_, v___y_286_, v___y_287_, v___y_288_,
    );
    return v___x_290_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___boxed(
    mut v_x_291_: *mut LeanObject,
    mut v_x_292_: *mut LeanObject,
    mut v_x_293_: *mut LeanObject,
    mut v___y_294_: *mut LeanObject,
    mut v___y_295_: *mut LeanObject,
    mut v___y_296_: *mut LeanObject,
    mut v___y_297_: *mut LeanObject,
    mut v___y_298_: *mut LeanObject,
    mut v___y_299_: *mut LeanObject,
    mut v___y_300_: *mut LeanObject,
    mut v___y_301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_302_: *mut LeanObject = core::ptr::null_mut();
    v_res_302_ = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0(
        v_x_291_, v_x_292_, v_x_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_,
        v___y_299_, v___y_300_,
    );
    lean_dec(v___y_300_);
    lean_dec_ref(v___y_299_);
    lean_dec(v___y_298_);
    lean_dec_ref(v___y_297_);
    lean_dec(v___y_296_);
    lean_dec_ref(v___y_295_);
    lean_dec(v___y_294_);
    return v_res_302_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_()
-> *mut LeanObject {
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    v___x_311_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
    v___x_312_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
    v___x_313_ = lean_alloc_closure(l_reduceCtorIdx___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_314_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_311_, v___x_312_, v___x_313_);
    return v___x_314_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9____boxed(
    mut v_a_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_316_: *mut LeanObject = core::ptr::null_mut();
    v_res_316_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
    return v_res_316_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CtorRecognizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(builtin);
}
