// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.List
// Imports: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
use crate::r#gen::Init::Data::List::Basic::l_List_replicateTR___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkListLit;
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_getNatValue_x3f;
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Nat::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    l_Lean_Meta_Simp_addSEvalprocBuiltinAttr, l_Lean_Meta_Simp_addSimprocBuiltinAttr,
    l_Lean_Meta_Simp_registerBuiltinDSimproc,
};
pub static l_List_reduceReplicate___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
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
static mut l_List_reduceReplicate___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_reduceReplicate___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_reduceReplicate___redArg___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 105, 115, 116, 0],
    };
static mut l_List_reduceReplicate___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_reduceReplicate___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_reduceReplicate___redArg___closed__2_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [114, 101, 112, 108, 105, 99, 97, 116, 101, 0],
    };
static mut l_List_reduceReplicate___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_reduceReplicate___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_List_reduceReplicate___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_reduceReplicate___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
            9582258842178272501 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_reduceReplicate___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_reduceReplicate___redArg___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_reduceReplicate___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            634820988191375095 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_reduceReplicate___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_reduceReplicate___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [114, 101, 100, 117, 99, 101, 82, 101, 112, 108, 105, 99, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_reduceReplicate___redArg___closed__1_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value) as *mut crate::leanh::LeanObject,4445492996492257536 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_List_reduceReplicate___redArg___closed__3_value) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value: crate::leanh::LeanArrayObject<4> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_List_reduceReplicate___redArg(
    mut v_e_161_: *mut crate::leanh::LeanObject,
    mut v_a_162_: *mut crate::leanh::LeanObject,
    mut v_a_163_: *mut crate::leanh::LeanObject,
    mut v_a_164_: *mut crate::leanh::LeanObject,
    mut v_a_165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_171_: u8 = 0;
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: u8 = 0;
    let mut v_arg_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: u8 = 0;
    let mut v_arg_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: u8 = 0;
    let mut v_arg_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: u8 = 0;
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_193_: u8 = 0;
    let mut v_val_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_197_: u8 = 0;
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_203_: u8 = 0;
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_210_: u8 = 0;
    let mut v_a_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_214_: u8 = 0;
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_218_: u8 = 0;
    let mut v_isSharedCheck_219_: u8 = 0;
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_224_: u8 = 0;
    let mut v_a_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_228_: u8 = 0;
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_232_: u8 = 0;
    let mut v_isSharedCheck_233_: u8 = 0;
    let mut v_a_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_237_: u8 = 0;
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_167_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_161_, v_a_163_);
                if crate::leanh::lean_obj_tag(v___x_167_) == 0 {
                    v_a_168_ = crate::leanh::lean_ctor_get(v___x_167_, 0);
                    v_isSharedCheck_233_ = (!crate::leanh::lean_is_exclusive(v___x_167_)) as u8;
                    if v_isSharedCheck_233_ == 0 {
                        v___x_170_ = v___x_167_;
                        v_isShared_171_ = v_isSharedCheck_233_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_168_);
                        crate::leanh::lean_dec(v___x_167_);
                        v___x_170_ = crate::leanh::lean_box(0);
                        v_isShared_171_ = v_isSharedCheck_233_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_234_ = crate::leanh::lean_ctor_get(v___x_167_, 0);
                    v_isSharedCheck_241_ = (!crate::leanh::lean_is_exclusive(v___x_167_)) as u8;
                    if v_isSharedCheck_241_ == 0 {
                        v___x_236_ = v___x_167_;
                        v_isShared_237_ = v_isSharedCheck_241_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_234_);
                        crate::leanh::lean_dec(v___x_167_);
                        v___x_236_ = crate::leanh::lean_box(0);
                        v_isShared_237_ = v_isSharedCheck_241_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_177_ = l_Lean_Expr_cleanupAnnotations(v_a_168_);
                v___x_178_ = l_Lean_Expr_isApp(v___x_177_);
                if v___x_178_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_177_);
                    state = 2;
                    continue;
                } else {
                    v_arg_179_ = crate::leanh::lean_ctor_get(v___x_177_, 1);
                    crate::leanh::lean_inc_ref(v_arg_179_);
                    v___x_180_ = l_Lean_Expr_appFnCleanup___redArg(v___x_177_);
                    v___x_181_ = l_Lean_Expr_isApp(v___x_180_);
                    if v___x_181_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_180_);
                        crate::leanh::lean_dec_ref(v_arg_179_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_182_ = crate::leanh::lean_ctor_get(v___x_180_, 1);
                        crate::leanh::lean_inc_ref(v_arg_182_);
                        v___x_183_ = l_Lean_Expr_appFnCleanup___redArg(v___x_180_);
                        v___x_184_ = l_Lean_Expr_isApp(v___x_183_);
                        if v___x_184_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_183_);
                            crate::leanh::lean_dec_ref(v_arg_182_);
                            crate::leanh::lean_dec_ref(v_arg_179_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_185_ = crate::leanh::lean_ctor_get(v___x_183_, 1);
                            crate::leanh::lean_inc_ref(v_arg_185_);
                            v___x_186_ = l_Lean_Expr_appFnCleanup___redArg(v___x_183_);
                            v___x_187_ = l_List_reduceReplicate___redArg___closed__3;
                            v___x_188_ = l_Lean_Expr_isConstOf(v___x_186_, v___x_187_);
                            crate::leanh::lean_dec_ref(v___x_186_);
                            if v___x_188_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_185_);
                                crate::leanh::lean_dec_ref(v_arg_182_);
                                crate::leanh::lean_dec_ref(v_arg_179_);
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_170_);
                                v___x_189_ = l_Lean_Meta_getNatValue_x3f(
                                    v_arg_182_, v_a_162_, v_a_163_, v_a_164_, v_a_165_,
                                );
                                crate::leanh::lean_dec_ref(v_arg_182_);
                                if crate::leanh::lean_obj_tag(v___x_189_) == 0 {
                                    v_a_190_ = crate::leanh::lean_ctor_get(v___x_189_, 0);
                                    v_isSharedCheck_224_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_189_)) as u8;
                                    if v_isSharedCheck_224_ == 0 {
                                        v___x_192_ = v___x_189_;
                                        v_isShared_193_ = v_isSharedCheck_224_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_190_);
                                        crate::leanh::lean_dec(v___x_189_);
                                        v___x_192_ = crate::leanh::lean_box(0);
                                        v_isShared_193_ = v_isSharedCheck_224_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_185_);
                                    crate::leanh::lean_dec_ref(v_arg_179_);
                                    v_a_225_ = crate::leanh::lean_ctor_get(v___x_189_, 0);
                                    v_isSharedCheck_232_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_189_)) as u8;
                                    if v_isSharedCheck_232_ == 0 {
                                        v___x_227_ = v___x_189_;
                                        v_isShared_228_ = v_isSharedCheck_232_;
                                        state = 12;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_225_);
                                        crate::leanh::lean_dec(v___x_189_);
                                        v___x_227_ = crate::leanh::lean_box(0);
                                        v_isShared_228_ = v_isSharedCheck_232_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_173_ = l_List_reduceReplicate___redArg___closed__0;
                if v_isShared_171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_170_, 0, v___x_173_);
                    v___x_175_ = v___x_170_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_176_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
                    v___x_175_ = v_reuseFailAlloc_176_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_175_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_190_) == 1 {
                    crate::leanh::lean_del_object(v___x_192_);
                    v_val_194_ = crate::leanh::lean_ctor_get(v_a_190_, 0);
                    v_isSharedCheck_219_ = (!crate::leanh::lean_is_exclusive(v_a_190_)) as u8;
                    if v_isSharedCheck_219_ == 0 {
                        v___x_196_ = v_a_190_;
                        v_isShared_197_ = v_isSharedCheck_219_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_194_);
                        crate::leanh::lean_dec(v_a_190_);
                        v___x_196_ = crate::leanh::lean_box(0);
                        v_isShared_197_ = v_isSharedCheck_219_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_190_);
                    crate::leanh::lean_dec_ref(v_arg_185_);
                    crate::leanh::lean_dec_ref(v_arg_179_);
                    v___x_220_ = l_List_reduceReplicate___redArg___closed__0;
                    if v_isShared_193_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_192_, 0, v___x_220_);
                        v___x_222_ = v___x_192_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_223_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
                        v___x_222_ = v_reuseFailAlloc_223_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v___x_198_ = l_List_replicateTR___redArg(v_val_194_, v_arg_179_);
                v___x_199_ = l_Lean_Meta_mkListLit(
                    v_arg_185_, v___x_198_, v_a_162_, v_a_163_, v_a_164_, v_a_165_,
                );
                if crate::leanh::lean_obj_tag(v___x_199_) == 0 {
                    v_a_200_ = crate::leanh::lean_ctor_get(v___x_199_, 0);
                    v_isSharedCheck_210_ = (!crate::leanh::lean_is_exclusive(v___x_199_)) as u8;
                    if v_isSharedCheck_210_ == 0 {
                        v___x_202_ = v___x_199_;
                        v_isShared_203_ = v_isSharedCheck_210_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_200_);
                        crate::leanh::lean_dec(v___x_199_);
                        v___x_202_ = crate::leanh::lean_box(0);
                        v_isShared_203_ = v_isSharedCheck_210_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_196_);
                    v_a_211_ = crate::leanh::lean_ctor_get(v___x_199_, 0);
                    v_isSharedCheck_218_ = (!crate::leanh::lean_is_exclusive(v___x_199_)) as u8;
                    if v_isSharedCheck_218_ == 0 {
                        v___x_213_ = v___x_199_;
                        v_isShared_214_ = v_isSharedCheck_218_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_211_);
                        crate::leanh::lean_dec(v___x_199_);
                        v___x_213_ = crate::leanh::lean_box(0);
                        v_isShared_214_ = v_isSharedCheck_218_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_197_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_196_, 0);
                    crate::leanh::lean_ctor_set(v___x_196_, 0, v_a_200_);
                    v___x_205_ = v___x_196_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_209_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_200_);
                    v___x_205_ = v_reuseFailAlloc_209_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_203_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_202_, 0, v___x_205_);
                    v___x_207_ = v___x_202_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
                    v___x_207_ = v_reuseFailAlloc_208_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_207_;
            }
            9 => {
                if v_isShared_214_ == 0 {
                    v___x_216_ = v___x_213_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_217_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
                    v___x_216_ = v_reuseFailAlloc_217_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_216_;
            }
            11 => {
                return v___x_222_;
            }
            12 => {
                if v_isShared_228_ == 0 {
                    v___x_230_ = v___x_227_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
                    v___x_230_ = v_reuseFailAlloc_231_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_230_;
            }
            14 => {
                if v_isShared_237_ == 0 {
                    v___x_239_ = v___x_236_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_240_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
                    v___x_239_ = v_reuseFailAlloc_240_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_reduceReplicate___redArg___boxed(
    mut v_e_242_: *mut crate::leanh::LeanObject,
    mut v_a_243_: *mut crate::leanh::LeanObject,
    mut v_a_244_: *mut crate::leanh::LeanObject,
    mut v_a_245_: *mut crate::leanh::LeanObject,
    mut v_a_246_: *mut crate::leanh::LeanObject,
    mut v_a_247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_248_ = l_List_reduceReplicate___redArg(v_e_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
    crate::leanh::lean_dec(v_a_246_);
    crate::leanh::lean_dec_ref(v_a_245_);
    crate::leanh::lean_dec(v_a_244_);
    crate::leanh::lean_dec_ref(v_a_243_);
    return v_res_248_;
}
pub unsafe fn l_List_reduceReplicate(
    mut v_e_249_: *mut crate::leanh::LeanObject,
    mut v_a_250_: *mut crate::leanh::LeanObject,
    mut v_a_251_: *mut crate::leanh::LeanObject,
    mut v_a_252_: *mut crate::leanh::LeanObject,
    mut v_a_253_: *mut crate::leanh::LeanObject,
    mut v_a_254_: *mut crate::leanh::LeanObject,
    mut v_a_255_: *mut crate::leanh::LeanObject,
    mut v_a_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_258_ = l_List_reduceReplicate___redArg(v_e_249_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
    return v___x_258_;
}
pub unsafe fn l_List_reduceReplicate___boxed(
    mut v_e_259_: *mut crate::leanh::LeanObject,
    mut v_a_260_: *mut crate::leanh::LeanObject,
    mut v_a_261_: *mut crate::leanh::LeanObject,
    mut v_a_262_: *mut crate::leanh::LeanObject,
    mut v_a_263_: *mut crate::leanh::LeanObject,
    mut v_a_264_: *mut crate::leanh::LeanObject,
    mut v_a_265_: *mut crate::leanh::LeanObject,
    mut v_a_266_: *mut crate::leanh::LeanObject,
    mut v_a_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l_List_reduceReplicate(
        v_e_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_,
    );
    crate::leanh::lean_dec(v_a_266_);
    crate::leanh::lean_dec_ref(v_a_265_);
    crate::leanh::lean_dec(v_a_264_);
    crate::leanh::lean_dec_ref(v_a_263_);
    crate::leanh::lean_dec(v_a_262_);
    crate::leanh::lean_dec_ref(v_a_261_);
    crate::leanh::lean_dec(v_a_260_);
    return v_res_268_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_285_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_;
    v___x_286_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_;
    v___x_287_ = crate::leanh::lean_alloc_closure(
        l_List_reduceReplicate___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_288_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_285_, v___x_286_, v___x_287_);
    return v___x_288_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14____boxed(
    mut v_a_289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_290_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_();
    return v_res_290_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = crate::leanh::lean_alloc_closure(
        l_List_reduceReplicate___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_292_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_292_, 0, v___x_291_);
    return v___x_292_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: u8 = 0;
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_294_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_;
    v___x_295_ = 1;
    v___x_296_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_);
    v___x_297_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_294_, v___x_295_, v___x_296_);
    return v___x_297_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16____boxed(
    mut v_a_298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_299_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_();
    return v_res_299_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_18_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: u8 = 0;
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_;
    v___x_302_ = 1;
    v___x_303_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_);
    v___x_304_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_301_, v___x_302_, v___x_303_);
    return v___x_304_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_18____boxed(
    mut v_a_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_306_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_18_();
    return v_res_306_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0____regBuiltin_List_reduceReplicate_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_14_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_16_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_0__List_reduceReplicate___regBuiltin_List_reduceReplicate_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List_1710460665____hygCtx___hyg_18_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
}
