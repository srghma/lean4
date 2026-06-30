// Lean compiler output
// Module: Lean.Linter.Util
// Imports: Lean.Server.InfoUtils Lean.Linter.Init Lean.Elab.Term
use crate::ffi::lean_name_eq;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::Impl::l_List_filterMapTR_go___redArg;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_typeNameImpl;
use crate::r#gen::Init::Prelude::l_id___boxed;
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_constName_x21, l_Lean_Expr_isConst};
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::Server::InfoUtils::{
    initialize_Lean_Server_InfoUtils,
    l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go, l_Lean_Elab_Info_contains,
    l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg, runtime_initialize_Lean_Server_InfoUtils,
};
pub static l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_id___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Linter_getDeclsByBody___lam__0___closed__0_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Linter_getDeclsByBody___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Linter_getDeclsByBody___lam__0___closed__1_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [69, 108, 97, 98, 0],
};
static mut l_Lean_Linter_getDeclsByBody___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Linter_getDeclsByBody___lam__0___closed__2_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Linter_getDeclsByBody___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Linter_getDeclsByBody___lam__0___closed__3_value: leanh::LeanStringObject<
    9,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [66, 111, 100, 121, 73, 110, 102, 111, 0],
};
static mut l_Lean_Linter_getDeclsByBody___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        11510100434945111860 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
        7892421401833366012 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__3_value)
            as *mut leanh::LeanObject,
        13586246166623106835 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_getDeclsByBody___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Linter_getDeclsByBody___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Linter_getDeclsByBody___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_getDeclsByBody___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_getDeclsByBody___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Linter_getNewDecls___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Linter_getNewDecls___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_getNewDecls___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_getNewDecls___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(
    mut v_toPure_178_: *mut leanh::LeanObject,
    mut v_x_179_: *mut leanh::LeanObject,
    mut v_x_180_: *mut leanh::LeanObject,
    mut v_x_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_182_: u8 = 0;
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_182_ = 1;
    v___x_183_ = leanh::lean_box((v___x_182_) as usize);
    v___x_184_ = leanh::lean_apply_2(v_toPure_178_, leanh::lean_box(0), v___x_183_);
    return v___x_184_;
}
pub unsafe fn l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed(
    mut v_toPure_185_: *mut leanh::LeanObject,
    mut v_x_186_: *mut leanh::LeanObject,
    mut v_x_187_: *mut leanh::LeanObject,
    mut v_x_188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_189_ =
        l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(
            v_toPure_185_,
            v_x_186_,
            v_x_187_,
            v_x_188_,
        );
    leanh::lean_dec_ref(v_x_188_);
    leanh::lean_dec_ref(v_x_187_);
    leanh::lean_dec_ref(v_x_186_);
    return v_res_189_;
}
pub unsafe fn l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(
    mut v_toPure_195_: *mut leanh::LeanObject,
    mut v_range_196_: *mut leanh::LeanObject,
    mut v_x_197_: *mut leanh::LeanObject,
    mut v_i_198_: *mut leanh::LeanObject,
    mut v_x_199_: *mut leanh::LeanObject,
    mut v_results_200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_202_: u8 = 0;
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_208_: u8 = 0;
    let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_215_: u8 = 0;
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_results_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_225_: u8 = 0;
    let mut v_i_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_229_: u8 = 0;
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_237_: u8 = 0;
    let mut v_isSharedCheck_238_: u8 = 0;
    let mut v_unused_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: u8 = 0;
    let mut v___x_246_: u8 = 0;
    let mut v___x_247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_218_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1;
                v___x_219_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2;
                v___x_220_ = l_List_filterMapTR_go___redArg(v___x_218_, v_results_200_, v___x_219_);
                v_results_221_ = l_List_filterMapTR_go___redArg(v___x_218_, v___x_220_, v___x_219_);
                if leanh::lean_obj_tag(v_results_221_) == 1 {
                    if leanh::lean_obj_tag(v_i_198_) == 4 {
                        v_head_222_ = leanh::lean_ctor_get(v_results_221_, 0);
                        v_isSharedCheck_238_ =
                            (!leanh::lean_is_exclusive(v_results_221_)) as u8;
                        if v_isSharedCheck_238_ == 0 {
                            v_unused_239_ = leanh::lean_ctor_get(v_results_221_, 1);
                            leanh::lean_dec(v_unused_239_);
                            v___x_224_ = v_results_221_;
                            v_isShared_225_ = v_isSharedCheck_238_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_head_222_);
                            leanh::lean_dec(v_results_221_);
                            v___x_224_ = leanh::lean_box(0);
                            v_isShared_225_ = v_isSharedCheck_238_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_i_198_);
                        v_head_240_ = leanh::lean_ctor_get(v_results_221_, 0);
                        leanh::lean_inc(v_head_240_);
                        leanh::lean_dec_ref_known(v_results_221_, 2);
                        v___x_241_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_241_, 0, v_head_240_);
                        v___x_242_ = leanh::lean_apply_2(
                            v_toPure_195_,
                            leanh::lean_box(0),
                            v___x_241_,
                        );
                        return v___x_242_;
                    }
                } else {
                    leanh::lean_dec(v_results_221_);
                    v_start_243_ = leanh::lean_ctor_get(v_range_196_, 0);
                    v_stop_244_ = leanh::lean_ctor_get(v_range_196_, 1);
                    v___x_245_ = 0;
                    v___x_246_ = l_Lean_Elab_Info_contains(v_i_198_, v_start_243_, v___x_245_);
                    if v___x_246_ == 0 {
                        v___y_202_ = v___x_246_;
                        state = 1;
                        continue;
                    } else {
                        v___x_247_ = l_Lean_Elab_Info_contains(v_i_198_, v_stop_244_, v___x_246_);
                        v___y_202_ = v___x_247_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_202_ == 0 {
                    leanh::lean_dec_ref(v_i_198_);
                    v___x_203_ = leanh::lean_box(0);
                    v___x_204_ = leanh::lean_apply_2(
                        v_toPure_195_,
                        leanh::lean_box(0),
                        v___x_203_,
                    );
                    return v___x_204_;
                } else {
                    if leanh::lean_obj_tag(v_i_198_) == 4 {
                        v_i_205_ = leanh::lean_ctor_get(v_i_198_, 0);
                        v_isSharedCheck_215_ = (!leanh::lean_is_exclusive(v_i_198_)) as u8;
                        if v_isSharedCheck_215_ == 0 {
                            v___x_207_ = v_i_198_;
                            v_isShared_208_ = v_isSharedCheck_215_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_i_205_);
                            leanh::lean_dec(v_i_198_);
                            v___x_207_ = leanh::lean_box(0);
                            v_isShared_208_ = v_isSharedCheck_215_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_i_198_);
                        v___x_216_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0;
                        v___x_217_ = leanh::lean_apply_2(
                            v_toPure_195_,
                            leanh::lean_box(0),
                            v___x_216_,
                        );
                        return v___x_217_;
                    }
                }
            }
            2 => {
                v___x_209_ = leanh::lean_box(0);
                v___x_210_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_210_, 0, v_i_205_);
                leanh::lean_ctor_set(v___x_210_, 1, v___x_209_);
                if v_isShared_208_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_207_, 1);
                    leanh::lean_ctor_set(v___x_207_, 0, v___x_210_);
                    v___x_212_ = v___x_207_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_214_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_210_);
                    v___x_212_ = v_reuseFailAlloc_214_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_213_ = leanh::lean_apply_2(
                    v_toPure_195_,
                    leanh::lean_box(0),
                    v___x_212_,
                );
                return v___x_213_;
            }
            4 => {
                v_i_226_ = leanh::lean_ctor_get(v_i_198_, 0);
                v_isSharedCheck_237_ = (!leanh::lean_is_exclusive(v_i_198_)) as u8;
                if v_isSharedCheck_237_ == 0 {
                    v___x_228_ = v_i_198_;
                    v_isShared_229_ = v_isSharedCheck_237_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_i_226_);
                    leanh::lean_dec(v_i_198_);
                    v___x_228_ = leanh::lean_box(0);
                    v_isShared_229_ = v_isSharedCheck_237_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_225_ == 0 {
                    leanh::lean_ctor_set(v___x_224_, 1, v_head_222_);
                    leanh::lean_ctor_set(v___x_224_, 0, v_i_226_);
                    v___x_231_ = v___x_224_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_236_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_236_, 0, v_i_226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_236_, 1, v_head_222_);
                    v___x_231_ = v_reuseFailAlloc_236_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_229_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_228_, 1);
                    leanh::lean_ctor_set(v___x_228_, 0, v___x_231_);
                    v___x_233_ = v___x_228_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_235_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_231_);
                    v___x_233_ = v_reuseFailAlloc_235_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_234_ = leanh::lean_apply_2(
                    v_toPure_195_,
                    leanh::lean_box(0),
                    v___x_233_,
                );
                return v___x_234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed(
    mut v_toPure_248_: *mut leanh::LeanObject,
    mut v_range_249_: *mut leanh::LeanObject,
    mut v_x_250_: *mut leanh::LeanObject,
    mut v_i_251_: *mut leanh::LeanObject,
    mut v_x_252_: *mut leanh::LeanObject,
    mut v_results_253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_254_ =
        l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(
            v_toPure_248_,
            v_range_249_,
            v_x_250_,
            v_i_251_,
            v_x_252_,
            v_results_253_,
        );
    leanh::lean_dec_ref(v_x_252_);
    leanh::lean_dec_ref(v_x_250_);
    leanh::lean_dec_ref(v_range_249_);
    return v_res_254_;
}
pub unsafe fn l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(
    mut v_inst_255_: *mut leanh::LeanObject,
    mut v_range_256_: *mut leanh::LeanObject,
    mut v_tree_257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_258_ = leanh::lean_ctor_get(v_inst_255_, 0);
    v_toPure_259_ = leanh::lean_ctor_get(v_toApplicative_258_, 1);
    leanh::lean_inc_n(v_toPure_259_, 2);
    v___f_260_ = leanh::lean_alloc_closure(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_260_, 0, v_toPure_259_);
    v___f_261_ = leanh::lean_alloc_closure(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 2);
    leanh::lean_closure_set(v___f_261_, 0, v_toPure_259_);
    leanh::lean_closure_set(v___f_261_, 1, v_range_256_);
    v___x_262_ = leanh::lean_box(0);
    v___x_263_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_255_,
        v___f_260_,
        v___f_261_,
        v___x_262_,
        v_tree_257_,
    );
    return v___x_263_;
}
pub unsafe fn l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go(
    mut v_m_264_: *mut leanh::LeanObject,
    mut v_inst_265_: *mut leanh::LeanObject,
    mut v_range_266_: *mut leanh::LeanObject,
    mut v_tree_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(
        v_inst_265_,
        v_range_266_,
        v_tree_267_,
    );
    return v___x_268_;
}
pub unsafe fn l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0(
    mut v_toPure_269_: *mut leanh::LeanObject,
    mut v_____do__lift_270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_278_: u8 = 0;
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_270_) == 1 {
                    v_val_274_ = leanh::lean_ctor_get(v_____do__lift_270_, 0);
                    leanh::lean_inc(v_val_274_);
                    leanh::lean_dec_ref_known(v_____do__lift_270_, 1);
                    if leanh::lean_obj_tag(v_val_274_) == 1 {
                        v_val_275_ = leanh::lean_ctor_get(v_val_274_, 0);
                        v_isSharedCheck_284_ = (!leanh::lean_is_exclusive(v_val_274_)) as u8;
                        if v_isSharedCheck_284_ == 0 {
                            v___x_277_ = v_val_274_;
                            v_isShared_278_ = v_isSharedCheck_284_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_275_);
                            leanh::lean_dec(v_val_274_);
                            v___x_277_ = leanh::lean_box(0);
                            v_isShared_278_ = v_isSharedCheck_284_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_274_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_____do__lift_270_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_272_ = leanh::lean_box(0);
                v___x_273_ = leanh::lean_apply_2(
                    v_toPure_269_,
                    leanh::lean_box(0),
                    v___x_272_,
                );
                return v___x_273_;
            }
            2 => {
                v___x_279_ = l_List_reverse___redArg(v_val_275_);
                if v_isShared_278_ == 0 {
                    leanh::lean_ctor_set(v___x_277_, 0, v___x_279_);
                    v___x_281_ = v___x_277_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_283_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_279_);
                    v___x_281_ = v_reuseFailAlloc_283_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_282_ = leanh::lean_apply_2(
                    v_toPure_269_,
                    leanh::lean_box(0),
                    v___x_281_,
                );
                return v___x_282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_collectMacroExpansions_x3f___redArg(
    mut v_inst_285_: *mut leanh::LeanObject,
    mut v_range_286_: *mut leanh::LeanObject,
    mut v_tree_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_288_ = leanh::lean_ctor_get(v_inst_285_, 0);
    v_toBind_289_ = leanh::lean_ctor_get(v_inst_285_, 1);
    leanh::lean_inc(v_toBind_289_);
    v_toPure_290_ = leanh::lean_ctor_get(v_toApplicative_288_, 1);
    leanh::lean_inc(v_toPure_290_);
    v___x_291_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(
        v_inst_285_,
        v_range_286_,
        v_tree_287_,
    );
    v___f_292_ = leanh::lean_alloc_closure(
        l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_292_, 0, v_toPure_290_);
    v___x_293_ = leanh::lean_apply_4(
        v_toBind_289_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_291_,
        v___f_292_,
    );
    return v___x_293_;
}
pub unsafe fn l_Lean_Linter_collectMacroExpansions_x3f(
    mut v_m_294_: *mut leanh::LeanObject,
    mut v_inst_295_: *mut leanh::LeanObject,
    mut v_range_296_: *mut leanh::LeanObject,
    mut v_tree_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ =
        l_Lean_Linter_collectMacroExpansions_x3f___redArg(v_inst_295_, v_range_296_, v_tree_297_);
    return v___x_298_;
}
pub unsafe fn l_Lean_Linter_getDeclsByBody___lam__0(
    mut v_ctx_308_: *mut leanh::LeanObject,
    mut v_i_309_: *mut leanh::LeanObject,
    mut v_x_310_: *mut leanh::LeanObject,
    mut v_decls_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_316_: u8 = 0;
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: u8 = 0;
    let mut v_parentDecl_x3f_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_325_: u8 = 0;
    let mut v_unused_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_i_309_) == 10 {
                    v_i_312_ = leanh::lean_ctor_get(v_i_309_, 0);
                    leanh::lean_inc_ref(v_i_312_);
                    leanh::lean_dec_ref_known(v_i_309_, 1);
                    v_value_313_ = leanh::lean_ctor_get(v_i_312_, 1);
                    v_isSharedCheck_325_ = (!leanh::lean_is_exclusive(v_i_312_)) as u8;
                    if v_isSharedCheck_325_ == 0 {
                        v_unused_326_ = leanh::lean_ctor_get(v_i_312_, 0);
                        leanh::lean_dec(v_unused_326_);
                        v___x_315_ = v_i_312_;
                        v_isShared_316_ = v_isSharedCheck_325_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_313_);
                        leanh::lean_dec(v_i_312_);
                        v___x_315_ = leanh::lean_box(0);
                        v_isShared_316_ = v_isSharedCheck_325_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_i_309_);
                    return v_decls_311_;
                }
            }
            1 => {
                v___x_317_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_value_313_);
                leanh::lean_dec(v_value_313_);
                v___x_318_ = l_Lean_Linter_getDeclsByBody___lam__0___closed__4;
                v___x_319_ = lean_name_eq(v___x_317_, v___x_318_);
                leanh::lean_dec(v___x_317_);
                if v___x_319_ == 0 {
                    leanh::lean_del_object(v___x_315_);
                    return v_decls_311_;
                } else {
                    v_parentDecl_x3f_320_ = leanh::lean_ctor_get(v_ctx_308_, 1);
                    if leanh::lean_obj_tag(v_parentDecl_x3f_320_) == 1 {
                        v_val_321_ = leanh::lean_ctor_get(v_parentDecl_x3f_320_, 0);
                        leanh::lean_inc(v_val_321_);
                        if v_isShared_316_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_315_, 1);
                            leanh::lean_ctor_set(v___x_315_, 1, v_decls_311_);
                            leanh::lean_ctor_set(v___x_315_, 0, v_val_321_);
                            v___x_323_ = v___x_315_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_324_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_324_, 0, v_val_321_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_324_, 1, v_decls_311_);
                            v___x_323_ = v_reuseFailAlloc_324_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_315_);
                        return v_decls_311_;
                    }
                }
            }
            2 => {
                return v___x_323_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_getDeclsByBody___lam__0___boxed(
    mut v_ctx_327_: *mut leanh::LeanObject,
    mut v_i_328_: *mut leanh::LeanObject,
    mut v_x_329_: *mut leanh::LeanObject,
    mut v_decls_330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_331_ =
        l_Lean_Linter_getDeclsByBody___lam__0(v_ctx_327_, v_i_328_, v_x_329_, v_decls_330_);
    leanh::lean_dec_ref(v_x_329_);
    leanh::lean_dec_ref(v_ctx_327_);
    return v_res_331_;
}
pub unsafe fn l_Lean_Linter_getDeclsByBody(
    mut v_t_333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_334_ = l_Lean_Linter_getDeclsByBody___closed__0;
    v___x_335_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_334_, v_t_333_);
    return v___x_335_;
}
pub unsafe fn l_Lean_Linter_getNewDecls___lam__0(
    mut v_x_336_: *mut leanh::LeanObject,
    mut v_i_337_: *mut leanh::LeanObject,
    mut v_x_338_: *mut leanh::LeanObject,
    mut v_acc_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_i_337_) == 1 {
        let mut v_i_340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isBinder_341_: u8 = 0;
        v_i_340_ = leanh::lean_ctor_get(v_i_337_, 0);
        v_isBinder_341_ = leanh::lean_ctor_get_uint8(
            v_i_340_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        );
        if v_isBinder_341_ == 0 {
            return v_acc_339_;
        } else {
            let mut v_expr_342_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_343_: u8 = 0;
            v_expr_342_ = leanh::lean_ctor_get(v_i_340_, 3);
            v___x_343_ = l_Lean_Expr_isConst(v_expr_342_);
            if v___x_343_ == 0 {
                return v_acc_339_;
            } else {
                let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_344_ = l_Lean_Expr_constName_x21(v_expr_342_);
                v___x_345_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_345_, 0, v___x_344_);
                leanh::lean_ctor_set(v___x_345_, 1, v_acc_339_);
                return v___x_345_;
            }
        }
    } else {
        return v_acc_339_;
    }
}
pub unsafe fn l_Lean_Linter_getNewDecls___lam__0___boxed(
    mut v_x_346_: *mut leanh::LeanObject,
    mut v_i_347_: *mut leanh::LeanObject,
    mut v_x_348_: *mut leanh::LeanObject,
    mut v_acc_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_350_ = l_Lean_Linter_getNewDecls___lam__0(v_x_346_, v_i_347_, v_x_348_, v_acc_349_);
    leanh::lean_dec_ref(v_x_348_);
    leanh::lean_dec_ref(v_i_347_);
    leanh::lean_dec_ref(v_x_346_);
    return v_res_350_;
}
pub unsafe fn l_Lean_Linter_getNewDecls(
    mut v_t_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_353_ = l_Lean_Linter_getNewDecls___closed__0;
    v___x_354_ = l_Lean_Elab_InfoTree_collectNodesBottomUp___redArg(v___f_353_, v_t_352_);
    return v___x_354_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Util(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Util(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Util(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_InfoUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_Util(builtin);
}