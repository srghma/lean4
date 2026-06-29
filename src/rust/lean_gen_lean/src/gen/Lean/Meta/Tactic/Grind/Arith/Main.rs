// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Main
// Imports: Init.Grind.Propagator Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr Lean.Meta.Tactic.Grind.PropagatorAttr
use crate::r#gen::Init::Grind::Propagator::{
    initialize_Init_Grind_Propagator, runtime_initialize_Init_Grind_Propagator,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::LeCnstr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr,
    l_Lean_Meta_Grind_Arith_Cutsat_propagateLe, l_Lean_Meta_Grind_Arith_Cutsat_propagateLt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::IneqCnstr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr,
    l_Lean_Meta_Grind_Arith_Linear_propagateIneq,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::PropagatorAttr::{
    initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
    l_Lean_Meta_Grind_registerBuiltinDownwardPropagator,
    runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_isEqFalse___redArg, l_Lean_Meta_Grind_isEqTrue___redArg,
};
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject,8347582161988589016 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject,7316284823769321069 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject,17878876274162330439 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject,11833570877100518198 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateLE(
    mut v_e_149_: *mut crate::leanh::LeanObject,
    mut v_a_150_: *mut crate::leanh::LeanObject,
    mut v_a_151_: *mut crate::leanh::LeanObject,
    mut v_a_152_: *mut crate::leanh::LeanObject,
    mut v_a_153_: *mut crate::leanh::LeanObject,
    mut v_a_154_: *mut crate::leanh::LeanObject,
    mut v_a_155_: *mut crate::leanh::LeanObject,
    mut v_a_156_: *mut crate::leanh::LeanObject,
    mut v_a_157_: *mut crate::leanh::LeanObject,
    mut v_a_158_: *mut crate::leanh::LeanObject,
    mut v_a_159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_163_: u8 = 0;
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_168_: u8 = 0;
    let mut v___x_169_: u8 = 0;
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: u8 = 0;
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: u8 = 0;
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_178_: u8 = 0;
    let mut v_a_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_182_: u8 = 0;
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_186_: u8 = 0;
    let mut v___x_187_: u8 = 0;
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: u8 = 0;
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_194_: u8 = 0;
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_149_);
                v___x_161_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                    v_e_149_, v_a_150_, v_a_154_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                );
                if crate::leanh::lean_obj_tag(v___x_161_) == 0 {
                    v_a_162_ = crate::leanh::lean_ctor_get(v___x_161_, 0);
                    crate::leanh::lean_inc(v_a_162_);
                    crate::leanh::lean_dec_ref_known(v___x_161_, 1);
                    v___x_163_ = (crate::leanh::lean_unbox(v_a_162_) as u8);
                    if v___x_163_ == 0 {
                        crate::leanh::lean_inc_ref(v_e_149_);
                        v___x_164_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                            v_e_149_, v_a_150_, v_a_154_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_164_) == 0 {
                            v_a_165_ = crate::leanh::lean_ctor_get(v___x_164_, 0);
                            v_isSharedCheck_178_ =
                                (!crate::leanh::lean_is_exclusive(v___x_164_)) as u8;
                            if v_isSharedCheck_178_ == 0 {
                                v___x_167_ = v___x_164_;
                                v_isShared_168_ = v_isSharedCheck_178_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_165_);
                                crate::leanh::lean_dec(v___x_164_);
                                v___x_167_ = crate::leanh::lean_box(0);
                                v_isShared_168_ = v_isSharedCheck_178_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_162_);
                            crate::leanh::lean_dec_ref(v_e_149_);
                            v_a_179_ = crate::leanh::lean_ctor_get(v___x_164_, 0);
                            v_isSharedCheck_186_ =
                                (!crate::leanh::lean_is_exclusive(v___x_164_)) as u8;
                            if v_isSharedCheck_186_ == 0 {
                                v___x_181_ = v___x_164_;
                                v_isShared_182_ = v_isSharedCheck_186_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_179_);
                                crate::leanh::lean_dec(v___x_164_);
                                v___x_181_ = crate::leanh::lean_box(0);
                                v_isShared_182_ = v_isSharedCheck_186_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_187_ = (crate::leanh::lean_unbox(v_a_162_) as u8);
                        crate::leanh::lean_inc_ref(v_e_149_);
                        v___x_188_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(
                            v_e_149_, v___x_187_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_,
                            v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_188_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_188_, 1);
                            v___x_189_ = (crate::leanh::lean_unbox(v_a_162_) as u8);
                            crate::leanh::lean_dec(v_a_162_);
                            v___x_190_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(
                                v_e_149_, v___x_189_, v_a_150_, v_a_151_, v_a_152_, v_a_153_,
                                v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                            );
                            return v___x_190_;
                        } else {
                            crate::leanh::lean_dec(v_a_162_);
                            crate::leanh::lean_dec_ref(v_e_149_);
                            return v___x_188_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_149_);
                    v_a_191_ = crate::leanh::lean_ctor_get(v___x_161_, 0);
                    v_isSharedCheck_198_ = (!crate::leanh::lean_is_exclusive(v___x_161_)) as u8;
                    if v_isSharedCheck_198_ == 0 {
                        v___x_193_ = v___x_161_;
                        v_isShared_194_ = v_isSharedCheck_198_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_191_);
                        crate::leanh::lean_dec(v___x_161_);
                        v___x_193_ = crate::leanh::lean_box(0);
                        v_isShared_194_ = v_isSharedCheck_198_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_169_ = (crate::leanh::lean_unbox(v_a_165_) as u8);
                crate::leanh::lean_dec(v_a_165_);
                if v___x_169_ == 0 {
                    crate::leanh::lean_dec(v_a_162_);
                    crate::leanh::lean_dec_ref(v_e_149_);
                    v___x_170_ = crate::leanh::lean_box(0);
                    if v_isShared_168_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_167_, 0, v___x_170_);
                        v___x_172_ = v___x_167_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_173_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
                        v___x_172_ = v_reuseFailAlloc_173_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_167_);
                    v___x_174_ = (crate::leanh::lean_unbox(v_a_162_) as u8);
                    crate::leanh::lean_inc_ref(v_e_149_);
                    v___x_175_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(
                        v_e_149_, v___x_174_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_,
                        v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_175_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_175_, 1);
                        v___x_176_ = (crate::leanh::lean_unbox(v_a_162_) as u8);
                        crate::leanh::lean_dec(v_a_162_);
                        v___x_177_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(
                            v_e_149_, v___x_176_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_,
                            v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                        );
                        return v___x_177_;
                    } else {
                        crate::leanh::lean_dec(v_a_162_);
                        crate::leanh::lean_dec_ref(v_e_149_);
                        return v___x_175_;
                    }
                }
            }
            2 => {
                return v___x_172_;
            }
            3 => {
                if v_isShared_182_ == 0 {
                    v___x_184_ = v___x_181_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
                    v___x_184_ = v_reuseFailAlloc_185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_184_;
            }
            5 => {
                if v_isShared_194_ == 0 {
                    v___x_196_ = v___x_193_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_197_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
                    v___x_196_ = v_reuseFailAlloc_197_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateLE___boxed(
    mut v_e_199_: *mut crate::leanh::LeanObject,
    mut v_a_200_: *mut crate::leanh::LeanObject,
    mut v_a_201_: *mut crate::leanh::LeanObject,
    mut v_a_202_: *mut crate::leanh::LeanObject,
    mut v_a_203_: *mut crate::leanh::LeanObject,
    mut v_a_204_: *mut crate::leanh::LeanObject,
    mut v_a_205_: *mut crate::leanh::LeanObject,
    mut v_a_206_: *mut crate::leanh::LeanObject,
    mut v_a_207_: *mut crate::leanh::LeanObject,
    mut v_a_208_: *mut crate::leanh::LeanObject,
    mut v_a_209_: *mut crate::leanh::LeanObject,
    mut v_a_210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_211_ = l_Lean_Meta_Grind_Arith_propagateLE(
        v_e_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_,
        v_a_208_, v_a_209_,
    );
    crate::leanh::lean_dec(v_a_209_);
    crate::leanh::lean_dec_ref(v_a_208_);
    crate::leanh::lean_dec(v_a_207_);
    crate::leanh::lean_dec_ref(v_a_206_);
    crate::leanh::lean_dec(v_a_205_);
    crate::leanh::lean_dec_ref(v_a_204_);
    crate::leanh::lean_dec(v_a_203_);
    crate::leanh::lean_dec_ref(v_a_202_);
    crate::leanh::lean_dec(v_a_201_);
    crate::leanh::lean_dec(v_a_200_);
    return v_res_211_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_218_ = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_;
    v___x_219_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateLE___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_220_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_218_, v___x_219_);
    return v___x_220_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8____boxed(
    mut v_a_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_222_ = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
    return v_res_222_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateLT(
    mut v_e_223_: *mut crate::leanh::LeanObject,
    mut v_a_224_: *mut crate::leanh::LeanObject,
    mut v_a_225_: *mut crate::leanh::LeanObject,
    mut v_a_226_: *mut crate::leanh::LeanObject,
    mut v_a_227_: *mut crate::leanh::LeanObject,
    mut v_a_228_: *mut crate::leanh::LeanObject,
    mut v_a_229_: *mut crate::leanh::LeanObject,
    mut v_a_230_: *mut crate::leanh::LeanObject,
    mut v_a_231_: *mut crate::leanh::LeanObject,
    mut v_a_232_: *mut crate::leanh::LeanObject,
    mut v_a_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: u8 = 0;
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_242_: u8 = 0;
    let mut v___x_243_: u8 = 0;
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: u8 = 0;
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: u8 = 0;
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_252_: u8 = 0;
    let mut v_a_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_256_: u8 = 0;
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_260_: u8 = 0;
    let mut v___x_261_: u8 = 0;
    let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: u8 = 0;
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_268_: u8 = 0;
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_223_);
                v___x_235_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                    v_e_223_, v_a_224_, v_a_228_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                );
                if crate::leanh::lean_obj_tag(v___x_235_) == 0 {
                    v_a_236_ = crate::leanh::lean_ctor_get(v___x_235_, 0);
                    crate::leanh::lean_inc(v_a_236_);
                    crate::leanh::lean_dec_ref_known(v___x_235_, 1);
                    v___x_237_ = (crate::leanh::lean_unbox(v_a_236_) as u8);
                    if v___x_237_ == 0 {
                        crate::leanh::lean_inc_ref(v_e_223_);
                        v___x_238_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                            v_e_223_, v_a_224_, v_a_228_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_238_) == 0 {
                            v_a_239_ = crate::leanh::lean_ctor_get(v___x_238_, 0);
                            v_isSharedCheck_252_ =
                                (!crate::leanh::lean_is_exclusive(v___x_238_)) as u8;
                            if v_isSharedCheck_252_ == 0 {
                                v___x_241_ = v___x_238_;
                                v_isShared_242_ = v_isSharedCheck_252_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_239_);
                                crate::leanh::lean_dec(v___x_238_);
                                v___x_241_ = crate::leanh::lean_box(0);
                                v_isShared_242_ = v_isSharedCheck_252_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_236_);
                            crate::leanh::lean_dec_ref(v_e_223_);
                            v_a_253_ = crate::leanh::lean_ctor_get(v___x_238_, 0);
                            v_isSharedCheck_260_ =
                                (!crate::leanh::lean_is_exclusive(v___x_238_)) as u8;
                            if v_isSharedCheck_260_ == 0 {
                                v___x_255_ = v___x_238_;
                                v_isShared_256_ = v_isSharedCheck_260_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_253_);
                                crate::leanh::lean_dec(v___x_238_);
                                v___x_255_ = crate::leanh::lean_box(0);
                                v_isShared_256_ = v_isSharedCheck_260_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_261_ = (crate::leanh::lean_unbox(v_a_236_) as u8);
                        crate::leanh::lean_inc_ref(v_e_223_);
                        v___x_262_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(
                            v_e_223_, v___x_261_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_,
                            v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_262_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_262_, 1);
                            v___x_263_ = (crate::leanh::lean_unbox(v_a_236_) as u8);
                            crate::leanh::lean_dec(v_a_236_);
                            v___x_264_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(
                                v_e_223_, v___x_263_, v_a_224_, v_a_225_, v_a_226_, v_a_227_,
                                v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                            );
                            return v___x_264_;
                        } else {
                            crate::leanh::lean_dec(v_a_236_);
                            crate::leanh::lean_dec_ref(v_e_223_);
                            return v___x_262_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_223_);
                    v_a_265_ = crate::leanh::lean_ctor_get(v___x_235_, 0);
                    v_isSharedCheck_272_ = (!crate::leanh::lean_is_exclusive(v___x_235_)) as u8;
                    if v_isSharedCheck_272_ == 0 {
                        v___x_267_ = v___x_235_;
                        v_isShared_268_ = v_isSharedCheck_272_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_265_);
                        crate::leanh::lean_dec(v___x_235_);
                        v___x_267_ = crate::leanh::lean_box(0);
                        v_isShared_268_ = v_isSharedCheck_272_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_243_ = (crate::leanh::lean_unbox(v_a_239_) as u8);
                crate::leanh::lean_dec(v_a_239_);
                if v___x_243_ == 0 {
                    crate::leanh::lean_dec(v_a_236_);
                    crate::leanh::lean_dec_ref(v_e_223_);
                    v___x_244_ = crate::leanh::lean_box(0);
                    if v_isShared_242_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_241_, 0, v___x_244_);
                        v___x_246_ = v___x_241_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_247_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
                        v___x_246_ = v_reuseFailAlloc_247_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_241_);
                    v___x_248_ = (crate::leanh::lean_unbox(v_a_236_) as u8);
                    crate::leanh::lean_inc_ref(v_e_223_);
                    v___x_249_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(
                        v_e_223_, v___x_248_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_,
                        v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_249_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_249_, 1);
                        v___x_250_ = (crate::leanh::lean_unbox(v_a_236_) as u8);
                        crate::leanh::lean_dec(v_a_236_);
                        v___x_251_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(
                            v_e_223_, v___x_250_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_,
                            v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                        );
                        return v___x_251_;
                    } else {
                        crate::leanh::lean_dec(v_a_236_);
                        crate::leanh::lean_dec_ref(v_e_223_);
                        return v___x_249_;
                    }
                }
            }
            2 => {
                return v___x_246_;
            }
            3 => {
                if v_isShared_256_ == 0 {
                    v___x_258_ = v___x_255_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_259_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
                    v___x_258_ = v_reuseFailAlloc_259_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_258_;
            }
            5 => {
                if v_isShared_268_ == 0 {
                    v___x_270_ = v___x_267_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
                    v___x_270_ = v_reuseFailAlloc_271_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateLT___boxed(
    mut v_e_273_: *mut crate::leanh::LeanObject,
    mut v_a_274_: *mut crate::leanh::LeanObject,
    mut v_a_275_: *mut crate::leanh::LeanObject,
    mut v_a_276_: *mut crate::leanh::LeanObject,
    mut v_a_277_: *mut crate::leanh::LeanObject,
    mut v_a_278_: *mut crate::leanh::LeanObject,
    mut v_a_279_: *mut crate::leanh::LeanObject,
    mut v_a_280_: *mut crate::leanh::LeanObject,
    mut v_a_281_: *mut crate::leanh::LeanObject,
    mut v_a_282_: *mut crate::leanh::LeanObject,
    mut v_a_283_: *mut crate::leanh::LeanObject,
    mut v_a_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_285_ = l_Lean_Meta_Grind_Arith_propagateLT(
        v_e_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_,
        v_a_282_, v_a_283_,
    );
    crate::leanh::lean_dec(v_a_283_);
    crate::leanh::lean_dec_ref(v_a_282_);
    crate::leanh::lean_dec(v_a_281_);
    crate::leanh::lean_dec_ref(v_a_280_);
    crate::leanh::lean_dec(v_a_279_);
    crate::leanh::lean_dec_ref(v_a_278_);
    crate::leanh::lean_dec(v_a_277_);
    crate::leanh::lean_dec_ref(v_a_276_);
    crate::leanh::lean_dec(v_a_275_);
    crate::leanh::lean_dec(v_a_274_);
    return v_res_285_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_;
    v___x_293_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateLT___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_294_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_292_, v___x_293_);
    return v___x_294_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8____boxed(
    mut v_a_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_296_ = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
    return v_res_296_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Main(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Propagator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Main(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Main(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Propagator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Main(builtin);
}
