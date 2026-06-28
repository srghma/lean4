// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Main
// Imports: Init.Grind.Propagator Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr Lean.Meta.Tactic.Grind.PropagatorAttr
use crate::r#gen::Init::Grind::Propagator::{
    initialize_Init_Grind_Propagator, runtime_initialize_Init_Grind_Propagator,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unbox,
};
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value) as *mut LeanObject,8347582161988589016 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value) as *mut LeanObject,7316284823769321069 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value) as *mut LeanObject,17878876274162330439 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value) as *mut LeanObject,11833570877100518198 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateLE(
    mut v_e_149_: *mut LeanObject,
    mut v_a_150_: *mut LeanObject,
    mut v_a_151_: *mut LeanObject,
    mut v_a_152_: *mut LeanObject,
    mut v_a_153_: *mut LeanObject,
    mut v_a_154_: *mut LeanObject,
    mut v_a_155_: *mut LeanObject,
    mut v_a_156_: *mut LeanObject,
    mut v_a_157_: *mut LeanObject,
    mut v_a_158_: *mut LeanObject,
    mut v_a_159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_163_: u8 = 0;
    let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_168_: u8 = 0;
    let mut v___x_169_: u8 = 0;
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_174_: u8 = 0;
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_176_: u8 = 0;
    let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_178_: u8 = 0;
    let mut v_a_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_182_: u8 = 0;
    let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_186_: u8 = 0;
    let mut v___x_187_: u8 = 0;
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_189_: u8 = 0;
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_194_: u8 = 0;
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_149_);
                v___x_161_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                    v_e_149_, v_a_150_, v_a_154_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                );
                if lean_obj_tag(v___x_161_) == 0 {
                    v_a_162_ = lean_ctor_get(v___x_161_, 0);
                    lean_inc(v_a_162_);
                    lean_dec_ref_known(v___x_161_, 1);
                    v___x_163_ = (lean_unbox(v_a_162_) as u8);
                    if v___x_163_ == 0 {
                        lean_inc_ref(v_e_149_);
                        v___x_164_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                            v_e_149_, v_a_150_, v_a_154_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                        );
                        if lean_obj_tag(v___x_164_) == 0 {
                            v_a_165_ = lean_ctor_get(v___x_164_, 0);
                            v_isSharedCheck_178_ = (!lean_is_exclusive(v___x_164_)) as u8;
                            if v_isSharedCheck_178_ == 0 {
                                v___x_167_ = v___x_164_;
                                v_isShared_168_ = v_isSharedCheck_178_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_165_);
                                lean_dec(v___x_164_);
                                v___x_167_ = lean_box(0);
                                v_isShared_168_ = v_isSharedCheck_178_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_162_);
                            lean_dec_ref(v_e_149_);
                            v_a_179_ = lean_ctor_get(v___x_164_, 0);
                            v_isSharedCheck_186_ = (!lean_is_exclusive(v___x_164_)) as u8;
                            if v_isSharedCheck_186_ == 0 {
                                v___x_181_ = v___x_164_;
                                v_isShared_182_ = v_isSharedCheck_186_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_179_);
                                lean_dec(v___x_164_);
                                v___x_181_ = lean_box(0);
                                v_isShared_182_ = v_isSharedCheck_186_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_187_ = (lean_unbox(v_a_162_) as u8);
                        lean_inc_ref(v_e_149_);
                        v___x_188_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(
                            v_e_149_, v___x_187_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_,
                            v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                        );
                        if lean_obj_tag(v___x_188_) == 0 {
                            lean_dec_ref_known(v___x_188_, 1);
                            v___x_189_ = (lean_unbox(v_a_162_) as u8);
                            lean_dec(v_a_162_);
                            v___x_190_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(
                                v_e_149_, v___x_189_, v_a_150_, v_a_151_, v_a_152_, v_a_153_,
                                v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                            );
                            return v___x_190_;
                        } else {
                            lean_dec(v_a_162_);
                            lean_dec_ref(v_e_149_);
                            return v___x_188_;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_149_);
                    v_a_191_ = lean_ctor_get(v___x_161_, 0);
                    v_isSharedCheck_198_ = (!lean_is_exclusive(v___x_161_)) as u8;
                    if v_isSharedCheck_198_ == 0 {
                        v___x_193_ = v___x_161_;
                        v_isShared_194_ = v_isSharedCheck_198_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_191_);
                        lean_dec(v___x_161_);
                        v___x_193_ = lean_box(0);
                        v_isShared_194_ = v_isSharedCheck_198_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_169_ = (lean_unbox(v_a_165_) as u8);
                lean_dec(v_a_165_);
                if v___x_169_ == 0 {
                    lean_dec(v_a_162_);
                    lean_dec_ref(v_e_149_);
                    v___x_170_ = lean_box(0);
                    if v_isShared_168_ == 0 {
                        lean_ctor_set(v___x_167_, 0, v___x_170_);
                        v___x_172_ = v___x_167_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
                        v___x_172_ = v_reuseFailAlloc_173_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_167_);
                    v___x_174_ = (lean_unbox(v_a_162_) as u8);
                    lean_inc_ref(v_e_149_);
                    v___x_175_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(
                        v_e_149_, v___x_174_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_,
                        v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                    );
                    if lean_obj_tag(v___x_175_) == 0 {
                        lean_dec_ref_known(v___x_175_, 1);
                        v___x_176_ = (lean_unbox(v_a_162_) as u8);
                        lean_dec(v_a_162_);
                        v___x_177_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(
                            v_e_149_, v___x_176_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_,
                            v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_,
                        );
                        return v___x_177_;
                    } else {
                        lean_dec(v_a_162_);
                        lean_dec_ref(v_e_149_);
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
                    v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
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
                    v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
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
    mut v_e_199_: *mut LeanObject,
    mut v_a_200_: *mut LeanObject,
    mut v_a_201_: *mut LeanObject,
    mut v_a_202_: *mut LeanObject,
    mut v_a_203_: *mut LeanObject,
    mut v_a_204_: *mut LeanObject,
    mut v_a_205_: *mut LeanObject,
    mut v_a_206_: *mut LeanObject,
    mut v_a_207_: *mut LeanObject,
    mut v_a_208_: *mut LeanObject,
    mut v_a_209_: *mut LeanObject,
    mut v_a_210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_211_: *mut LeanObject = core::ptr::null_mut();
    v_res_211_ = l_Lean_Meta_Grind_Arith_propagateLE(
        v_e_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_,
        v_a_208_, v_a_209_,
    );
    lean_dec(v_a_209_);
    lean_dec_ref(v_a_208_);
    lean_dec(v_a_207_);
    lean_dec_ref(v_a_206_);
    lean_dec(v_a_205_);
    lean_dec_ref(v_a_204_);
    lean_dec(v_a_203_);
    lean_dec_ref(v_a_202_);
    lean_dec(v_a_201_);
    lean_dec(v_a_200_);
    return v_res_211_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_()
-> *mut LeanObject {
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    v___x_218_ = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_;
    v___x_219_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateLE___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_220_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_218_, v___x_219_);
    return v___x_220_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8____boxed(
    mut v_a_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_222_: *mut LeanObject = core::ptr::null_mut();
    v_res_222_ = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
    return v_res_222_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateLT(
    mut v_e_223_: *mut LeanObject,
    mut v_a_224_: *mut LeanObject,
    mut v_a_225_: *mut LeanObject,
    mut v_a_226_: *mut LeanObject,
    mut v_a_227_: *mut LeanObject,
    mut v_a_228_: *mut LeanObject,
    mut v_a_229_: *mut LeanObject,
    mut v_a_230_: *mut LeanObject,
    mut v_a_231_: *mut LeanObject,
    mut v_a_232_: *mut LeanObject,
    mut v_a_233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_237_: u8 = 0;
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_242_: u8 = 0;
    let mut v___x_243_: u8 = 0;
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_248_: u8 = 0;
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: u8 = 0;
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_252_: u8 = 0;
    let mut v_a_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_256_: u8 = 0;
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_260_: u8 = 0;
    let mut v___x_261_: u8 = 0;
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_263_: u8 = 0;
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_268_: u8 = 0;
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_223_);
                v___x_235_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                    v_e_223_, v_a_224_, v_a_228_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                );
                if lean_obj_tag(v___x_235_) == 0 {
                    v_a_236_ = lean_ctor_get(v___x_235_, 0);
                    lean_inc(v_a_236_);
                    lean_dec_ref_known(v___x_235_, 1);
                    v___x_237_ = (lean_unbox(v_a_236_) as u8);
                    if v___x_237_ == 0 {
                        lean_inc_ref(v_e_223_);
                        v___x_238_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                            v_e_223_, v_a_224_, v_a_228_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                        );
                        if lean_obj_tag(v___x_238_) == 0 {
                            v_a_239_ = lean_ctor_get(v___x_238_, 0);
                            v_isSharedCheck_252_ = (!lean_is_exclusive(v___x_238_)) as u8;
                            if v_isSharedCheck_252_ == 0 {
                                v___x_241_ = v___x_238_;
                                v_isShared_242_ = v_isSharedCheck_252_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_239_);
                                lean_dec(v___x_238_);
                                v___x_241_ = lean_box(0);
                                v_isShared_242_ = v_isSharedCheck_252_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_236_);
                            lean_dec_ref(v_e_223_);
                            v_a_253_ = lean_ctor_get(v___x_238_, 0);
                            v_isSharedCheck_260_ = (!lean_is_exclusive(v___x_238_)) as u8;
                            if v_isSharedCheck_260_ == 0 {
                                v___x_255_ = v___x_238_;
                                v_isShared_256_ = v_isSharedCheck_260_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_253_);
                                lean_dec(v___x_238_);
                                v___x_255_ = lean_box(0);
                                v_isShared_256_ = v_isSharedCheck_260_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_261_ = (lean_unbox(v_a_236_) as u8);
                        lean_inc_ref(v_e_223_);
                        v___x_262_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(
                            v_e_223_, v___x_261_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_,
                            v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                        );
                        if lean_obj_tag(v___x_262_) == 0 {
                            lean_dec_ref_known(v___x_262_, 1);
                            v___x_263_ = (lean_unbox(v_a_236_) as u8);
                            lean_dec(v_a_236_);
                            v___x_264_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(
                                v_e_223_, v___x_263_, v_a_224_, v_a_225_, v_a_226_, v_a_227_,
                                v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                            );
                            return v___x_264_;
                        } else {
                            lean_dec(v_a_236_);
                            lean_dec_ref(v_e_223_);
                            return v___x_262_;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_223_);
                    v_a_265_ = lean_ctor_get(v___x_235_, 0);
                    v_isSharedCheck_272_ = (!lean_is_exclusive(v___x_235_)) as u8;
                    if v_isSharedCheck_272_ == 0 {
                        v___x_267_ = v___x_235_;
                        v_isShared_268_ = v_isSharedCheck_272_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_265_);
                        lean_dec(v___x_235_);
                        v___x_267_ = lean_box(0);
                        v_isShared_268_ = v_isSharedCheck_272_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_243_ = (lean_unbox(v_a_239_) as u8);
                lean_dec(v_a_239_);
                if v___x_243_ == 0 {
                    lean_dec(v_a_236_);
                    lean_dec_ref(v_e_223_);
                    v___x_244_ = lean_box(0);
                    if v_isShared_242_ == 0 {
                        lean_ctor_set(v___x_241_, 0, v___x_244_);
                        v___x_246_ = v___x_241_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
                        v___x_246_ = v_reuseFailAlloc_247_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_241_);
                    v___x_248_ = (lean_unbox(v_a_236_) as u8);
                    lean_inc_ref(v_e_223_);
                    v___x_249_ = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(
                        v_e_223_, v___x_248_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_,
                        v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                    );
                    if lean_obj_tag(v___x_249_) == 0 {
                        lean_dec_ref_known(v___x_249_, 1);
                        v___x_250_ = (lean_unbox(v_a_236_) as u8);
                        lean_dec(v_a_236_);
                        v___x_251_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(
                            v_e_223_, v___x_250_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_,
                            v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_,
                        );
                        return v___x_251_;
                    } else {
                        lean_dec(v_a_236_);
                        lean_dec_ref(v_e_223_);
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
                    v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
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
                    v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
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
    mut v_e_273_: *mut LeanObject,
    mut v_a_274_: *mut LeanObject,
    mut v_a_275_: *mut LeanObject,
    mut v_a_276_: *mut LeanObject,
    mut v_a_277_: *mut LeanObject,
    mut v_a_278_: *mut LeanObject,
    mut v_a_279_: *mut LeanObject,
    mut v_a_280_: *mut LeanObject,
    mut v_a_281_: *mut LeanObject,
    mut v_a_282_: *mut LeanObject,
    mut v_a_283_: *mut LeanObject,
    mut v_a_284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_285_: *mut LeanObject = core::ptr::null_mut();
    v_res_285_ = l_Lean_Meta_Grind_Arith_propagateLT(
        v_e_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_,
        v_a_282_, v_a_283_,
    );
    lean_dec(v_a_283_);
    lean_dec_ref(v_a_282_);
    lean_dec(v_a_281_);
    lean_dec_ref(v_a_280_);
    lean_dec(v_a_279_);
    lean_dec_ref(v_a_278_);
    lean_dec(v_a_277_);
    lean_dec_ref(v_a_276_);
    lean_dec(v_a_275_);
    lean_dec(v_a_274_);
    return v_res_285_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_()
-> *mut LeanObject {
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    v___x_292_ = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_;
    v___x_293_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateLT___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_294_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_292_, v___x_293_);
    return v___x_294_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8____boxed(
    mut v_a_295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_296_: *mut LeanObject = core::ptr::null_mut();
    v_res_296_ = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
    return v_res_296_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Propagator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Main_0__Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Propagator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Main(builtin);
}
