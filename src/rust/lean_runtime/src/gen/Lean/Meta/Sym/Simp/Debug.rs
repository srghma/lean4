// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Debug
// Imports: Lean.Meta.Sym.Simp.Discharger Lean.Meta.Sym.Simp.Rewrite Lean.Meta.Sym.Simp.Goal Lean.Meta.Sym.Util
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Meta::Sym::Simp::Discharger::{
    initialize_Lean_Meta_Sym_Simp_Discharger, l_Lean_Meta_Sym_Simp_dischargeNone___boxed,
    runtime_initialize_Lean_Meta_Sym_Simp_Discharger,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Goal::{
    initialize_Lean_Meta_Sym_Simp_Goal, l_Lean_Meta_Sym_SimpGoalResult_toOption,
    l_Lean_Meta_Sym_simpGoal, runtime_initialize_Lean_Meta_Sym_Simp_Goal,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Rewrite::{
    initialize_Lean_Meta_Sym_Simp_Rewrite, l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed,
    runtime_initialize_Lean_Meta_Sym_Simp_Rewrite,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Theorems::{
    l_Lean_Meta_Sym_Simp_Theorems_insert, l_Lean_Meta_Sym_Simp_mkTheoremFromDecl,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_SymM_run___redArg;
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_preprocessMVar,
    runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox_usize,
};
static mut l_Lean_Meta_Sym_mkSimprocFor___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_mkSimprocFor___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_mkSimprocFor___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_mkSimprocFor___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_mkMethods___lam__0___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [0 as *mut LeanObject],
    };
static mut l_Lean_Meta_Sym_mkMethods___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkMethods___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_mkMethods___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_Simp_dischargeNone___boxed as *const core::ffi::c_void,
    m_arity: 11,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_mkMethods___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkMethods___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_mkMethods___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_mkMethods___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 11,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_mkMethods___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkMethods___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_simpGoalUsing___lam__0___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((100000 as usize) << 1) | 1) as *mut LeanObject,
            (((2 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_simpGoalUsing___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_simpGoalUsing___lam__0___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0(
    mut v_as_211_: *mut LeanObject,
    mut v_sz_212_: usize,
    mut v_i_213_: usize,
    mut v_b_214_: *mut LeanObject,
    mut v___y_215_: *mut LeanObject,
    mut v___y_216_: *mut LeanObject,
    mut v___y_217_: *mut LeanObject,
    mut v___y_218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_220_: u8 = 0;
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: usize = 0;
    let mut v___x_227_: usize = 0;
    let mut v_a_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_232_: u8 = 0;
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_220_ = lean_usize_dec_lt(v_i_213_, v_sz_212_);
                if v___x_220_ == 0 {
                    v___x_221_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_221_, 0, v_b_214_);
                    return v___x_221_;
                } else {
                    v_a_222_ = lean_array_uget_borrowed(v_as_211_, v_i_213_);
                    lean_inc(v_a_222_);
                    v___x_223_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(
                        v_a_222_, v___y_215_, v___y_216_, v___y_217_, v___y_218_,
                    );
                    if lean_obj_tag(v___x_223_) == 0 {
                        v_a_224_ = lean_ctor_get(v___x_223_, 0);
                        lean_inc(v_a_224_);
                        lean_dec_ref_known(v___x_223_, 1);
                        v___x_225_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_214_, v_a_224_);
                        v___x_226_ = 1usize;
                        v___x_227_ = lean_usize_add(v_i_213_, v___x_226_);
                        v_i_213_ = v___x_227_;
                        v_b_214_ = v___x_225_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_b_214_);
                        v_a_229_ = lean_ctor_get(v___x_223_, 0);
                        v_isSharedCheck_236_ = (!lean_is_exclusive(v___x_223_)) as u8;
                        if v_isSharedCheck_236_ == 0 {
                            v___x_231_ = v___x_223_;
                            v_isShared_232_ = v_isSharedCheck_236_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_229_);
                            lean_dec(v___x_223_);
                            v___x_231_ = lean_box(0);
                            v_isShared_232_ = v_isSharedCheck_236_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_232_ == 0 {
                    v___x_234_ = v___x_231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
                    v___x_234_ = v_reuseFailAlloc_235_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0___boxed(
    mut v_as_237_: *mut LeanObject,
    mut v_sz_238_: *mut LeanObject,
    mut v_i_239_: *mut LeanObject,
    mut v_b_240_: *mut LeanObject,
    mut v___y_241_: *mut LeanObject,
    mut v___y_242_: *mut LeanObject,
    mut v___y_243_: *mut LeanObject,
    mut v___y_244_: *mut LeanObject,
    mut v___y_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_246_: usize = 0;
    let mut v_i_boxed_247_: usize = 0;
    let mut v_res_248_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_246_ = lean_unbox_usize(v_sz_238_);
    lean_dec(v_sz_238_);
    v_i_boxed_247_ = lean_unbox_usize(v_i_239_);
    lean_dec(v_i_239_);
    v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0(v_as_237_, v_sz_boxed_246_, v_i_boxed_247_, v_b_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
    lean_dec(v___y_244_);
    lean_dec_ref(v___y_243_);
    lean_dec(v___y_242_);
    lean_dec_ref(v___y_241_);
    lean_dec_ref(v_as_237_);
    return v_res_248_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_mkSimprocFor___closed__0() -> *mut LeanObject {
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    v___x_249_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_249_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_mkSimprocFor___closed__1() -> *mut LeanObject {
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thms_251_: *mut LeanObject = core::ptr::null_mut();
    v___x_250_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_mkSimprocFor___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_mkSimprocFor___closed__0_once),
        _init_l_Lean_Meta_Sym_mkSimprocFor___closed__0,
    );
    v_thms_251_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v_thms_251_, 0, v___x_250_);
    return v_thms_251_;
}
pub unsafe fn l_Lean_Meta_Sym_mkSimprocFor(
    mut v_declNames_252_: *mut LeanObject,
    mut v_d_253_: *mut LeanObject,
    mut v_a_254_: *mut LeanObject,
    mut v_a_255_: *mut LeanObject,
    mut v_a_256_: *mut LeanObject,
    mut v_a_257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_thms_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_260_: usize = 0;
    let mut v___x_261_: usize = 0;
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_266_: u8 = 0;
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_271_: u8 = 0;
    let mut v_a_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_275_: u8 = 0;
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_thms_259_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_mkSimprocFor___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_mkSimprocFor___closed__1_once),
                    _init_l_Lean_Meta_Sym_mkSimprocFor___closed__1,
                );
                v_sz_260_ = lean_array_size(v_declNames_252_);
                v___x_261_ = 0usize;
                v___x_262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0(v_declNames_252_, v_sz_260_, v___x_261_, v_thms_259_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
                if lean_obj_tag(v___x_262_) == 0 {
                    v_a_263_ = lean_ctor_get(v___x_262_, 0);
                    v_isSharedCheck_271_ = (!lean_is_exclusive(v___x_262_)) as u8;
                    if v_isSharedCheck_271_ == 0 {
                        v___x_265_ = v___x_262_;
                        v_isShared_266_ = v_isSharedCheck_271_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_263_);
                        lean_dec(v___x_262_);
                        v___x_265_ = lean_box(0);
                        v_isShared_266_ = v_isSharedCheck_271_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_d_253_);
                    v_a_272_ = lean_ctor_get(v___x_262_, 0);
                    v_isSharedCheck_279_ = (!lean_is_exclusive(v___x_262_)) as u8;
                    if v_isSharedCheck_279_ == 0 {
                        v___x_274_ = v___x_262_;
                        v_isShared_275_ = v_isSharedCheck_279_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_272_);
                        lean_dec(v___x_262_);
                        v___x_274_ = lean_box(0);
                        v_isShared_275_ = v_isSharedCheck_279_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_267_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed as *mut core::ffi::c_void,
                    13,
                    2,
                );
                lean_closure_set(v___x_267_, 0, v_a_263_);
                lean_closure_set(v___x_267_, 1, v_d_253_);
                if v_isShared_266_ == 0 {
                    lean_ctor_set(v___x_265_, 0, v___x_267_);
                    v___x_269_ = v___x_265_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
                    v___x_269_ = v_reuseFailAlloc_270_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_269_;
            }
            3 => {
                if v_isShared_275_ == 0 {
                    v___x_277_ = v___x_274_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
                    v___x_277_ = v_reuseFailAlloc_278_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_mkSimprocFor___boxed(
    mut v_declNames_280_: *mut LeanObject,
    mut v_d_281_: *mut LeanObject,
    mut v_a_282_: *mut LeanObject,
    mut v_a_283_: *mut LeanObject,
    mut v_a_284_: *mut LeanObject,
    mut v_a_285_: *mut LeanObject,
    mut v_a_286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_287_: *mut LeanObject = core::ptr::null_mut();
    v_res_287_ = l_Lean_Meta_Sym_mkSimprocFor(
        v_declNames_280_,
        v_d_281_,
        v_a_282_,
        v_a_283_,
        v_a_284_,
        v_a_285_,
    );
    lean_dec(v_a_285_);
    lean_dec_ref(v_a_284_);
    lean_dec(v_a_283_);
    lean_dec_ref(v_a_282_);
    lean_dec_ref(v_declNames_280_);
    return v_res_287_;
}
pub unsafe fn l_Lean_Meta_Sym_mkMethods___lam__0(
    mut v_x_290_: *mut LeanObject,
    mut v___y_291_: *mut LeanObject,
    mut v___y_292_: *mut LeanObject,
    mut v___y_293_: *mut LeanObject,
    mut v___y_294_: *mut LeanObject,
    mut v___y_295_: *mut LeanObject,
    mut v___y_296_: *mut LeanObject,
    mut v___y_297_: *mut LeanObject,
    mut v___y_298_: *mut LeanObject,
    mut v___y_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    v___x_301_ = l_Lean_Meta_Sym_mkMethods___lam__0___closed__0;
    v___x_302_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_302_, 0, v___x_301_);
    return v___x_302_;
}
pub unsafe fn l_Lean_Meta_Sym_mkMethods___lam__0___boxed(
    mut v_x_303_: *mut LeanObject,
    mut v___y_304_: *mut LeanObject,
    mut v___y_305_: *mut LeanObject,
    mut v___y_306_: *mut LeanObject,
    mut v___y_307_: *mut LeanObject,
    mut v___y_308_: *mut LeanObject,
    mut v___y_309_: *mut LeanObject,
    mut v___y_310_: *mut LeanObject,
    mut v___y_311_: *mut LeanObject,
    mut v___y_312_: *mut LeanObject,
    mut v___y_313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_314_: *mut LeanObject = core::ptr::null_mut();
    v_res_314_ = l_Lean_Meta_Sym_mkMethods___lam__0(
        v_x_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_,
        v___y_310_, v___y_311_, v___y_312_,
    );
    lean_dec(v___y_312_);
    lean_dec_ref(v___y_311_);
    lean_dec(v___y_310_);
    lean_dec_ref(v___y_309_);
    lean_dec(v___y_308_);
    lean_dec_ref(v___y_307_);
    lean_dec(v___y_306_);
    lean_dec_ref(v___y_305_);
    lean_dec(v___y_304_);
    lean_dec_ref(v_x_303_);
    return v_res_314_;
}
pub unsafe fn l_Lean_Meta_Sym_mkMethods(
    mut v_declNames_317_: *mut LeanObject,
    mut v_a_318_: *mut LeanObject,
    mut v_a_319_: *mut LeanObject,
    mut v_a_320_: *mut LeanObject,
    mut v_a_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_328_: u8 = 0;
    let mut v___f_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_334_: u8 = 0;
    let mut v_a_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_338_: u8 = 0;
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_323_ = l_Lean_Meta_Sym_mkMethods___closed__0;
                v___x_324_ = l_Lean_Meta_Sym_mkSimprocFor(
                    v_declNames_317_,
                    v___x_323_,
                    v_a_318_,
                    v_a_319_,
                    v_a_320_,
                    v_a_321_,
                );
                if lean_obj_tag(v___x_324_) == 0 {
                    v_a_325_ = lean_ctor_get(v___x_324_, 0);
                    v_isSharedCheck_334_ = (!lean_is_exclusive(v___x_324_)) as u8;
                    if v_isSharedCheck_334_ == 0 {
                        v___x_327_ = v___x_324_;
                        v_isShared_328_ = v_isSharedCheck_334_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_325_);
                        lean_dec(v___x_324_);
                        v___x_327_ = lean_box(0);
                        v_isShared_328_ = v_isSharedCheck_334_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_335_ = lean_ctor_get(v___x_324_, 0);
                    v_isSharedCheck_342_ = (!lean_is_exclusive(v___x_324_)) as u8;
                    if v_isSharedCheck_342_ == 0 {
                        v___x_337_ = v___x_324_;
                        v_isShared_338_ = v_isSharedCheck_342_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_335_);
                        lean_dec(v___x_324_);
                        v___x_337_ = lean_box(0);
                        v_isShared_338_ = v_isSharedCheck_342_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___f_329_ = l_Lean_Meta_Sym_mkMethods___closed__1;
                v___x_330_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_330_, 0, v___f_329_);
                lean_ctor_set(v___x_330_, 1, v_a_325_);
                if v_isShared_328_ == 0 {
                    lean_ctor_set(v___x_327_, 0, v___x_330_);
                    v___x_332_ = v___x_327_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
                    v___x_332_ = v_reuseFailAlloc_333_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_332_;
            }
            3 => {
                if v_isShared_338_ == 0 {
                    v___x_340_ = v___x_337_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
                    v___x_340_ = v_reuseFailAlloc_341_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_mkMethods___boxed(
    mut v_declNames_343_: *mut LeanObject,
    mut v_a_344_: *mut LeanObject,
    mut v_a_345_: *mut LeanObject,
    mut v_a_346_: *mut LeanObject,
    mut v_a_347_: *mut LeanObject,
    mut v_a_348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_349_: *mut LeanObject = core::ptr::null_mut();
    v_res_349_ =
        l_Lean_Meta_Sym_mkMethods(v_declNames_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
    lean_dec(v_a_347_);
    lean_dec_ref(v_a_346_);
    lean_dec(v_a_345_);
    lean_dec_ref(v_a_344_);
    lean_dec_ref(v_declNames_343_);
    return v_res_349_;
}
pub unsafe fn l_Lean_Meta_Sym_simpGoalUsing___lam__0(
    mut v_declNames_353_: *mut LeanObject,
    mut v_mvarId_354_: *mut LeanObject,
    mut v___y_355_: *mut LeanObject,
    mut v___y_356_: *mut LeanObject,
    mut v___y_357_: *mut LeanObject,
    mut v___y_358_: *mut LeanObject,
    mut v___y_359_: *mut LeanObject,
    mut v___y_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_373_: u8 = 0;
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_377_: u8 = 0;
    let mut v_a_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_381_: u8 = 0;
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_385_: u8 = 0;
    let mut v_a_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_389_: u8 = 0;
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_393_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_362_ = l_Lean_Meta_Sym_mkMethods(
                    v_declNames_353_,
                    v___y_357_,
                    v___y_358_,
                    v___y_359_,
                    v___y_360_,
                );
                if lean_obj_tag(v___x_362_) == 0 {
                    v_a_363_ = lean_ctor_get(v___x_362_, 0);
                    lean_inc(v_a_363_);
                    lean_dec_ref_known(v___x_362_, 1);
                    v___x_364_ = l_Lean_Meta_Sym_preprocessMVar(
                        v_mvarId_354_,
                        v___y_355_,
                        v___y_356_,
                        v___y_357_,
                        v___y_358_,
                        v___y_359_,
                        v___y_360_,
                    );
                    if lean_obj_tag(v___x_364_) == 0 {
                        v_a_365_ = lean_ctor_get(v___x_364_, 0);
                        lean_inc(v_a_365_);
                        lean_dec_ref_known(v___x_364_, 1);
                        v___x_366_ = l_Lean_Meta_Sym_simpGoalUsing___lam__0___closed__0;
                        v___x_367_ = l_Lean_Meta_Sym_simpGoal(
                            v_a_365_, v_a_363_, v___x_366_, v___y_355_, v___y_356_, v___y_357_,
                            v___y_358_, v___y_359_, v___y_360_,
                        );
                        if lean_obj_tag(v___x_367_) == 0 {
                            v_a_368_ = lean_ctor_get(v___x_367_, 0);
                            lean_inc(v_a_368_);
                            lean_dec_ref_known(v___x_367_, 1);
                            v___x_369_ = l_Lean_Meta_Sym_SimpGoalResult_toOption(
                                v_a_368_, v___y_359_, v___y_360_,
                            );
                            return v___x_369_;
                        } else {
                            v_a_370_ = lean_ctor_get(v___x_367_, 0);
                            v_isSharedCheck_377_ = (!lean_is_exclusive(v___x_367_)) as u8;
                            if v_isSharedCheck_377_ == 0 {
                                v___x_372_ = v___x_367_;
                                v_isShared_373_ = v_isSharedCheck_377_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_370_);
                                lean_dec(v___x_367_);
                                v___x_372_ = lean_box(0);
                                v_isShared_373_ = v_isSharedCheck_377_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_363_);
                        v_a_378_ = lean_ctor_get(v___x_364_, 0);
                        v_isSharedCheck_385_ = (!lean_is_exclusive(v___x_364_)) as u8;
                        if v_isSharedCheck_385_ == 0 {
                            v___x_380_ = v___x_364_;
                            v_isShared_381_ = v_isSharedCheck_385_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_378_);
                            lean_dec(v___x_364_);
                            v___x_380_ = lean_box(0);
                            v_isShared_381_ = v_isSharedCheck_385_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_mvarId_354_);
                    v_a_386_ = lean_ctor_get(v___x_362_, 0);
                    v_isSharedCheck_393_ = (!lean_is_exclusive(v___x_362_)) as u8;
                    if v_isSharedCheck_393_ == 0 {
                        v___x_388_ = v___x_362_;
                        v_isShared_389_ = v_isSharedCheck_393_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_386_);
                        lean_dec(v___x_362_);
                        v___x_388_ = lean_box(0);
                        v_isShared_389_ = v_isSharedCheck_393_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_373_ == 0 {
                    v___x_375_ = v___x_372_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
                    v___x_375_ = v_reuseFailAlloc_376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_375_;
            }
            3 => {
                if v_isShared_381_ == 0 {
                    v___x_383_ = v___x_380_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
                    v___x_383_ = v_reuseFailAlloc_384_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_383_;
            }
            5 => {
                if v_isShared_389_ == 0 {
                    v___x_391_ = v___x_388_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
                    v___x_391_ = v_reuseFailAlloc_392_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_simpGoalUsing___lam__0___boxed(
    mut v_declNames_394_: *mut LeanObject,
    mut v_mvarId_395_: *mut LeanObject,
    mut v___y_396_: *mut LeanObject,
    mut v___y_397_: *mut LeanObject,
    mut v___y_398_: *mut LeanObject,
    mut v___y_399_: *mut LeanObject,
    mut v___y_400_: *mut LeanObject,
    mut v___y_401_: *mut LeanObject,
    mut v___y_402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_403_: *mut LeanObject = core::ptr::null_mut();
    v_res_403_ = l_Lean_Meta_Sym_simpGoalUsing___lam__0(
        v_declNames_394_,
        v_mvarId_395_,
        v___y_396_,
        v___y_397_,
        v___y_398_,
        v___y_399_,
        v___y_400_,
        v___y_401_,
    );
    lean_dec(v___y_401_);
    lean_dec_ref(v___y_400_);
    lean_dec(v___y_399_);
    lean_dec_ref(v___y_398_);
    lean_dec(v___y_397_);
    lean_dec_ref(v___y_396_);
    lean_dec_ref(v_declNames_394_);
    return v_res_403_;
}
pub unsafe fn l_Lean_Meta_Sym_simpGoalUsing(
    mut v_declNames_404_: *mut LeanObject,
    mut v_mvarId_405_: *mut LeanObject,
    mut v_a_406_: *mut LeanObject,
    mut v_a_407_: *mut LeanObject,
    mut v_a_408_: *mut LeanObject,
    mut v_a_409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    v___f_411_ = lean_alloc_closure(
        l_Lean_Meta_Sym_simpGoalUsing___lam__0___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    lean_closure_set(v___f_411_, 0, v_declNames_404_);
    lean_closure_set(v___f_411_, 1, v_mvarId_405_);
    v___x_412_ =
        l_Lean_Meta_Sym_SymM_run___redArg(v___f_411_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
    return v___x_412_;
}
pub unsafe fn l_Lean_Meta_Sym_simpGoalUsing___boxed(
    mut v_declNames_413_: *mut LeanObject,
    mut v_mvarId_414_: *mut LeanObject,
    mut v_a_415_: *mut LeanObject,
    mut v_a_416_: *mut LeanObject,
    mut v_a_417_: *mut LeanObject,
    mut v_a_418_: *mut LeanObject,
    mut v_a_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_420_: *mut LeanObject = core::ptr::null_mut();
    v_res_420_ = l_Lean_Meta_Sym_simpGoalUsing(
        v_declNames_413_,
        v_mvarId_414_,
        v_a_415_,
        v_a_416_,
        v_a_417_,
        v_a_418_,
    );
    lean_dec(v_a_418_);
    lean_dec_ref(v_a_417_);
    lean_dec(v_a_416_);
    lean_dec_ref(v_a_415_);
    return v_res_420_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Debug(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Debug(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Debug(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Goal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Debug(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Debug(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Debug(builtin);
}
