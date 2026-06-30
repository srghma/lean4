// Lean compiler output
// Module: Lean.DeclarationRange
// Imports: Lean.MonadEnv
use crate::ffi::{
    lean_array_push, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::r#gen::Lean::AuxRecursor::{l_Lean_isAuxRecursor, l_Lean_isNoConfusion};
use crate::r#gen::Lean::Data::DeclarationRange::l_Lean_instInhabitedDeclarationRanges_default;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getPrefix, l_Lean_Name_isAnonymous};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_MapDeclarationExtension_insert___redArg, l_Lean_mkMapDeclarationExtension___redArg,
};
use crate::r#gen::Lean::MonadEnv::{
    initialize_Lean_MonadEnv, l_Lean_isRec___redArg, runtime_initialize_Lean_MonadEnv,
};
pub static mut l_Lean_builtinDeclRanges: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [100, 101, 99, 108, 82, 97, 110, 103, 101, 69, 120, 116, 0]};
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1330934816184234758 as *mut leanh::LeanObject] };
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_declRangeExt: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_213_ = leanh::lean_box(1);
    v___x_214_ = lean_st_mk_ref(v___x_213_);
    v___x_215_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_215_, 0, v___x_214_);
    return v___x_215_;
}
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2____boxed(
    mut v_a_216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_217_ = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_();
    return v_res_217_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_218_: *mut leanh::LeanObject,
    mut v_x_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_219_) == 0 {
                    v_k_220_ = leanh::lean_ctor_get(v_x_219_, 1);
                    v_v_221_ = leanh::lean_ctor_get(v_x_219_, 2);
                    v_l_222_ = leanh::lean_ctor_get(v_x_219_, 3);
                    v_r_223_ = leanh::lean_ctor_get(v_x_219_, 4);
                    v___x_224_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_218_, v_l_222_);
                    leanh::lean_inc(v_v_221_);
                    leanh::lean_inc(v_k_220_);
                    v___x_225_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_225_, 0, v_k_220_);
                    leanh::lean_ctor_set(v___x_225_, 1, v_v_221_);
                    v___x_226_ = lean_array_push(v___x_224_, v___x_225_);
                    v_init_218_ = v___x_226_;
                    v_x_219_ = v_r_223_;
                    state = 0;
                    continue;
                } else {
                    return v_init_218_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_228_: *mut leanh::LeanObject,
    mut v_x_229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_230_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_228_, v_x_229_);
    leanh::lean_dec(v_x_229_);
    return v_res_230_;
}
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_(
    mut v_x_235_: *mut leanh::LeanObject,
    mut v_s_236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ents_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_237_ = l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_;
    v_ents_238_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v___x_237_, v_s_236_);
    v___x_239_ = l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_;
    leanh::lean_inc_ref(v_ents_238_);
    v___x_240_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_240_, 0, v___x_239_);
    leanh::lean_ctor_set(v___x_240_, 1, v_ents_238_);
    leanh::lean_ctor_set(v___x_240_, 2, v_ents_238_);
    return v___x_240_;
}
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed(
    mut v_x_241_: *mut leanh::LeanObject,
    mut v_s_242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_243_ = l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_(v_x_241_, v_s_242_);
    leanh::lean_dec(v_s_242_);
    leanh::lean_dec_ref(v_x_241_);
    return v_res_243_;
}
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_253_ = l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_;
    v___x_254_ = l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_;
    v___x_255_ = l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_;
    v___x_256_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_254_, v___x_255_, v___f_253_);
    return v___x_256_;
}
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed(
    mut v_a_257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_258_ = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_();
    return v_res_258_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0(
    mut v_init_259_: *mut leanh::LeanObject,
    mut v_t_260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_261_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_259_, v_t_260_);
    return v___x_261_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_262_: *mut leanh::LeanObject,
    mut v_t_263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_264_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0(v_init_262_, v_t_263_);
    leanh::lean_dec(v_t_263_);
    return v_res_264_;
}
pub unsafe fn l_Lean_addBuiltinDeclarationRanges(
    mut v_declName_265_: *mut leanh::LeanObject,
    mut v_declRanges_266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = l_Lean_builtinDeclRanges;
    v___x_269_ = lean_st_ref_take(v___x_268_);
    v___x_270_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_declName_265_,
        v_declRanges_266_,
        v___x_269_,
    );
    v___x_271_ = lean_st_ref_set(v___x_268_, v___x_270_);
    v___x_272_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_272_, 0, v___x_271_);
    return v___x_272_;
}
pub unsafe fn l_Lean_addBuiltinDeclarationRanges___boxed(
    mut v_declName_273_: *mut leanh::LeanObject,
    mut v_declRanges_274_: *mut leanh::LeanObject,
    mut v_a_275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_276_ = l_Lean_addBuiltinDeclarationRanges(v_declName_273_, v_declRanges_274_);
    return v_res_276_;
}
pub unsafe fn l_Lean_addDeclarationRanges___redArg___lam__0(
    mut v_declName_277_: *mut leanh::LeanObject,
    mut v_declRanges_278_: *mut leanh::LeanObject,
    mut v_env_279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_280_ = l_Lean_declRangeExt;
    v___x_281_ = l_Lean_MapDeclarationExtension_insert___redArg(
        v___x_280_,
        v_env_279_,
        v_declName_277_,
        v_declRanges_278_,
    );
    return v___x_281_;
}
pub unsafe fn l_Lean_addDeclarationRanges___redArg(
    mut v_inst_282_: *mut leanh::LeanObject,
    mut v_inst_283_: *mut leanh::LeanObject,
    mut v_declName_284_: *mut leanh::LeanObject,
    mut v_declRanges_285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_286_: u8 = 0;
    v___x_286_ = l_Lean_Name_isAnonymous(v_declName_284_);
    if v___x_286_ == 0 {
        let mut v_modifyEnv_287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_282_);
        v_modifyEnv_287_ = leanh::lean_ctor_get(v_inst_283_, 1);
        leanh::lean_inc(v_modifyEnv_287_);
        leanh::lean_dec_ref(v_inst_283_);
        v___f_288_ = leanh::lean_alloc_closure(
            l_Lean_addDeclarationRanges___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_288_, 0, v_declName_284_);
        leanh::lean_closure_set(v___f_288_, 1, v_declRanges_285_);
        v___x_289_ = leanh::lean_apply_1(v_modifyEnv_287_, v___f_288_);
        return v___x_289_;
    } else {
        let mut v_toApplicative_290_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_291_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_declRanges_285_);
        leanh::lean_dec(v_declName_284_);
        leanh::lean_dec_ref(v_inst_283_);
        v_toApplicative_290_ = leanh::lean_ctor_get(v_inst_282_, 0);
        leanh::lean_inc_ref(v_toApplicative_290_);
        leanh::lean_dec_ref(v_inst_282_);
        v_toPure_291_ = leanh::lean_ctor_get(v_toApplicative_290_, 1);
        leanh::lean_inc(v_toPure_291_);
        leanh::lean_dec_ref(v_toApplicative_290_);
        v___x_292_ = leanh::lean_box(0);
        v___x_293_ =
            leanh::lean_apply_2(v_toPure_291_, leanh::lean_box(0), v___x_292_);
        return v___x_293_;
    }
}
pub unsafe fn l_Lean_addDeclarationRanges(
    mut v_m_294_: *mut leanh::LeanObject,
    mut v_inst_295_: *mut leanh::LeanObject,
    mut v_inst_296_: *mut leanh::LeanObject,
    mut v_declName_297_: *mut leanh::LeanObject,
    mut v_declRanges_298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_299_ = l_Lean_addDeclarationRanges___redArg(
        v_inst_295_,
        v_inst_296_,
        v_declName_297_,
        v_declRanges_298_,
    );
    return v___x_299_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___redArg___lam__0(
    mut v___x_300_: *mut leanh::LeanObject,
    mut v_____do__lift_301_: *mut leanh::LeanObject,
    mut v_declName_302_: *mut leanh::LeanObject,
    mut v_toPure_303_: *mut leanh::LeanObject,
    mut v_____do__lift_304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: u8 = 0;
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_305_ = l_Lean_declRangeExt;
    v_toEnvExtension_306_ = leanh::lean_ctor_get(v___x_305_, 0);
    v_asyncMode_307_ = leanh::lean_ctor_get(v_toEnvExtension_306_, 2);
    v___x_308_ = 0;
    leanh::lean_inc(v_declName_302_);
    leanh::lean_inc_ref(v___x_300_);
    v___x_309_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_300_,
        v___x_305_,
        v_____do__lift_301_,
        v_declName_302_,
        v_asyncMode_307_,
        v___x_308_,
    );
    if leanh::lean_obj_tag(v___x_309_) == 0 {
        let mut v___x_310_: u8 = 0;
        let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_310_ = 1;
        v___x_311_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
            v___x_300_,
            v___x_305_,
            v_____do__lift_304_,
            v_declName_302_,
            v_asyncMode_307_,
            v___x_310_,
        );
        v___x_312_ =
            leanh::lean_apply_2(v_toPure_303_, leanh::lean_box(0), v___x_311_);
        return v___x_312_;
    } else {
        let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_____do__lift_304_);
        leanh::lean_dec(v_declName_302_);
        leanh::lean_dec_ref(v___x_300_);
        v___x_313_ =
            leanh::lean_apply_2(v_toPure_303_, leanh::lean_box(0), v___x_309_);
        return v___x_313_;
    }
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___redArg___lam__1(
    mut v___x_314_: *mut leanh::LeanObject,
    mut v_declName_315_: *mut leanh::LeanObject,
    mut v_toPure_316_: *mut leanh::LeanObject,
    mut v_toBind_317_: *mut leanh::LeanObject,
    mut v_getEnv_318_: *mut leanh::LeanObject,
    mut v_____do__lift_319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_320_ = leanh::lean_alloc_closure(
        l_Lean_findDeclarationRangesCore_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_320_, 0, v___x_314_);
    leanh::lean_closure_set(v___f_320_, 1, v_____do__lift_319_);
    leanh::lean_closure_set(v___f_320_, 2, v_declName_315_);
    leanh::lean_closure_set(v___f_320_, 3, v_toPure_316_);
    v___x_321_ = leanh::lean_apply_4(
        v_toBind_317_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_318_,
        v___f_320_,
    );
    return v___x_321_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___redArg(
    mut v_inst_322_: *mut leanh::LeanObject,
    mut v_inst_323_: *mut leanh::LeanObject,
    mut v_declName_324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_325_ = leanh::lean_ctor_get(v_inst_322_, 0);
    leanh::lean_inc_ref(v_toApplicative_325_);
    v_toBind_326_ = leanh::lean_ctor_get(v_inst_322_, 1);
    leanh::lean_inc_n(v_toBind_326_, 2);
    leanh::lean_dec_ref(v_inst_322_);
    v_getEnv_327_ = leanh::lean_ctor_get(v_inst_323_, 0);
    leanh::lean_inc_n(v_getEnv_327_, 2);
    leanh::lean_dec_ref(v_inst_323_);
    v_toPure_328_ = leanh::lean_ctor_get(v_toApplicative_325_, 1);
    leanh::lean_inc(v_toPure_328_);
    leanh::lean_dec_ref(v_toApplicative_325_);
    v___x_329_ = l_Lean_instInhabitedDeclarationRanges_default;
    v___f_330_ = leanh::lean_alloc_closure(
        l_Lean_findDeclarationRangesCore_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_330_, 0, v___x_329_);
    leanh::lean_closure_set(v___f_330_, 1, v_declName_324_);
    leanh::lean_closure_set(v___f_330_, 2, v_toPure_328_);
    leanh::lean_closure_set(v___f_330_, 3, v_toBind_326_);
    leanh::lean_closure_set(v___f_330_, 4, v_getEnv_327_);
    v___x_331_ = leanh::lean_apply_4(
        v_toBind_326_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_327_,
        v___f_330_,
    );
    return v___x_331_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f(
    mut v_m_332_: *mut leanh::LeanObject,
    mut v_inst_333_: *mut leanh::LeanObject,
    mut v_inst_334_: *mut leanh::LeanObject,
    mut v_declName_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_336_ =
        l_Lean_findDeclarationRangesCore_x3f___redArg(v_inst_333_, v_inst_334_, v_declName_335_);
    return v___x_336_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__0(
    mut v_declName_337_: *mut leanh::LeanObject,
    mut v_toPure_338_: *mut leanh::LeanObject,
    mut v_____do__lift_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_____do__lift_339_,
            v_declName_337_,
        );
    v___x_341_ = leanh::lean_apply_2(v_toPure_338_, leanh::lean_box(0), v___x_340_);
    return v___x_341_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__0___boxed(
    mut v_declName_342_: *mut leanh::LeanObject,
    mut v_toPure_343_: *mut leanh::LeanObject,
    mut v_____do__lift_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_345_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__0(
        v_declName_342_,
        v_toPure_343_,
        v_____do__lift_344_,
    );
    leanh::lean_dec(v_____do__lift_344_);
    leanh::lean_dec(v_declName_342_);
    return v_res_345_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__1(
    mut v___x_346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = lean_st_ref_get(v___x_346_);
    return v___x_348_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__1___boxed(
    mut v___x_349_: *mut leanh::LeanObject,
    mut v___y_350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_351_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__1(v___x_349_);
    leanh::lean_dec(v___x_349_);
    return v_res_351_;
}
pub unsafe fn _init_l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_352_ = l_Lean_builtinDeclRanges;
    v___f_353_ = leanh::lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_353_, 0, v___x_352_);
    return v___f_353_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__2(
    mut v_inst_354_: *mut leanh::LeanObject,
    mut v_toBind_355_: *mut leanh::LeanObject,
    mut v___f_356_: *mut leanh::LeanObject,
    mut v_toPure_357_: *mut leanh::LeanObject,
    mut v_ranges_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_ranges_358_) == 0 {
        let mut v___f_359_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_357_);
        v___f_359_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0_once
            ),
            _init_l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0,
        );
        v___x_360_ = leanh::lean_apply_2(v_inst_354_, leanh::lean_box(0), v___f_359_);
        v___x_361_ = leanh::lean_apply_4(
            v_toBind_355_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_360_,
            v___f_356_,
        );
        return v___x_361_;
    } else {
        let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_356_);
        leanh::lean_dec(v_toBind_355_);
        leanh::lean_dec(v_inst_354_);
        v___x_362_ =
            leanh::lean_apply_2(v_toPure_357_, leanh::lean_box(0), v_ranges_358_);
        return v___x_362_;
    }
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__3(
    mut v___f_363_: *mut leanh::LeanObject,
    mut v_ranges_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_365_ = leanh::lean_apply_1(v___f_363_, v_ranges_364_);
    return v___x_365_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__5(
    mut v_declName_366_: *mut leanh::LeanObject,
    mut v_inst_367_: *mut leanh::LeanObject,
    mut v_inst_368_: *mut leanh::LeanObject,
    mut v_toBind_369_: *mut leanh::LeanObject,
    mut v___f_370_: *mut leanh::LeanObject,
    mut v___f_371_: *mut leanh::LeanObject,
    mut v_env_372_: *mut leanh::LeanObject,
    mut v_____do__lift_373_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_379_: u8 = 0;
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: u8 = 0;
    let mut v___x_383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_366_);
                leanh::lean_inc_ref(v_env_372_);
                v___x_382_ = l_Lean_isAuxRecursor(v_env_372_, v_declName_366_);
                if v___x_382_ == 0 {
                    leanh::lean_inc(v_declName_366_);
                    v___x_383_ = l_Lean_isNoConfusion(v_env_372_, v_declName_366_);
                    v___y_379_ = v___x_383_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_372_);
                    v___y_379_ = v___x_382_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_375_ = l_Lean_Name_getPrefix(v_declName_366_);
                leanh::lean_dec(v_declName_366_);
                v___x_376_ = l_Lean_findDeclarationRangesCore_x3f___redArg(
                    v_inst_367_,
                    v_inst_368_,
                    v___x_375_,
                );
                v___x_377_ = leanh::lean_apply_4(
                    v_toBind_369_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_376_,
                    v___f_370_,
                );
                return v___x_377_;
            }
            2 => {
                if v___y_379_ == 0 {
                    if v_____do__lift_373_ == 0 {
                        leanh::lean_dec(v___f_370_);
                        v___x_380_ = l_Lean_findDeclarationRangesCore_x3f___redArg(
                            v_inst_367_,
                            v_inst_368_,
                            v_declName_366_,
                        );
                        v___x_381_ = leanh::lean_apply_4(
                            v_toBind_369_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_380_,
                            v___f_371_,
                        );
                        return v___x_381_;
                    } else {
                        leanh::lean_dec(v___f_371_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___f_371_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__5___boxed(
    mut v_declName_384_: *mut leanh::LeanObject,
    mut v_inst_385_: *mut leanh::LeanObject,
    mut v_inst_386_: *mut leanh::LeanObject,
    mut v_toBind_387_: *mut leanh::LeanObject,
    mut v___f_388_: *mut leanh::LeanObject,
    mut v___f_389_: *mut leanh::LeanObject,
    mut v_env_390_: *mut leanh::LeanObject,
    mut v_____do__lift_391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_270__boxed_392_: u8 = 0;
    let mut v_res_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_270__boxed_392_ = (leanh::lean_unbox(v_____do__lift_391_) as u8);
    v_res_393_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__5(
        v_declName_384_,
        v_inst_385_,
        v_inst_386_,
        v_toBind_387_,
        v___f_388_,
        v___f_389_,
        v_env_390_,
        v_____do__lift_270__boxed_392_,
    );
    return v_res_393_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__4(
    mut v_declName_394_: *mut leanh::LeanObject,
    mut v_inst_395_: *mut leanh::LeanObject,
    mut v_inst_396_: *mut leanh::LeanObject,
    mut v_toBind_397_: *mut leanh::LeanObject,
    mut v___f_398_: *mut leanh::LeanObject,
    mut v___f_399_: *mut leanh::LeanObject,
    mut v_env_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_397_);
    leanh::lean_inc_ref(v_inst_396_);
    leanh::lean_inc_ref(v_inst_395_);
    leanh::lean_inc(v_declName_394_);
    v___f_401_ = leanh::lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__5___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_401_, 0, v_declName_394_);
    leanh::lean_closure_set(v___f_401_, 1, v_inst_395_);
    leanh::lean_closure_set(v___f_401_, 2, v_inst_396_);
    leanh::lean_closure_set(v___f_401_, 3, v_toBind_397_);
    leanh::lean_closure_set(v___f_401_, 4, v___f_398_);
    leanh::lean_closure_set(v___f_401_, 5, v___f_399_);
    leanh::lean_closure_set(v___f_401_, 6, v_env_400_);
    v___x_402_ = l_Lean_isRec___redArg(v_inst_395_, v_inst_396_, v_declName_394_);
    v___x_403_ = leanh::lean_apply_4(
        v_toBind_397_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_402_,
        v___f_401_,
    );
    return v___x_403_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg(
    mut v_inst_404_: *mut leanh::LeanObject,
    mut v_inst_405_: *mut leanh::LeanObject,
    mut v_inst_406_: *mut leanh::LeanObject,
    mut v_declName_407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_408_ = leanh::lean_ctor_get(v_inst_404_, 0);
    v_toBind_409_ = leanh::lean_ctor_get(v_inst_404_, 1);
    leanh::lean_inc_n(v_toBind_409_, 3);
    v_getEnv_410_ = leanh::lean_ctor_get(v_inst_405_, 0);
    leanh::lean_inc(v_getEnv_410_);
    v_toPure_411_ = leanh::lean_ctor_get(v_toApplicative_408_, 1);
    leanh::lean_inc_n(v_toPure_411_, 2);
    leanh::lean_inc(v_declName_407_);
    v___f_412_ = leanh::lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_412_, 0, v_declName_407_);
    leanh::lean_closure_set(v___f_412_, 1, v_toPure_411_);
    v___f_413_ = leanh::lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_413_, 0, v_inst_406_);
    leanh::lean_closure_set(v___f_413_, 1, v_toBind_409_);
    leanh::lean_closure_set(v___f_413_, 2, v___f_412_);
    leanh::lean_closure_set(v___f_413_, 3, v_toPure_411_);
    v___f_414_ = leanh::lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_414_, 0, v___f_413_);
    leanh::lean_inc_ref(v___f_414_);
    v___f_415_ = leanh::lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_415_, 0, v_declName_407_);
    leanh::lean_closure_set(v___f_415_, 1, v_inst_404_);
    leanh::lean_closure_set(v___f_415_, 2, v_inst_405_);
    leanh::lean_closure_set(v___f_415_, 3, v_toBind_409_);
    leanh::lean_closure_set(v___f_415_, 4, v___f_414_);
    leanh::lean_closure_set(v___f_415_, 5, v___f_414_);
    v___x_416_ = leanh::lean_apply_4(
        v_toBind_409_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_410_,
        v___f_415_,
    );
    return v___x_416_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f(
    mut v_m_417_: *mut leanh::LeanObject,
    mut v_inst_418_: *mut leanh::LeanObject,
    mut v_inst_419_: *mut leanh::LeanObject,
    mut v_inst_420_: *mut leanh::LeanObject,
    mut v_declName_421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_422_ = l_Lean_findDeclarationRanges_x3f___redArg(
        v_inst_418_,
        v_inst_419_,
        v_inst_420_,
        v_declName_421_,
    );
    return v___x_422_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DeclarationRange(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_MonadEnv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_builtinDeclRanges = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_builtinDeclRanges);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_declRangeExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_declRangeExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DeclarationRange(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DeclarationRange(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_MonadEnv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DeclarationRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_DeclarationRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_DeclarationRange(builtin);
}