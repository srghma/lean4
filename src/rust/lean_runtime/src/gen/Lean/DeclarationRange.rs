// Lean compiler output
// Module: Lean.DeclarationRange
// Imports: Lean.MonadEnv
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
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
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_obj_tag, lean_unbox,
};
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [100, 101, 99, 108, 82, 97, 110, 103, 101, 69, 120, 116, 0]};
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__2_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut LeanObject,1330934816184234758 as *mut LeanObject] };
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut LeanObject] };
static mut l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    v___x_213_ = lean_box(1);
    v___x_214_ = lean_st_mk_ref(v___x_213_);
    v___x_215_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_215_, 0, v___x_214_);
    return v___x_215_;
}
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2____boxed(
    mut v_a_216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_217_: *mut LeanObject = core::ptr::null_mut();
    v_res_217_ = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_();
    return v_res_217_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_218_: *mut LeanObject,
    mut v_x_219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_219_) == 0 {
                    v_k_220_ = lean_ctor_get(v_x_219_, 1);
                    v_v_221_ = lean_ctor_get(v_x_219_, 2);
                    v_l_222_ = lean_ctor_get(v_x_219_, 3);
                    v_r_223_ = lean_ctor_get(v_x_219_, 4);
                    v___x_224_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_218_, v_l_222_);
                    lean_inc(v_v_221_);
                    lean_inc(v_k_220_);
                    v___x_225_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_225_, 0, v_k_220_);
                    lean_ctor_set(v___x_225_, 1, v_v_221_);
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
    mut v_init_228_: *mut LeanObject,
    mut v_x_229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_230_: *mut LeanObject = core::ptr::null_mut();
    v_res_230_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_228_, v_x_229_);
    lean_dec(v_x_229_);
    return v_res_230_;
}
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_(
    mut v_x_235_: *mut LeanObject,
    mut v_s_236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ents_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    v___x_237_ = l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_;
    v_ents_238_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v___x_237_, v_s_236_);
    v___x_239_ = l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_;
    lean_inc_ref(v_ents_238_);
    v___x_240_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_240_, 0, v___x_239_);
    lean_ctor_set(v___x_240_, 1, v_ents_238_);
    lean_ctor_set(v___x_240_, 2, v_ents_238_);
    return v___x_240_;
}
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed(
    mut v_x_241_: *mut LeanObject,
    mut v_s_242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_243_: *mut LeanObject = core::ptr::null_mut();
    v_res_243_ = l___private_Lean_DeclarationRange_0__Lean_initFn___lam__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_(v_x_241_, v_s_242_);
    lean_dec(v_s_242_);
    lean_dec_ref(v_x_241_);
    return v_res_243_;
}
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    v___f_253_ = l___private_Lean_DeclarationRange_0__Lean_initFn___closed__0_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_;
    v___x_254_ = l___private_Lean_DeclarationRange_0__Lean_initFn___closed__3_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_;
    v___x_255_ = l___private_Lean_DeclarationRange_0__Lean_initFn___closed__4_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_;
    v___x_256_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_254_, v___x_255_, v___f_253_);
    return v___x_256_;
}
pub unsafe fn l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2____boxed(
    mut v_a_257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_258_: *mut LeanObject = core::ptr::null_mut();
    v_res_258_ = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_();
    return v_res_258_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0(
    mut v_init_259_: *mut LeanObject,
    mut v_t_260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    v___x_261_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0_spec__0(v_init_259_, v_t_260_);
    return v___x_261_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_262_: *mut LeanObject,
    mut v_t_263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_264_: *mut LeanObject = core::ptr::null_mut();
    v_res_264_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2__spec__0(v_init_262_, v_t_263_);
    lean_dec(v_t_263_);
    return v_res_264_;
}
pub unsafe fn l_Lean_addBuiltinDeclarationRanges(
    mut v_declName_265_: *mut LeanObject,
    mut v_declRanges_266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    v___x_268_ = l_Lean_builtinDeclRanges;
    v___x_269_ = lean_st_ref_take(v___x_268_);
    v___x_270_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_declName_265_,
        v_declRanges_266_,
        v___x_269_,
    );
    v___x_271_ = lean_st_ref_set(v___x_268_, v___x_270_);
    v___x_272_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_272_, 0, v___x_271_);
    return v___x_272_;
}
pub unsafe fn l_Lean_addBuiltinDeclarationRanges___boxed(
    mut v_declName_273_: *mut LeanObject,
    mut v_declRanges_274_: *mut LeanObject,
    mut v_a_275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_276_: *mut LeanObject = core::ptr::null_mut();
    v_res_276_ = l_Lean_addBuiltinDeclarationRanges(v_declName_273_, v_declRanges_274_);
    return v_res_276_;
}
pub unsafe fn l_Lean_addDeclarationRanges___redArg___lam__0(
    mut v_declName_277_: *mut LeanObject,
    mut v_declRanges_278_: *mut LeanObject,
    mut v_env_279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_282_: *mut LeanObject,
    mut v_inst_283_: *mut LeanObject,
    mut v_declName_284_: *mut LeanObject,
    mut v_declRanges_285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_286_: u8 = 0;
    v___x_286_ = l_Lean_Name_isAnonymous(v_declName_284_);
    if v___x_286_ == 0 {
        let mut v_modifyEnv_287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_282_);
        v_modifyEnv_287_ = lean_ctor_get(v_inst_283_, 1);
        lean_inc(v_modifyEnv_287_);
        lean_dec_ref(v_inst_283_);
        v___f_288_ = lean_alloc_closure(
            l_Lean_addDeclarationRanges___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_288_, 0, v_declName_284_);
        lean_closure_set(v___f_288_, 1, v_declRanges_285_);
        v___x_289_ = lean_apply_1(v_modifyEnv_287_, v___f_288_);
        return v___x_289_;
    } else {
        let mut v_toApplicative_290_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_declRanges_285_);
        lean_dec(v_declName_284_);
        lean_dec_ref(v_inst_283_);
        v_toApplicative_290_ = lean_ctor_get(v_inst_282_, 0);
        lean_inc_ref(v_toApplicative_290_);
        lean_dec_ref(v_inst_282_);
        v_toPure_291_ = lean_ctor_get(v_toApplicative_290_, 1);
        lean_inc(v_toPure_291_);
        lean_dec_ref(v_toApplicative_290_);
        v___x_292_ = lean_box(0);
        v___x_293_ = lean_apply_2(v_toPure_291_, lean_box(0), v___x_292_);
        return v___x_293_;
    }
}
pub unsafe fn l_Lean_addDeclarationRanges(
    mut v_m_294_: *mut LeanObject,
    mut v_inst_295_: *mut LeanObject,
    mut v_inst_296_: *mut LeanObject,
    mut v_declName_297_: *mut LeanObject,
    mut v_declRanges_298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    v___x_299_ = l_Lean_addDeclarationRanges___redArg(
        v_inst_295_,
        v_inst_296_,
        v_declName_297_,
        v_declRanges_298_,
    );
    return v___x_299_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___redArg___lam__0(
    mut v___x_300_: *mut LeanObject,
    mut v_____do__lift_301_: *mut LeanObject,
    mut v_declName_302_: *mut LeanObject,
    mut v_toPure_303_: *mut LeanObject,
    mut v_____do__lift_304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_308_: u8 = 0;
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    v___x_305_ = l_Lean_declRangeExt;
    v_toEnvExtension_306_ = lean_ctor_get(v___x_305_, 0);
    v_asyncMode_307_ = lean_ctor_get(v_toEnvExtension_306_, 2);
    v___x_308_ = 0;
    lean_inc(v_declName_302_);
    lean_inc_ref(v___x_300_);
    v___x_309_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_300_,
        v___x_305_,
        v_____do__lift_301_,
        v_declName_302_,
        v_asyncMode_307_,
        v___x_308_,
    );
    if lean_obj_tag(v___x_309_) == 0 {
        let mut v___x_310_: u8 = 0;
        let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
        v___x_310_ = 1;
        v___x_311_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
            v___x_300_,
            v___x_305_,
            v_____do__lift_304_,
            v_declName_302_,
            v_asyncMode_307_,
            v___x_310_,
        );
        v___x_312_ = lean_apply_2(v_toPure_303_, lean_box(0), v___x_311_);
        return v___x_312_;
    } else {
        let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_____do__lift_304_);
        lean_dec(v_declName_302_);
        lean_dec_ref(v___x_300_);
        v___x_313_ = lean_apply_2(v_toPure_303_, lean_box(0), v___x_309_);
        return v___x_313_;
    }
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___redArg___lam__1(
    mut v___x_314_: *mut LeanObject,
    mut v_declName_315_: *mut LeanObject,
    mut v_toPure_316_: *mut LeanObject,
    mut v_toBind_317_: *mut LeanObject,
    mut v_getEnv_318_: *mut LeanObject,
    mut v_____do__lift_319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    v___f_320_ = lean_alloc_closure(
        l_Lean_findDeclarationRangesCore_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_320_, 0, v___x_314_);
    lean_closure_set(v___f_320_, 1, v_____do__lift_319_);
    lean_closure_set(v___f_320_, 2, v_declName_315_);
    lean_closure_set(v___f_320_, 3, v_toPure_316_);
    v___x_321_ = lean_apply_4(
        v_toBind_317_,
        lean_box(0),
        lean_box(0),
        v_getEnv_318_,
        v___f_320_,
    );
    return v___x_321_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___redArg(
    mut v_inst_322_: *mut LeanObject,
    mut v_inst_323_: *mut LeanObject,
    mut v_declName_324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_325_ = lean_ctor_get(v_inst_322_, 0);
    lean_inc_ref(v_toApplicative_325_);
    v_toBind_326_ = lean_ctor_get(v_inst_322_, 1);
    lean_inc_n(v_toBind_326_, 2);
    lean_dec_ref(v_inst_322_);
    v_getEnv_327_ = lean_ctor_get(v_inst_323_, 0);
    lean_inc_n(v_getEnv_327_, 2);
    lean_dec_ref(v_inst_323_);
    v_toPure_328_ = lean_ctor_get(v_toApplicative_325_, 1);
    lean_inc(v_toPure_328_);
    lean_dec_ref(v_toApplicative_325_);
    v___x_329_ = l_Lean_instInhabitedDeclarationRanges_default;
    v___f_330_ = lean_alloc_closure(
        l_Lean_findDeclarationRangesCore_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_330_, 0, v___x_329_);
    lean_closure_set(v___f_330_, 1, v_declName_324_);
    lean_closure_set(v___f_330_, 2, v_toPure_328_);
    lean_closure_set(v___f_330_, 3, v_toBind_326_);
    lean_closure_set(v___f_330_, 4, v_getEnv_327_);
    v___x_331_ = lean_apply_4(
        v_toBind_326_,
        lean_box(0),
        lean_box(0),
        v_getEnv_327_,
        v___f_330_,
    );
    return v___x_331_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f(
    mut v_m_332_: *mut LeanObject,
    mut v_inst_333_: *mut LeanObject,
    mut v_inst_334_: *mut LeanObject,
    mut v_declName_335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    v___x_336_ =
        l_Lean_findDeclarationRangesCore_x3f___redArg(v_inst_333_, v_inst_334_, v_declName_335_);
    return v___x_336_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__0(
    mut v_declName_337_: *mut LeanObject,
    mut v_toPure_338_: *mut LeanObject,
    mut v_____do__lift_339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    v___x_340_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_____do__lift_339_,
            v_declName_337_,
        );
    v___x_341_ = lean_apply_2(v_toPure_338_, lean_box(0), v___x_340_);
    return v___x_341_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__0___boxed(
    mut v_declName_342_: *mut LeanObject,
    mut v_toPure_343_: *mut LeanObject,
    mut v_____do__lift_344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_345_: *mut LeanObject = core::ptr::null_mut();
    v_res_345_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__0(
        v_declName_342_,
        v_toPure_343_,
        v_____do__lift_344_,
    );
    lean_dec(v_____do__lift_344_);
    lean_dec(v_declName_342_);
    return v_res_345_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__1(
    mut v___x_346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    v___x_348_ = lean_st_ref_get(v___x_346_);
    return v___x_348_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__1___boxed(
    mut v___x_349_: *mut LeanObject,
    mut v___y_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_351_: *mut LeanObject = core::ptr::null_mut();
    v_res_351_ = l_Lean_findDeclarationRanges_x3f___redArg___lam__1(v___x_349_);
    lean_dec(v___x_349_);
    return v_res_351_;
}
pub unsafe fn _init_l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0()
-> *mut LeanObject {
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_353_: *mut LeanObject = core::ptr::null_mut();
    v___x_352_ = l_Lean_builtinDeclRanges;
    v___f_353_ = lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_353_, 0, v___x_352_);
    return v___f_353_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__2(
    mut v_inst_354_: *mut LeanObject,
    mut v_toBind_355_: *mut LeanObject,
    mut v___f_356_: *mut LeanObject,
    mut v_toPure_357_: *mut LeanObject,
    mut v_ranges_358_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_ranges_358_) == 0 {
        let mut v___f_359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_357_);
        v___f_359_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0_once
            ),
            _init_l_Lean_findDeclarationRanges_x3f___redArg___lam__2___closed__0,
        );
        v___x_360_ = lean_apply_2(v_inst_354_, lean_box(0), v___f_359_);
        v___x_361_ = lean_apply_4(
            v_toBind_355_,
            lean_box(0),
            lean_box(0),
            v___x_360_,
            v___f_356_,
        );
        return v___x_361_;
    } else {
        let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_356_);
        lean_dec(v_toBind_355_);
        lean_dec(v_inst_354_);
        v___x_362_ = lean_apply_2(v_toPure_357_, lean_box(0), v_ranges_358_);
        return v___x_362_;
    }
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__3(
    mut v___f_363_: *mut LeanObject,
    mut v_ranges_364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    v___x_365_ = lean_apply_1(v___f_363_, v_ranges_364_);
    return v___x_365_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__5(
    mut v_declName_366_: *mut LeanObject,
    mut v_inst_367_: *mut LeanObject,
    mut v_inst_368_: *mut LeanObject,
    mut v_toBind_369_: *mut LeanObject,
    mut v___f_370_: *mut LeanObject,
    mut v___f_371_: *mut LeanObject,
    mut v_env_372_: *mut LeanObject,
    mut v_____do__lift_373_: u8,
) -> *mut LeanObject {
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_379_: u8 = 0;
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: u8 = 0;
    let mut v___x_383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_366_);
                lean_inc_ref(v_env_372_);
                v___x_382_ = l_Lean_isAuxRecursor(v_env_372_, v_declName_366_);
                if v___x_382_ == 0 {
                    lean_inc(v_declName_366_);
                    v___x_383_ = l_Lean_isNoConfusion(v_env_372_, v_declName_366_);
                    v___y_379_ = v___x_383_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_env_372_);
                    v___y_379_ = v___x_382_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_375_ = l_Lean_Name_getPrefix(v_declName_366_);
                lean_dec(v_declName_366_);
                v___x_376_ = l_Lean_findDeclarationRangesCore_x3f___redArg(
                    v_inst_367_,
                    v_inst_368_,
                    v___x_375_,
                );
                v___x_377_ = lean_apply_4(
                    v_toBind_369_,
                    lean_box(0),
                    lean_box(0),
                    v___x_376_,
                    v___f_370_,
                );
                return v___x_377_;
            }
            2 => {
                if v___y_379_ == 0 {
                    if v_____do__lift_373_ == 0 {
                        lean_dec(v___f_370_);
                        v___x_380_ = l_Lean_findDeclarationRangesCore_x3f___redArg(
                            v_inst_367_,
                            v_inst_368_,
                            v_declName_366_,
                        );
                        v___x_381_ = lean_apply_4(
                            v_toBind_369_,
                            lean_box(0),
                            lean_box(0),
                            v___x_380_,
                            v___f_371_,
                        );
                        return v___x_381_;
                    } else {
                        lean_dec(v___f_371_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___f_371_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg___lam__5___boxed(
    mut v_declName_384_: *mut LeanObject,
    mut v_inst_385_: *mut LeanObject,
    mut v_inst_386_: *mut LeanObject,
    mut v_toBind_387_: *mut LeanObject,
    mut v___f_388_: *mut LeanObject,
    mut v___f_389_: *mut LeanObject,
    mut v_env_390_: *mut LeanObject,
    mut v_____do__lift_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_270__boxed_392_: u8 = 0;
    let mut v_res_393_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_270__boxed_392_ = (lean_unbox(v_____do__lift_391_) as u8);
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
    mut v_declName_394_: *mut LeanObject,
    mut v_inst_395_: *mut LeanObject,
    mut v_inst_396_: *mut LeanObject,
    mut v_toBind_397_: *mut LeanObject,
    mut v___f_398_: *mut LeanObject,
    mut v___f_399_: *mut LeanObject,
    mut v_env_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_397_);
    lean_inc_ref(v_inst_396_);
    lean_inc_ref(v_inst_395_);
    lean_inc(v_declName_394_);
    v___f_401_ = lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__5___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_401_, 0, v_declName_394_);
    lean_closure_set(v___f_401_, 1, v_inst_395_);
    lean_closure_set(v___f_401_, 2, v_inst_396_);
    lean_closure_set(v___f_401_, 3, v_toBind_397_);
    lean_closure_set(v___f_401_, 4, v___f_398_);
    lean_closure_set(v___f_401_, 5, v___f_399_);
    lean_closure_set(v___f_401_, 6, v_env_400_);
    v___x_402_ = l_Lean_isRec___redArg(v_inst_395_, v_inst_396_, v_declName_394_);
    v___x_403_ = lean_apply_4(
        v_toBind_397_,
        lean_box(0),
        lean_box(0),
        v___x_402_,
        v___f_401_,
    );
    return v___x_403_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___redArg(
    mut v_inst_404_: *mut LeanObject,
    mut v_inst_405_: *mut LeanObject,
    mut v_inst_406_: *mut LeanObject,
    mut v_declName_407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_408_ = lean_ctor_get(v_inst_404_, 0);
    v_toBind_409_ = lean_ctor_get(v_inst_404_, 1);
    lean_inc_n(v_toBind_409_, 3);
    v_getEnv_410_ = lean_ctor_get(v_inst_405_, 0);
    lean_inc(v_getEnv_410_);
    v_toPure_411_ = lean_ctor_get(v_toApplicative_408_, 1);
    lean_inc_n(v_toPure_411_, 2);
    lean_inc(v_declName_407_);
    v___f_412_ = lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_412_, 0, v_declName_407_);
    lean_closure_set(v___f_412_, 1, v_toPure_411_);
    v___f_413_ = lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_413_, 0, v_inst_406_);
    lean_closure_set(v___f_413_, 1, v_toBind_409_);
    lean_closure_set(v___f_413_, 2, v___f_412_);
    lean_closure_set(v___f_413_, 3, v_toPure_411_);
    v___f_414_ = lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_414_, 0, v___f_413_);
    lean_inc_ref(v___f_414_);
    v___f_415_ = lean_alloc_closure(
        l_Lean_findDeclarationRanges_x3f___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_415_, 0, v_declName_407_);
    lean_closure_set(v___f_415_, 1, v_inst_404_);
    lean_closure_set(v___f_415_, 2, v_inst_405_);
    lean_closure_set(v___f_415_, 3, v_toBind_409_);
    lean_closure_set(v___f_415_, 4, v___f_414_);
    lean_closure_set(v___f_415_, 5, v___f_414_);
    v___x_416_ = lean_apply_4(
        v_toBind_409_,
        lean_box(0),
        lean_box(0),
        v_getEnv_410_,
        v___f_415_,
    );
    return v___x_416_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f(
    mut v_m_417_: *mut LeanObject,
    mut v_inst_418_: *mut LeanObject,
    mut v_inst_419_: *mut LeanObject,
    mut v_inst_420_: *mut LeanObject,
    mut v_declName_421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    v___x_422_ = l_Lean_findDeclarationRanges_x3f___redArg(
        v_inst_418_,
        v_inst_419_,
        v_inst_420_,
        v_declName_421_,
    );
    return v___x_422_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DeclarationRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_MonadEnv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_3757377111____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_builtinDeclRanges = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_builtinDeclRanges);
    lean_dec_ref(res);
    res = l___private_Lean_DeclarationRange_0__Lean_initFn_00___x40_Lean_DeclarationRange_1764327334____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_declRangeExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_declRangeExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DeclarationRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DeclarationRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_MonadEnv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_DeclarationRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_DeclarationRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_DeclarationRange(builtin);
}
