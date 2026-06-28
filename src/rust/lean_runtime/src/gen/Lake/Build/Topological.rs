// Lean compiler output
// Module: Lake.Build.Topological
// Imports: Lake.Util.Cycle Lake.Util.Store Lake.Util.EquipT
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_elem___redArg, l_List_partition_loop___redArg,
};
use crate::r#gen::Lake::Util::Cycle::{
    initialize_Lake_Util_Cycle, runtime_initialize_Lake_Util_Cycle,
};
use crate::r#gen::Lake::Util::EquipT::{
    initialize_Lake_Util_EquipT, runtime_initialize_Lake_Util_EquipT,
};
use crate::r#gen::Lake::Util::Store::{
    initialize_Lake_Util_Store, runtime_initialize_Lake_Util_Store,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag, lean_unbox,
};
pub static l_Lake_recFetchAcyclic___redArg___lam__3___closed__0_value: LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_recFetchAcyclic___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_recFetchAcyclic___redArg___lam__3___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lake_recFetch___redArg(
    mut v_fetch_165_: *mut LeanObject,
    mut v_a_166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_fetch_165_);
    v___x_167_ = lean_alloc_closure(l_Lake_recFetch___redArg as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_167_, 0, v_fetch_165_);
    v___x_168_ = lean_apply_2(v_fetch_165_, v_a_166_, v___x_167_);
    return v___x_168_;
}
pub unsafe fn l_Lake_recFetch(
    mut v_m_169_: *mut LeanObject,
    mut v_00_u03b1_170_: *mut LeanObject,
    mut v_00_u03b2_171_: *mut LeanObject,
    mut v_inst_172_: *mut LeanObject,
    mut v_fetch_173_: *mut LeanObject,
    mut v_a_174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    v___x_175_ = l_Lake_recFetch___redArg(v_fetch_173_, v_a_174_);
    return v___x_175_;
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__0(
    mut v___y_176_: *mut LeanObject,
    mut v_withCallStack_177_: *mut LeanObject,
    mut v_stack_178_: *mut LeanObject,
    mut v_a_179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    v___x_180_ = lean_apply_1(v___y_176_, v_a_179_);
    v___x_181_ = lean_apply_3(v_withCallStack_177_, lean_box(0), v_stack_178_, v___x_180_);
    return v___x_181_;
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__1(
    mut v___y_182_: *mut LeanObject,
    mut v_withCallStack_183_: *mut LeanObject,
    mut v_fetch_184_: *mut LeanObject,
    mut v_a_185_: *mut LeanObject,
    mut v_stack_186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    v___f_187_ = lean_alloc_closure(
        l_Lake_recFetchAcyclic___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_187_, 0, v___y_182_);
    lean_closure_set(v___f_187_, 1, v_withCallStack_183_);
    lean_closure_set(v___f_187_, 2, v_stack_186_);
    v___x_188_ = lean_apply_2(v_fetch_184_, v_a_185_, v___f_187_);
    return v___x_188_;
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__2(
    mut v_inst_189_: *mut LeanObject,
    mut v___x_190_: *mut LeanObject,
    mut v___x_191_: u8,
    mut v_x_192_: *mut LeanObject,
) -> u8 {
    let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_194_: u8 = 0;
    v___x_193_ = lean_apply_2(v_inst_189_, v_x_192_, v___x_190_);
    v___x_194_ = (lean_unbox(v___x_193_) as u8);
    if v___x_194_ == 0 {
        return v___x_191_;
    } else {
        let mut v___x_195_: u8 = 0;
        v___x_195_ = 0;
        return v___x_195_;
    }
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__2___boxed(
    mut v_inst_196_: *mut LeanObject,
    mut v___x_197_: *mut LeanObject,
    mut v___x_198_: *mut LeanObject,
    mut v_x_199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_136__boxed_200_: u8 = 0;
    let mut v_res_201_: u8 = 0;
    let mut v_r_202_: *mut LeanObject = core::ptr::null_mut();
    v___x_136__boxed_200_ = (lean_unbox(v___x_198_) as u8);
    v_res_201_ = l_Lake_recFetchAcyclic___redArg___lam__2(
        v_inst_196_,
        v___x_197_,
        v___x_136__boxed_200_,
        v_x_199_,
    );
    v_r_202_ = lean_box((v_res_201_) as usize);
    return v_r_202_;
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__3(
    mut v_inst_205_: *mut LeanObject,
    mut v___x_206_: *mut LeanObject,
    mut v_withCallStack_207_: *mut LeanObject,
    mut v___x_208_: *mut LeanObject,
    mut v_throwCycle_209_: *mut LeanObject,
    mut v_parents_210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_211_: u8 = 0;
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_222_: u8 = 0;
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_229_: u8 = 0;
    let mut v_unused_230_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_parents_210_);
                lean_inc(v___x_206_);
                lean_inc_ref(v_inst_205_);
                v___x_211_ = l_List_elem___redArg(v_inst_205_, v___x_206_, v_parents_210_);
                if v___x_211_ == 0 {
                    lean_dec(v_throwCycle_209_);
                    lean_dec_ref(v_inst_205_);
                    v___x_212_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_212_, 0, v___x_206_);
                    lean_ctor_set(v___x_212_, 1, v_parents_210_);
                    v___x_213_ =
                        lean_apply_3(v_withCallStack_207_, lean_box(0), v___x_212_, v___x_208_);
                    return v___x_213_;
                } else {
                    lean_dec(v___x_208_);
                    lean_dec(v_withCallStack_207_);
                    v___x_214_ = lean_box((v___x_211_) as usize);
                    lean_inc(v___x_206_);
                    v___f_215_ = lean_alloc_closure(
                        l_Lake_recFetchAcyclic___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_215_, 0, v_inst_205_);
                    lean_closure_set(v___f_215_, 1, v___x_206_);
                    lean_closure_set(v___f_215_, 2, v___x_214_);
                    v___x_216_ = lean_box(0);
                    v___x_217_ = l_Lake_recFetchAcyclic___redArg___lam__3___closed__0;
                    v___x_218_ =
                        l_List_partition_loop___redArg(v___f_215_, v_parents_210_, v___x_217_);
                    v_fst_219_ = lean_ctor_get(v___x_218_, 0);
                    v_isSharedCheck_229_ = (!lean_is_exclusive(v___x_218_)) as u8;
                    if v_isSharedCheck_229_ == 0 {
                        v_unused_230_ = lean_ctor_get(v___x_218_, 1);
                        lean_dec(v_unused_230_);
                        v___x_221_ = v___x_218_;
                        v_isShared_222_ = v_isSharedCheck_229_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_219_);
                        lean_dec(v___x_218_);
                        v___x_221_ = lean_box(0);
                        v_isShared_222_ = v_isSharedCheck_229_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___x_206_);
                if v_isShared_222_ == 0 {
                    lean_ctor_set_tag(v___x_221_, 1);
                    lean_ctor_set(v___x_221_, 1, v_fst_219_);
                    lean_ctor_set(v___x_221_, 0, v___x_206_);
                    v___x_224_ = v___x_221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_206_);
                    lean_ctor_set(v_reuseFailAlloc_228_, 1, v_fst_219_);
                    v___x_224_ = v_reuseFailAlloc_228_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_225_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_225_, 0, v___x_206_);
                lean_ctor_set(v___x_225_, 1, v___x_216_);
                v___x_226_ = l_List_appendTR___redArg(v___x_224_, v___x_225_);
                v___x_227_ = lean_apply_2(v_throwCycle_209_, lean_box(0), v___x_226_);
                return v___x_227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__4(
    mut v_toMonadCallStack_231_: *mut LeanObject,
    mut v_fetch_232_: *mut LeanObject,
    mut v_keyOf_233_: *mut LeanObject,
    mut v_toBind_234_: *mut LeanObject,
    mut v_inst_235_: *mut LeanObject,
    mut v_throwCycle_236_: *mut LeanObject,
    mut v_a_237_: *mut LeanObject,
    mut v___y_238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getCallStack_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withCallStack_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    v_getCallStack_239_ = lean_ctor_get(v_toMonadCallStack_231_, 0);
    lean_inc_n(v_getCallStack_239_, 2);
    v_withCallStack_240_ = lean_ctor_get(v_toMonadCallStack_231_, 1);
    lean_inc_n(v_withCallStack_240_, 2);
    lean_dec_ref(v_toMonadCallStack_231_);
    lean_inc(v_a_237_);
    v___f_241_ = lean_alloc_closure(
        l_Lake_recFetchAcyclic___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_241_, 0, v___y_238_);
    lean_closure_set(v___f_241_, 1, v_withCallStack_240_);
    lean_closure_set(v___f_241_, 2, v_fetch_232_);
    lean_closure_set(v___f_241_, 3, v_a_237_);
    v___x_242_ = lean_apply_1(v_keyOf_233_, v_a_237_);
    lean_inc(v_toBind_234_);
    v___x_243_ = lean_apply_4(
        v_toBind_234_,
        lean_box(0),
        lean_box(0),
        v_getCallStack_239_,
        v___f_241_,
    );
    v___f_244_ = lean_alloc_closure(
        l_Lake_recFetchAcyclic___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_244_, 0, v_inst_235_);
    lean_closure_set(v___f_244_, 1, v___x_242_);
    lean_closure_set(v___f_244_, 2, v_withCallStack_240_);
    lean_closure_set(v___f_244_, 3, v___x_243_);
    lean_closure_set(v___f_244_, 4, v_throwCycle_236_);
    v___x_245_ = lean_apply_4(
        v_toBind_234_,
        lean_box(0),
        lean_box(0),
        v_getCallStack_239_,
        v___f_244_,
    );
    return v___x_245_;
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg(
    mut v_inst_246_: *mut LeanObject,
    mut v_inst_247_: *mut LeanObject,
    mut v_inst_248_: *mut LeanObject,
    mut v_keyOf_249_: *mut LeanObject,
    mut v_fetch_250_: *mut LeanObject,
    mut v_a_251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadCallStack_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throwCycle_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_252_ = lean_ctor_get(v_inst_247_, 1);
    lean_inc(v_toBind_252_);
    lean_dec_ref(v_inst_247_);
    v_toMonadCallStack_253_ = lean_ctor_get(v_inst_248_, 0);
    lean_inc_ref(v_toMonadCallStack_253_);
    v_throwCycle_254_ = lean_ctor_get(v_inst_248_, 1);
    lean_inc(v_throwCycle_254_);
    lean_dec_ref(v_inst_248_);
    v___f_255_ = lean_alloc_closure(
        l_Lake_recFetchAcyclic___redArg___lam__4 as *mut core::ffi::c_void,
        8,
        6,
    );
    lean_closure_set(v___f_255_, 0, v_toMonadCallStack_253_);
    lean_closure_set(v___f_255_, 1, v_fetch_250_);
    lean_closure_set(v___f_255_, 2, v_keyOf_249_);
    lean_closure_set(v___f_255_, 3, v_toBind_252_);
    lean_closure_set(v___f_255_, 4, v_inst_246_);
    lean_closure_set(v___f_255_, 5, v_throwCycle_254_);
    v___x_256_ = l_Lake_recFetch___redArg(v___f_255_, v_a_251_);
    return v___x_256_;
}
pub unsafe fn l_Lake_recFetchAcyclic(
    mut v_00_u03ba_257_: *mut LeanObject,
    mut v_m_258_: *mut LeanObject,
    mut v_00_u03b1_259_: *mut LeanObject,
    mut v_00_u03b2_260_: *mut LeanObject,
    mut v_inst_261_: *mut LeanObject,
    mut v_inst_262_: *mut LeanObject,
    mut v_inst_263_: *mut LeanObject,
    mut v_keyOf_264_: *mut LeanObject,
    mut v_fetch_265_: *mut LeanObject,
    mut v_a_266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    v___x_267_ = l_Lake_recFetchAcyclic___redArg(
        v_inst_261_,
        v_inst_262_,
        v_inst_263_,
        v_keyOf_264_,
        v_fetch_265_,
        v_a_266_,
    );
    return v___x_267_;
}
pub unsafe fn l_Lake_recFetchMemoize___redArg___lam__0(
    mut v_toApplicative_268_: *mut LeanObject,
    mut v_a_269_: *mut LeanObject,
    mut v_a_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_271_ = lean_ctor_get(v_toApplicative_268_, 1);
    lean_inc(v_toPure_271_);
    lean_dec_ref(v_toApplicative_268_);
    v___x_272_ = lean_apply_2(v_toPure_271_, lean_box(0), v_a_269_);
    return v___x_272_;
}
pub unsafe fn l_Lake_recFetchMemoize___redArg___lam__1(
    mut v_toApplicative_273_: *mut LeanObject,
    mut v_store_274_: *mut LeanObject,
    mut v___x_275_: *mut LeanObject,
    mut v_toBind_276_: *mut LeanObject,
    mut v_a_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_277_);
    v___f_278_ = lean_alloc_closure(
        l_Lake_recFetchMemoize___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_278_, 0, v_toApplicative_273_);
    lean_closure_set(v___f_278_, 1, v_a_277_);
    v___x_279_ = lean_apply_2(v_store_274_, v___x_275_, v_a_277_);
    v___x_280_ = lean_apply_4(
        v_toBind_276_,
        lean_box(0),
        lean_box(0),
        v___x_279_,
        v___f_278_,
    );
    return v___x_280_;
}
pub unsafe fn l_Lake_recFetchMemoize___redArg___lam__2(
    mut v_compute_281_: *mut LeanObject,
    mut v_a_282_: *mut LeanObject,
    mut v___y_283_: *mut LeanObject,
    mut v_toBind_284_: *mut LeanObject,
    mut v___f_285_: *mut LeanObject,
    mut v_toApplicative_286_: *mut LeanObject,
    mut v_a_287_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_287_) == 0 {
        let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_286_);
        v___x_288_ = lean_apply_2(v_compute_281_, v_a_282_, v___y_283_);
        v___x_289_ = lean_apply_4(
            v_toBind_284_,
            lean_box(0),
            lean_box(0),
            v___x_288_,
            v___f_285_,
        );
        return v___x_289_;
    } else {
        let mut v_val_290_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_285_);
        lean_dec(v_toBind_284_);
        lean_dec(v___y_283_);
        lean_dec(v_a_282_);
        lean_dec(v_compute_281_);
        v_val_290_ = lean_ctor_get(v_a_287_, 0);
        lean_inc(v_val_290_);
        lean_dec_ref_known(v_a_287_, 1);
        v_toPure_291_ = lean_ctor_get(v_toApplicative_286_, 1);
        lean_inc(v_toPure_291_);
        lean_dec_ref(v_toApplicative_286_);
        v___x_292_ = lean_apply_2(v_toPure_291_, lean_box(0), v_val_290_);
        return v___x_292_;
    }
}
pub unsafe fn l_Lake_recFetchMemoize___redArg___lam__3(
    mut v_inst_293_: *mut LeanObject,
    mut v_inst_294_: *mut LeanObject,
    mut v_keyOf_295_: *mut LeanObject,
    mut v_compute_296_: *mut LeanObject,
    mut v_a_297_: *mut LeanObject,
    mut v___y_298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fetch_x3f_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_store_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_299_ = lean_ctor_get(v_inst_293_, 0);
    lean_inc_ref_n(v_toApplicative_299_, 2);
    v_toBind_300_ = lean_ctor_get(v_inst_293_, 1);
    lean_inc_n(v_toBind_300_, 3);
    lean_dec_ref(v_inst_293_);
    v_fetch_x3f_301_ = lean_ctor_get(v_inst_294_, 0);
    lean_inc(v_fetch_x3f_301_);
    v_store_302_ = lean_ctor_get(v_inst_294_, 1);
    lean_inc(v_store_302_);
    lean_dec_ref(v_inst_294_);
    lean_inc(v_a_297_);
    v___x_303_ = lean_apply_1(v_keyOf_295_, v_a_297_);
    lean_inc(v___x_303_);
    v___f_304_ = lean_alloc_closure(
        l_Lake_recFetchMemoize___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_304_, 0, v_toApplicative_299_);
    lean_closure_set(v___f_304_, 1, v_store_302_);
    lean_closure_set(v___f_304_, 2, v___x_303_);
    lean_closure_set(v___f_304_, 3, v_toBind_300_);
    v___f_305_ = lean_alloc_closure(
        l_Lake_recFetchMemoize___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_305_, 0, v_compute_296_);
    lean_closure_set(v___f_305_, 1, v_a_297_);
    lean_closure_set(v___f_305_, 2, v___y_298_);
    lean_closure_set(v___f_305_, 3, v_toBind_300_);
    lean_closure_set(v___f_305_, 4, v___f_304_);
    lean_closure_set(v___f_305_, 5, v_toApplicative_299_);
    v___x_306_ = lean_apply_1(v_fetch_x3f_301_, v___x_303_);
    v___x_307_ = lean_apply_4(
        v_toBind_300_,
        lean_box(0),
        lean_box(0),
        v___x_306_,
        v___f_305_,
    );
    return v___x_307_;
}
pub unsafe fn l_Lake_recFetchMemoize___redArg(
    mut v_inst_308_: *mut LeanObject,
    mut v_inst_309_: *mut LeanObject,
    mut v_inst_310_: *mut LeanObject,
    mut v_inst_311_: *mut LeanObject,
    mut v_keyOf_312_: *mut LeanObject,
    mut v_compute_313_: *mut LeanObject,
    mut v_a_314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_keyOf_312_);
    lean_inc_ref(v_inst_309_);
    v___f_315_ = lean_alloc_closure(
        l_Lake_recFetchMemoize___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_315_, 0, v_inst_309_);
    lean_closure_set(v___f_315_, 1, v_inst_311_);
    lean_closure_set(v___f_315_, 2, v_keyOf_312_);
    lean_closure_set(v___f_315_, 3, v_compute_313_);
    v___x_316_ = l_Lake_recFetchAcyclic___redArg(
        v_inst_308_,
        v_inst_309_,
        v_inst_310_,
        v_keyOf_312_,
        v___f_315_,
        v_a_314_,
    );
    return v___x_316_;
}
pub unsafe fn l_Lake_recFetchMemoize(
    mut v_00_u03ba_317_: *mut LeanObject,
    mut v_m_318_: *mut LeanObject,
    mut v_00_u03b2_319_: *mut LeanObject,
    mut v_00_u03b1_320_: *mut LeanObject,
    mut v_inst_321_: *mut LeanObject,
    mut v_inst_322_: *mut LeanObject,
    mut v_inst_323_: *mut LeanObject,
    mut v_inst_324_: *mut LeanObject,
    mut v_keyOf_325_: *mut LeanObject,
    mut v_compute_326_: *mut LeanObject,
    mut v_a_327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    v___x_328_ = l_Lake_recFetchMemoize___redArg(
        v_inst_321_,
        v_inst_322_,
        v_inst_323_,
        v_inst_324_,
        v_keyOf_325_,
        v_compute_326_,
        v_a_327_,
    );
    return v___x_328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Topological(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Cycle(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Store(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EquipT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Topological(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Topological(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Cycle(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Store(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_EquipT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Topological(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Topological(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Topological(builtin);
}
