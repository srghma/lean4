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
pub static l_Lake_recFetchAcyclic___redArg___lam__3___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_recFetchAcyclic___redArg___lam__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_recFetchAcyclic___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_recFetch___redArg(
    mut v_fetch_165_: *mut crate::leanh::LeanObject,
    mut v_a_166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_fetch_165_);
    v___x_167_ =
        crate::leanh::lean_alloc_closure(l_Lake_recFetch___redArg as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___x_167_, 0, v_fetch_165_);
    v___x_168_ = crate::leanh::lean_apply_2(v_fetch_165_, v_a_166_, v___x_167_);
    return v___x_168_;
}
pub unsafe fn l_Lake_recFetch(
    mut v_m_169_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_170_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_171_: *mut crate::leanh::LeanObject,
    mut v_inst_172_: *mut crate::leanh::LeanObject,
    mut v_fetch_173_: *mut crate::leanh::LeanObject,
    mut v_a_174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_175_ = l_Lake_recFetch___redArg(v_fetch_173_, v_a_174_);
    return v___x_175_;
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__0(
    mut v___y_176_: *mut crate::leanh::LeanObject,
    mut v_withCallStack_177_: *mut crate::leanh::LeanObject,
    mut v_stack_178_: *mut crate::leanh::LeanObject,
    mut v_a_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_180_ = crate::leanh::lean_apply_1(v___y_176_, v_a_179_);
    v___x_181_ = crate::leanh::lean_apply_3(
        v_withCallStack_177_,
        crate::leanh::lean_box(0),
        v_stack_178_,
        v___x_180_,
    );
    return v___x_181_;
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__1(
    mut v___y_182_: *mut crate::leanh::LeanObject,
    mut v_withCallStack_183_: *mut crate::leanh::LeanObject,
    mut v_fetch_184_: *mut crate::leanh::LeanObject,
    mut v_a_185_: *mut crate::leanh::LeanObject,
    mut v_stack_186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_187_ = crate::leanh::lean_alloc_closure(
        l_Lake_recFetchAcyclic___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_187_, 0, v___y_182_);
    crate::leanh::lean_closure_set(v___f_187_, 1, v_withCallStack_183_);
    crate::leanh::lean_closure_set(v___f_187_, 2, v_stack_186_);
    v___x_188_ = crate::leanh::lean_apply_2(v_fetch_184_, v_a_185_, v___f_187_);
    return v___x_188_;
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__2(
    mut v_inst_189_: *mut crate::leanh::LeanObject,
    mut v___x_190_: *mut crate::leanh::LeanObject,
    mut v___x_191_: u8,
    mut v_x_192_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: u8 = 0;
    v___x_193_ = crate::leanh::lean_apply_2(v_inst_189_, v_x_192_, v___x_190_);
    v___x_194_ = (crate::leanh::lean_unbox(v___x_193_) as u8);
    if v___x_194_ == 0 {
        return v___x_191_;
    } else {
        let mut v___x_195_: u8 = 0;
        v___x_195_ = 0;
        return v___x_195_;
    }
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__2___boxed(
    mut v_inst_196_: *mut crate::leanh::LeanObject,
    mut v___x_197_: *mut crate::leanh::LeanObject,
    mut v___x_198_: *mut crate::leanh::LeanObject,
    mut v_x_199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_136__boxed_200_: u8 = 0;
    let mut v_res_201_: u8 = 0;
    let mut v_r_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_136__boxed_200_ = (crate::leanh::lean_unbox(v___x_198_) as u8);
    v_res_201_ = l_Lake_recFetchAcyclic___redArg___lam__2(
        v_inst_196_,
        v___x_197_,
        v___x_136__boxed_200_,
        v_x_199_,
    );
    v_r_202_ = crate::leanh::lean_box((v_res_201_) as usize);
    return v_r_202_;
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__3(
    mut v_inst_205_: *mut crate::leanh::LeanObject,
    mut v___x_206_: *mut crate::leanh::LeanObject,
    mut v_withCallStack_207_: *mut crate::leanh::LeanObject,
    mut v___x_208_: *mut crate::leanh::LeanObject,
    mut v_throwCycle_209_: *mut crate::leanh::LeanObject,
    mut v_parents_210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_211_: u8 = 0;
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_222_: u8 = 0;
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_229_: u8 = 0;
    let mut v_unused_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_parents_210_);
                crate::leanh::lean_inc(v___x_206_);
                crate::leanh::lean_inc_ref(v_inst_205_);
                v___x_211_ = l_List_elem___redArg(v_inst_205_, v___x_206_, v_parents_210_);
                if v___x_211_ == 0 {
                    crate::leanh::lean_dec(v_throwCycle_209_);
                    crate::leanh::lean_dec_ref(v_inst_205_);
                    v___x_212_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_212_, 0, v___x_206_);
                    crate::leanh::lean_ctor_set(v___x_212_, 1, v_parents_210_);
                    v___x_213_ = crate::leanh::lean_apply_3(
                        v_withCallStack_207_,
                        crate::leanh::lean_box(0),
                        v___x_212_,
                        v___x_208_,
                    );
                    return v___x_213_;
                } else {
                    crate::leanh::lean_dec(v___x_208_);
                    crate::leanh::lean_dec(v_withCallStack_207_);
                    v___x_214_ = crate::leanh::lean_box((v___x_211_) as usize);
                    crate::leanh::lean_inc(v___x_206_);
                    v___f_215_ = crate::leanh::lean_alloc_closure(
                        l_Lake_recFetchAcyclic___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_215_, 0, v_inst_205_);
                    crate::leanh::lean_closure_set(v___f_215_, 1, v___x_206_);
                    crate::leanh::lean_closure_set(v___f_215_, 2, v___x_214_);
                    v___x_216_ = crate::leanh::lean_box(0);
                    v___x_217_ = l_Lake_recFetchAcyclic___redArg___lam__3___closed__0;
                    v___x_218_ =
                        l_List_partition_loop___redArg(v___f_215_, v_parents_210_, v___x_217_);
                    v_fst_219_ = crate::leanh::lean_ctor_get(v___x_218_, 0);
                    v_isSharedCheck_229_ = (!crate::leanh::lean_is_exclusive(v___x_218_)) as u8;
                    if v_isSharedCheck_229_ == 0 {
                        v_unused_230_ = crate::leanh::lean_ctor_get(v___x_218_, 1);
                        crate::leanh::lean_dec(v_unused_230_);
                        v___x_221_ = v___x_218_;
                        v_isShared_222_ = v_isSharedCheck_229_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_219_);
                        crate::leanh::lean_dec(v___x_218_);
                        v___x_221_ = crate::leanh::lean_box(0);
                        v_isShared_222_ = v_isSharedCheck_229_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___x_206_);
                if v_isShared_222_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_221_, 1);
                    crate::leanh::lean_ctor_set(v___x_221_, 1, v_fst_219_);
                    crate::leanh::lean_ctor_set(v___x_221_, 0, v___x_206_);
                    v___x_224_ = v___x_221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_228_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_228_, 1, v_fst_219_);
                    v___x_224_ = v_reuseFailAlloc_228_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_225_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_225_, 0, v___x_206_);
                crate::leanh::lean_ctor_set(v___x_225_, 1, v___x_216_);
                v___x_226_ = l_List_appendTR___redArg(v___x_224_, v___x_225_);
                v___x_227_ = crate::leanh::lean_apply_2(
                    v_throwCycle_209_,
                    crate::leanh::lean_box(0),
                    v___x_226_,
                );
                return v___x_227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg___lam__4(
    mut v_toMonadCallStack_231_: *mut crate::leanh::LeanObject,
    mut v_fetch_232_: *mut crate::leanh::LeanObject,
    mut v_keyOf_233_: *mut crate::leanh::LeanObject,
    mut v_toBind_234_: *mut crate::leanh::LeanObject,
    mut v_inst_235_: *mut crate::leanh::LeanObject,
    mut v_throwCycle_236_: *mut crate::leanh::LeanObject,
    mut v_a_237_: *mut crate::leanh::LeanObject,
    mut v___y_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCallStack_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_withCallStack_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getCallStack_239_ = crate::leanh::lean_ctor_get(v_toMonadCallStack_231_, 0);
    crate::leanh::lean_inc_n(v_getCallStack_239_, 2);
    v_withCallStack_240_ = crate::leanh::lean_ctor_get(v_toMonadCallStack_231_, 1);
    crate::leanh::lean_inc_n(v_withCallStack_240_, 2);
    crate::leanh::lean_dec_ref(v_toMonadCallStack_231_);
    crate::leanh::lean_inc(v_a_237_);
    v___f_241_ = crate::leanh::lean_alloc_closure(
        l_Lake_recFetchAcyclic___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_241_, 0, v___y_238_);
    crate::leanh::lean_closure_set(v___f_241_, 1, v_withCallStack_240_);
    crate::leanh::lean_closure_set(v___f_241_, 2, v_fetch_232_);
    crate::leanh::lean_closure_set(v___f_241_, 3, v_a_237_);
    v___x_242_ = crate::leanh::lean_apply_1(v_keyOf_233_, v_a_237_);
    crate::leanh::lean_inc(v_toBind_234_);
    v___x_243_ = crate::leanh::lean_apply_4(
        v_toBind_234_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCallStack_239_,
        v___f_241_,
    );
    v___f_244_ = crate::leanh::lean_alloc_closure(
        l_Lake_recFetchAcyclic___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_244_, 0, v_inst_235_);
    crate::leanh::lean_closure_set(v___f_244_, 1, v___x_242_);
    crate::leanh::lean_closure_set(v___f_244_, 2, v_withCallStack_240_);
    crate::leanh::lean_closure_set(v___f_244_, 3, v___x_243_);
    crate::leanh::lean_closure_set(v___f_244_, 4, v_throwCycle_236_);
    v___x_245_ = crate::leanh::lean_apply_4(
        v_toBind_234_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCallStack_239_,
        v___f_244_,
    );
    return v___x_245_;
}
pub unsafe fn l_Lake_recFetchAcyclic___redArg(
    mut v_inst_246_: *mut crate::leanh::LeanObject,
    mut v_inst_247_: *mut crate::leanh::LeanObject,
    mut v_inst_248_: *mut crate::leanh::LeanObject,
    mut v_keyOf_249_: *mut crate::leanh::LeanObject,
    mut v_fetch_250_: *mut crate::leanh::LeanObject,
    mut v_a_251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadCallStack_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_throwCycle_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_252_ = crate::leanh::lean_ctor_get(v_inst_247_, 1);
    crate::leanh::lean_inc(v_toBind_252_);
    crate::leanh::lean_dec_ref(v_inst_247_);
    v_toMonadCallStack_253_ = crate::leanh::lean_ctor_get(v_inst_248_, 0);
    crate::leanh::lean_inc_ref(v_toMonadCallStack_253_);
    v_throwCycle_254_ = crate::leanh::lean_ctor_get(v_inst_248_, 1);
    crate::leanh::lean_inc(v_throwCycle_254_);
    crate::leanh::lean_dec_ref(v_inst_248_);
    v___f_255_ = crate::leanh::lean_alloc_closure(
        l_Lake_recFetchAcyclic___redArg___lam__4 as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___f_255_, 0, v_toMonadCallStack_253_);
    crate::leanh::lean_closure_set(v___f_255_, 1, v_fetch_250_);
    crate::leanh::lean_closure_set(v___f_255_, 2, v_keyOf_249_);
    crate::leanh::lean_closure_set(v___f_255_, 3, v_toBind_252_);
    crate::leanh::lean_closure_set(v___f_255_, 4, v_inst_246_);
    crate::leanh::lean_closure_set(v___f_255_, 5, v_throwCycle_254_);
    v___x_256_ = l_Lake_recFetch___redArg(v___f_255_, v_a_251_);
    return v___x_256_;
}
pub unsafe fn l_Lake_recFetchAcyclic(
    mut v_00_u03ba_257_: *mut crate::leanh::LeanObject,
    mut v_m_258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_259_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_260_: *mut crate::leanh::LeanObject,
    mut v_inst_261_: *mut crate::leanh::LeanObject,
    mut v_inst_262_: *mut crate::leanh::LeanObject,
    mut v_inst_263_: *mut crate::leanh::LeanObject,
    mut v_keyOf_264_: *mut crate::leanh::LeanObject,
    mut v_fetch_265_: *mut crate::leanh::LeanObject,
    mut v_a_266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_toApplicative_268_: *mut crate::leanh::LeanObject,
    mut v_a_269_: *mut crate::leanh::LeanObject,
    mut v_a_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_271_ = crate::leanh::lean_ctor_get(v_toApplicative_268_, 1);
    crate::leanh::lean_inc(v_toPure_271_);
    crate::leanh::lean_dec_ref(v_toApplicative_268_);
    v___x_272_ = crate::leanh::lean_apply_2(v_toPure_271_, crate::leanh::lean_box(0), v_a_269_);
    return v___x_272_;
}
pub unsafe fn l_Lake_recFetchMemoize___redArg___lam__1(
    mut v_toApplicative_273_: *mut crate::leanh::LeanObject,
    mut v_store_274_: *mut crate::leanh::LeanObject,
    mut v___x_275_: *mut crate::leanh::LeanObject,
    mut v_toBind_276_: *mut crate::leanh::LeanObject,
    mut v_a_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_277_);
    v___f_278_ = crate::leanh::lean_alloc_closure(
        l_Lake_recFetchMemoize___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_278_, 0, v_toApplicative_273_);
    crate::leanh::lean_closure_set(v___f_278_, 1, v_a_277_);
    v___x_279_ = crate::leanh::lean_apply_2(v_store_274_, v___x_275_, v_a_277_);
    v___x_280_ = crate::leanh::lean_apply_4(
        v_toBind_276_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_279_,
        v___f_278_,
    );
    return v___x_280_;
}
pub unsafe fn l_Lake_recFetchMemoize___redArg___lam__2(
    mut v_compute_281_: *mut crate::leanh::LeanObject,
    mut v_a_282_: *mut crate::leanh::LeanObject,
    mut v___y_283_: *mut crate::leanh::LeanObject,
    mut v_toBind_284_: *mut crate::leanh::LeanObject,
    mut v___f_285_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_286_: *mut crate::leanh::LeanObject,
    mut v_a_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_287_) == 0 {
        let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toApplicative_286_);
        v___x_288_ = crate::leanh::lean_apply_2(v_compute_281_, v_a_282_, v___y_283_);
        v___x_289_ = crate::leanh::lean_apply_4(
            v_toBind_284_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_288_,
            v___f_285_,
        );
        return v___x_289_;
    } else {
        let mut v_val_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_285_);
        crate::leanh::lean_dec(v_toBind_284_);
        crate::leanh::lean_dec(v___y_283_);
        crate::leanh::lean_dec(v_a_282_);
        crate::leanh::lean_dec(v_compute_281_);
        v_val_290_ = crate::leanh::lean_ctor_get(v_a_287_, 0);
        crate::leanh::lean_inc(v_val_290_);
        crate::leanh::lean_dec_ref_known(v_a_287_, 1);
        v_toPure_291_ = crate::leanh::lean_ctor_get(v_toApplicative_286_, 1);
        crate::leanh::lean_inc(v_toPure_291_);
        crate::leanh::lean_dec_ref(v_toApplicative_286_);
        v___x_292_ =
            crate::leanh::lean_apply_2(v_toPure_291_, crate::leanh::lean_box(0), v_val_290_);
        return v___x_292_;
    }
}
pub unsafe fn l_Lake_recFetchMemoize___redArg___lam__3(
    mut v_inst_293_: *mut crate::leanh::LeanObject,
    mut v_inst_294_: *mut crate::leanh::LeanObject,
    mut v_keyOf_295_: *mut crate::leanh::LeanObject,
    mut v_compute_296_: *mut crate::leanh::LeanObject,
    mut v_a_297_: *mut crate::leanh::LeanObject,
    mut v___y_298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fetch_x3f_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_store_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_299_ = crate::leanh::lean_ctor_get(v_inst_293_, 0);
    crate::leanh::lean_inc_ref_n(v_toApplicative_299_, 2);
    v_toBind_300_ = crate::leanh::lean_ctor_get(v_inst_293_, 1);
    crate::leanh::lean_inc_n(v_toBind_300_, 3);
    crate::leanh::lean_dec_ref(v_inst_293_);
    v_fetch_x3f_301_ = crate::leanh::lean_ctor_get(v_inst_294_, 0);
    crate::leanh::lean_inc(v_fetch_x3f_301_);
    v_store_302_ = crate::leanh::lean_ctor_get(v_inst_294_, 1);
    crate::leanh::lean_inc(v_store_302_);
    crate::leanh::lean_dec_ref(v_inst_294_);
    crate::leanh::lean_inc(v_a_297_);
    v___x_303_ = crate::leanh::lean_apply_1(v_keyOf_295_, v_a_297_);
    crate::leanh::lean_inc(v___x_303_);
    v___f_304_ = crate::leanh::lean_alloc_closure(
        l_Lake_recFetchMemoize___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_304_, 0, v_toApplicative_299_);
    crate::leanh::lean_closure_set(v___f_304_, 1, v_store_302_);
    crate::leanh::lean_closure_set(v___f_304_, 2, v___x_303_);
    crate::leanh::lean_closure_set(v___f_304_, 3, v_toBind_300_);
    v___f_305_ = crate::leanh::lean_alloc_closure(
        l_Lake_recFetchMemoize___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_305_, 0, v_compute_296_);
    crate::leanh::lean_closure_set(v___f_305_, 1, v_a_297_);
    crate::leanh::lean_closure_set(v___f_305_, 2, v___y_298_);
    crate::leanh::lean_closure_set(v___f_305_, 3, v_toBind_300_);
    crate::leanh::lean_closure_set(v___f_305_, 4, v___f_304_);
    crate::leanh::lean_closure_set(v___f_305_, 5, v_toApplicative_299_);
    v___x_306_ = crate::leanh::lean_apply_1(v_fetch_x3f_301_, v___x_303_);
    v___x_307_ = crate::leanh::lean_apply_4(
        v_toBind_300_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_306_,
        v___f_305_,
    );
    return v___x_307_;
}
pub unsafe fn l_Lake_recFetchMemoize___redArg(
    mut v_inst_308_: *mut crate::leanh::LeanObject,
    mut v_inst_309_: *mut crate::leanh::LeanObject,
    mut v_inst_310_: *mut crate::leanh::LeanObject,
    mut v_inst_311_: *mut crate::leanh::LeanObject,
    mut v_keyOf_312_: *mut crate::leanh::LeanObject,
    mut v_compute_313_: *mut crate::leanh::LeanObject,
    mut v_a_314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_keyOf_312_);
    crate::leanh::lean_inc_ref(v_inst_309_);
    v___f_315_ = crate::leanh::lean_alloc_closure(
        l_Lake_recFetchMemoize___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_315_, 0, v_inst_309_);
    crate::leanh::lean_closure_set(v___f_315_, 1, v_inst_311_);
    crate::leanh::lean_closure_set(v___f_315_, 2, v_keyOf_312_);
    crate::leanh::lean_closure_set(v___f_315_, 3, v_compute_313_);
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
    mut v_00_u03ba_317_: *mut crate::leanh::LeanObject,
    mut v_m_318_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_319_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_320_: *mut crate::leanh::LeanObject,
    mut v_inst_321_: *mut crate::leanh::LeanObject,
    mut v_inst_322_: *mut crate::leanh::LeanObject,
    mut v_inst_323_: *mut crate::leanh::LeanObject,
    mut v_inst_324_: *mut crate::leanh::LeanObject,
    mut v_keyOf_325_: *mut crate::leanh::LeanObject,
    mut v_compute_326_: *mut crate::leanh::LeanObject,
    mut v_a_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
pub unsafe fn runtime_initialize_Lake_Build_Topological(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Cycle(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EquipT(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Topological(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Topological(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Cycle(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_EquipT(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Topological(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Topological(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Topological(builtin);
}
