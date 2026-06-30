// Lean compiler output
// Module: Lean.Data.SSet
// Imports: Lean.Data.SMap
use crate::ffi::lean_mk_array;
use crate::r#gen::Init::Data::Repr::{l_List_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::l_List_foldl___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::SMap::{
    initialize_Lean_Data_SMap, l_Lean_SMap_contains___redArg, l_Lean_SMap_empty,
    l_Lean_SMap_fold___redArg, l_Lean_SMap_forM___redArg, l_Lean_SMap_insert___redArg,
    l_Lean_SMap_switch___redArg, runtime_initialize_Lean_Data_SMap,
};
static mut l_Lean_SSet_instInhabited___aux__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SSet_instInhabited___aux__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SSet_instInhabited___aux__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SSet_instInhabited___aux__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SSet_instInhabited___aux__1___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SSet_instInhabited___aux__1___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SSet_instInhabited___aux__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SSet_instInhabited___aux__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SSet_instInhabited___aux__1___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SSet_instInhabited___aux__1___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SSet_toList___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_SSet_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SSet_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SSet_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instReprSSet___redArg___lam__0___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [46, 116, 111, 83, 83, 101, 116, 0],
    };
static mut l_instReprSSet___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSSet___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instReprSSet___redArg___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprSSet___redArg___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprSSet___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSSet___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_SSet_instInhabited___aux__1___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_209_ = leanh::lean_box(0);
    v___x_210_ = leanh::lean_unsigned_to_nat(16);
    v___x_211_ = lean_mk_array(v___x_210_, v___x_209_);
    return v___x_211_;
}
pub unsafe fn _init_l_Lean_SSet_instInhabited___aux__1___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_212_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__0_once),
        _init_l_Lean_SSet_instInhabited___aux__1___closed__0,
    );
    v___x_213_ = leanh::lean_unsigned_to_nat(0);
    v___x_214_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_214_, 0, v___x_213_);
    leanh::lean_ctor_set(v___x_214_, 1, v___x_212_);
    return v___x_214_;
}
pub unsafe fn _init_l_Lean_SSet_instInhabited___aux__1___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_215_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_215_;
}
pub unsafe fn _init_l_Lean_SSet_instInhabited___aux__1___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_216_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__2_once),
        _init_l_Lean_SSet_instInhabited___aux__1___closed__2,
    );
    v___x_217_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_217_, 0, v___x_216_);
    return v___x_217_;
}
pub unsafe fn _init_l_Lean_SSet_instInhabited___aux__1___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: u8 = 0;
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_218_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__3_once),
        _init_l_Lean_SSet_instInhabited___aux__1___closed__3,
    );
    v___x_219_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__1_once),
        _init_l_Lean_SSet_instInhabited___aux__1___closed__1,
    );
    v___x_220_ = 1;
    v___x_221_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_221_, 0, v___x_219_);
    leanh::lean_ctor_set(v___x_221_, 1, v___x_218_);
    leanh::lean_ctor_set_uint8(
        v___x_221_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_220_,
    );
    return v___x_221_;
}
pub unsafe fn l_Lean_SSet_instInhabited___aux__1(
    mut v_00_u03b1_222_: *mut leanh::LeanObject,
    mut v_inst_223_: *mut leanh::LeanObject,
    mut v_inst_224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_225_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__4_once),
        _init_l_Lean_SSet_instInhabited___aux__1___closed__4,
    );
    return v___x_225_;
}
pub unsafe fn l_Lean_SSet_instInhabited___aux__1___boxed(
    mut v_00_u03b1_226_: *mut leanh::LeanObject,
    mut v_inst_227_: *mut leanh::LeanObject,
    mut v_inst_228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l_Lean_SSet_instInhabited___aux__1(v_00_u03b1_226_, v_inst_227_, v_inst_228_);
    leanh::lean_dec_ref(v_inst_228_);
    leanh::lean_dec_ref(v_inst_227_);
    return v_res_229_;
}
pub unsafe fn l_Lean_SSet_instInhabited(
    mut v_00_u03b1_230_: *mut leanh::LeanObject,
    mut v_inst_231_: *mut leanh::LeanObject,
    mut v_inst_232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_233_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__4_once),
        _init_l_Lean_SSet_instInhabited___aux__1___closed__4,
    );
    return v___x_233_;
}
pub unsafe fn l_Lean_SSet_instInhabited___boxed(
    mut v_00_u03b1_234_: *mut leanh::LeanObject,
    mut v_inst_235_: *mut leanh::LeanObject,
    mut v_inst_236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_237_ = l_Lean_SSet_instInhabited(v_00_u03b1_234_, v_inst_235_, v_inst_236_);
    leanh::lean_dec_ref(v_inst_236_);
    leanh::lean_dec_ref(v_inst_235_);
    return v_res_237_;
}
pub unsafe fn l_Lean_SSet_empty___redArg(
    mut v_inst_238_: *mut leanh::LeanObject,
    mut v_inst_239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_240_ = l_Lean_SMap_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_238_,
        v_inst_239_,
    );
    return v___x_240_;
}
pub unsafe fn l_Lean_SSet_empty___redArg___boxed(
    mut v_inst_241_: *mut leanh::LeanObject,
    mut v_inst_242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_243_ = l_Lean_SSet_empty___redArg(v_inst_241_, v_inst_242_);
    leanh::lean_dec_ref(v_inst_242_);
    leanh::lean_dec_ref(v_inst_241_);
    return v_res_243_;
}
pub unsafe fn l_Lean_SSet_empty(
    mut v_00_u03b1_244_: *mut leanh::LeanObject,
    mut v_inst_245_: *mut leanh::LeanObject,
    mut v_inst_246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = l_Lean_SMap_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_245_,
        v_inst_246_,
    );
    return v___x_247_;
}
pub unsafe fn l_Lean_SSet_empty___boxed(
    mut v_00_u03b1_248_: *mut leanh::LeanObject,
    mut v_inst_249_: *mut leanh::LeanObject,
    mut v_inst_250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_251_ = l_Lean_SSet_empty(v_00_u03b1_248_, v_inst_249_, v_inst_250_);
    leanh::lean_dec_ref(v_inst_250_);
    leanh::lean_dec_ref(v_inst_249_);
    return v_res_251_;
}
pub unsafe fn l_Lean_SSet_insert___redArg(
    mut v_inst_252_: *mut leanh::LeanObject,
    mut v_inst_253_: *mut leanh::LeanObject,
    mut v_s_254_: *mut leanh::LeanObject,
    mut v_a_255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_256_ = leanh::lean_box(0);
    v___x_257_ =
        l_Lean_SMap_insert___redArg(v_inst_252_, v_inst_253_, v_s_254_, v_a_255_, v___x_256_);
    return v___x_257_;
}
pub unsafe fn l_Lean_SSet_insert(
    mut v_00_u03b1_258_: *mut leanh::LeanObject,
    mut v_inst_259_: *mut leanh::LeanObject,
    mut v_inst_260_: *mut leanh::LeanObject,
    mut v_s_261_: *mut leanh::LeanObject,
    mut v_a_262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_263_ = leanh::lean_box(0);
    v___x_264_ =
        l_Lean_SMap_insert___redArg(v_inst_259_, v_inst_260_, v_s_261_, v_a_262_, v___x_263_);
    return v___x_264_;
}
pub unsafe fn l_Lean_SSet_contains___redArg(
    mut v_inst_265_: *mut leanh::LeanObject,
    mut v_inst_266_: *mut leanh::LeanObject,
    mut v_s_267_: *mut leanh::LeanObject,
    mut v_a_268_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_269_: u8 = 0;
    v___x_269_ = l_Lean_SMap_contains___redArg(v_inst_265_, v_inst_266_, v_s_267_, v_a_268_);
    return v___x_269_;
}
pub unsafe fn l_Lean_SSet_contains___redArg___boxed(
    mut v_inst_270_: *mut leanh::LeanObject,
    mut v_inst_271_: *mut leanh::LeanObject,
    mut v_s_272_: *mut leanh::LeanObject,
    mut v_a_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_274_: u8 = 0;
    let mut v_r_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_274_ = l_Lean_SSet_contains___redArg(v_inst_270_, v_inst_271_, v_s_272_, v_a_273_);
    v_r_275_ = leanh::lean_box((v_res_274_) as usize);
    return v_r_275_;
}
pub unsafe fn l_Lean_SSet_contains(
    mut v_00_u03b1_276_: *mut leanh::LeanObject,
    mut v_inst_277_: *mut leanh::LeanObject,
    mut v_inst_278_: *mut leanh::LeanObject,
    mut v_s_279_: *mut leanh::LeanObject,
    mut v_a_280_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_281_: u8 = 0;
    v___x_281_ = l_Lean_SMap_contains___redArg(v_inst_277_, v_inst_278_, v_s_279_, v_a_280_);
    return v___x_281_;
}
pub unsafe fn l_Lean_SSet_contains___boxed(
    mut v_00_u03b1_282_: *mut leanh::LeanObject,
    mut v_inst_283_: *mut leanh::LeanObject,
    mut v_inst_284_: *mut leanh::LeanObject,
    mut v_s_285_: *mut leanh::LeanObject,
    mut v_a_286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_287_: u8 = 0;
    let mut v_r_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_287_ = l_Lean_SSet_contains(
        v_00_u03b1_282_,
        v_inst_283_,
        v_inst_284_,
        v_s_285_,
        v_a_286_,
    );
    v_r_288_ = leanh::lean_box((v_res_287_) as usize);
    return v_r_288_;
}
pub unsafe fn l_Lean_SSet_forM___redArg___lam__0(
    mut v_f_289_: *mut leanh::LeanObject,
    mut v_a_290_: *mut leanh::LeanObject,
    mut v_x_291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = leanh::lean_apply_1(v_f_289_, v_a_290_);
    return v___x_292_;
}
pub unsafe fn l_Lean_SSet_forM___redArg(
    mut v_inst_293_: *mut leanh::LeanObject,
    mut v_s_294_: *mut leanh::LeanObject,
    mut v_f_295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_296_ = leanh::lean_alloc_closure(
        l_Lean_SSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_296_, 0, v_f_295_);
    v___x_297_ = l_Lean_SMap_forM___redArg(v_inst_293_, v_s_294_, v___f_296_);
    return v___x_297_;
}
pub unsafe fn l_Lean_SSet_forM(
    mut v_00_u03b1_298_: *mut leanh::LeanObject,
    mut v_inst_299_: *mut leanh::LeanObject,
    mut v_inst_300_: *mut leanh::LeanObject,
    mut v_m_301_: *mut leanh::LeanObject,
    mut v_inst_302_: *mut leanh::LeanObject,
    mut v_s_303_: *mut leanh::LeanObject,
    mut v_f_304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_305_ = leanh::lean_alloc_closure(
        l_Lean_SSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_305_, 0, v_f_304_);
    v___x_306_ = l_Lean_SMap_forM___redArg(v_inst_302_, v_s_303_, v___f_305_);
    return v___x_306_;
}
pub unsafe fn l_Lean_SSet_forM___boxed(
    mut v_00_u03b1_307_: *mut leanh::LeanObject,
    mut v_inst_308_: *mut leanh::LeanObject,
    mut v_inst_309_: *mut leanh::LeanObject,
    mut v_m_310_: *mut leanh::LeanObject,
    mut v_inst_311_: *mut leanh::LeanObject,
    mut v_s_312_: *mut leanh::LeanObject,
    mut v_f_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_314_ = l_Lean_SSet_forM(
        v_00_u03b1_307_,
        v_inst_308_,
        v_inst_309_,
        v_m_310_,
        v_inst_311_,
        v_s_312_,
        v_f_313_,
    );
    leanh::lean_dec_ref(v_inst_309_);
    leanh::lean_dec_ref(v_inst_308_);
    return v_res_314_;
}
pub unsafe fn l_Lean_SSet_switch___redArg(
    mut v_s_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_316_ = l_Lean_SMap_switch___redArg(v_s_315_);
    return v___x_316_;
}
pub unsafe fn l_Lean_SSet_switch(
    mut v_00_u03b1_317_: *mut leanh::LeanObject,
    mut v_inst_318_: *mut leanh::LeanObject,
    mut v_inst_319_: *mut leanh::LeanObject,
    mut v_s_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_321_ = l_Lean_SMap_switch___redArg(v_s_320_);
    return v___x_321_;
}
pub unsafe fn l_Lean_SSet_switch___boxed(
    mut v_00_u03b1_322_: *mut leanh::LeanObject,
    mut v_inst_323_: *mut leanh::LeanObject,
    mut v_inst_324_: *mut leanh::LeanObject,
    mut v_s_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Lean_SSet_switch(v_00_u03b1_322_, v_inst_323_, v_inst_324_, v_s_325_);
    leanh::lean_dec_ref(v_inst_324_);
    leanh::lean_dec_ref(v_inst_323_);
    return v_res_326_;
}
pub unsafe fn l_Lean_SSet_fold___redArg___lam__0(
    mut v_f_327_: *mut leanh::LeanObject,
    mut v_d_328_: *mut leanh::LeanObject,
    mut v_a_329_: *mut leanh::LeanObject,
    mut v_x_330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_331_ = leanh::lean_apply_2(v_f_327_, v_d_328_, v_a_329_);
    return v___x_331_;
}
pub unsafe fn l_Lean_SSet_fold___redArg(
    mut v_f_332_: *mut leanh::LeanObject,
    mut v_init_333_: *mut leanh::LeanObject,
    mut v_s_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_335_ = leanh::lean_alloc_closure(
        l_Lean_SSet_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_335_, 0, v_f_332_);
    v___x_336_ = l_Lean_SMap_fold___redArg(v___f_335_, v_init_333_, v_s_334_);
    return v___x_336_;
}
pub unsafe fn l_Lean_SSet_fold(
    mut v_00_u03b1_337_: *mut leanh::LeanObject,
    mut v_inst_338_: *mut leanh::LeanObject,
    mut v_inst_339_: *mut leanh::LeanObject,
    mut v_00_u03c3_340_: *mut leanh::LeanObject,
    mut v_f_341_: *mut leanh::LeanObject,
    mut v_init_342_: *mut leanh::LeanObject,
    mut v_s_343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_344_ = leanh::lean_alloc_closure(
        l_Lean_SSet_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_344_, 0, v_f_341_);
    v___x_345_ = l_Lean_SMap_fold___redArg(v___f_344_, v_init_342_, v_s_343_);
    return v___x_345_;
}
pub unsafe fn l_Lean_SSet_fold___boxed(
    mut v_00_u03b1_346_: *mut leanh::LeanObject,
    mut v_inst_347_: *mut leanh::LeanObject,
    mut v_inst_348_: *mut leanh::LeanObject,
    mut v_00_u03c3_349_: *mut leanh::LeanObject,
    mut v_f_350_: *mut leanh::LeanObject,
    mut v_init_351_: *mut leanh::LeanObject,
    mut v_s_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_353_ = l_Lean_SSet_fold(
        v_00_u03b1_346_,
        v_inst_347_,
        v_inst_348_,
        v_00_u03c3_349_,
        v_f_350_,
        v_init_351_,
        v_s_352_,
    );
    leanh::lean_dec_ref(v_inst_348_);
    leanh::lean_dec_ref(v_inst_347_);
    return v_res_353_;
}
pub unsafe fn l_Lean_SSet_toList___redArg___lam__0(
    mut v_d_354_: *mut leanh::LeanObject,
    mut v_a_355_: *mut leanh::LeanObject,
    mut v_x_356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_357_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_357_, 0, v_a_355_);
    leanh::lean_ctor_set(v___x_357_, 1, v_d_354_);
    return v___x_357_;
}
pub unsafe fn l_Lean_SSet_toList___redArg(
    mut v_m_359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_360_ = l_Lean_SSet_toList___redArg___closed__0;
    v___x_361_ = leanh::lean_box(0);
    v___x_362_ = l_Lean_SMap_fold___redArg(v___f_360_, v___x_361_, v_m_359_);
    return v___x_362_;
}
pub unsafe fn l_Lean_SSet_toList(
    mut v_00_u03b1_363_: *mut leanh::LeanObject,
    mut v_inst_364_: *mut leanh::LeanObject,
    mut v_inst_365_: *mut leanh::LeanObject,
    mut v_m_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_367_ = l_Lean_SSet_toList___redArg(v_m_366_);
    return v___x_367_;
}
pub unsafe fn l_Lean_SSet_toList___boxed(
    mut v_00_u03b1_368_: *mut leanh::LeanObject,
    mut v_inst_369_: *mut leanh::LeanObject,
    mut v_inst_370_: *mut leanh::LeanObject,
    mut v_m_371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_372_ = l_Lean_SSet_toList(v_00_u03b1_368_, v_inst_369_, v_inst_370_, v_m_371_);
    leanh::lean_dec_ref(v_inst_370_);
    leanh::lean_dec_ref(v_inst_369_);
    return v_res_372_;
}
pub unsafe fn l_List_toSSet___redArg___lam__0(
    mut v_inst_373_: *mut leanh::LeanObject,
    mut v_inst_374_: *mut leanh::LeanObject,
    mut v_s_375_: *mut leanh::LeanObject,
    mut v_a_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = leanh::lean_box(0);
    v___x_378_ =
        l_Lean_SMap_insert___redArg(v_inst_373_, v_inst_374_, v_s_375_, v_a_376_, v___x_377_);
    return v___x_378_;
}
pub unsafe fn l_List_toSSet___redArg(
    mut v_inst_379_: *mut leanh::LeanObject,
    mut v_inst_380_: *mut leanh::LeanObject,
    mut v_es_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_382_ = leanh::lean_alloc_closure(
        l_List_toSSet___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_382_, 0, v_inst_379_);
    leanh::lean_closure_set(v___f_382_, 1, v_inst_380_);
    v___x_383_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Lean_SSet_instInhabited___aux__1___closed__4_once),
        _init_l_Lean_SSet_instInhabited___aux__1___closed__4,
    );
    v___x_384_ = l_List_foldl___redArg(v___f_382_, v___x_383_, v_es_381_);
    return v___x_384_;
}
pub unsafe fn l_List_toSSet(
    mut v_00_u03b1_385_: *mut leanh::LeanObject,
    mut v_inst_386_: *mut leanh::LeanObject,
    mut v_inst_387_: *mut leanh::LeanObject,
    mut v_es_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_389_ = l_List_toSSet___redArg(v_inst_386_, v_inst_387_, v_es_388_);
    return v___x_389_;
}
pub unsafe fn l_instReprSSet___redArg___lam__0(
    mut v_inst_393_: *mut leanh::LeanObject,
    mut v_v_394_: *mut leanh::LeanObject,
    mut v_prec_395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_396_ = l_Lean_SSet_toList___redArg(v_v_394_);
    v___x_397_ = l_List_repr___redArg(v_inst_393_, v___x_396_);
    v___x_398_ = l_instReprSSet___redArg___lam__0___closed__1;
    v___x_399_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_399_, 0, v___x_397_);
    leanh::lean_ctor_set(v___x_399_, 1, v___x_398_);
    v___x_400_ = l_Repr_addAppParen(v___x_399_, v_prec_395_);
    return v___x_400_;
}
pub unsafe fn l_instReprSSet___redArg___lam__0___boxed(
    mut v_inst_401_: *mut leanh::LeanObject,
    mut v_v_402_: *mut leanh::LeanObject,
    mut v_prec_403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_404_ = l_instReprSSet___redArg___lam__0(v_inst_401_, v_v_402_, v_prec_403_);
    leanh::lean_dec(v_prec_403_);
    return v_res_404_;
}
pub unsafe fn l_instReprSSet___redArg(
    mut v_inst_405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_406_ = leanh::lean_alloc_closure(
        l_instReprSSet___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_406_, 0, v_inst_405_);
    return v___f_406_;
}
pub unsafe fn l_instReprSSet(
    mut v_00_u03b1_407_: *mut leanh::LeanObject,
    mut v_x_408_: *mut leanh::LeanObject,
    mut v_x_409_: *mut leanh::LeanObject,
    mut v_inst_410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_411_ = leanh::lean_alloc_closure(
        l_instReprSSet___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_411_, 0, v_inst_410_);
    return v___f_411_;
}
pub unsafe fn l_instReprSSet___boxed(
    mut v_00_u03b1_412_: *mut leanh::LeanObject,
    mut v_x_413_: *mut leanh::LeanObject,
    mut v_x_414_: *mut leanh::LeanObject,
    mut v_inst_415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_416_ = l_instReprSSet(v_00_u03b1_412_, v_x_413_, v_x_414_, v_inst_415_);
    leanh::lean_dec_ref(v_x_414_);
    leanh::lean_dec_ref(v_x_413_);
    return v_res_416_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_SSet(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_SMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_SSet(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_SSet(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_SMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_SSet(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_SSet(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_SSet(builtin);
}