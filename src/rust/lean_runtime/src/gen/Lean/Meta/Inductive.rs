// Lean compiler output
// Module: Lean.Meta.Inductive
// Imports: Lean.Meta.Basic
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_findAsync_x3f,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofConstName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_forallMetaTelescope,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_isExprDefEq, runtime_initialize_Lean_Meta_Basic,
};
use crate::lean_imports_rs::Init::Prelude::{lean_name_eq, lean_panic_fn_borrowed};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__2_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
        111, 114, 0,
    ],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__4_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__5_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__6_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0_spec__1(
    mut v_msgData_292_: *mut crate::leanh::LeanObject,
    mut v___y_293_: *mut crate::leanh::LeanObject,
    mut v___y_294_: *mut crate::leanh::LeanObject,
    mut v___y_295_: *mut crate::leanh::LeanObject,
    mut v___y_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = lean_st_ref_get(v___y_296_);
    v_env_299_ = crate::leanh::lean_ctor_get(v___x_298_, 0);
    crate::leanh::lean_inc_ref(v_env_299_);
    crate::leanh::lean_dec(v___x_298_);
    v___x_300_ = lean_st_ref_get(v___y_294_);
    v_mctx_301_ = crate::leanh::lean_ctor_get(v___x_300_, 0);
    crate::leanh::lean_inc_ref(v_mctx_301_);
    crate::leanh::lean_dec(v___x_300_);
    v_lctx_302_ = crate::leanh::lean_ctor_get(v___y_293_, 2);
    v_options_303_ = crate::leanh::lean_ctor_get(v___y_295_, 2);
    crate::leanh::lean_inc_ref(v_options_303_);
    crate::leanh::lean_inc_ref(v_lctx_302_);
    v___x_304_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_304_, 0, v_env_299_);
    crate::leanh::lean_ctor_set(v___x_304_, 1, v_mctx_301_);
    crate::leanh::lean_ctor_set(v___x_304_, 2, v_lctx_302_);
    crate::leanh::lean_ctor_set(v___x_304_, 3, v_options_303_);
    v___x_305_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_305_, 0, v___x_304_);
    crate::leanh::lean_ctor_set(v___x_305_, 1, v_msgData_292_);
    v___x_306_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_306_, 0, v___x_305_);
    return v___x_306_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_307_: *mut crate::leanh::LeanObject,
    mut v___y_308_: *mut crate::leanh::LeanObject,
    mut v___y_309_: *mut crate::leanh::LeanObject,
    mut v___y_310_: *mut crate::leanh::LeanObject,
    mut v___y_311_: *mut crate::leanh::LeanObject,
    mut v___y_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_313_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0_spec__1(v_msgData_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
    crate::leanh::lean_dec(v___y_311_);
    crate::leanh::lean_dec_ref(v___y_310_);
    crate::leanh::lean_dec(v___y_309_);
    crate::leanh::lean_dec_ref(v___y_308_);
    return v_res_313_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg(
    mut v_msg_314_: *mut crate::leanh::LeanObject,
    mut v___y_315_: *mut crate::leanh::LeanObject,
    mut v___y_316_: *mut crate::leanh::LeanObject,
    mut v___y_317_: *mut crate::leanh::LeanObject,
    mut v___y_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_325_: u8 = 0;
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_320_ = crate::leanh::lean_ctor_get(v___y_317_, 5);
                v___x_321_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0_spec__1(v_msg_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
                v_a_322_ = crate::leanh::lean_ctor_get(v___x_321_, 0);
                v_isSharedCheck_330_ = (!crate::leanh::lean_is_exclusive(v___x_321_)) as u8;
                if v_isSharedCheck_330_ == 0 {
                    v___x_324_ = v___x_321_;
                    v_isShared_325_ = v_isSharedCheck_330_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_322_);
                    crate::leanh::lean_dec(v___x_321_);
                    v___x_324_ = crate::leanh::lean_box(0);
                    v_isShared_325_ = v_isSharedCheck_330_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_320_);
                v___x_326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_326_, 0, v_ref_320_);
                crate::leanh::lean_ctor_set(v___x_326_, 1, v_a_322_);
                if v_isShared_325_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_324_, 1);
                    crate::leanh::lean_ctor_set(v___x_324_, 0, v___x_326_);
                    v___x_328_ = v___x_324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
                    v___x_328_ = v_reuseFailAlloc_329_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg___boxed(
    mut v_msg_331_: *mut crate::leanh::LeanObject,
    mut v___y_332_: *mut crate::leanh::LeanObject,
    mut v___y_333_: *mut crate::leanh::LeanObject,
    mut v___y_334_: *mut crate::leanh::LeanObject,
    mut v___y_335_: *mut crate::leanh::LeanObject,
    mut v___y_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_337_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg(v_msg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
    crate::leanh::lean_dec(v___y_335_);
    crate::leanh::lean_dec_ref(v___y_334_);
    crate::leanh::lean_dec(v___y_333_);
    crate::leanh::lean_dec_ref(v___y_332_);
    return v_res_337_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_338_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1(
    mut v_msg_343_: *mut crate::leanh::LeanObject,
    mut v___y_344_: *mut crate::leanh::LeanObject,
    mut v___y_345_: *mut crate::leanh::LeanObject,
    mut v___y_346_: *mut crate::leanh::LeanObject,
    mut v___y_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_354_: u8 = 0;
    let mut v_toFunctor_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_361_: u8 = 0;
    let mut v___f_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_378_: u8 = 0;
    let mut v_toFunctor_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_385_: u8 = 0;
    let mut v___f_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849__overap_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_404_: u8 = 0;
    let mut v_unused_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_406_: u8 = 0;
    let mut v_unused_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_410_: u8 = 0;
    let mut v_unused_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_412_: u8 = 0;
    let mut v_unused_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_349_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0);
                v___x_350_ = l_StateRefT_x27_instMonad___redArg(v___x_349_);
                v_toApplicative_351_ = crate::leanh::lean_ctor_get(v___x_350_, 0);
                v_isSharedCheck_412_ = (!crate::leanh::lean_is_exclusive(v___x_350_)) as u8;
                if v_isSharedCheck_412_ == 0 {
                    v_unused_413_ = crate::leanh::lean_ctor_get(v___x_350_, 1);
                    crate::leanh::lean_dec(v_unused_413_);
                    v___x_353_ = v___x_350_;
                    v_isShared_354_ = v_isSharedCheck_412_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_351_);
                    crate::leanh::lean_dec(v___x_350_);
                    v___x_353_ = crate::leanh::lean_box(0);
                    v_isShared_354_ = v_isSharedCheck_412_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_355_ = crate::leanh::lean_ctor_get(v_toApplicative_351_, 0);
                v_toSeq_356_ = crate::leanh::lean_ctor_get(v_toApplicative_351_, 2);
                v_toSeqLeft_357_ = crate::leanh::lean_ctor_get(v_toApplicative_351_, 3);
                v_toSeqRight_358_ = crate::leanh::lean_ctor_get(v_toApplicative_351_, 4);
                v_isSharedCheck_410_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_351_)) as u8;
                if v_isSharedCheck_410_ == 0 {
                    v_unused_411_ = crate::leanh::lean_ctor_get(v_toApplicative_351_, 1);
                    crate::leanh::lean_dec(v_unused_411_);
                    v___x_360_ = v_toApplicative_351_;
                    v_isShared_361_ = v_isSharedCheck_410_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_358_);
                    crate::leanh::lean_inc(v_toSeqLeft_357_);
                    crate::leanh::lean_inc(v_toSeq_356_);
                    crate::leanh::lean_inc(v_toFunctor_355_);
                    crate::leanh::lean_dec(v_toApplicative_351_);
                    v___x_360_ = crate::leanh::lean_box(0);
                    v_isShared_361_ = v_isSharedCheck_410_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_362_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__1;
                v___f_363_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_355_);
                v___f_364_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_364_, 0, v_toFunctor_355_);
                v___f_365_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_365_, 0, v_toFunctor_355_);
                v___x_366_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_366_, 0, v___f_364_);
                crate::leanh::lean_ctor_set(v___x_366_, 1, v___f_365_);
                v___f_367_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_367_, 0, v_toSeqRight_358_);
                v___f_368_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_368_, 0, v_toSeqLeft_357_);
                v___f_369_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_369_, 0, v_toSeq_356_);
                if v_isShared_361_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_360_, 4, v___f_367_);
                    crate::leanh::lean_ctor_set(v___x_360_, 3, v___f_368_);
                    crate::leanh::lean_ctor_set(v___x_360_, 2, v___f_369_);
                    crate::leanh::lean_ctor_set(v___x_360_, 1, v___f_362_);
                    crate::leanh::lean_ctor_set(v___x_360_, 0, v___x_366_);
                    v___x_371_ = v___x_360_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_409_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_409_, 1, v___f_362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_409_, 2, v___f_369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_409_, 3, v___f_368_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_409_, 4, v___f_367_);
                    v___x_371_ = v_reuseFailAlloc_409_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_354_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_353_, 1, v___f_363_);
                    crate::leanh::lean_ctor_set(v___x_353_, 0, v___x_371_);
                    v___x_373_ = v___x_353_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_408_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_408_, 1, v___f_363_);
                    v___x_373_ = v_reuseFailAlloc_408_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_374_ = l_StateRefT_x27_instMonad___redArg(v___x_373_);
                v_toApplicative_375_ = crate::leanh::lean_ctor_get(v___x_374_, 0);
                v_isSharedCheck_406_ = (!crate::leanh::lean_is_exclusive(v___x_374_)) as u8;
                if v_isSharedCheck_406_ == 0 {
                    v_unused_407_ = crate::leanh::lean_ctor_get(v___x_374_, 1);
                    crate::leanh::lean_dec(v_unused_407_);
                    v___x_377_ = v___x_374_;
                    v_isShared_378_ = v_isSharedCheck_406_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_375_);
                    crate::leanh::lean_dec(v___x_374_);
                    v___x_377_ = crate::leanh::lean_box(0);
                    v_isShared_378_ = v_isSharedCheck_406_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_379_ = crate::leanh::lean_ctor_get(v_toApplicative_375_, 0);
                v_toSeq_380_ = crate::leanh::lean_ctor_get(v_toApplicative_375_, 2);
                v_toSeqLeft_381_ = crate::leanh::lean_ctor_get(v_toApplicative_375_, 3);
                v_toSeqRight_382_ = crate::leanh::lean_ctor_get(v_toApplicative_375_, 4);
                v_isSharedCheck_404_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_375_)) as u8;
                if v_isSharedCheck_404_ == 0 {
                    v_unused_405_ = crate::leanh::lean_ctor_get(v_toApplicative_375_, 1);
                    crate::leanh::lean_dec(v_unused_405_);
                    v___x_384_ = v_toApplicative_375_;
                    v_isShared_385_ = v_isSharedCheck_404_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_382_);
                    crate::leanh::lean_inc(v_toSeqLeft_381_);
                    crate::leanh::lean_inc(v_toSeq_380_);
                    crate::leanh::lean_inc(v_toFunctor_379_);
                    crate::leanh::lean_dec(v_toApplicative_375_);
                    v___x_384_ = crate::leanh::lean_box(0);
                    v_isShared_385_ = v_isSharedCheck_404_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_386_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__3;
                v___f_387_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_379_);
                v___f_388_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_388_, 0, v_toFunctor_379_);
                v___f_389_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_389_, 0, v_toFunctor_379_);
                v___x_390_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_390_, 0, v___f_388_);
                crate::leanh::lean_ctor_set(v___x_390_, 1, v___f_389_);
                v___f_391_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_391_, 0, v_toSeqRight_382_);
                v___f_392_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_392_, 0, v_toSeqLeft_381_);
                v___f_393_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_393_, 0, v_toSeq_380_);
                if v_isShared_385_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_384_, 4, v___f_391_);
                    crate::leanh::lean_ctor_set(v___x_384_, 3, v___f_392_);
                    crate::leanh::lean_ctor_set(v___x_384_, 2, v___f_393_);
                    crate::leanh::lean_ctor_set(v___x_384_, 1, v___f_386_);
                    crate::leanh::lean_ctor_set(v___x_384_, 0, v___x_390_);
                    v___x_395_ = v___x_384_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_403_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_390_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_403_, 1, v___f_386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_403_, 2, v___f_393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_403_, 3, v___f_392_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_403_, 4, v___f_391_);
                    v___x_395_ = v_reuseFailAlloc_403_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_378_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_377_, 1, v___f_387_);
                    crate::leanh::lean_ctor_set(v___x_377_, 0, v___x_395_);
                    v___x_397_ = v___x_377_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_402_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_402_, 1, v___f_387_);
                    v___x_397_ = v_reuseFailAlloc_402_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_398_ = crate::leanh::lean_box(0);
                v___x_399_ = l_instInhabitedOfMonad___redArg(v___x_397_, v___x_398_);
                v___x_1849__overap_400_ = lean_panic_fn_borrowed(v___x_399_, v_msg_343_);
                crate::leanh::lean_dec(v___x_399_);
                crate::leanh::lean_inc(v___y_347_);
                crate::leanh::lean_inc_ref(v___y_346_);
                crate::leanh::lean_inc(v___y_345_);
                crate::leanh::lean_inc_ref(v___y_344_);
                v___x_401_ = crate::leanh::lean_apply_5(
                    v___x_1849__overap_400_,
                    v___y_344_,
                    v___y_345_,
                    v___y_346_,
                    v___y_347_,
                    crate::leanh::lean_box(0),
                );
                return v___x_401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___boxed(
    mut v_msg_414_: *mut crate::leanh::LeanObject,
    mut v___y_415_: *mut crate::leanh::LeanObject,
    mut v___y_416_: *mut crate::leanh::LeanObject,
    mut v___y_417_: *mut crate::leanh::LeanObject,
    mut v___y_418_: *mut crate::leanh::LeanObject,
    mut v___y_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_420_ =
        l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1(
            v_msg_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_,
        );
    crate::leanh::lean_dec(v___y_418_);
    crate::leanh::lean_dec_ref(v___y_417_);
    crate::leanh::lean_dec(v___y_416_);
    crate::leanh::lean_dec_ref(v___y_415_);
    return v_res_420_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_422_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__0;
    v___x_423_ = l_Lean_stringToMessageData(v___x_422_);
    return v___x_423_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_425_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__2;
    v___x_426_ = l_Lean_stringToMessageData(v___x_425_);
    return v___x_426_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__6;
    v___x_431_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_432_ = crate::leanh::lean_unsigned_to_nat(122);
    v___x_433_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__5;
    v___x_434_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__4;
    v___x_435_ =
        l_mkPanicMessageWithDecl(v___x_434_, v___x_433_, v___x_432_, v___x_431_, v___x_430_);
    return v___x_435_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0(
    mut v_constName_436_: *mut crate::leanh::LeanObject,
    mut v___y_437_: *mut crate::leanh::LeanObject,
    mut v___y_438_: *mut crate::leanh::LeanObject,
    mut v___y_439_: *mut crate::leanh::LeanObject,
    mut v___y_440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: u8 = 0;
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: u8 = 0;
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_455_: u8 = 0;
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_460_: u8 = 0;
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_464_: u8 = 0;
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_470_: u8 = 0;
    let mut v_val_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_475_: u8 = 0;
    let mut v_a_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_479_: u8 = 0;
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_450_ = lean_st_ref_get(v___y_440_);
                v_env_451_ = crate::leanh::lean_ctor_get(v___x_450_, 0);
                crate::leanh::lean_inc_ref(v_env_451_);
                crate::leanh::lean_dec(v___x_450_);
                v___x_452_ = 0;
                crate::leanh::lean_inc(v_constName_436_);
                v___x_453_ =
                    l_Lean_Environment_findAsync_x3f(v_env_451_, v_constName_436_, v___x_452_);
                if crate::leanh::lean_obj_tag(v___x_453_) == 1 {
                    v_val_454_ = crate::leanh::lean_ctor_get(v___x_453_, 0);
                    crate::leanh::lean_inc(v_val_454_);
                    crate::leanh::lean_dec_ref_known(v___x_453_, 1);
                    v_kind_455_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_454_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_455_ == 6 {
                        v___x_456_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_454_);
                        if crate::leanh::lean_obj_tag(v___x_456_) == 6 {
                            crate::leanh::lean_dec(v_constName_436_);
                            v_val_457_ = crate::leanh::lean_ctor_get(v___x_456_, 0);
                            v_isSharedCheck_464_ =
                                (!crate::leanh::lean_is_exclusive(v___x_456_)) as u8;
                            if v_isSharedCheck_464_ == 0 {
                                v___x_459_ = v___x_456_;
                                v_isShared_460_ = v_isSharedCheck_464_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_457_);
                                crate::leanh::lean_dec(v___x_456_);
                                v___x_459_ = crate::leanh::lean_box(0);
                                v_isShared_460_ = v_isSharedCheck_464_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_456_);
                            v___x_465_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7);
                            v___x_466_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1(v___x_465_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
                            if crate::leanh::lean_obj_tag(v___x_466_) == 0 {
                                v_a_467_ = crate::leanh::lean_ctor_get(v___x_466_, 0);
                                v_isSharedCheck_475_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_466_)) as u8;
                                if v_isSharedCheck_475_ == 0 {
                                    v___x_469_ = v___x_466_;
                                    v_isShared_470_ = v_isSharedCheck_475_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_467_);
                                    crate::leanh::lean_dec(v___x_466_);
                                    v___x_469_ = crate::leanh::lean_box(0);
                                    v_isShared_470_ = v_isSharedCheck_475_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_436_);
                                v_a_476_ = crate::leanh::lean_ctor_get(v___x_466_, 0);
                                v_isSharedCheck_483_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_466_)) as u8;
                                if v_isSharedCheck_483_ == 0 {
                                    v___x_478_ = v___x_466_;
                                    v_isShared_479_ = v_isSharedCheck_483_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_476_);
                                    crate::leanh::lean_dec(v___x_466_);
                                    v___x_478_ = crate::leanh::lean_box(0);
                                    v_isShared_479_ = v_isSharedCheck_483_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_454_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_453_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_443_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1);
                v___x_444_ = 0;
                v___x_445_ = l_Lean_MessageData_ofConstName(v_constName_436_, v___x_444_);
                v___x_446_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_446_, 0, v___x_443_);
                crate::leanh::lean_ctor_set(v___x_446_, 1, v___x_445_);
                v___x_447_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3);
                v___x_448_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_448_, 0, v___x_446_);
                crate::leanh::lean_ctor_set(v___x_448_, 1, v___x_447_);
                v___x_449_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg(v___x_448_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
                return v___x_449_;
            }
            2 => {
                if v_isShared_460_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_459_, 0);
                    v___x_462_ = v___x_459_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_463_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_463_, 0, v_val_457_);
                    v___x_462_ = v_reuseFailAlloc_463_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_462_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_467_) == 0 {
                    crate::leanh::lean_del_object(v___x_469_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_436_);
                    v_val_471_ = crate::leanh::lean_ctor_get(v_a_467_, 0);
                    crate::leanh::lean_inc(v_val_471_);
                    crate::leanh::lean_dec_ref_known(v_a_467_, 1);
                    if v_isShared_470_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_469_, 0, v_val_471_);
                        v___x_473_ = v___x_469_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_474_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_474_, 0, v_val_471_);
                        v___x_473_ = v_reuseFailAlloc_474_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_473_;
            }
            6 => {
                if v_isShared_479_ == 0 {
                    v___x_481_ = v___x_478_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_482_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
                    v___x_481_ = v_reuseFailAlloc_482_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___boxed(
    mut v_constName_484_: *mut crate::leanh::LeanObject,
    mut v___y_485_: *mut crate::leanh::LeanObject,
    mut v___y_486_: *mut crate::leanh::LeanObject,
    mut v___y_487_: *mut crate::leanh::LeanObject,
    mut v___y_488_: *mut crate::leanh::LeanObject,
    mut v___y_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_490_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0(
        v_constName_484_,
        v___y_485_,
        v___y_486_,
        v___y_487_,
        v___y_488_,
    );
    crate::leanh::lean_dec(v___y_488_);
    crate::leanh::lean_dec_ref(v___y_487_);
    crate::leanh::lean_dec(v___y_486_);
    crate::leanh::lean_dec_ref(v___y_485_);
    return v_res_490_;
}
pub unsafe fn l_Lean_Meta_compatibleCtors(
    mut v_ctorName_u2081_491_: *mut crate::leanh::LeanObject,
    mut v_ctorName_u2082_492_: *mut crate::leanh::LeanObject,
    mut v_a_493_: *mut crate::leanh::LeanObject,
    mut v_a_494_: *mut crate::leanh::LeanObject,
    mut v_a_495_: *mut crate::leanh::LeanObject,
    mut v_a_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_504_: u8 = 0;
    let mut v_toConstantVal_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: u8 = 0;
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: u8 = 0;
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_529_: u8 = 0;
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_533_: u8 = 0;
    let mut v_a_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_537_: u8 = 0;
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_541_: u8 = 0;
    let mut v_isSharedCheck_542_: u8 = 0;
    let mut v_a_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_546_: u8 = 0;
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_550_: u8 = 0;
    let mut v_a_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_554_: u8 = 0;
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_498_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0(
                    v_ctorName_u2081_491_,
                    v_a_493_,
                    v_a_494_,
                    v_a_495_,
                    v_a_496_,
                );
                if crate::leanh::lean_obj_tag(v___x_498_) == 0 {
                    v_a_499_ = crate::leanh::lean_ctor_get(v___x_498_, 0);
                    crate::leanh::lean_inc(v_a_499_);
                    crate::leanh::lean_dec_ref_known(v___x_498_, 1);
                    v___x_500_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0(
                        v_ctorName_u2082_492_,
                        v_a_493_,
                        v_a_494_,
                        v_a_495_,
                        v_a_496_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_500_) == 0 {
                        v_a_501_ = crate::leanh::lean_ctor_get(v___x_500_, 0);
                        v_isSharedCheck_542_ = (!crate::leanh::lean_is_exclusive(v___x_500_)) as u8;
                        if v_isSharedCheck_542_ == 0 {
                            v___x_503_ = v___x_500_;
                            v_isShared_504_ = v_isSharedCheck_542_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_501_);
                            crate::leanh::lean_dec(v___x_500_);
                            v___x_503_ = crate::leanh::lean_box(0);
                            v_isShared_504_ = v_isSharedCheck_542_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_499_);
                        v_a_543_ = crate::leanh::lean_ctor_get(v___x_500_, 0);
                        v_isSharedCheck_550_ = (!crate::leanh::lean_is_exclusive(v___x_500_)) as u8;
                        if v_isSharedCheck_550_ == 0 {
                            v___x_545_ = v___x_500_;
                            v_isShared_546_ = v_isSharedCheck_550_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_543_);
                            crate::leanh::lean_dec(v___x_500_);
                            v___x_545_ = crate::leanh::lean_box(0);
                            v_isShared_546_ = v_isSharedCheck_550_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_ctorName_u2082_492_);
                    v_a_551_ = crate::leanh::lean_ctor_get(v___x_498_, 0);
                    v_isSharedCheck_558_ = (!crate::leanh::lean_is_exclusive(v___x_498_)) as u8;
                    if v_isSharedCheck_558_ == 0 {
                        v___x_553_ = v___x_498_;
                        v_isShared_554_ = v_isSharedCheck_558_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_551_);
                        crate::leanh::lean_dec(v___x_498_);
                        v___x_553_ = crate::leanh::lean_box(0);
                        v_isShared_554_ = v_isSharedCheck_558_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_toConstantVal_505_ = crate::leanh::lean_ctor_get(v_a_499_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_505_);
                v_induct_506_ = crate::leanh::lean_ctor_get(v_a_499_, 1);
                crate::leanh::lean_inc(v_induct_506_);
                crate::leanh::lean_dec(v_a_499_);
                v_toConstantVal_507_ = crate::leanh::lean_ctor_get(v_a_501_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_507_);
                v_induct_508_ = crate::leanh::lean_ctor_get(v_a_501_, 1);
                crate::leanh::lean_inc(v_induct_508_);
                crate::leanh::lean_dec(v_a_501_);
                v___x_509_ = lean_name_eq(v_induct_506_, v_induct_508_);
                crate::leanh::lean_dec(v_induct_508_);
                crate::leanh::lean_dec(v_induct_506_);
                if v___x_509_ == 0 {
                    crate::leanh::lean_dec_ref(v_toConstantVal_507_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_505_);
                    v___x_510_ = crate::leanh::lean_box((v___x_509_) as usize);
                    if v_isShared_504_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_503_, 0, v___x_510_);
                        v___x_512_ = v___x_503_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_513_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
                        v___x_512_ = v_reuseFailAlloc_513_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_503_);
                    v_type_514_ = crate::leanh::lean_ctor_get(v_toConstantVal_505_, 2);
                    crate::leanh::lean_inc_ref(v_type_514_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_505_);
                    v___x_515_ = 0;
                    v___x_516_ = l_Lean_Meta_forallMetaTelescope(
                        v_type_514_,
                        v___x_515_,
                        v_a_493_,
                        v_a_494_,
                        v_a_495_,
                        v_a_496_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_516_) == 0 {
                        v_a_517_ = crate::leanh::lean_ctor_get(v___x_516_, 0);
                        crate::leanh::lean_inc(v_a_517_);
                        crate::leanh::lean_dec_ref_known(v___x_516_, 1);
                        v_snd_518_ = crate::leanh::lean_ctor_get(v_a_517_, 1);
                        crate::leanh::lean_inc(v_snd_518_);
                        crate::leanh::lean_dec(v_a_517_);
                        v_snd_519_ = crate::leanh::lean_ctor_get(v_snd_518_, 1);
                        crate::leanh::lean_inc(v_snd_519_);
                        crate::leanh::lean_dec(v_snd_518_);
                        v_type_520_ = crate::leanh::lean_ctor_get(v_toConstantVal_507_, 2);
                        crate::leanh::lean_inc_ref(v_type_520_);
                        crate::leanh::lean_dec_ref(v_toConstantVal_507_);
                        v___x_521_ = l_Lean_Meta_forallMetaTelescope(
                            v_type_520_,
                            v___x_515_,
                            v_a_493_,
                            v_a_494_,
                            v_a_495_,
                            v_a_496_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_521_) == 0 {
                            v_a_522_ = crate::leanh::lean_ctor_get(v___x_521_, 0);
                            crate::leanh::lean_inc(v_a_522_);
                            crate::leanh::lean_dec_ref_known(v___x_521_, 1);
                            v_snd_523_ = crate::leanh::lean_ctor_get(v_a_522_, 1);
                            crate::leanh::lean_inc(v_snd_523_);
                            crate::leanh::lean_dec(v_a_522_);
                            v_snd_524_ = crate::leanh::lean_ctor_get(v_snd_523_, 1);
                            crate::leanh::lean_inc(v_snd_524_);
                            crate::leanh::lean_dec(v_snd_523_);
                            v___x_525_ = l_Lean_Meta_isExprDefEq(
                                v_snd_519_, v_snd_524_, v_a_493_, v_a_494_, v_a_495_, v_a_496_,
                            );
                            return v___x_525_;
                        } else {
                            crate::leanh::lean_dec(v_snd_519_);
                            v_a_526_ = crate::leanh::lean_ctor_get(v___x_521_, 0);
                            v_isSharedCheck_533_ =
                                (!crate::leanh::lean_is_exclusive(v___x_521_)) as u8;
                            if v_isSharedCheck_533_ == 0 {
                                v___x_528_ = v___x_521_;
                                v_isShared_529_ = v_isSharedCheck_533_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_526_);
                                crate::leanh::lean_dec(v___x_521_);
                                v___x_528_ = crate::leanh::lean_box(0);
                                v_isShared_529_ = v_isSharedCheck_533_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_toConstantVal_507_);
                        v_a_534_ = crate::leanh::lean_ctor_get(v___x_516_, 0);
                        v_isSharedCheck_541_ = (!crate::leanh::lean_is_exclusive(v___x_516_)) as u8;
                        if v_isSharedCheck_541_ == 0 {
                            v___x_536_ = v___x_516_;
                            v_isShared_537_ = v_isSharedCheck_541_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_534_);
                            crate::leanh::lean_dec(v___x_516_);
                            v___x_536_ = crate::leanh::lean_box(0);
                            v_isShared_537_ = v_isSharedCheck_541_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_512_;
            }
            3 => {
                if v_isShared_529_ == 0 {
                    v___x_531_ = v___x_528_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_532_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
                    v___x_531_ = v_reuseFailAlloc_532_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_531_;
            }
            5 => {
                if v_isShared_537_ == 0 {
                    v___x_539_ = v___x_536_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
                    v___x_539_ = v_reuseFailAlloc_540_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_539_;
            }
            7 => {
                if v_isShared_546_ == 0 {
                    v___x_548_ = v___x_545_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
                    v___x_548_ = v_reuseFailAlloc_549_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_548_;
            }
            9 => {
                if v_isShared_554_ == 0 {
                    v___x_556_ = v___x_553_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_557_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
                    v___x_556_ = v_reuseFailAlloc_557_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_compatibleCtors___boxed(
    mut v_ctorName_u2081_559_: *mut crate::leanh::LeanObject,
    mut v_ctorName_u2082_560_: *mut crate::leanh::LeanObject,
    mut v_a_561_: *mut crate::leanh::LeanObject,
    mut v_a_562_: *mut crate::leanh::LeanObject,
    mut v_a_563_: *mut crate::leanh::LeanObject,
    mut v_a_564_: *mut crate::leanh::LeanObject,
    mut v_a_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_566_ = l_Lean_Meta_compatibleCtors(
        v_ctorName_u2081_559_,
        v_ctorName_u2082_560_,
        v_a_561_,
        v_a_562_,
        v_a_563_,
        v_a_564_,
    );
    crate::leanh::lean_dec(v_a_564_);
    crate::leanh::lean_dec_ref(v_a_563_);
    crate::leanh::lean_dec(v_a_562_);
    crate::leanh::lean_dec_ref(v_a_561_);
    return v_res_566_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0(
    mut v_00_u03b1_567_: *mut crate::leanh::LeanObject,
    mut v_msg_568_: *mut crate::leanh::LeanObject,
    mut v___y_569_: *mut crate::leanh::LeanObject,
    mut v___y_570_: *mut crate::leanh::LeanObject,
    mut v___y_571_: *mut crate::leanh::LeanObject,
    mut v___y_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_574_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg(v_msg_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
    return v___x_574_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___boxed(
    mut v_00_u03b1_575_: *mut crate::leanh::LeanObject,
    mut v_msg_576_: *mut crate::leanh::LeanObject,
    mut v___y_577_: *mut crate::leanh::LeanObject,
    mut v___y_578_: *mut crate::leanh::LeanObject,
    mut v___y_579_: *mut crate::leanh::LeanObject,
    mut v___y_580_: *mut crate::leanh::LeanObject,
    mut v___y_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_582_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0(v_00_u03b1_575_, v_msg_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
    crate::leanh::lean_dec(v___y_580_);
    crate::leanh::lean_dec_ref(v___y_579_);
    crate::leanh::lean_dec(v___y_578_);
    crate::leanh::lean_dec_ref(v___y_577_);
    return v_res_582_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Inductive(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Inductive(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Inductive(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Inductive(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Inductive(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Inductive(builtin);
}
