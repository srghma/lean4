// Lean compiler output
// Module: Lean.Util.MonadCache
// Imports: Std.Data.HashMap.Basic
use crate::r#gen::Init::Control::State::l_StateT_get;
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_get___boxed;
use crate::r#gen::Init::System::ST::{
    l_ST_Prim_Ref_get___boxed, l_ST_Prim_Ref_modifyGetUnsafe___boxed, l_ST_Prim_mkRef___boxed,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
use crate::r#gen::Std::Data::HashMap::Basic::{
    initialize_Std_Data_HashMap_Basic, runtime_initialize_Std_Data_HashMap_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
pub static l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__2 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MonadCacheT_run___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadCacheT_run___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadCacheT_run___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadCacheT_run___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadCacheT_run___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadCacheT_run___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MonadStateCacheT_run___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_MonadStateCacheT_run___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadStateCacheT_run___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_checkCache___redArg___lam__0(
    mut v_toPure_2029_: *mut crate::leanh::LeanObject,
    mut v_b_2030_: *mut crate::leanh::LeanObject,
    mut v_____r_2031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2032_ = crate::leanh::lean_apply_2(v_toPure_2029_, crate::leanh::lean_box(0), v_b_2030_);
    return v___x_2032_;
}
pub unsafe fn l_Lean_checkCache___redArg___lam__1(
    mut v_toPure_2033_: *mut crate::leanh::LeanObject,
    mut v_cache_2034_: *mut crate::leanh::LeanObject,
    mut v_a_2035_: *mut crate::leanh::LeanObject,
    mut v_toBind_2036_: *mut crate::leanh::LeanObject,
    mut v_b_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_b_2037_);
    v___f_2038_ = crate::leanh::lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2038_, 0, v_toPure_2033_);
    crate::leanh::lean_closure_set(v___f_2038_, 1, v_b_2037_);
    v___x_2039_ = crate::leanh::lean_apply_2(v_cache_2034_, v_a_2035_, v_b_2037_);
    v___x_2040_ = crate::leanh::lean_apply_4(
        v_toBind_2036_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2039_,
        v___f_2038_,
    );
    return v___x_2040_;
}
pub unsafe fn l_Lean_checkCache___redArg___lam__2(
    mut v_f_2041_: *mut crate::leanh::LeanObject,
    mut v_toBind_2042_: *mut crate::leanh::LeanObject,
    mut v___f_2043_: *mut crate::leanh::LeanObject,
    mut v_toPure_2044_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2045_) == 0 {
        let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2044_);
        v___x_2046_ = crate::leanh::lean_box(0);
        v___x_2047_ = crate::leanh::lean_apply_1(v_f_2041_, v___x_2046_);
        v___x_2048_ = crate::leanh::lean_apply_4(
            v_toBind_2042_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2047_,
            v___f_2043_,
        );
        return v___x_2048_;
    } else {
        let mut v_val_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2043_);
        crate::leanh::lean_dec(v_toBind_2042_);
        crate::leanh::lean_dec(v_f_2041_);
        v_val_2049_ = crate::leanh::lean_ctor_get(v_____do__lift_2045_, 0);
        crate::leanh::lean_inc(v_val_2049_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2045_, 1);
        v___x_2050_ =
            crate::leanh::lean_apply_2(v_toPure_2044_, crate::leanh::lean_box(0), v_val_2049_);
        return v___x_2050_;
    }
}
pub unsafe fn l_Lean_checkCache___redArg(
    mut v_inst_2051_: *mut crate::leanh::LeanObject,
    mut v_inst_2052_: *mut crate::leanh::LeanObject,
    mut v_a_2053_: *mut crate::leanh::LeanObject,
    mut v_f_2054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_findCached_x3f_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2055_ = crate::leanh::lean_ctor_get(v_inst_2052_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2055_);
    v_toBind_2056_ = crate::leanh::lean_ctor_get(v_inst_2052_, 1);
    crate::leanh::lean_inc_n(v_toBind_2056_, 3);
    crate::leanh::lean_dec_ref(v_inst_2052_);
    v_findCached_x3f_2057_ = crate::leanh::lean_ctor_get(v_inst_2051_, 0);
    crate::leanh::lean_inc(v_findCached_x3f_2057_);
    v_cache_2058_ = crate::leanh::lean_ctor_get(v_inst_2051_, 1);
    crate::leanh::lean_inc(v_cache_2058_);
    crate::leanh::lean_dec_ref(v_inst_2051_);
    v_toPure_2059_ = crate::leanh::lean_ctor_get(v_toApplicative_2055_, 1);
    crate::leanh::lean_inc_n(v_toPure_2059_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_2055_);
    crate::leanh::lean_inc(v_a_2053_);
    v___x_2060_ = crate::leanh::lean_apply_1(v_findCached_x3f_2057_, v_a_2053_);
    v___f_2061_ = crate::leanh::lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2061_, 0, v_toPure_2059_);
    crate::leanh::lean_closure_set(v___f_2061_, 1, v_cache_2058_);
    crate::leanh::lean_closure_set(v___f_2061_, 2, v_a_2053_);
    crate::leanh::lean_closure_set(v___f_2061_, 3, v_toBind_2056_);
    v___f_2062_ = crate::leanh::lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2062_, 0, v_f_2054_);
    crate::leanh::lean_closure_set(v___f_2062_, 1, v_toBind_2056_);
    crate::leanh::lean_closure_set(v___f_2062_, 2, v___f_2061_);
    crate::leanh::lean_closure_set(v___f_2062_, 3, v_toPure_2059_);
    v___x_2063_ = crate::leanh::lean_apply_4(
        v_toBind_2056_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2060_,
        v___f_2062_,
    );
    return v___x_2063_;
}
pub unsafe fn l_Lean_checkCache(
    mut v_00_u03b1_2064_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2065_: *mut crate::leanh::LeanObject,
    mut v_m_2066_: *mut crate::leanh::LeanObject,
    mut v_inst_2067_: *mut crate::leanh::LeanObject,
    mut v_inst_2068_: *mut crate::leanh::LeanObject,
    mut v_a_2069_: *mut crate::leanh::LeanObject,
    mut v_f_2070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_findCached_x3f_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2071_ = crate::leanh::lean_ctor_get(v_inst_2068_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2071_);
    v_toBind_2072_ = crate::leanh::lean_ctor_get(v_inst_2068_, 1);
    crate::leanh::lean_inc_n(v_toBind_2072_, 3);
    crate::leanh::lean_dec_ref(v_inst_2068_);
    v_findCached_x3f_2073_ = crate::leanh::lean_ctor_get(v_inst_2067_, 0);
    crate::leanh::lean_inc(v_findCached_x3f_2073_);
    v_cache_2074_ = crate::leanh::lean_ctor_get(v_inst_2067_, 1);
    crate::leanh::lean_inc(v_cache_2074_);
    crate::leanh::lean_dec_ref(v_inst_2067_);
    v_toPure_2075_ = crate::leanh::lean_ctor_get(v_toApplicative_2071_, 1);
    crate::leanh::lean_inc_n(v_toPure_2075_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_2071_);
    crate::leanh::lean_inc(v_a_2069_);
    v___x_2076_ = crate::leanh::lean_apply_1(v_findCached_x3f_2073_, v_a_2069_);
    v___f_2077_ = crate::leanh::lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2077_, 0, v_toPure_2075_);
    crate::leanh::lean_closure_set(v___f_2077_, 1, v_cache_2074_);
    crate::leanh::lean_closure_set(v___f_2077_, 2, v_a_2069_);
    crate::leanh::lean_closure_set(v___f_2077_, 3, v_toBind_2072_);
    v___f_2078_ = crate::leanh::lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2078_, 0, v_f_2070_);
    crate::leanh::lean_closure_set(v___f_2078_, 1, v_toBind_2072_);
    crate::leanh::lean_closure_set(v___f_2078_, 2, v___f_2077_);
    crate::leanh::lean_closure_set(v___f_2078_, 3, v_toPure_2075_);
    v___x_2079_ = crate::leanh::lean_apply_4(
        v_toBind_2072_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2076_,
        v___f_2078_,
    );
    return v___x_2079_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__0(
    mut v_inst_2080_: *mut crate::leanh::LeanObject,
    mut v_a_2081_: *mut crate::leanh::LeanObject,
    mut v_x_2082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_findCached_x3f_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_findCached_x3f_2083_ = crate::leanh::lean_ctor_get(v_inst_2080_, 0);
    crate::leanh::lean_inc(v_findCached_x3f_2083_);
    crate::leanh::lean_dec_ref(v_inst_2080_);
    v___x_2084_ = crate::leanh::lean_apply_1(v_findCached_x3f_2083_, v_a_2081_);
    return v___x_2084_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__0___boxed(
    mut v_inst_2085_: *mut crate::leanh::LeanObject,
    mut v_a_2086_: *mut crate::leanh::LeanObject,
    mut v_x_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2088_ =
        l_Lean_instMonadCacheReaderT___redArg___lam__0(v_inst_2085_, v_a_2086_, v_x_2087_);
    crate::leanh::lean_dec(v_x_2087_);
    return v_res_2088_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__1(
    mut v_inst_2089_: *mut crate::leanh::LeanObject,
    mut v_a_2090_: *mut crate::leanh::LeanObject,
    mut v_b_2091_: *mut crate::leanh::LeanObject,
    mut v_x_2092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cache_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cache_2093_ = crate::leanh::lean_ctor_get(v_inst_2089_, 1);
    crate::leanh::lean_inc(v_cache_2093_);
    crate::leanh::lean_dec_ref(v_inst_2089_);
    v___x_2094_ = crate::leanh::lean_apply_2(v_cache_2093_, v_a_2090_, v_b_2091_);
    return v___x_2094_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__1___boxed(
    mut v_inst_2095_: *mut crate::leanh::LeanObject,
    mut v_a_2096_: *mut crate::leanh::LeanObject,
    mut v_b_2097_: *mut crate::leanh::LeanObject,
    mut v_x_2098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2099_ = l_Lean_instMonadCacheReaderT___redArg___lam__1(
        v_inst_2095_,
        v_a_2096_,
        v_b_2097_,
        v_x_2098_,
    );
    crate::leanh::lean_dec(v_x_2098_);
    return v_res_2099_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg(
    mut v_inst_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_2100_);
    v___f_2101_ = crate::leanh::lean_alloc_closure(
        l_Lean_instMonadCacheReaderT___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2101_, 0, v_inst_2100_);
    v___f_2102_ = crate::leanh::lean_alloc_closure(
        l_Lean_instMonadCacheReaderT___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2102_, 0, v_inst_2100_);
    v___x_2103_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2103_, 0, v___f_2101_);
    crate::leanh::lean_ctor_set(v___x_2103_, 1, v___f_2102_);
    return v___x_2103_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT(
    mut v_00_u03b1_2104_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2105_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_2106_: *mut crate::leanh::LeanObject,
    mut v_m_2107_: *mut crate::leanh::LeanObject,
    mut v_inst_2108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2109_ = l_Lean_instMonadCacheReaderT___redArg(v_inst_2108_);
    return v___x_2109_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__0(
    mut v_a_2110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2111_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2111_, 0, v_a_2110_);
    return v___x_2111_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1(
    mut v_inst_2112_: *mut crate::leanh::LeanObject,
    mut v_inst_2113_: *mut crate::leanh::LeanObject,
    mut v___f_2114_: *mut crate::leanh::LeanObject,
    mut v_a_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_findCached_x3f_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2116_ = crate::leanh::lean_ctor_get(v_inst_2113_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2116_);
    crate::leanh::lean_dec_ref(v_inst_2113_);
    v_toFunctor_2117_ = crate::leanh::lean_ctor_get(v_toApplicative_2116_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_2117_);
    crate::leanh::lean_dec_ref(v_toApplicative_2116_);
    v_findCached_x3f_2118_ = crate::leanh::lean_ctor_get(v_inst_2112_, 0);
    crate::leanh::lean_inc(v_findCached_x3f_2118_);
    crate::leanh::lean_dec_ref(v_inst_2112_);
    v_map_2119_ = crate::leanh::lean_ctor_get(v_toFunctor_2117_, 0);
    crate::leanh::lean_inc(v_map_2119_);
    crate::leanh::lean_dec_ref(v_toFunctor_2117_);
    v___x_2120_ = crate::leanh::lean_apply_1(v_findCached_x3f_2118_, v_a_2115_);
    v___x_2121_ = crate::leanh::lean_apply_4(
        v_map_2119_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2114_,
        v___x_2120_,
    );
    return v___x_2121_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__2(
    mut v_a_2122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2123_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2123_, 0, v_a_2122_);
    return v___x_2123_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3(
    mut v_inst_2124_: *mut crate::leanh::LeanObject,
    mut v_inst_2125_: *mut crate::leanh::LeanObject,
    mut v___f_2126_: *mut crate::leanh::LeanObject,
    mut v_a_2127_: *mut crate::leanh::LeanObject,
    mut v_b_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2129_ = crate::leanh::lean_ctor_get(v_inst_2125_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2129_);
    crate::leanh::lean_dec_ref(v_inst_2125_);
    v_toFunctor_2130_ = crate::leanh::lean_ctor_get(v_toApplicative_2129_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_2130_);
    crate::leanh::lean_dec_ref(v_toApplicative_2129_);
    v_cache_2131_ = crate::leanh::lean_ctor_get(v_inst_2124_, 1);
    crate::leanh::lean_inc(v_cache_2131_);
    crate::leanh::lean_dec_ref(v_inst_2124_);
    v_map_2132_ = crate::leanh::lean_ctor_get(v_toFunctor_2130_, 0);
    crate::leanh::lean_inc(v_map_2132_);
    crate::leanh::lean_dec_ref(v_toFunctor_2130_);
    v___x_2133_ = crate::leanh::lean_apply_2(v_cache_2131_, v_a_2127_, v_b_2128_);
    v___x_2134_ = crate::leanh::lean_apply_4(
        v_map_2132_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2126_,
        v___x_2133_,
    );
    return v___x_2134_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg(
    mut v_inst_2137_: *mut crate::leanh::LeanObject,
    mut v_inst_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2139_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0;
    crate::leanh::lean_inc_ref(v_inst_2138_);
    crate::leanh::lean_inc_ref(v_inst_2137_);
    v___f_2140_ = crate::leanh::lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2140_, 0, v_inst_2137_);
    crate::leanh::lean_closure_set(v___f_2140_, 1, v_inst_2138_);
    crate::leanh::lean_closure_set(v___f_2140_, 2, v___f_2139_);
    v___f_2141_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1;
    v___f_2142_ = crate::leanh::lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2142_, 0, v_inst_2137_);
    crate::leanh::lean_closure_set(v___f_2142_, 1, v_inst_2138_);
    crate::leanh::lean_closure_set(v___f_2142_, 2, v___f_2141_);
    v___x_2143_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2143_, 0, v___f_2140_);
    crate::leanh::lean_ctor_set(v___x_2143_, 1, v___f_2142_);
    return v___x_2143_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad(
    mut v_00_u03b1_2144_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2145_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2146_: *mut crate::leanh::LeanObject,
    mut v_m_2147_: *mut crate::leanh::LeanObject,
    mut v_inst_2148_: *mut crate::leanh::LeanObject,
    mut v_inst_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2150_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0;
    crate::leanh::lean_inc_ref(v_inst_2149_);
    crate::leanh::lean_inc_ref(v_inst_2148_);
    v___f_2151_ = crate::leanh::lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2151_, 0, v_inst_2148_);
    crate::leanh::lean_closure_set(v___f_2151_, 1, v_inst_2149_);
    crate::leanh::lean_closure_set(v___f_2151_, 2, v___f_2150_);
    v___f_2152_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1;
    v___f_2153_ = crate::leanh::lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2153_, 0, v_inst_2148_);
    crate::leanh::lean_closure_set(v___f_2153_, 1, v_inst_2149_);
    crate::leanh::lean_closure_set(v___f_2153_, 2, v___f_2152_);
    v___x_2154_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2154_, 0, v___f_2151_);
    crate::leanh::lean_ctor_set(v___x_2154_, 1, v___f_2153_);
    return v___x_2154_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0(
    mut v_inst_2155_: *mut crate::leanh::LeanObject,
    mut v_inst_2156_: *mut crate::leanh::LeanObject,
    mut v_a_2157_: *mut crate::leanh::LeanObject,
    mut v_toPure_2158_: *mut crate::leanh::LeanObject,
    mut v_c_2159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2160_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_inst_2155_,
        v_inst_2156_,
        v_c_2159_,
        v_a_2157_,
    );
    v___x_2161_ =
        crate::leanh::lean_apply_2(v_toPure_2158_, crate::leanh::lean_box(0), v___x_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed(
    mut v_inst_2162_: *mut crate::leanh::LeanObject,
    mut v_inst_2163_: *mut crate::leanh::LeanObject,
    mut v_a_2164_: *mut crate::leanh::LeanObject,
    mut v_toPure_2165_: *mut crate::leanh::LeanObject,
    mut v_c_2166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2167_ = l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0(
        v_inst_2162_,
        v_inst_2163_,
        v_a_2164_,
        v_toPure_2165_,
        v_c_2166_,
    );
    crate::leanh::lean_dec_ref(v_c_2166_);
    return v_res_2167_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg(
    mut v_inst_2168_: *mut crate::leanh::LeanObject,
    mut v_inst_2169_: *mut crate::leanh::LeanObject,
    mut v_inst_2170_: *mut crate::leanh::LeanObject,
    mut v_inst_2171_: *mut crate::leanh::LeanObject,
    mut v_a_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCache_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2173_ = crate::leanh::lean_ctor_get(v_inst_2170_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2173_);
    v_toBind_2174_ = crate::leanh::lean_ctor_get(v_inst_2170_, 1);
    crate::leanh::lean_inc(v_toBind_2174_);
    crate::leanh::lean_dec_ref(v_inst_2170_);
    v_getCache_2175_ = crate::leanh::lean_ctor_get(v_inst_2171_, 0);
    crate::leanh::lean_inc(v_getCache_2175_);
    crate::leanh::lean_dec_ref(v_inst_2171_);
    v_toPure_2176_ = crate::leanh::lean_ctor_get(v_toApplicative_2173_, 1);
    crate::leanh::lean_inc(v_toPure_2176_);
    crate::leanh::lean_dec_ref(v_toApplicative_2173_);
    v___f_2177_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2177_, 0, v_inst_2168_);
    crate::leanh::lean_closure_set(v___f_2177_, 1, v_inst_2169_);
    crate::leanh::lean_closure_set(v___f_2177_, 2, v_a_2172_);
    crate::leanh::lean_closure_set(v___f_2177_, 3, v_toPure_2176_);
    v___x_2178_ = crate::leanh::lean_apply_4(
        v_toBind_2174_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCache_2175_,
        v___f_2177_,
    );
    return v___x_2178_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f(
    mut v_00_u03b1_2179_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2180_: *mut crate::leanh::LeanObject,
    mut v_m_2181_: *mut crate::leanh::LeanObject,
    mut v_inst_2182_: *mut crate::leanh::LeanObject,
    mut v_inst_2183_: *mut crate::leanh::LeanObject,
    mut v_inst_2184_: *mut crate::leanh::LeanObject,
    mut v_inst_2185_: *mut crate::leanh::LeanObject,
    mut v_a_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCache_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2187_ = crate::leanh::lean_ctor_get(v_inst_2184_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2187_);
    v_toBind_2188_ = crate::leanh::lean_ctor_get(v_inst_2184_, 1);
    crate::leanh::lean_inc(v_toBind_2188_);
    crate::leanh::lean_dec_ref(v_inst_2184_);
    v_getCache_2189_ = crate::leanh::lean_ctor_get(v_inst_2185_, 0);
    crate::leanh::lean_inc(v_getCache_2189_);
    crate::leanh::lean_dec_ref(v_inst_2185_);
    v_toPure_2190_ = crate::leanh::lean_ctor_get(v_toApplicative_2187_, 1);
    crate::leanh::lean_inc(v_toPure_2190_);
    crate::leanh::lean_dec_ref(v_toApplicative_2187_);
    v___f_2191_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2191_, 0, v_inst_2182_);
    crate::leanh::lean_closure_set(v___f_2191_, 1, v_inst_2183_);
    crate::leanh::lean_closure_set(v___f_2191_, 2, v_a_2186_);
    crate::leanh::lean_closure_set(v___f_2191_, 3, v_toPure_2190_);
    v___x_2192_ = crate::leanh::lean_apply_4(
        v_toBind_2188_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCache_2189_,
        v___f_2191_,
    );
    return v___x_2192_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0(
    mut v_inst_2193_: *mut crate::leanh::LeanObject,
    mut v_inst_2194_: *mut crate::leanh::LeanObject,
    mut v_a_2195_: *mut crate::leanh::LeanObject,
    mut v_b_2196_: *mut crate::leanh::LeanObject,
    mut v_s_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2198_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_inst_2193_,
        v_inst_2194_,
        v_s_2197_,
        v_a_2195_,
        v_b_2196_,
    );
    return v___x_2198_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_cache___redArg(
    mut v_inst_2199_: *mut crate::leanh::LeanObject,
    mut v_inst_2200_: *mut crate::leanh::LeanObject,
    mut v_inst_2201_: *mut crate::leanh::LeanObject,
    mut v_a_2202_: *mut crate::leanh::LeanObject,
    mut v_b_2203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyCache_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyCache_2204_ = crate::leanh::lean_ctor_get(v_inst_2201_, 1);
    crate::leanh::lean_inc(v_modifyCache_2204_);
    crate::leanh::lean_dec_ref(v_inst_2201_);
    v___f_2205_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2205_, 0, v_inst_2199_);
    crate::leanh::lean_closure_set(v___f_2205_, 1, v_inst_2200_);
    crate::leanh::lean_closure_set(v___f_2205_, 2, v_a_2202_);
    crate::leanh::lean_closure_set(v___f_2205_, 3, v_b_2203_);
    v___x_2206_ = crate::leanh::lean_apply_1(v_modifyCache_2204_, v___f_2205_);
    return v___x_2206_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_cache(
    mut v_00_u03b1_2207_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2208_: *mut crate::leanh::LeanObject,
    mut v_m_2209_: *mut crate::leanh::LeanObject,
    mut v_inst_2210_: *mut crate::leanh::LeanObject,
    mut v_inst_2211_: *mut crate::leanh::LeanObject,
    mut v_inst_2212_: *mut crate::leanh::LeanObject,
    mut v_a_2213_: *mut crate::leanh::LeanObject,
    mut v_b_2214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyCache_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyCache_2215_ = crate::leanh::lean_ctor_get(v_inst_2212_, 1);
    crate::leanh::lean_inc(v_modifyCache_2215_);
    crate::leanh::lean_dec_ref(v_inst_2212_);
    v___f_2216_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2216_, 0, v_inst_2210_);
    crate::leanh::lean_closure_set(v___f_2216_, 1, v_inst_2211_);
    crate::leanh::lean_closure_set(v___f_2216_, 2, v_a_2213_);
    crate::leanh::lean_closure_set(v___f_2216_, 3, v_b_2214_);
    v___x_2217_ = crate::leanh::lean_apply_1(v_modifyCache_2215_, v___f_2216_);
    return v___x_2217_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad___redArg(
    mut v_inst_2218_: *mut crate::leanh::LeanObject,
    mut v_inst_2219_: *mut crate::leanh::LeanObject,
    mut v_inst_2220_: *mut crate::leanh::LeanObject,
    mut v_inst_2221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_2221_);
    crate::leanh::lean_inc_ref(v_inst_2219_);
    crate::leanh::lean_inc_ref(v_inst_2218_);
    v___x_2222_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_findCached_x3f as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___x_2222_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2222_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2222_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2222_, 3, v_inst_2218_);
    crate::leanh::lean_closure_set(v___x_2222_, 4, v_inst_2219_);
    crate::leanh::lean_closure_set(v___x_2222_, 5, v_inst_2220_);
    crate::leanh::lean_closure_set(v___x_2222_, 6, v_inst_2221_);
    v___x_2223_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_cache as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___x_2223_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2223_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2223_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2223_, 3, v_inst_2218_);
    crate::leanh::lean_closure_set(v___x_2223_, 4, v_inst_2219_);
    crate::leanh::lean_closure_set(v___x_2223_, 5, v_inst_2221_);
    v___x_2224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2224_, 0, v___x_2222_);
    crate::leanh::lean_ctor_set(v___x_2224_, 1, v___x_2223_);
    return v___x_2224_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad(
    mut v_00_u03b1_2225_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2226_: *mut crate::leanh::LeanObject,
    mut v_m_2227_: *mut crate::leanh::LeanObject,
    mut v_inst_2228_: *mut crate::leanh::LeanObject,
    mut v_inst_2229_: *mut crate::leanh::LeanObject,
    mut v_inst_2230_: *mut crate::leanh::LeanObject,
    mut v_inst_2231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2232_ = l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad___redArg(
        v_inst_2228_,
        v_inst_2229_,
        v_inst_2230_,
        v_inst_2231_,
    );
    return v___x_2232_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(
    mut v_f_2233_: *mut crate::leanh::LeanObject,
    mut v_s_2234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2235_ = crate::leanh::lean_box(0);
    v___x_2236_ = crate::leanh::lean_apply_1(v_f_2233_, v_s_2234_);
    v___x_2237_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2237_, 0, v___x_2235_);
    crate::leanh::lean_ctor_set(v___x_2237_, 1, v___x_2236_);
    return v___x_2237_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1(
    mut v_inst_2238_: *mut crate::leanh::LeanObject,
    mut v_f_2239_: *mut crate::leanh::LeanObject,
    mut v___y_2240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2241_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2241_, 0, v_f_2239_);
    crate::leanh::lean_inc(v___y_2240_);
    v___x_2242_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_2242_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2242_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2242_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2242_, 3, v___y_2240_);
    crate::leanh::lean_closure_set(v___x_2242_, 4, v___f_2241_);
    v___x_2243_ = crate::leanh::lean_apply_2(v_inst_2238_, crate::leanh::lean_box(0), v___x_2242_);
    return v___x_2243_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1___boxed(
    mut v_inst_2244_: *mut crate::leanh::LeanObject,
    mut v_f_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2247_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1(
        v_inst_2244_,
        v_f_2245_,
        v___y_2246_,
    );
    crate::leanh::lean_dec(v___y_2246_);
    return v_res_2247_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(
    mut v_inst_2248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_inst_2248_);
    v___f_2249_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2249_, 0, v_inst_2248_);
    v___x_2250_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_get___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_2250_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2250_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2250_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2250_, 3, v_inst_2248_);
    v___x_2251_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2251_, 0, v___x_2250_);
    crate::leanh::lean_ctor_set(v___x_2251_, 1, v___f_2249_);
    return v___x_2251_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter(
    mut v_00_u03c9_2252_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2253_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2254_: *mut crate::leanh::LeanObject,
    mut v_m_2255_: *mut crate::leanh::LeanObject,
    mut v_inst_2256_: *mut crate::leanh::LeanObject,
    mut v_inst_2257_: *mut crate::leanh::LeanObject,
    mut v_inst_2258_: *mut crate::leanh::LeanObject,
    mut v_inst_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2260_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_2259_);
    return v___x_2260_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___boxed(
    mut v_00_u03c9_2261_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2262_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2263_: *mut crate::leanh::LeanObject,
    mut v_m_2264_: *mut crate::leanh::LeanObject,
    mut v_inst_2265_: *mut crate::leanh::LeanObject,
    mut v_inst_2266_: *mut crate::leanh::LeanObject,
    mut v_inst_2267_: *mut crate::leanh::LeanObject,
    mut v_inst_2268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2269_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter(
        v_00_u03c9_2261_,
        v_00_u03b1_2262_,
        v_00_u03b2_2263_,
        v_m_2264_,
        v_inst_2265_,
        v_inst_2266_,
        v_inst_2267_,
        v_inst_2268_,
    );
    crate::leanh::lean_dec_ref(v_inst_2267_);
    crate::leanh::lean_dec_ref(v_inst_2266_);
    return v_res_2269_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__0(
    mut v_a_2270_: *mut crate::leanh::LeanObject,
    mut v_toPure_2271_: *mut crate::leanh::LeanObject,
    mut v_s_2272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2273_, 0, v_a_2270_);
    crate::leanh::lean_ctor_set(v___x_2273_, 1, v_s_2272_);
    v___x_2274_ =
        crate::leanh::lean_apply_2(v_toPure_2271_, crate::leanh::lean_box(0), v___x_2273_);
    return v___x_2274_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__1(
    mut v_toPure_2275_: *mut crate::leanh::LeanObject,
    mut v_ref_2276_: *mut crate::leanh::LeanObject,
    mut v_inst_2277_: *mut crate::leanh::LeanObject,
    mut v_toBind_2278_: *mut crate::leanh::LeanObject,
    mut v_a_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2280_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2280_, 0, v_a_2279_);
    crate::leanh::lean_closure_set(v___f_2280_, 1, v_toPure_2275_);
    v___x_2281_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_2281_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2281_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2281_, 2, v_ref_2276_);
    v___x_2282_ = crate::leanh::lean_apply_2(v_inst_2277_, crate::leanh::lean_box(0), v___x_2281_);
    v___x_2283_ = crate::leanh::lean_apply_4(
        v_toBind_2278_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2282_,
        v___f_2280_,
    );
    return v___x_2283_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__2(
    mut v_toPure_2284_: *mut crate::leanh::LeanObject,
    mut v_inst_2285_: *mut crate::leanh::LeanObject,
    mut v_toBind_2286_: *mut crate::leanh::LeanObject,
    mut v_x_2287_: *mut crate::leanh::LeanObject,
    mut v_ref_2288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_2286_);
    crate::leanh::lean_inc(v_ref_2288_);
    v___f_2289_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2289_, 0, v_toPure_2284_);
    crate::leanh::lean_closure_set(v___f_2289_, 1, v_ref_2288_);
    crate::leanh::lean_closure_set(v___f_2289_, 2, v_inst_2285_);
    crate::leanh::lean_closure_set(v___f_2289_, 3, v_toBind_2286_);
    v___x_2290_ = crate::leanh::lean_apply_1(v_x_2287_, v_ref_2288_);
    v___x_2291_ = crate::leanh::lean_apply_4(
        v_toBind_2286_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2290_,
        v___f_2289_,
    );
    return v___x_2291_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__3(
    mut v_toPure_2292_: *mut crate::leanh::LeanObject,
    mut v_____x_2293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2294_ = crate::leanh::lean_ctor_get(v_____x_2293_, 0);
    crate::leanh::lean_inc(v_fst_2294_);
    crate::leanh::lean_dec_ref(v_____x_2293_);
    v___x_2295_ =
        crate::leanh::lean_apply_2(v_toPure_2292_, crate::leanh::lean_box(0), v_fst_2294_);
    return v___x_2295_;
}
pub unsafe fn _init_l_Lean_MonadCacheT_run___redArg___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2296_ = crate::leanh::lean_box(0);
    v___x_2297_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2298_ = lean_mk_array(v___x_2297_, v___x_2296_);
    return v___x_2298_;
}
pub unsafe fn _init_l_Lean_MonadCacheT_run___redArg___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__0_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__0,
    );
    v___x_2300_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2301_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2301_, 0, v___x_2300_);
    crate::leanh::lean_ctor_set(v___x_2301_, 1, v___x_2299_);
    return v___x_2301_;
}
pub unsafe fn _init_l_Lean_MonadCacheT_run___redArg___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__1,
    );
    v___x_2303_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_2303_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2303_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2303_, 2, v___x_2302_);
    return v___x_2303_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg(
    mut v_inst_2304_: *mut crate::leanh::LeanObject,
    mut v_inst_2305_: *mut crate::leanh::LeanObject,
    mut v_x_2306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2307_ = crate::leanh::lean_ctor_get(v_inst_2305_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2307_);
    v_toBind_2308_ = crate::leanh::lean_ctor_get(v_inst_2305_, 1);
    crate::leanh::lean_inc_n(v_toBind_2308_, 3);
    crate::leanh::lean_dec_ref(v_inst_2305_);
    v_toPure_2309_ = crate::leanh::lean_ctor_get(v_toApplicative_2307_, 1);
    crate::leanh::lean_inc_n(v_toPure_2309_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_2307_);
    v___x_2310_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__2,
    );
    crate::leanh::lean_inc(v_inst_2304_);
    v___x_2311_ = crate::leanh::lean_apply_2(v_inst_2304_, crate::leanh::lean_box(0), v___x_2310_);
    v___f_2312_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2312_, 0, v_toPure_2309_);
    crate::leanh::lean_closure_set(v___f_2312_, 1, v_inst_2304_);
    crate::leanh::lean_closure_set(v___f_2312_, 2, v_toBind_2308_);
    crate::leanh::lean_closure_set(v___f_2312_, 3, v_x_2306_);
    v___f_2313_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2313_, 0, v_toPure_2309_);
    v___x_2314_ = crate::leanh::lean_apply_4(
        v_toBind_2308_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2311_,
        v___f_2312_,
    );
    v___x_2315_ = crate::leanh::lean_apply_4(
        v_toBind_2308_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2314_,
        v___f_2313_,
    );
    return v___x_2315_;
}
pub unsafe fn l_Lean_MonadCacheT_run(
    mut v_00_u03c9_2316_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2317_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2318_: *mut crate::leanh::LeanObject,
    mut v_m_2319_: *mut crate::leanh::LeanObject,
    mut v_inst_2320_: *mut crate::leanh::LeanObject,
    mut v_inst_2321_: *mut crate::leanh::LeanObject,
    mut v_inst_2322_: *mut crate::leanh::LeanObject,
    mut v_inst_2323_: *mut crate::leanh::LeanObject,
    mut v_inst_2324_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2325_: *mut crate::leanh::LeanObject,
    mut v_x_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2327_ = crate::leanh::lean_ctor_get(v_inst_2324_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2327_);
    v_toBind_2328_ = crate::leanh::lean_ctor_get(v_inst_2324_, 1);
    crate::leanh::lean_inc_n(v_toBind_2328_, 3);
    crate::leanh::lean_dec_ref(v_inst_2324_);
    v_toPure_2329_ = crate::leanh::lean_ctor_get(v_toApplicative_2327_, 1);
    crate::leanh::lean_inc_n(v_toPure_2329_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_2327_);
    v___x_2330_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__2,
    );
    crate::leanh::lean_inc(v_inst_2323_);
    v___x_2331_ = crate::leanh::lean_apply_2(v_inst_2323_, crate::leanh::lean_box(0), v___x_2330_);
    v___f_2332_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2332_, 0, v_toPure_2329_);
    crate::leanh::lean_closure_set(v___f_2332_, 1, v_inst_2323_);
    crate::leanh::lean_closure_set(v___f_2332_, 2, v_toBind_2328_);
    crate::leanh::lean_closure_set(v___f_2332_, 3, v_x_2326_);
    v___f_2333_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2333_, 0, v_toPure_2329_);
    v___x_2334_ = crate::leanh::lean_apply_4(
        v_toBind_2328_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2331_,
        v___f_2332_,
    );
    v___x_2335_ = crate::leanh::lean_apply_4(
        v_toBind_2328_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2334_,
        v___f_2333_,
    );
    return v___x_2335_;
}
pub unsafe fn l_Lean_MonadCacheT_run___boxed(
    mut v_00_u03c9_2336_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2337_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2338_: *mut crate::leanh::LeanObject,
    mut v_m_2339_: *mut crate::leanh::LeanObject,
    mut v_inst_2340_: *mut crate::leanh::LeanObject,
    mut v_inst_2341_: *mut crate::leanh::LeanObject,
    mut v_inst_2342_: *mut crate::leanh::LeanObject,
    mut v_inst_2343_: *mut crate::leanh::LeanObject,
    mut v_inst_2344_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2345_: *mut crate::leanh::LeanObject,
    mut v_x_2346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2347_ = l_Lean_MonadCacheT_run(
        v_00_u03c9_2336_,
        v_00_u03b1_2337_,
        v_00_u03b2_2338_,
        v_m_2339_,
        v_inst_2340_,
        v_inst_2341_,
        v_inst_2342_,
        v_inst_2343_,
        v_inst_2344_,
        v_00_u03c3_2345_,
        v_x_2346_,
    );
    crate::leanh::lean_dec_ref(v_inst_2342_);
    crate::leanh::lean_dec_ref(v_inst_2341_);
    return v_res_2347_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1___redArg(
    mut v_inst_2348_: *mut crate::leanh::LeanObject,
    mut v_a_2349_: *mut crate::leanh::LeanObject,
    mut v_a_2350_: *mut crate::leanh::LeanObject,
    mut v_a_2351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2352_ = crate::leanh::lean_ctor_get(v_inst_2348_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2352_);
    crate::leanh::lean_dec_ref(v_inst_2348_);
    v_toFunctor_2353_ = crate::leanh::lean_ctor_get(v_toApplicative_2352_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_2353_);
    crate::leanh::lean_dec_ref(v_toApplicative_2352_);
    v_map_2354_ = crate::leanh::lean_ctor_get(v_toFunctor_2353_, 0);
    crate::leanh::lean_inc(v_map_2354_);
    crate::leanh::lean_dec_ref(v_toFunctor_2353_);
    crate::leanh::lean_inc(v_a_2351_);
    v___x_2355_ = crate::leanh::lean_apply_1(v_a_2350_, v_a_2351_);
    v___x_2356_ = crate::leanh::lean_apply_4(
        v_map_2354_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_a_2349_,
        v___x_2355_,
    );
    return v___x_2356_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1___redArg___boxed(
    mut v_inst_2357_: *mut crate::leanh::LeanObject,
    mut v_a_2358_: *mut crate::leanh::LeanObject,
    mut v_a_2359_: *mut crate::leanh::LeanObject,
    mut v_a_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2361_ = l_Lean_MonadCacheT_instMonad___aux__1___redArg(
        v_inst_2357_,
        v_a_2358_,
        v_a_2359_,
        v_a_2360_,
    );
    crate::leanh::lean_dec(v_a_2360_);
    return v_res_2361_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1(
    mut v_00_u03c9_2362_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2363_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2364_: *mut crate::leanh::LeanObject,
    mut v_m_2365_: *mut crate::leanh::LeanObject,
    mut v_inst_2366_: *mut crate::leanh::LeanObject,
    mut v_inst_2367_: *mut crate::leanh::LeanObject,
    mut v_inst_2368_: *mut crate::leanh::LeanObject,
    mut v_inst_2369_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2370_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2371_: *mut crate::leanh::LeanObject,
    mut v_a_2372_: *mut crate::leanh::LeanObject,
    mut v_a_2373_: *mut crate::leanh::LeanObject,
    mut v_a_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2375_ = crate::leanh::lean_ctor_get(v_inst_2369_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2375_);
    crate::leanh::lean_dec_ref(v_inst_2369_);
    v_toFunctor_2376_ = crate::leanh::lean_ctor_get(v_toApplicative_2375_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_2376_);
    crate::leanh::lean_dec_ref(v_toApplicative_2375_);
    v_map_2377_ = crate::leanh::lean_ctor_get(v_toFunctor_2376_, 0);
    crate::leanh::lean_inc(v_map_2377_);
    crate::leanh::lean_dec_ref(v_toFunctor_2376_);
    crate::leanh::lean_inc(v_a_2374_);
    v___x_2378_ = crate::leanh::lean_apply_1(v_a_2373_, v_a_2374_);
    v___x_2379_ = crate::leanh::lean_apply_4(
        v_map_2377_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_a_2372_,
        v___x_2378_,
    );
    return v___x_2379_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1___boxed(
    mut v_00_u03c9_2380_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2381_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2382_: *mut crate::leanh::LeanObject,
    mut v_m_2383_: *mut crate::leanh::LeanObject,
    mut v_inst_2384_: *mut crate::leanh::LeanObject,
    mut v_inst_2385_: *mut crate::leanh::LeanObject,
    mut v_inst_2386_: *mut crate::leanh::LeanObject,
    mut v_inst_2387_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2388_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2389_: *mut crate::leanh::LeanObject,
    mut v_a_2390_: *mut crate::leanh::LeanObject,
    mut v_a_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2393_ = l_Lean_MonadCacheT_instMonad___aux__1(
        v_00_u03c9_2380_,
        v_00_u03b1_2381_,
        v_00_u03b2_2382_,
        v_m_2383_,
        v_inst_2384_,
        v_inst_2385_,
        v_inst_2386_,
        v_inst_2387_,
        v_00_u03b1_2388_,
        v_00_u03b2_2389_,
        v_a_2390_,
        v_a_2391_,
        v_a_2392_,
    );
    crate::leanh::lean_dec(v_a_2392_);
    crate::leanh::lean_dec_ref(v_inst_2386_);
    crate::leanh::lean_dec_ref(v_inst_2385_);
    return v_res_2393_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3___redArg(
    mut v_inst_2394_: *mut crate::leanh::LeanObject,
    mut v_a_2395_: *mut crate::leanh::LeanObject,
    mut v_a_2396_: *mut crate::leanh::LeanObject,
    mut v_a_2397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapConst_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2398_ = crate::leanh::lean_ctor_get(v_inst_2394_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2398_);
    crate::leanh::lean_dec_ref(v_inst_2394_);
    v_toFunctor_2399_ = crate::leanh::lean_ctor_get(v_toApplicative_2398_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_2399_);
    crate::leanh::lean_dec_ref(v_toApplicative_2398_);
    v_mapConst_2400_ = crate::leanh::lean_ctor_get(v_toFunctor_2399_, 1);
    crate::leanh::lean_inc(v_mapConst_2400_);
    crate::leanh::lean_dec_ref(v_toFunctor_2399_);
    crate::leanh::lean_inc(v_a_2397_);
    v___x_2401_ = crate::leanh::lean_apply_1(v_a_2396_, v_a_2397_);
    v___x_2402_ = crate::leanh::lean_apply_4(
        v_mapConst_2400_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_a_2395_,
        v___x_2401_,
    );
    return v___x_2402_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3___redArg___boxed(
    mut v_inst_2403_: *mut crate::leanh::LeanObject,
    mut v_a_2404_: *mut crate::leanh::LeanObject,
    mut v_a_2405_: *mut crate::leanh::LeanObject,
    mut v_a_2406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_Lean_MonadCacheT_instMonad___aux__3___redArg(
        v_inst_2403_,
        v_a_2404_,
        v_a_2405_,
        v_a_2406_,
    );
    crate::leanh::lean_dec(v_a_2406_);
    return v_res_2407_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3(
    mut v_00_u03c9_2408_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2409_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2410_: *mut crate::leanh::LeanObject,
    mut v_m_2411_: *mut crate::leanh::LeanObject,
    mut v_inst_2412_: *mut crate::leanh::LeanObject,
    mut v_inst_2413_: *mut crate::leanh::LeanObject,
    mut v_inst_2414_: *mut crate::leanh::LeanObject,
    mut v_inst_2415_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2416_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2417_: *mut crate::leanh::LeanObject,
    mut v_a_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
    mut v_a_2420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapConst_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2421_ = crate::leanh::lean_ctor_get(v_inst_2415_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2421_);
    crate::leanh::lean_dec_ref(v_inst_2415_);
    v_toFunctor_2422_ = crate::leanh::lean_ctor_get(v_toApplicative_2421_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_2422_);
    crate::leanh::lean_dec_ref(v_toApplicative_2421_);
    v_mapConst_2423_ = crate::leanh::lean_ctor_get(v_toFunctor_2422_, 1);
    crate::leanh::lean_inc(v_mapConst_2423_);
    crate::leanh::lean_dec_ref(v_toFunctor_2422_);
    crate::leanh::lean_inc(v_a_2420_);
    v___x_2424_ = crate::leanh::lean_apply_1(v_a_2419_, v_a_2420_);
    v___x_2425_ = crate::leanh::lean_apply_4(
        v_mapConst_2423_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_a_2418_,
        v___x_2424_,
    );
    return v___x_2425_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3___boxed(
    mut v_00_u03c9_2426_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2427_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2428_: *mut crate::leanh::LeanObject,
    mut v_m_2429_: *mut crate::leanh::LeanObject,
    mut v_inst_2430_: *mut crate::leanh::LeanObject,
    mut v_inst_2431_: *mut crate::leanh::LeanObject,
    mut v_inst_2432_: *mut crate::leanh::LeanObject,
    mut v_inst_2433_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2434_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2435_: *mut crate::leanh::LeanObject,
    mut v_a_2436_: *mut crate::leanh::LeanObject,
    mut v_a_2437_: *mut crate::leanh::LeanObject,
    mut v_a_2438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2439_ = l_Lean_MonadCacheT_instMonad___aux__3(
        v_00_u03c9_2426_,
        v_00_u03b1_2427_,
        v_00_u03b2_2428_,
        v_m_2429_,
        v_inst_2430_,
        v_inst_2431_,
        v_inst_2432_,
        v_inst_2433_,
        v_00_u03b1_2434_,
        v_00_u03b2_2435_,
        v_a_2436_,
        v_a_2437_,
        v_a_2438_,
    );
    crate::leanh::lean_dec(v_a_2438_);
    crate::leanh::lean_dec_ref(v_inst_2432_);
    crate::leanh::lean_dec_ref(v_inst_2431_);
    return v_res_2439_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__5___redArg(
    mut v_inst_2440_: *mut crate::leanh::LeanObject,
    mut v_a_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2442_ = crate::leanh::lean_ctor_get(v_inst_2440_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2442_);
    crate::leanh::lean_dec_ref(v_inst_2440_);
    v_toPure_2443_ = crate::leanh::lean_ctor_get(v_toApplicative_2442_, 1);
    crate::leanh::lean_inc(v_toPure_2443_);
    crate::leanh::lean_dec_ref(v_toApplicative_2442_);
    v___x_2444_ = crate::leanh::lean_apply_2(v_toPure_2443_, crate::leanh::lean_box(0), v_a_2441_);
    return v___x_2444_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__5(
    mut v_00_u03c9_2445_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2446_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2447_: *mut crate::leanh::LeanObject,
    mut v_m_2448_: *mut crate::leanh::LeanObject,
    mut v_inst_2449_: *mut crate::leanh::LeanObject,
    mut v_inst_2450_: *mut crate::leanh::LeanObject,
    mut v_inst_2451_: *mut crate::leanh::LeanObject,
    mut v_inst_2452_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2453_: *mut crate::leanh::LeanObject,
    mut v_a_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2456_ = crate::leanh::lean_ctor_get(v_inst_2452_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2456_);
    crate::leanh::lean_dec_ref(v_inst_2452_);
    v_toPure_2457_ = crate::leanh::lean_ctor_get(v_toApplicative_2456_, 1);
    crate::leanh::lean_inc(v_toPure_2457_);
    crate::leanh::lean_dec_ref(v_toApplicative_2456_);
    v___x_2458_ = crate::leanh::lean_apply_2(v_toPure_2457_, crate::leanh::lean_box(0), v_a_2454_);
    return v___x_2458_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__5___boxed(
    mut v_00_u03c9_2459_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2460_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2461_: *mut crate::leanh::LeanObject,
    mut v_m_2462_: *mut crate::leanh::LeanObject,
    mut v_inst_2463_: *mut crate::leanh::LeanObject,
    mut v_inst_2464_: *mut crate::leanh::LeanObject,
    mut v_inst_2465_: *mut crate::leanh::LeanObject,
    mut v_inst_2466_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2470_ = l_Lean_MonadCacheT_instMonad___aux__5(
        v_00_u03c9_2459_,
        v_00_u03b1_2460_,
        v_00_u03b2_2461_,
        v_m_2462_,
        v_inst_2463_,
        v_inst_2464_,
        v_inst_2465_,
        v_inst_2466_,
        v_00_u03b1_2467_,
        v_a_2468_,
        v_a_2469_,
    );
    crate::leanh::lean_dec(v_a_2469_);
    crate::leanh::lean_dec_ref(v_inst_2465_);
    crate::leanh::lean_dec_ref(v_inst_2464_);
    return v_res_2470_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0(
    mut v_a_2471_: *mut crate::leanh::LeanObject,
    mut v_a_2472_: *mut crate::leanh::LeanObject,
    mut v_x_2473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_a_2472_);
    v___x_2475_ = crate::leanh::lean_apply_2(v_a_2471_, v___x_2474_, v_a_2472_);
    return v___x_2475_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed(
    mut v_a_2476_: *mut crate::leanh::LeanObject,
    mut v_a_2477_: *mut crate::leanh::LeanObject,
    mut v_x_2478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2479_ =
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0(v_a_2476_, v_a_2477_, v_x_2478_);
    crate::leanh::lean_dec(v_a_2477_);
    return v_res_2479_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg(
    mut v_inst_2480_: *mut crate::leanh::LeanObject,
    mut v_a_2481_: *mut crate::leanh::LeanObject,
    mut v_a_2482_: *mut crate::leanh::LeanObject,
    mut v_a_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2484_ = crate::leanh::lean_ctor_get(v_inst_2480_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2484_);
    crate::leanh::lean_dec_ref(v_inst_2480_);
    v_toSeq_2485_ = crate::leanh::lean_ctor_get(v_toApplicative_2484_, 2);
    crate::leanh::lean_inc(v_toSeq_2485_);
    crate::leanh::lean_dec_ref(v_toApplicative_2484_);
    crate::leanh::lean_inc_n(v_a_2483_, 2);
    v___f_2486_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2486_, 0, v_a_2482_);
    crate::leanh::lean_closure_set(v___f_2486_, 1, v_a_2483_);
    v___x_2487_ = crate::leanh::lean_apply_1(v_a_2481_, v_a_2483_);
    v___x_2488_ = crate::leanh::lean_apply_4(
        v_toSeq_2485_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2487_,
        v___f_2486_,
    );
    return v___x_2488_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg___boxed(
    mut v_inst_2489_: *mut crate::leanh::LeanObject,
    mut v_a_2490_: *mut crate::leanh::LeanObject,
    mut v_a_2491_: *mut crate::leanh::LeanObject,
    mut v_a_2492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2493_ = l_Lean_MonadCacheT_instMonad___aux__7___redArg(
        v_inst_2489_,
        v_a_2490_,
        v_a_2491_,
        v_a_2492_,
    );
    crate::leanh::lean_dec(v_a_2492_);
    return v_res_2493_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7(
    mut v_00_u03c9_2494_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2495_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2496_: *mut crate::leanh::LeanObject,
    mut v_m_2497_: *mut crate::leanh::LeanObject,
    mut v_inst_2498_: *mut crate::leanh::LeanObject,
    mut v_inst_2499_: *mut crate::leanh::LeanObject,
    mut v_inst_2500_: *mut crate::leanh::LeanObject,
    mut v_inst_2501_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2502_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2503_: *mut crate::leanh::LeanObject,
    mut v_a_2504_: *mut crate::leanh::LeanObject,
    mut v_a_2505_: *mut crate::leanh::LeanObject,
    mut v_a_2506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2507_ = crate::leanh::lean_ctor_get(v_inst_2501_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2507_);
    crate::leanh::lean_dec_ref(v_inst_2501_);
    v_toSeq_2508_ = crate::leanh::lean_ctor_get(v_toApplicative_2507_, 2);
    crate::leanh::lean_inc(v_toSeq_2508_);
    crate::leanh::lean_dec_ref(v_toApplicative_2507_);
    crate::leanh::lean_inc_n(v_a_2506_, 2);
    v___f_2509_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2509_, 0, v_a_2505_);
    crate::leanh::lean_closure_set(v___f_2509_, 1, v_a_2506_);
    v___x_2510_ = crate::leanh::lean_apply_1(v_a_2504_, v_a_2506_);
    v___x_2511_ = crate::leanh::lean_apply_4(
        v_toSeq_2508_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2510_,
        v___f_2509_,
    );
    return v___x_2511_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___boxed(
    mut v_00_u03c9_2512_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2513_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2514_: *mut crate::leanh::LeanObject,
    mut v_m_2515_: *mut crate::leanh::LeanObject,
    mut v_inst_2516_: *mut crate::leanh::LeanObject,
    mut v_inst_2517_: *mut crate::leanh::LeanObject,
    mut v_inst_2518_: *mut crate::leanh::LeanObject,
    mut v_inst_2519_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2520_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2521_: *mut crate::leanh::LeanObject,
    mut v_a_2522_: *mut crate::leanh::LeanObject,
    mut v_a_2523_: *mut crate::leanh::LeanObject,
    mut v_a_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2525_ = l_Lean_MonadCacheT_instMonad___aux__7(
        v_00_u03c9_2512_,
        v_00_u03b1_2513_,
        v_00_u03b2_2514_,
        v_m_2515_,
        v_inst_2516_,
        v_inst_2517_,
        v_inst_2518_,
        v_inst_2519_,
        v_00_u03b1_2520_,
        v_00_u03b2_2521_,
        v_a_2522_,
        v_a_2523_,
        v_a_2524_,
    );
    crate::leanh::lean_dec(v_a_2524_);
    crate::leanh::lean_dec_ref(v_inst_2518_);
    crate::leanh::lean_dec_ref(v_inst_2517_);
    return v_res_2525_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9___redArg(
    mut v_inst_2526_: *mut crate::leanh::LeanObject,
    mut v_a_2527_: *mut crate::leanh::LeanObject,
    mut v_a_2528_: *mut crate::leanh::LeanObject,
    mut v_a_2529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2530_ = crate::leanh::lean_ctor_get(v_inst_2526_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2530_);
    crate::leanh::lean_dec_ref(v_inst_2526_);
    v_toSeqLeft_2531_ = crate::leanh::lean_ctor_get(v_toApplicative_2530_, 3);
    crate::leanh::lean_inc(v_toSeqLeft_2531_);
    crate::leanh::lean_dec_ref(v_toApplicative_2530_);
    crate::leanh::lean_inc_n(v_a_2529_, 2);
    v___f_2532_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2532_, 0, v_a_2528_);
    crate::leanh::lean_closure_set(v___f_2532_, 1, v_a_2529_);
    v___x_2533_ = crate::leanh::lean_apply_1(v_a_2527_, v_a_2529_);
    v___x_2534_ = crate::leanh::lean_apply_4(
        v_toSeqLeft_2531_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2533_,
        v___f_2532_,
    );
    return v___x_2534_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9___redArg___boxed(
    mut v_inst_2535_: *mut crate::leanh::LeanObject,
    mut v_a_2536_: *mut crate::leanh::LeanObject,
    mut v_a_2537_: *mut crate::leanh::LeanObject,
    mut v_a_2538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Lean_MonadCacheT_instMonad___aux__9___redArg(
        v_inst_2535_,
        v_a_2536_,
        v_a_2537_,
        v_a_2538_,
    );
    crate::leanh::lean_dec(v_a_2538_);
    return v_res_2539_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9(
    mut v_00_u03c9_2540_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2541_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2542_: *mut crate::leanh::LeanObject,
    mut v_m_2543_: *mut crate::leanh::LeanObject,
    mut v_inst_2544_: *mut crate::leanh::LeanObject,
    mut v_inst_2545_: *mut crate::leanh::LeanObject,
    mut v_inst_2546_: *mut crate::leanh::LeanObject,
    mut v_inst_2547_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2548_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2549_: *mut crate::leanh::LeanObject,
    mut v_a_2550_: *mut crate::leanh::LeanObject,
    mut v_a_2551_: *mut crate::leanh::LeanObject,
    mut v_a_2552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2553_ = crate::leanh::lean_ctor_get(v_inst_2547_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2553_);
    crate::leanh::lean_dec_ref(v_inst_2547_);
    v_toSeqLeft_2554_ = crate::leanh::lean_ctor_get(v_toApplicative_2553_, 3);
    crate::leanh::lean_inc(v_toSeqLeft_2554_);
    crate::leanh::lean_dec_ref(v_toApplicative_2553_);
    crate::leanh::lean_inc_n(v_a_2552_, 2);
    v___f_2555_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2555_, 0, v_a_2551_);
    crate::leanh::lean_closure_set(v___f_2555_, 1, v_a_2552_);
    v___x_2556_ = crate::leanh::lean_apply_1(v_a_2550_, v_a_2552_);
    v___x_2557_ = crate::leanh::lean_apply_4(
        v_toSeqLeft_2554_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2556_,
        v___f_2555_,
    );
    return v___x_2557_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9___boxed(
    mut v_00_u03c9_2558_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2559_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2560_: *mut crate::leanh::LeanObject,
    mut v_m_2561_: *mut crate::leanh::LeanObject,
    mut v_inst_2562_: *mut crate::leanh::LeanObject,
    mut v_inst_2563_: *mut crate::leanh::LeanObject,
    mut v_inst_2564_: *mut crate::leanh::LeanObject,
    mut v_inst_2565_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2566_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2567_: *mut crate::leanh::LeanObject,
    mut v_a_2568_: *mut crate::leanh::LeanObject,
    mut v_a_2569_: *mut crate::leanh::LeanObject,
    mut v_a_2570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2571_ = l_Lean_MonadCacheT_instMonad___aux__9(
        v_00_u03c9_2558_,
        v_00_u03b1_2559_,
        v_00_u03b2_2560_,
        v_m_2561_,
        v_inst_2562_,
        v_inst_2563_,
        v_inst_2564_,
        v_inst_2565_,
        v_00_u03b1_2566_,
        v_00_u03b2_2567_,
        v_a_2568_,
        v_a_2569_,
        v_a_2570_,
    );
    crate::leanh::lean_dec(v_a_2570_);
    crate::leanh::lean_dec_ref(v_inst_2564_);
    crate::leanh::lean_dec_ref(v_inst_2563_);
    return v_res_2571_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11___redArg(
    mut v_inst_2572_: *mut crate::leanh::LeanObject,
    mut v_a_2573_: *mut crate::leanh::LeanObject,
    mut v_a_2574_: *mut crate::leanh::LeanObject,
    mut v_a_2575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2576_ = crate::leanh::lean_ctor_get(v_inst_2572_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2576_);
    crate::leanh::lean_dec_ref(v_inst_2572_);
    v_toSeqRight_2577_ = crate::leanh::lean_ctor_get(v_toApplicative_2576_, 4);
    crate::leanh::lean_inc(v_toSeqRight_2577_);
    crate::leanh::lean_dec_ref(v_toApplicative_2576_);
    crate::leanh::lean_inc_n(v_a_2575_, 2);
    v___f_2578_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2578_, 0, v_a_2574_);
    crate::leanh::lean_closure_set(v___f_2578_, 1, v_a_2575_);
    v___x_2579_ = crate::leanh::lean_apply_1(v_a_2573_, v_a_2575_);
    v___x_2580_ = crate::leanh::lean_apply_4(
        v_toSeqRight_2577_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2579_,
        v___f_2578_,
    );
    return v___x_2580_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11___redArg___boxed(
    mut v_inst_2581_: *mut crate::leanh::LeanObject,
    mut v_a_2582_: *mut crate::leanh::LeanObject,
    mut v_a_2583_: *mut crate::leanh::LeanObject,
    mut v_a_2584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2585_ = l_Lean_MonadCacheT_instMonad___aux__11___redArg(
        v_inst_2581_,
        v_a_2582_,
        v_a_2583_,
        v_a_2584_,
    );
    crate::leanh::lean_dec(v_a_2584_);
    return v_res_2585_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11(
    mut v_00_u03c9_2586_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2587_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2588_: *mut crate::leanh::LeanObject,
    mut v_m_2589_: *mut crate::leanh::LeanObject,
    mut v_inst_2590_: *mut crate::leanh::LeanObject,
    mut v_inst_2591_: *mut crate::leanh::LeanObject,
    mut v_inst_2592_: *mut crate::leanh::LeanObject,
    mut v_inst_2593_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2594_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2595_: *mut crate::leanh::LeanObject,
    mut v_a_2596_: *mut crate::leanh::LeanObject,
    mut v_a_2597_: *mut crate::leanh::LeanObject,
    mut v_a_2598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2599_ = crate::leanh::lean_ctor_get(v_inst_2593_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2599_);
    crate::leanh::lean_dec_ref(v_inst_2593_);
    v_toSeqRight_2600_ = crate::leanh::lean_ctor_get(v_toApplicative_2599_, 4);
    crate::leanh::lean_inc(v_toSeqRight_2600_);
    crate::leanh::lean_dec_ref(v_toApplicative_2599_);
    crate::leanh::lean_inc_n(v_a_2598_, 2);
    v___f_2601_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2601_, 0, v_a_2597_);
    crate::leanh::lean_closure_set(v___f_2601_, 1, v_a_2598_);
    v___x_2602_ = crate::leanh::lean_apply_1(v_a_2596_, v_a_2598_);
    v___x_2603_ = crate::leanh::lean_apply_4(
        v_toSeqRight_2600_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2602_,
        v___f_2601_,
    );
    return v___x_2603_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11___boxed(
    mut v_00_u03c9_2604_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2605_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2606_: *mut crate::leanh::LeanObject,
    mut v_m_2607_: *mut crate::leanh::LeanObject,
    mut v_inst_2608_: *mut crate::leanh::LeanObject,
    mut v_inst_2609_: *mut crate::leanh::LeanObject,
    mut v_inst_2610_: *mut crate::leanh::LeanObject,
    mut v_inst_2611_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2612_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2613_: *mut crate::leanh::LeanObject,
    mut v_a_2614_: *mut crate::leanh::LeanObject,
    mut v_a_2615_: *mut crate::leanh::LeanObject,
    mut v_a_2616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2617_ = l_Lean_MonadCacheT_instMonad___aux__11(
        v_00_u03c9_2604_,
        v_00_u03b1_2605_,
        v_00_u03b2_2606_,
        v_m_2607_,
        v_inst_2608_,
        v_inst_2609_,
        v_inst_2610_,
        v_inst_2611_,
        v_00_u03b1_2612_,
        v_00_u03b2_2613_,
        v_a_2614_,
        v_a_2615_,
        v_a_2616_,
    );
    crate::leanh::lean_dec(v_a_2616_);
    crate::leanh::lean_dec_ref(v_inst_2610_);
    crate::leanh::lean_dec_ref(v_inst_2609_);
    return v_res_2617_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2619_);
    v___x_2621_ = crate::leanh::lean_apply_2(v_a_2618_, v_a_2620_, v_a_2619_);
    return v___x_2621_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed(
    mut v_a_2622_: *mut crate::leanh::LeanObject,
    mut v_a_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2625_ =
        l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(v_a_2622_, v_a_2623_, v_a_2624_);
    crate::leanh::lean_dec(v_a_2623_);
    return v_res_2625_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg(
    mut v_inst_2626_: *mut crate::leanh::LeanObject,
    mut v_a_2627_: *mut crate::leanh::LeanObject,
    mut v_a_2628_: *mut crate::leanh::LeanObject,
    mut v_a_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2630_ = crate::leanh::lean_ctor_get(v_inst_2626_, 1);
    crate::leanh::lean_inc(v_toBind_2630_);
    crate::leanh::lean_dec_ref(v_inst_2626_);
    crate::leanh::lean_inc_n(v_a_2629_, 2);
    v___f_2631_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2631_, 0, v_a_2628_);
    crate::leanh::lean_closure_set(v___f_2631_, 1, v_a_2629_);
    v___x_2632_ = crate::leanh::lean_apply_1(v_a_2627_, v_a_2629_);
    v___x_2633_ = crate::leanh::lean_apply_4(
        v_toBind_2630_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2632_,
        v___f_2631_,
    );
    return v___x_2633_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg___boxed(
    mut v_inst_2634_: *mut crate::leanh::LeanObject,
    mut v_a_2635_: *mut crate::leanh::LeanObject,
    mut v_a_2636_: *mut crate::leanh::LeanObject,
    mut v_a_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2638_ = l_Lean_MonadCacheT_instMonad___aux__13___redArg(
        v_inst_2634_,
        v_a_2635_,
        v_a_2636_,
        v_a_2637_,
    );
    crate::leanh::lean_dec(v_a_2637_);
    return v_res_2638_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13(
    mut v_00_u03c9_2639_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2640_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2641_: *mut crate::leanh::LeanObject,
    mut v_m_2642_: *mut crate::leanh::LeanObject,
    mut v_inst_2643_: *mut crate::leanh::LeanObject,
    mut v_inst_2644_: *mut crate::leanh::LeanObject,
    mut v_inst_2645_: *mut crate::leanh::LeanObject,
    mut v_inst_2646_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2647_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2648_: *mut crate::leanh::LeanObject,
    mut v_a_2649_: *mut crate::leanh::LeanObject,
    mut v_a_2650_: *mut crate::leanh::LeanObject,
    mut v_a_2651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2652_ = crate::leanh::lean_ctor_get(v_inst_2646_, 1);
    crate::leanh::lean_inc(v_toBind_2652_);
    crate::leanh::lean_dec_ref(v_inst_2646_);
    crate::leanh::lean_inc_n(v_a_2651_, 2);
    v___f_2653_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2653_, 0, v_a_2650_);
    crate::leanh::lean_closure_set(v___f_2653_, 1, v_a_2651_);
    v___x_2654_ = crate::leanh::lean_apply_1(v_a_2649_, v_a_2651_);
    v___x_2655_ = crate::leanh::lean_apply_4(
        v_toBind_2652_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2654_,
        v___f_2653_,
    );
    return v___x_2655_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___boxed(
    mut v_00_u03c9_2656_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2657_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2658_: *mut crate::leanh::LeanObject,
    mut v_m_2659_: *mut crate::leanh::LeanObject,
    mut v_inst_2660_: *mut crate::leanh::LeanObject,
    mut v_inst_2661_: *mut crate::leanh::LeanObject,
    mut v_inst_2662_: *mut crate::leanh::LeanObject,
    mut v_inst_2663_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2664_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2665_: *mut crate::leanh::LeanObject,
    mut v_a_2666_: *mut crate::leanh::LeanObject,
    mut v_a_2667_: *mut crate::leanh::LeanObject,
    mut v_a_2668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2669_ = l_Lean_MonadCacheT_instMonad___aux__13(
        v_00_u03c9_2656_,
        v_00_u03b1_2657_,
        v_00_u03b2_2658_,
        v_m_2659_,
        v_inst_2660_,
        v_inst_2661_,
        v_inst_2662_,
        v_inst_2663_,
        v_00_u03b1_2664_,
        v_00_u03b2_2665_,
        v_a_2666_,
        v_a_2667_,
        v_a_2668_,
    );
    crate::leanh::lean_dec(v_a_2668_);
    crate::leanh::lean_dec_ref(v_inst_2662_);
    crate::leanh::lean_dec_ref(v_inst_2661_);
    return v_res_2669_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___redArg(
    mut v_inst_2670_: *mut crate::leanh::LeanObject,
    mut v_inst_2671_: *mut crate::leanh::LeanObject,
    mut v_inst_2672_: *mut crate::leanh::LeanObject,
    mut v_inst_2673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_2673_, 6);
    crate::leanh::lean_inc_ref_n(v_inst_2672_, 6);
    crate::leanh::lean_inc_ref_n(v_inst_2671_, 6);
    v___x_2674_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__1___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    crate::leanh::lean_closure_set(v___x_2674_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2674_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2674_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2674_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2674_, 4, v_inst_2670_);
    crate::leanh::lean_closure_set(v___x_2674_, 5, v_inst_2671_);
    crate::leanh::lean_closure_set(v___x_2674_, 6, v_inst_2672_);
    crate::leanh::lean_closure_set(v___x_2674_, 7, v_inst_2673_);
    v___x_2675_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__3___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    crate::leanh::lean_closure_set(v___x_2675_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2675_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2675_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2675_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2675_, 4, v_inst_2670_);
    crate::leanh::lean_closure_set(v___x_2675_, 5, v_inst_2671_);
    crate::leanh::lean_closure_set(v___x_2675_, 6, v_inst_2672_);
    crate::leanh::lean_closure_set(v___x_2675_, 7, v_inst_2673_);
    v___x_2676_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2676_, 0, v___x_2674_);
    crate::leanh::lean_ctor_set(v___x_2676_, 1, v___x_2675_);
    v___x_2677_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__5___boxed as *mut core::ffi::c_void,
        11,
        8,
    );
    crate::leanh::lean_closure_set(v___x_2677_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2677_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2677_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2677_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2677_, 4, v_inst_2670_);
    crate::leanh::lean_closure_set(v___x_2677_, 5, v_inst_2671_);
    crate::leanh::lean_closure_set(v___x_2677_, 6, v_inst_2672_);
    crate::leanh::lean_closure_set(v___x_2677_, 7, v_inst_2673_);
    v___x_2678_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    crate::leanh::lean_closure_set(v___x_2678_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2678_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2678_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2678_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2678_, 4, v_inst_2670_);
    crate::leanh::lean_closure_set(v___x_2678_, 5, v_inst_2671_);
    crate::leanh::lean_closure_set(v___x_2678_, 6, v_inst_2672_);
    crate::leanh::lean_closure_set(v___x_2678_, 7, v_inst_2673_);
    v___x_2679_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__9___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    crate::leanh::lean_closure_set(v___x_2679_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2679_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2679_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2679_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2679_, 4, v_inst_2670_);
    crate::leanh::lean_closure_set(v___x_2679_, 5, v_inst_2671_);
    crate::leanh::lean_closure_set(v___x_2679_, 6, v_inst_2672_);
    crate::leanh::lean_closure_set(v___x_2679_, 7, v_inst_2673_);
    v___x_2680_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__11___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    crate::leanh::lean_closure_set(v___x_2680_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2680_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2680_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2680_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2680_, 4, v_inst_2670_);
    crate::leanh::lean_closure_set(v___x_2680_, 5, v_inst_2671_);
    crate::leanh::lean_closure_set(v___x_2680_, 6, v_inst_2672_);
    crate::leanh::lean_closure_set(v___x_2680_, 7, v_inst_2673_);
    v___x_2681_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2681_, 0, v___x_2676_);
    crate::leanh::lean_ctor_set(v___x_2681_, 1, v___x_2677_);
    crate::leanh::lean_ctor_set(v___x_2681_, 2, v___x_2678_);
    crate::leanh::lean_ctor_set(v___x_2681_, 3, v___x_2679_);
    crate::leanh::lean_ctor_set(v___x_2681_, 4, v___x_2680_);
    v___x_2682_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    crate::leanh::lean_closure_set(v___x_2682_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2682_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2682_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2682_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2682_, 4, v_inst_2670_);
    crate::leanh::lean_closure_set(v___x_2682_, 5, v_inst_2671_);
    crate::leanh::lean_closure_set(v___x_2682_, 6, v_inst_2672_);
    crate::leanh::lean_closure_set(v___x_2682_, 7, v_inst_2673_);
    v___x_2683_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2683_, 0, v___x_2681_);
    crate::leanh::lean_ctor_set(v___x_2683_, 1, v___x_2682_);
    return v___x_2683_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad(
    mut v_00_u03c9_2684_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2685_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2686_: *mut crate::leanh::LeanObject,
    mut v_m_2687_: *mut crate::leanh::LeanObject,
    mut v_inst_2688_: *mut crate::leanh::LeanObject,
    mut v_inst_2689_: *mut crate::leanh::LeanObject,
    mut v_inst_2690_: *mut crate::leanh::LeanObject,
    mut v_inst_2691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2692_ = l_Lean_MonadCacheT_instMonad___redArg(
        v_inst_2688_,
        v_inst_2689_,
        v_inst_2690_,
        v_inst_2691_,
    );
    return v___x_2692_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1___redArg(
    mut v_x_2693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_2693_);
    return v_x_2693_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1___redArg___boxed(
    mut v_x_2694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2695_ = l_Lean_MonadCacheT_instMonadLift___aux__1___redArg(v_x_2694_);
    crate::leanh::lean_dec(v_x_2694_);
    return v_res_2695_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1(
    mut v_00_u03c9_2696_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2697_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2698_: *mut crate::leanh::LeanObject,
    mut v_m_2699_: *mut crate::leanh::LeanObject,
    mut v_inst_2700_: *mut crate::leanh::LeanObject,
    mut v_inst_2701_: *mut crate::leanh::LeanObject,
    mut v_inst_2702_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2703_: *mut crate::leanh::LeanObject,
    mut v_x_2704_: *mut crate::leanh::LeanObject,
    mut v_a_2705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_2704_);
    return v_x_2704_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1___boxed(
    mut v_00_u03c9_2706_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2707_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2708_: *mut crate::leanh::LeanObject,
    mut v_m_2709_: *mut crate::leanh::LeanObject,
    mut v_inst_2710_: *mut crate::leanh::LeanObject,
    mut v_inst_2711_: *mut crate::leanh::LeanObject,
    mut v_inst_2712_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2713_: *mut crate::leanh::LeanObject,
    mut v_x_2714_: *mut crate::leanh::LeanObject,
    mut v_a_2715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2716_ = l_Lean_MonadCacheT_instMonadLift___aux__1(
        v_00_u03c9_2706_,
        v_00_u03b1_2707_,
        v_00_u03b2_2708_,
        v_m_2709_,
        v_inst_2710_,
        v_inst_2711_,
        v_inst_2712_,
        v_00_u03b1_2713_,
        v_x_2714_,
        v_a_2715_,
    );
    crate::leanh::lean_dec(v_a_2715_);
    crate::leanh::lean_dec(v_x_2714_);
    crate::leanh::lean_dec_ref(v_inst_2712_);
    crate::leanh::lean_dec_ref(v_inst_2711_);
    return v_res_2716_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___redArg(
    mut v_inst_2717_: *mut crate::leanh::LeanObject,
    mut v_inst_2718_: *mut crate::leanh::LeanObject,
    mut v_inst_2719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2720_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    crate::leanh::lean_closure_set(v___x_2720_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2720_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2720_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2720_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2720_, 4, v_inst_2717_);
    crate::leanh::lean_closure_set(v___x_2720_, 5, v_inst_2718_);
    crate::leanh::lean_closure_set(v___x_2720_, 6, v_inst_2719_);
    return v___x_2720_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift(
    mut v_00_u03c9_2721_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2722_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2723_: *mut crate::leanh::LeanObject,
    mut v_m_2724_: *mut crate::leanh::LeanObject,
    mut v_inst_2725_: *mut crate::leanh::LeanObject,
    mut v_inst_2726_: *mut crate::leanh::LeanObject,
    mut v_inst_2727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2728_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    crate::leanh::lean_closure_set(v___x_2728_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2728_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2728_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2728_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2728_, 4, v_inst_2725_);
    crate::leanh::lean_closure_set(v___x_2728_, 5, v_inst_2726_);
    crate::leanh::lean_closure_set(v___x_2728_, 6, v_inst_2727_);
    return v___x_2728_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__1___redArg(
    mut v_inst_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_2731_ = crate::leanh::lean_ctor_get(v_inst_2729_, 0);
    crate::leanh::lean_inc(v_throw_2731_);
    crate::leanh::lean_dec_ref(v_inst_2729_);
    v___x_2732_ = crate::leanh::lean_apply_2(v_throw_2731_, crate::leanh::lean_box(0), v_a_2730_);
    return v___x_2732_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__1(
    mut v_00_u03c9_2733_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2734_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2735_: *mut crate::leanh::LeanObject,
    mut v_m_2736_: *mut crate::leanh::LeanObject,
    mut v_inst_2737_: *mut crate::leanh::LeanObject,
    mut v_inst_2738_: *mut crate::leanh::LeanObject,
    mut v_inst_2739_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2740_: *mut crate::leanh::LeanObject,
    mut v_inst_2741_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2742_: *mut crate::leanh::LeanObject,
    mut v_a_2743_: *mut crate::leanh::LeanObject,
    mut v_a_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_2745_ = crate::leanh::lean_ctor_get(v_inst_2741_, 0);
    crate::leanh::lean_inc(v_throw_2745_);
    crate::leanh::lean_dec_ref(v_inst_2741_);
    v___x_2746_ = crate::leanh::lean_apply_2(v_throw_2745_, crate::leanh::lean_box(0), v_a_2743_);
    return v___x_2746_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__1___boxed(
    mut v_00_u03c9_2747_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2748_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2749_: *mut crate::leanh::LeanObject,
    mut v_m_2750_: *mut crate::leanh::LeanObject,
    mut v_inst_2751_: *mut crate::leanh::LeanObject,
    mut v_inst_2752_: *mut crate::leanh::LeanObject,
    mut v_inst_2753_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2754_: *mut crate::leanh::LeanObject,
    mut v_inst_2755_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2756_: *mut crate::leanh::LeanObject,
    mut v_a_2757_: *mut crate::leanh::LeanObject,
    mut v_a_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2759_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__1(
        v_00_u03c9_2747_,
        v_00_u03b1_2748_,
        v_00_u03b2_2749_,
        v_m_2750_,
        v_inst_2751_,
        v_inst_2752_,
        v_inst_2753_,
        v_00_u03b5_2754_,
        v_inst_2755_,
        v_00_u03b1_2756_,
        v_a_2757_,
        v_a_2758_,
    );
    crate::leanh::lean_dec(v_a_2758_);
    crate::leanh::lean_dec_ref(v_inst_2753_);
    crate::leanh::lean_dec_ref(v_inst_2752_);
    return v_res_2759_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0(
    mut v_c_2760_: *mut crate::leanh::LeanObject,
    mut v_s_2761_: *mut crate::leanh::LeanObject,
    mut v_e_2762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_s_2761_);
    v___x_2763_ = crate::leanh::lean_apply_2(v_c_2760_, v_e_2762_, v_s_2761_);
    return v___x_2763_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed(
    mut v_c_2764_: *mut crate::leanh::LeanObject,
    mut v_s_2765_: *mut crate::leanh::LeanObject,
    mut v_e_2766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0(
        v_c_2764_, v_s_2765_, v_e_2766_,
    );
    crate::leanh::lean_dec(v_s_2765_);
    return v_res_2767_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg(
    mut v_inst_2768_: *mut crate::leanh::LeanObject,
    mut v_x_2769_: *mut crate::leanh::LeanObject,
    mut v_c_2770_: *mut crate::leanh::LeanObject,
    mut v_s_2771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_2772_ = crate::leanh::lean_ctor_get(v_inst_2768_, 1);
    crate::leanh::lean_inc(v_tryCatch_2772_);
    crate::leanh::lean_dec_ref(v_inst_2768_);
    crate::leanh::lean_inc_n(v_s_2771_, 2);
    v___f_2773_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2773_, 0, v_c_2770_);
    crate::leanh::lean_closure_set(v___f_2773_, 1, v_s_2771_);
    v___x_2774_ = crate::leanh::lean_apply_1(v_x_2769_, v_s_2771_);
    v___x_2775_ = crate::leanh::lean_apply_3(
        v_tryCatch_2772_,
        crate::leanh::lean_box(0),
        v___x_2774_,
        v___f_2773_,
    );
    return v___x_2775_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___boxed(
    mut v_inst_2776_: *mut crate::leanh::LeanObject,
    mut v_x_2777_: *mut crate::leanh::LeanObject,
    mut v_c_2778_: *mut crate::leanh::LeanObject,
    mut v_s_2779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2780_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg(
        v_inst_2776_,
        v_x_2777_,
        v_c_2778_,
        v_s_2779_,
    );
    crate::leanh::lean_dec(v_s_2779_);
    return v_res_2780_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3(
    mut v_00_u03c9_2781_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2782_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2783_: *mut crate::leanh::LeanObject,
    mut v_m_2784_: *mut crate::leanh::LeanObject,
    mut v_inst_2785_: *mut crate::leanh::LeanObject,
    mut v_inst_2786_: *mut crate::leanh::LeanObject,
    mut v_inst_2787_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2788_: *mut crate::leanh::LeanObject,
    mut v_inst_2789_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2790_: *mut crate::leanh::LeanObject,
    mut v_x_2791_: *mut crate::leanh::LeanObject,
    mut v_c_2792_: *mut crate::leanh::LeanObject,
    mut v_s_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_2794_ = crate::leanh::lean_ctor_get(v_inst_2789_, 1);
    crate::leanh::lean_inc(v_tryCatch_2794_);
    crate::leanh::lean_dec_ref(v_inst_2789_);
    crate::leanh::lean_inc_n(v_s_2793_, 2);
    v___f_2795_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2795_, 0, v_c_2792_);
    crate::leanh::lean_closure_set(v___f_2795_, 1, v_s_2793_);
    v___x_2796_ = crate::leanh::lean_apply_1(v_x_2791_, v_s_2793_);
    v___x_2797_ = crate::leanh::lean_apply_3(
        v_tryCatch_2794_,
        crate::leanh::lean_box(0),
        v___x_2796_,
        v___f_2795_,
    );
    return v___x_2797_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___boxed(
    mut v_00_u03c9_2798_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2799_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2800_: *mut crate::leanh::LeanObject,
    mut v_m_2801_: *mut crate::leanh::LeanObject,
    mut v_inst_2802_: *mut crate::leanh::LeanObject,
    mut v_inst_2803_: *mut crate::leanh::LeanObject,
    mut v_inst_2804_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2805_: *mut crate::leanh::LeanObject,
    mut v_inst_2806_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2807_: *mut crate::leanh::LeanObject,
    mut v_x_2808_: *mut crate::leanh::LeanObject,
    mut v_c_2809_: *mut crate::leanh::LeanObject,
    mut v_s_2810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2811_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3(
        v_00_u03c9_2798_,
        v_00_u03b1_2799_,
        v_00_u03b2_2800_,
        v_m_2801_,
        v_inst_2802_,
        v_inst_2803_,
        v_inst_2804_,
        v_00_u03b5_2805_,
        v_inst_2806_,
        v_00_u03b1_2807_,
        v_x_2808_,
        v_c_2809_,
        v_s_2810_,
    );
    crate::leanh::lean_dec(v_s_2810_);
    crate::leanh::lean_dec_ref(v_inst_2804_);
    crate::leanh::lean_dec_ref(v_inst_2803_);
    return v_res_2811_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___redArg(
    mut v_inst_2812_: *mut crate::leanh::LeanObject,
    mut v_inst_2813_: *mut crate::leanh::LeanObject,
    mut v_inst_2814_: *mut crate::leanh::LeanObject,
    mut v_inst_2815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_2815_);
    crate::leanh::lean_inc_ref(v_inst_2814_);
    crate::leanh::lean_inc_ref(v_inst_2813_);
    v___x_2816_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__1___boxed as *mut core::ffi::c_void,
        12,
        9,
    );
    crate::leanh::lean_closure_set(v___x_2816_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2816_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2816_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2816_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2816_, 4, v_inst_2812_);
    crate::leanh::lean_closure_set(v___x_2816_, 5, v_inst_2813_);
    crate::leanh::lean_closure_set(v___x_2816_, 6, v_inst_2814_);
    crate::leanh::lean_closure_set(v___x_2816_, 7, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2816_, 8, v_inst_2815_);
    v___x_2817_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__3___boxed as *mut core::ffi::c_void,
        13,
        9,
    );
    crate::leanh::lean_closure_set(v___x_2817_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2817_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2817_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2817_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2817_, 4, v_inst_2812_);
    crate::leanh::lean_closure_set(v___x_2817_, 5, v_inst_2813_);
    crate::leanh::lean_closure_set(v___x_2817_, 6, v_inst_2814_);
    crate::leanh::lean_closure_set(v___x_2817_, 7, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2817_, 8, v_inst_2815_);
    v___x_2818_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2818_, 0, v___x_2816_);
    crate::leanh::lean_ctor_set(v___x_2818_, 1, v___x_2817_);
    return v___x_2818_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf(
    mut v_00_u03c9_2819_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2820_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2821_: *mut crate::leanh::LeanObject,
    mut v_m_2822_: *mut crate::leanh::LeanObject,
    mut v_inst_2823_: *mut crate::leanh::LeanObject,
    mut v_inst_2824_: *mut crate::leanh::LeanObject,
    mut v_inst_2825_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2826_: *mut crate::leanh::LeanObject,
    mut v_inst_2827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2828_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(
        v_inst_2823_,
        v_inst_2824_,
        v_inst_2825_,
        v_inst_2827_,
    );
    return v___x_2828_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0(
    mut v_a_2829_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2830_: *mut crate::leanh::LeanObject,
    mut v_x_2831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2829_);
    v___x_2832_ = crate::leanh::lean_apply_1(v_x_2831_, v_a_2829_);
    return v___x_2832_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed(
    mut v_a_2833_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2834_: *mut crate::leanh::LeanObject,
    mut v_x_2835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2836_ = l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0(
        v_a_2833_,
        v_00_u03b2_2834_,
        v_x_2835_,
    );
    crate::leanh::lean_dec(v_a_2833_);
    return v_res_2836_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg(
    mut v_a_2837_: *mut crate::leanh::LeanObject,
    mut v_a_2838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2838_);
    v___f_2839_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2839_, 0, v_a_2838_);
    v___x_2840_ = crate::leanh::lean_apply_1(v_a_2837_, v___f_2839_);
    return v___x_2840_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___boxed(
    mut v_a_2841_: *mut crate::leanh::LeanObject,
    mut v_a_2842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2843_ = l_Lean_MonadCacheT_instMonadControl___aux__1___redArg(v_a_2841_, v_a_2842_);
    crate::leanh::lean_dec(v_a_2842_);
    return v_res_2843_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1(
    mut v_00_u03c9_2844_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2845_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2846_: *mut crate::leanh::LeanObject,
    mut v_m_2847_: *mut crate::leanh::LeanObject,
    mut v_inst_2848_: *mut crate::leanh::LeanObject,
    mut v_inst_2849_: *mut crate::leanh::LeanObject,
    mut v_inst_2850_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2851_: *mut crate::leanh::LeanObject,
    mut v_a_2852_: *mut crate::leanh::LeanObject,
    mut v_a_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2853_);
    v___f_2854_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2854_, 0, v_a_2853_);
    v___x_2855_ = crate::leanh::lean_apply_1(v_a_2852_, v___f_2854_);
    return v___x_2855_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___boxed(
    mut v_00_u03c9_2856_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2857_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2858_: *mut crate::leanh::LeanObject,
    mut v_m_2859_: *mut crate::leanh::LeanObject,
    mut v_inst_2860_: *mut crate::leanh::LeanObject,
    mut v_inst_2861_: *mut crate::leanh::LeanObject,
    mut v_inst_2862_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2863_: *mut crate::leanh::LeanObject,
    mut v_a_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2866_ = l_Lean_MonadCacheT_instMonadControl___aux__1(
        v_00_u03c9_2856_,
        v_00_u03b1_2857_,
        v_00_u03b2_2858_,
        v_m_2859_,
        v_inst_2860_,
        v_inst_2861_,
        v_inst_2862_,
        v_00_u03b1_2863_,
        v_a_2864_,
        v_a_2865_,
    );
    crate::leanh::lean_dec(v_a_2865_);
    crate::leanh::lean_dec_ref(v_inst_2862_);
    crate::leanh::lean_dec_ref(v_inst_2861_);
    return v_res_2866_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3___redArg(
    mut v_a_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_2867_);
    return v_a_2867_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3___redArg___boxed(
    mut v_a_2868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2869_ = l_Lean_MonadCacheT_instMonadControl___aux__3___redArg(v_a_2868_);
    crate::leanh::lean_dec(v_a_2868_);
    return v_res_2869_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3(
    mut v_00_u03c9_2870_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2871_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2872_: *mut crate::leanh::LeanObject,
    mut v_m_2873_: *mut crate::leanh::LeanObject,
    mut v_inst_2874_: *mut crate::leanh::LeanObject,
    mut v_inst_2875_: *mut crate::leanh::LeanObject,
    mut v_inst_2876_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2877_: *mut crate::leanh::LeanObject,
    mut v_a_2878_: *mut crate::leanh::LeanObject,
    mut v_a_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_2878_);
    return v_a_2878_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3___boxed(
    mut v_00_u03c9_2880_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2881_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2882_: *mut crate::leanh::LeanObject,
    mut v_m_2883_: *mut crate::leanh::LeanObject,
    mut v_inst_2884_: *mut crate::leanh::LeanObject,
    mut v_inst_2885_: *mut crate::leanh::LeanObject,
    mut v_inst_2886_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2887_: *mut crate::leanh::LeanObject,
    mut v_a_2888_: *mut crate::leanh::LeanObject,
    mut v_a_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2890_ = l_Lean_MonadCacheT_instMonadControl___aux__3(
        v_00_u03c9_2880_,
        v_00_u03b1_2881_,
        v_00_u03b2_2882_,
        v_m_2883_,
        v_inst_2884_,
        v_inst_2885_,
        v_inst_2886_,
        v_00_u03b1_2887_,
        v_a_2888_,
        v_a_2889_,
    );
    crate::leanh::lean_dec(v_a_2889_);
    crate::leanh::lean_dec(v_a_2888_);
    crate::leanh::lean_dec_ref(v_inst_2886_);
    crate::leanh::lean_dec_ref(v_inst_2885_);
    return v_res_2890_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___redArg(
    mut v_inst_2891_: *mut crate::leanh::LeanObject,
    mut v_inst_2892_: *mut crate::leanh::LeanObject,
    mut v_inst_2893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_2893_);
    crate::leanh::lean_inc_ref(v_inst_2892_);
    v___x_2894_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__1___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    crate::leanh::lean_closure_set(v___x_2894_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2894_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2894_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2894_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2894_, 4, v_inst_2891_);
    crate::leanh::lean_closure_set(v___x_2894_, 5, v_inst_2892_);
    crate::leanh::lean_closure_set(v___x_2894_, 6, v_inst_2893_);
    v___x_2895_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__3___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    crate::leanh::lean_closure_set(v___x_2895_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2895_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2895_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2895_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2895_, 4, v_inst_2891_);
    crate::leanh::lean_closure_set(v___x_2895_, 5, v_inst_2892_);
    crate::leanh::lean_closure_set(v___x_2895_, 6, v_inst_2893_);
    v___x_2896_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2896_, 0, v___x_2894_);
    crate::leanh::lean_ctor_set(v___x_2896_, 1, v___x_2895_);
    return v___x_2896_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl(
    mut v_00_u03c9_2897_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2898_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2899_: *mut crate::leanh::LeanObject,
    mut v_m_2900_: *mut crate::leanh::LeanObject,
    mut v_inst_2901_: *mut crate::leanh::LeanObject,
    mut v_inst_2902_: *mut crate::leanh::LeanObject,
    mut v_inst_2903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2904_ =
        l_Lean_MonadCacheT_instMonadControl___redArg(v_inst_2901_, v_inst_2902_, v_inst_2903_);
    return v___x_2904_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0(
    mut v_f_2905_: *mut crate::leanh::LeanObject,
    mut v_a_2906_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2906_);
    v___x_2908_ = crate::leanh::lean_apply_2(v_f_2905_, v_a_x3f_2907_, v_a_2906_);
    return v___x_2908_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed(
    mut v_f_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2912_ = l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0(
        v_f_2909_,
        v_a_2910_,
        v_a_x3f_2911_,
    );
    crate::leanh::lean_dec(v_a_2910_);
    return v_res_2912_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg(
    mut v_inst_2913_: *mut crate::leanh::LeanObject,
    mut v_x_2914_: *mut crate::leanh::LeanObject,
    mut v_f_2915_: *mut crate::leanh::LeanObject,
    mut v_a_2916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_a_2916_, 2);
    v___f_2917_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2917_, 0, v_f_2915_);
    crate::leanh::lean_closure_set(v___f_2917_, 1, v_a_2916_);
    v___x_2918_ = crate::leanh::lean_apply_1(v_x_2914_, v_a_2916_);
    v___x_2919_ = crate::leanh::lean_apply_4(
        v_inst_2913_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2918_,
        v___f_2917_,
    );
    return v___x_2919_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___boxed(
    mut v_inst_2920_: *mut crate::leanh::LeanObject,
    mut v_x_2921_: *mut crate::leanh::LeanObject,
    mut v_f_2922_: *mut crate::leanh::LeanObject,
    mut v_a_2923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2924_ = l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg(
        v_inst_2920_,
        v_x_2921_,
        v_f_2922_,
        v_a_2923_,
    );
    crate::leanh::lean_dec(v_a_2923_);
    return v_res_2924_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1(
    mut v_00_u03c9_2925_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2926_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2927_: *mut crate::leanh::LeanObject,
    mut v_m_2928_: *mut crate::leanh::LeanObject,
    mut v_inst_2929_: *mut crate::leanh::LeanObject,
    mut v_inst_2930_: *mut crate::leanh::LeanObject,
    mut v_inst_2931_: *mut crate::leanh::LeanObject,
    mut v_inst_2932_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2933_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2934_: *mut crate::leanh::LeanObject,
    mut v_x_2935_: *mut crate::leanh::LeanObject,
    mut v_f_2936_: *mut crate::leanh::LeanObject,
    mut v_a_2937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_a_2937_, 2);
    v___f_2938_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2938_, 0, v_f_2936_);
    crate::leanh::lean_closure_set(v___f_2938_, 1, v_a_2937_);
    v___x_2939_ = crate::leanh::lean_apply_1(v_x_2935_, v_a_2937_);
    v___x_2940_ = crate::leanh::lean_apply_4(
        v_inst_2932_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2939_,
        v___f_2938_,
    );
    return v___x_2940_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed(
    mut v_00_u03c9_2941_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2942_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2943_: *mut crate::leanh::LeanObject,
    mut v_m_2944_: *mut crate::leanh::LeanObject,
    mut v_inst_2945_: *mut crate::leanh::LeanObject,
    mut v_inst_2946_: *mut crate::leanh::LeanObject,
    mut v_inst_2947_: *mut crate::leanh::LeanObject,
    mut v_inst_2948_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2949_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2950_: *mut crate::leanh::LeanObject,
    mut v_x_2951_: *mut crate::leanh::LeanObject,
    mut v_f_2952_: *mut crate::leanh::LeanObject,
    mut v_a_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2954_ = l_Lean_MonadCacheT_instMonadFinally___aux__1(
        v_00_u03c9_2941_,
        v_00_u03b1_2942_,
        v_00_u03b2_2943_,
        v_m_2944_,
        v_inst_2945_,
        v_inst_2946_,
        v_inst_2947_,
        v_inst_2948_,
        v_00_u03b1_2949_,
        v_00_u03b2_2950_,
        v_x_2951_,
        v_f_2952_,
        v_a_2953_,
    );
    crate::leanh::lean_dec(v_a_2953_);
    crate::leanh::lean_dec_ref(v_inst_2947_);
    crate::leanh::lean_dec_ref(v_inst_2946_);
    return v_res_2954_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___redArg(
    mut v_inst_2955_: *mut crate::leanh::LeanObject,
    mut v_inst_2956_: *mut crate::leanh::LeanObject,
    mut v_inst_2957_: *mut crate::leanh::LeanObject,
    mut v_inst_2958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2959_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    crate::leanh::lean_closure_set(v___x_2959_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2959_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2959_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2959_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2959_, 4, v_inst_2955_);
    crate::leanh::lean_closure_set(v___x_2959_, 5, v_inst_2956_);
    crate::leanh::lean_closure_set(v___x_2959_, 6, v_inst_2957_);
    crate::leanh::lean_closure_set(v___x_2959_, 7, v_inst_2958_);
    return v___x_2959_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally(
    mut v_00_u03c9_2960_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2961_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2962_: *mut crate::leanh::LeanObject,
    mut v_m_2963_: *mut crate::leanh::LeanObject,
    mut v_inst_2964_: *mut crate::leanh::LeanObject,
    mut v_inst_2965_: *mut crate::leanh::LeanObject,
    mut v_inst_2966_: *mut crate::leanh::LeanObject,
    mut v_inst_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2968_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    crate::leanh::lean_closure_set(v___x_2968_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2968_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2968_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2968_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2968_, 4, v_inst_2964_);
    crate::leanh::lean_closure_set(v___x_2968_, 5, v_inst_2965_);
    crate::leanh::lean_closure_set(v___x_2968_, 6, v_inst_2966_);
    crate::leanh::lean_closure_set(v___x_2968_, 7, v_inst_2967_);
    return v___x_2968_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1___redArg(
    mut v_inst_2969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRef_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getRef_2970_ = crate::leanh::lean_ctor_get(v_inst_2969_, 0);
    crate::leanh::lean_inc(v_getRef_2970_);
    return v_getRef_2970_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1___redArg___boxed(
    mut v_inst_2971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2972_ = l_Lean_MonadCacheT_instMonadRef___aux__1___redArg(v_inst_2971_);
    crate::leanh::lean_dec_ref(v_inst_2971_);
    return v_res_2972_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1(
    mut v_00_u03c9_2973_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2974_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2975_: *mut crate::leanh::LeanObject,
    mut v_m_2976_: *mut crate::leanh::LeanObject,
    mut v_inst_2977_: *mut crate::leanh::LeanObject,
    mut v_inst_2978_: *mut crate::leanh::LeanObject,
    mut v_inst_2979_: *mut crate::leanh::LeanObject,
    mut v_inst_2980_: *mut crate::leanh::LeanObject,
    mut v_a_2981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRef_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getRef_2982_ = crate::leanh::lean_ctor_get(v_inst_2980_, 0);
    crate::leanh::lean_inc(v_getRef_2982_);
    return v_getRef_2982_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1___boxed(
    mut v_00_u03c9_2983_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2984_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2985_: *mut crate::leanh::LeanObject,
    mut v_m_2986_: *mut crate::leanh::LeanObject,
    mut v_inst_2987_: *mut crate::leanh::LeanObject,
    mut v_inst_2988_: *mut crate::leanh::LeanObject,
    mut v_inst_2989_: *mut crate::leanh::LeanObject,
    mut v_inst_2990_: *mut crate::leanh::LeanObject,
    mut v_a_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2992_ = l_Lean_MonadCacheT_instMonadRef___aux__1(
        v_00_u03c9_2983_,
        v_00_u03b1_2984_,
        v_00_u03b2_2985_,
        v_m_2986_,
        v_inst_2987_,
        v_inst_2988_,
        v_inst_2989_,
        v_inst_2990_,
        v_a_2991_,
    );
    crate::leanh::lean_dec(v_a_2991_);
    crate::leanh::lean_dec_ref(v_inst_2990_);
    crate::leanh::lean_dec_ref(v_inst_2989_);
    crate::leanh::lean_dec_ref(v_inst_2988_);
    return v_res_2992_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3___redArg(
    mut v_inst_2993_: *mut crate::leanh::LeanObject,
    mut v_ref_2994_: *mut crate::leanh::LeanObject,
    mut v_x_2995_: *mut crate::leanh::LeanObject,
    mut v_a_2996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_withRef_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_withRef_2997_ = crate::leanh::lean_ctor_get(v_inst_2993_, 1);
    crate::leanh::lean_inc(v_withRef_2997_);
    crate::leanh::lean_dec_ref(v_inst_2993_);
    crate::leanh::lean_inc(v_a_2996_);
    v___x_2998_ = crate::leanh::lean_apply_1(v_x_2995_, v_a_2996_);
    v___x_2999_ = crate::leanh::lean_apply_3(
        v_withRef_2997_,
        crate::leanh::lean_box(0),
        v_ref_2994_,
        v___x_2998_,
    );
    return v___x_2999_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3___redArg___boxed(
    mut v_inst_3000_: *mut crate::leanh::LeanObject,
    mut v_ref_3001_: *mut crate::leanh::LeanObject,
    mut v_x_3002_: *mut crate::leanh::LeanObject,
    mut v_a_3003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3004_ = l_Lean_MonadCacheT_instMonadRef___aux__3___redArg(
        v_inst_3000_,
        v_ref_3001_,
        v_x_3002_,
        v_a_3003_,
    );
    crate::leanh::lean_dec(v_a_3003_);
    return v_res_3004_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3(
    mut v_00_u03c9_3005_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3006_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3007_: *mut crate::leanh::LeanObject,
    mut v_m_3008_: *mut crate::leanh::LeanObject,
    mut v_inst_3009_: *mut crate::leanh::LeanObject,
    mut v_inst_3010_: *mut crate::leanh::LeanObject,
    mut v_inst_3011_: *mut crate::leanh::LeanObject,
    mut v_inst_3012_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3013_: *mut crate::leanh::LeanObject,
    mut v_ref_3014_: *mut crate::leanh::LeanObject,
    mut v_x_3015_: *mut crate::leanh::LeanObject,
    mut v_a_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_withRef_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_withRef_3017_ = crate::leanh::lean_ctor_get(v_inst_3012_, 1);
    crate::leanh::lean_inc(v_withRef_3017_);
    crate::leanh::lean_dec_ref(v_inst_3012_);
    crate::leanh::lean_inc(v_a_3016_);
    v___x_3018_ = crate::leanh::lean_apply_1(v_x_3015_, v_a_3016_);
    v___x_3019_ = crate::leanh::lean_apply_3(
        v_withRef_3017_,
        crate::leanh::lean_box(0),
        v_ref_3014_,
        v___x_3018_,
    );
    return v___x_3019_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3___boxed(
    mut v_00_u03c9_3020_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3021_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3022_: *mut crate::leanh::LeanObject,
    mut v_m_3023_: *mut crate::leanh::LeanObject,
    mut v_inst_3024_: *mut crate::leanh::LeanObject,
    mut v_inst_3025_: *mut crate::leanh::LeanObject,
    mut v_inst_3026_: *mut crate::leanh::LeanObject,
    mut v_inst_3027_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3028_: *mut crate::leanh::LeanObject,
    mut v_ref_3029_: *mut crate::leanh::LeanObject,
    mut v_x_3030_: *mut crate::leanh::LeanObject,
    mut v_a_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3032_ = l_Lean_MonadCacheT_instMonadRef___aux__3(
        v_00_u03c9_3020_,
        v_00_u03b1_3021_,
        v_00_u03b2_3022_,
        v_m_3023_,
        v_inst_3024_,
        v_inst_3025_,
        v_inst_3026_,
        v_inst_3027_,
        v_00_u03b1_3028_,
        v_ref_3029_,
        v_x_3030_,
        v_a_3031_,
    );
    crate::leanh::lean_dec(v_a_3031_);
    crate::leanh::lean_dec_ref(v_inst_3026_);
    crate::leanh::lean_dec_ref(v_inst_3025_);
    return v_res_3032_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___redArg(
    mut v_inst_3033_: *mut crate::leanh::LeanObject,
    mut v_inst_3034_: *mut crate::leanh::LeanObject,
    mut v_inst_3035_: *mut crate::leanh::LeanObject,
    mut v_inst_3036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_3036_);
    crate::leanh::lean_inc_ref(v_inst_3035_);
    crate::leanh::lean_inc_ref(v_inst_3034_);
    v___x_3037_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadRef___aux__1___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___x_3037_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3037_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3037_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3037_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3037_, 4, v_inst_3033_);
    crate::leanh::lean_closure_set(v___x_3037_, 5, v_inst_3034_);
    crate::leanh::lean_closure_set(v___x_3037_, 6, v_inst_3035_);
    crate::leanh::lean_closure_set(v___x_3037_, 7, v_inst_3036_);
    v___x_3038_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadRef___aux__3___boxed as *mut core::ffi::c_void,
        12,
        8,
    );
    crate::leanh::lean_closure_set(v___x_3038_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3038_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3038_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3038_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3038_, 4, v_inst_3033_);
    crate::leanh::lean_closure_set(v___x_3038_, 5, v_inst_3034_);
    crate::leanh::lean_closure_set(v___x_3038_, 6, v_inst_3035_);
    crate::leanh::lean_closure_set(v___x_3038_, 7, v_inst_3036_);
    v___x_3039_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3039_, 0, v___x_3037_);
    crate::leanh::lean_ctor_set(v___x_3039_, 1, v___x_3038_);
    return v___x_3039_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef(
    mut v_00_u03c9_3040_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3041_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3042_: *mut crate::leanh::LeanObject,
    mut v_m_3043_: *mut crate::leanh::LeanObject,
    mut v_inst_3044_: *mut crate::leanh::LeanObject,
    mut v_inst_3045_: *mut crate::leanh::LeanObject,
    mut v_inst_3046_: *mut crate::leanh::LeanObject,
    mut v_inst_3047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = l_Lean_MonadCacheT_instMonadRef___redArg(
        v_inst_3044_,
        v_inst_3045_,
        v_inst_3046_,
        v_inst_3047_,
    );
    return v___x_3048_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__1___redArg(
    mut v_inst_3049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_failure_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_failure_3050_ = crate::leanh::lean_ctor_get(v_inst_3049_, 1);
    crate::leanh::lean_inc(v_failure_3050_);
    crate::leanh::lean_dec_ref(v_inst_3049_);
    v___x_3051_ = crate::leanh::lean_apply_1(v_failure_3050_, crate::leanh::lean_box(0));
    return v___x_3051_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__1(
    mut v_00_u03c9_3052_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3053_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3054_: *mut crate::leanh::LeanObject,
    mut v_m_3055_: *mut crate::leanh::LeanObject,
    mut v_inst_3056_: *mut crate::leanh::LeanObject,
    mut v_inst_3057_: *mut crate::leanh::LeanObject,
    mut v_inst_3058_: *mut crate::leanh::LeanObject,
    mut v_inst_3059_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3060_: *mut crate::leanh::LeanObject,
    mut v_a_3061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_failure_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_failure_3062_ = crate::leanh::lean_ctor_get(v_inst_3059_, 1);
    crate::leanh::lean_inc(v_failure_3062_);
    crate::leanh::lean_dec_ref(v_inst_3059_);
    v___x_3063_ = crate::leanh::lean_apply_1(v_failure_3062_, crate::leanh::lean_box(0));
    return v___x_3063_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__1___boxed(
    mut v_00_u03c9_3064_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3065_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3066_: *mut crate::leanh::LeanObject,
    mut v_m_3067_: *mut crate::leanh::LeanObject,
    mut v_inst_3068_: *mut crate::leanh::LeanObject,
    mut v_inst_3069_: *mut crate::leanh::LeanObject,
    mut v_inst_3070_: *mut crate::leanh::LeanObject,
    mut v_inst_3071_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3072_: *mut crate::leanh::LeanObject,
    mut v_a_3073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3074_ = l_Lean_MonadCacheT_instAlternative___aux__1(
        v_00_u03c9_3064_,
        v_00_u03b1_3065_,
        v_00_u03b2_3066_,
        v_m_3067_,
        v_inst_3068_,
        v_inst_3069_,
        v_inst_3070_,
        v_inst_3071_,
        v_00_u03b1_3072_,
        v_a_3073_,
    );
    crate::leanh::lean_dec(v_a_3073_);
    crate::leanh::lean_dec_ref(v_inst_3070_);
    crate::leanh::lean_dec_ref(v_inst_3069_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3___redArg(
    mut v_inst_3075_: *mut crate::leanh::LeanObject,
    mut v_a_3076_: *mut crate::leanh::LeanObject,
    mut v_a_3077_: *mut crate::leanh::LeanObject,
    mut v_a_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_orElse_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_orElse_3079_ = crate::leanh::lean_ctor_get(v_inst_3075_, 2);
    crate::leanh::lean_inc(v_orElse_3079_);
    crate::leanh::lean_dec_ref(v_inst_3075_);
    crate::leanh::lean_inc_n(v_a_3078_, 2);
    v___f_3080_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3080_, 0, v_a_3077_);
    crate::leanh::lean_closure_set(v___f_3080_, 1, v_a_3078_);
    v___x_3081_ = crate::leanh::lean_apply_1(v_a_3076_, v_a_3078_);
    v___x_3082_ = crate::leanh::lean_apply_3(
        v_orElse_3079_,
        crate::leanh::lean_box(0),
        v___x_3081_,
        v___f_3080_,
    );
    return v___x_3082_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3___redArg___boxed(
    mut v_inst_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
    mut v_a_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3087_ = l_Lean_MonadCacheT_instAlternative___aux__3___redArg(
        v_inst_3083_,
        v_a_3084_,
        v_a_3085_,
        v_a_3086_,
    );
    crate::leanh::lean_dec(v_a_3086_);
    return v_res_3087_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3(
    mut v_00_u03c9_3088_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3089_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3090_: *mut crate::leanh::LeanObject,
    mut v_m_3091_: *mut crate::leanh::LeanObject,
    mut v_inst_3092_: *mut crate::leanh::LeanObject,
    mut v_inst_3093_: *mut crate::leanh::LeanObject,
    mut v_inst_3094_: *mut crate::leanh::LeanObject,
    mut v_inst_3095_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3096_: *mut crate::leanh::LeanObject,
    mut v_a_3097_: *mut crate::leanh::LeanObject,
    mut v_a_3098_: *mut crate::leanh::LeanObject,
    mut v_a_3099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_orElse_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_orElse_3100_ = crate::leanh::lean_ctor_get(v_inst_3095_, 2);
    crate::leanh::lean_inc(v_orElse_3100_);
    crate::leanh::lean_dec_ref(v_inst_3095_);
    crate::leanh::lean_inc_n(v_a_3099_, 2);
    v___f_3101_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3101_, 0, v_a_3098_);
    crate::leanh::lean_closure_set(v___f_3101_, 1, v_a_3099_);
    v___x_3102_ = crate::leanh::lean_apply_1(v_a_3097_, v_a_3099_);
    v___x_3103_ = crate::leanh::lean_apply_3(
        v_orElse_3100_,
        crate::leanh::lean_box(0),
        v___x_3102_,
        v___f_3101_,
    );
    return v___x_3103_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3___boxed(
    mut v_00_u03c9_3104_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3105_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3106_: *mut crate::leanh::LeanObject,
    mut v_m_3107_: *mut crate::leanh::LeanObject,
    mut v_inst_3108_: *mut crate::leanh::LeanObject,
    mut v_inst_3109_: *mut crate::leanh::LeanObject,
    mut v_inst_3110_: *mut crate::leanh::LeanObject,
    mut v_inst_3111_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3112_: *mut crate::leanh::LeanObject,
    mut v_a_3113_: *mut crate::leanh::LeanObject,
    mut v_a_3114_: *mut crate::leanh::LeanObject,
    mut v_a_3115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3116_ = l_Lean_MonadCacheT_instAlternative___aux__3(
        v_00_u03c9_3104_,
        v_00_u03b1_3105_,
        v_00_u03b2_3106_,
        v_m_3107_,
        v_inst_3108_,
        v_inst_3109_,
        v_inst_3110_,
        v_inst_3111_,
        v_00_u03b1_3112_,
        v_a_3113_,
        v_a_3114_,
        v_a_3115_,
    );
    crate::leanh::lean_dec(v_a_3115_);
    crate::leanh::lean_dec_ref(v_inst_3110_);
    crate::leanh::lean_dec_ref(v_inst_3109_);
    return v_res_3116_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___redArg(
    mut v_inst_3117_: *mut crate::leanh::LeanObject,
    mut v_inst_3118_: *mut crate::leanh::LeanObject,
    mut v_inst_3119_: *mut crate::leanh::LeanObject,
    mut v_inst_3120_: *mut crate::leanh::LeanObject,
    mut v_inst_3121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_3119_, 2);
    crate::leanh::lean_inc_ref_n(v_inst_3118_, 2);
    v___x_3122_ = l_Lean_MonadCacheT_instMonad___redArg(
        v_inst_3117_,
        v_inst_3118_,
        v_inst_3119_,
        v_inst_3120_,
    );
    v_toApplicative_3123_ = crate::leanh::lean_ctor_get(v___x_3122_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3123_);
    crate::leanh::lean_dec_ref(v___x_3122_);
    crate::leanh::lean_inc_ref(v_inst_3121_);
    v___x_3124_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instAlternative___aux__1___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    crate::leanh::lean_closure_set(v___x_3124_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3124_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3124_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3124_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3124_, 4, v_inst_3117_);
    crate::leanh::lean_closure_set(v___x_3124_, 5, v_inst_3118_);
    crate::leanh::lean_closure_set(v___x_3124_, 6, v_inst_3119_);
    crate::leanh::lean_closure_set(v___x_3124_, 7, v_inst_3121_);
    v___x_3125_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instAlternative___aux__3___boxed as *mut core::ffi::c_void,
        12,
        8,
    );
    crate::leanh::lean_closure_set(v___x_3125_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3125_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3125_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3125_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3125_, 4, v_inst_3117_);
    crate::leanh::lean_closure_set(v___x_3125_, 5, v_inst_3118_);
    crate::leanh::lean_closure_set(v___x_3125_, 6, v_inst_3119_);
    crate::leanh::lean_closure_set(v___x_3125_, 7, v_inst_3121_);
    v___x_3126_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3126_, 0, v_toApplicative_3123_);
    crate::leanh::lean_ctor_set(v___x_3126_, 1, v___x_3124_);
    crate::leanh::lean_ctor_set(v___x_3126_, 2, v___x_3125_);
    return v___x_3126_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative(
    mut v_00_u03c9_3127_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3128_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3129_: *mut crate::leanh::LeanObject,
    mut v_m_3130_: *mut crate::leanh::LeanObject,
    mut v_inst_3131_: *mut crate::leanh::LeanObject,
    mut v_inst_3132_: *mut crate::leanh::LeanObject,
    mut v_inst_3133_: *mut crate::leanh::LeanObject,
    mut v_inst_3134_: *mut crate::leanh::LeanObject,
    mut v_inst_3135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3136_ = l_Lean_MonadCacheT_instAlternative___redArg(
        v_inst_3131_,
        v_inst_3132_,
        v_inst_3133_,
        v_inst_3134_,
        v_inst_3135_,
    );
    return v___x_3136_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(
    mut v_inst_3137_: *mut crate::leanh::LeanObject,
    mut v_f_3138_: *mut crate::leanh::LeanObject,
    mut v___y_3139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3143_: u8 = 0;
    let mut v_toPure_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut v_unused_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3140_ = crate::leanh::lean_ctor_get(v_inst_3137_, 0);
                v_isSharedCheck_3151_ = (!crate::leanh::lean_is_exclusive(v_inst_3137_)) as u8;
                if v_isSharedCheck_3151_ == 0 {
                    v_unused_3152_ = crate::leanh::lean_ctor_get(v_inst_3137_, 1);
                    crate::leanh::lean_dec(v_unused_3152_);
                    v___x_3142_ = v_inst_3137_;
                    v_isShared_3143_ = v_isSharedCheck_3151_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3140_);
                    crate::leanh::lean_dec(v_inst_3137_);
                    v___x_3142_ = crate::leanh::lean_box(0);
                    v_isShared_3143_ = v_isSharedCheck_3151_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3144_ = crate::leanh::lean_ctor_get(v_toApplicative_3140_, 1);
                crate::leanh::lean_inc(v_toPure_3144_);
                crate::leanh::lean_dec_ref(v_toApplicative_3140_);
                v___x_3145_ = crate::leanh::lean_box(0);
                v___x_3146_ = crate::leanh::lean_apply_1(v_f_3138_, v___y_3139_);
                if v_isShared_3143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3142_, 1, v___x_3146_);
                    crate::leanh::lean_ctor_set(v___x_3142_, 0, v___x_3145_);
                    v___x_3148_ = v___x_3142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_3146_);
                    v___x_3148_ = v_reuseFailAlloc_3150_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3149_ = crate::leanh::lean_apply_2(
                    v_toPure_3144_,
                    crate::leanh::lean_box(0),
                    v___x_3148_,
                );
                return v___x_3149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(
    mut v_inst_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_3153_);
    v___f_3154_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3154_, 0, v_inst_3153_);
    v___x_3155_ = crate::leanh::lean_alloc_closure(l_StateT_get as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_3155_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3155_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3155_, 2, v_inst_3153_);
    v___x_3156_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3156_, 0, v___x_3155_);
    crate::leanh::lean_ctor_set(v___x_3156_, 1, v___f_3154_);
    return v___x_3156_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(
    mut v_00_u03b1_3157_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3158_: *mut crate::leanh::LeanObject,
    mut v_m_3159_: *mut crate::leanh::LeanObject,
    mut v_inst_3160_: *mut crate::leanh::LeanObject,
    mut v_inst_3161_: *mut crate::leanh::LeanObject,
    mut v_inst_3162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3163_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_3162_);
    return v___x_3163_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___boxed(
    mut v_00_u03b1_3164_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3165_: *mut crate::leanh::LeanObject,
    mut v_m_3166_: *mut crate::leanh::LeanObject,
    mut v_inst_3167_: *mut crate::leanh::LeanObject,
    mut v_inst_3168_: *mut crate::leanh::LeanObject,
    mut v_inst_3169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3170_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(
        v_00_u03b1_3164_,
        v_00_u03b2_3165_,
        v_m_3166_,
        v_inst_3167_,
        v_inst_3168_,
        v_inst_3169_,
    );
    crate::leanh::lean_dec_ref(v_inst_3168_);
    crate::leanh::lean_dec_ref(v_inst_3167_);
    return v_res_3170_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___redArg___lam__0(
    mut v_x_3171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3172_ = crate::leanh::lean_ctor_get(v_x_3171_, 0);
    crate::leanh::lean_inc(v_fst_3172_);
    return v_fst_3172_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed(
    mut v_x_3173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3174_ = l_Lean_MonadStateCacheT_run___redArg___lam__0(v_x_3173_);
    crate::leanh::lean_dec_ref(v_x_3173_);
    return v_res_3174_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___redArg(
    mut v_inst_3176_: *mut crate::leanh::LeanObject,
    mut v_x_3177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3178_ = crate::leanh::lean_ctor_get(v_inst_3176_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3178_);
    crate::leanh::lean_dec_ref(v_inst_3176_);
    v_toFunctor_3179_ = crate::leanh::lean_ctor_get(v_toApplicative_3178_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_3179_);
    crate::leanh::lean_dec_ref(v_toApplicative_3178_);
    v_map_3180_ = crate::leanh::lean_ctor_get(v_toFunctor_3179_, 0);
    crate::leanh::lean_inc(v_map_3180_);
    crate::leanh::lean_dec_ref(v_toFunctor_3179_);
    v___f_3181_ = l_Lean_MonadStateCacheT_run___redArg___closed__0;
    v___x_3182_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__1,
    );
    v___x_3183_ = crate::leanh::lean_apply_1(v_x_3177_, v___x_3182_);
    v___x_3184_ = crate::leanh::lean_apply_4(
        v_map_3180_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_3181_,
        v___x_3183_,
    );
    return v___x_3184_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run(
    mut v_00_u03b1_3185_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3186_: *mut crate::leanh::LeanObject,
    mut v_m_3187_: *mut crate::leanh::LeanObject,
    mut v_inst_3188_: *mut crate::leanh::LeanObject,
    mut v_inst_3189_: *mut crate::leanh::LeanObject,
    mut v_inst_3190_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3191_: *mut crate::leanh::LeanObject,
    mut v_x_3192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3193_ = crate::leanh::lean_ctor_get(v_inst_3190_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3193_);
    crate::leanh::lean_dec_ref(v_inst_3190_);
    v_toFunctor_3194_ = crate::leanh::lean_ctor_get(v_toApplicative_3193_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_3194_);
    crate::leanh::lean_dec_ref(v_toApplicative_3193_);
    v_map_3195_ = crate::leanh::lean_ctor_get(v_toFunctor_3194_, 0);
    crate::leanh::lean_inc(v_map_3195_);
    crate::leanh::lean_dec_ref(v_toFunctor_3194_);
    v___f_3196_ = l_Lean_MonadStateCacheT_run___redArg___closed__0;
    v___x_3197_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__1,
    );
    v___x_3198_ = crate::leanh::lean_apply_1(v_x_3192_, v___x_3197_);
    v___x_3199_ = crate::leanh::lean_apply_4(
        v_map_3195_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_3196_,
        v___x_3198_,
    );
    return v___x_3199_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___boxed(
    mut v_00_u03b1_3200_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3201_: *mut crate::leanh::LeanObject,
    mut v_m_3202_: *mut crate::leanh::LeanObject,
    mut v_inst_3203_: *mut crate::leanh::LeanObject,
    mut v_inst_3204_: *mut crate::leanh::LeanObject,
    mut v_inst_3205_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3206_: *mut crate::leanh::LeanObject,
    mut v_x_3207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3208_ = l_Lean_MonadStateCacheT_run(
        v_00_u03b1_3200_,
        v_00_u03b2_3201_,
        v_m_3202_,
        v_inst_3203_,
        v_inst_3204_,
        v_inst_3205_,
        v_00_u03c3_3206_,
        v_x_3207_,
    );
    crate::leanh::lean_dec_ref(v_inst_3204_);
    crate::leanh::lean_dec_ref(v_inst_3203_);
    return v_res_3208_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0(
    mut v_f_3209_: *mut crate::leanh::LeanObject,
    mut v_toPure_3210_: *mut crate::leanh::LeanObject,
    mut v_____x_3211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3212_ = crate::leanh::lean_ctor_get(v_____x_3211_, 0);
                v_snd_3213_ = crate::leanh::lean_ctor_get(v_____x_3211_, 1);
                v_isSharedCheck_3222_ = (!crate::leanh::lean_is_exclusive(v_____x_3211_)) as u8;
                if v_isSharedCheck_3222_ == 0 {
                    v___x_3215_ = v_____x_3211_;
                    v_isShared_3216_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3213_);
                    crate::leanh::lean_inc(v_fst_3212_);
                    crate::leanh::lean_dec(v_____x_3211_);
                    v___x_3215_ = crate::leanh::lean_box(0);
                    v_isShared_3216_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3217_ = crate::leanh::lean_apply_1(v_f_3209_, v_fst_3212_);
                if v_isShared_3216_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3215_, 0, v___x_3217_);
                    v___x_3219_ = v___x_3215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_snd_3213_);
                    v___x_3219_ = v_reuseFailAlloc_3221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3220_ = crate::leanh::lean_apply_2(
                    v_toPure_3210_,
                    crate::leanh::lean_box(0),
                    v___x_3219_,
                );
                return v___x_3220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1___redArg(
    mut v_inst_3223_: *mut crate::leanh::LeanObject,
    mut v_f_3224_: *mut crate::leanh::LeanObject,
    mut v_x_3225_: *mut crate::leanh::LeanObject,
    mut v_a_3226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3227_ = crate::leanh::lean_ctor_get(v_inst_3223_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3227_);
    v_toBind_3228_ = crate::leanh::lean_ctor_get(v_inst_3223_, 1);
    crate::leanh::lean_inc(v_toBind_3228_);
    crate::leanh::lean_dec_ref(v_inst_3223_);
    v_toPure_3229_ = crate::leanh::lean_ctor_get(v_toApplicative_3227_, 1);
    crate::leanh::lean_inc(v_toPure_3229_);
    crate::leanh::lean_dec_ref(v_toApplicative_3227_);
    v___x_3230_ = crate::leanh::lean_apply_1(v_x_3225_, v_a_3226_);
    v___f_3231_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3231_, 0, v_f_3224_);
    crate::leanh::lean_closure_set(v___f_3231_, 1, v_toPure_3229_);
    v___x_3232_ = crate::leanh::lean_apply_4(
        v_toBind_3228_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3230_,
        v___f_3231_,
    );
    return v___x_3232_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1(
    mut v_00_u03b1_3233_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3234_: *mut crate::leanh::LeanObject,
    mut v_m_3235_: *mut crate::leanh::LeanObject,
    mut v_inst_3236_: *mut crate::leanh::LeanObject,
    mut v_inst_3237_: *mut crate::leanh::LeanObject,
    mut v_inst_3238_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3239_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3240_: *mut crate::leanh::LeanObject,
    mut v_f_3241_: *mut crate::leanh::LeanObject,
    mut v_x_3242_: *mut crate::leanh::LeanObject,
    mut v_a_3243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3244_ = crate::leanh::lean_ctor_get(v_inst_3238_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3244_);
    v_toBind_3245_ = crate::leanh::lean_ctor_get(v_inst_3238_, 1);
    crate::leanh::lean_inc(v_toBind_3245_);
    crate::leanh::lean_dec_ref(v_inst_3238_);
    v_toPure_3246_ = crate::leanh::lean_ctor_get(v_toApplicative_3244_, 1);
    crate::leanh::lean_inc(v_toPure_3246_);
    crate::leanh::lean_dec_ref(v_toApplicative_3244_);
    v___x_3247_ = crate::leanh::lean_apply_1(v_x_3242_, v_a_3243_);
    v___f_3248_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3248_, 0, v_f_3241_);
    crate::leanh::lean_closure_set(v___f_3248_, 1, v_toPure_3246_);
    v___x_3249_ = crate::leanh::lean_apply_4(
        v_toBind_3245_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3247_,
        v___f_3248_,
    );
    return v___x_3249_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1___boxed(
    mut v_00_u03b1_3250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3251_: *mut crate::leanh::LeanObject,
    mut v_m_3252_: *mut crate::leanh::LeanObject,
    mut v_inst_3253_: *mut crate::leanh::LeanObject,
    mut v_inst_3254_: *mut crate::leanh::LeanObject,
    mut v_inst_3255_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3256_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3257_: *mut crate::leanh::LeanObject,
    mut v_f_3258_: *mut crate::leanh::LeanObject,
    mut v_x_3259_: *mut crate::leanh::LeanObject,
    mut v_a_3260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3261_ = l_Lean_MonadStateCacheT_instMonad___aux__1(
        v_00_u03b1_3250_,
        v_00_u03b2_3251_,
        v_m_3252_,
        v_inst_3253_,
        v_inst_3254_,
        v_inst_3255_,
        v_00_u03b1_3256_,
        v_00_u03b2_3257_,
        v_f_3258_,
        v_x_3259_,
        v_a_3260_,
    );
    crate::leanh::lean_dec_ref(v_inst_3254_);
    crate::leanh::lean_dec_ref(v_inst_3253_);
    return v_res_3261_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0(
    mut v_a_3262_: *mut crate::leanh::LeanObject,
    mut v_toPure_3263_: *mut crate::leanh::LeanObject,
    mut v_____x_3264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_unused_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3265_ = crate::leanh::lean_ctor_get(v_____x_3264_, 1);
                v_isSharedCheck_3273_ = (!crate::leanh::lean_is_exclusive(v_____x_3264_)) as u8;
                if v_isSharedCheck_3273_ == 0 {
                    v_unused_3274_ = crate::leanh::lean_ctor_get(v_____x_3264_, 0);
                    crate::leanh::lean_dec(v_unused_3274_);
                    v___x_3267_ = v_____x_3264_;
                    v_isShared_3268_ = v_isSharedCheck_3273_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3265_);
                    crate::leanh::lean_dec(v_____x_3264_);
                    v___x_3267_ = crate::leanh::lean_box(0);
                    v_isShared_3268_ = v_isSharedCheck_3273_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3267_, 0, v_a_3262_);
                    v___x_3270_ = v___x_3267_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3272_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_snd_3265_);
                    v___x_3270_ = v_reuseFailAlloc_3272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3271_ = crate::leanh::lean_apply_2(
                    v_toPure_3263_,
                    crate::leanh::lean_box(0),
                    v___x_3270_,
                );
                return v___x_3271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3___redArg(
    mut v_inst_3275_: *mut crate::leanh::LeanObject,
    mut v_a_3276_: *mut crate::leanh::LeanObject,
    mut v_a_3277_: *mut crate::leanh::LeanObject,
    mut v_a_3278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3279_ = crate::leanh::lean_ctor_get(v_inst_3275_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3279_);
    v_toBind_3280_ = crate::leanh::lean_ctor_get(v_inst_3275_, 1);
    crate::leanh::lean_inc(v_toBind_3280_);
    crate::leanh::lean_dec_ref(v_inst_3275_);
    v_toPure_3281_ = crate::leanh::lean_ctor_get(v_toApplicative_3279_, 1);
    crate::leanh::lean_inc(v_toPure_3281_);
    crate::leanh::lean_dec_ref(v_toApplicative_3279_);
    v___x_3282_ = crate::leanh::lean_apply_1(v_a_3277_, v_a_3278_);
    v___f_3283_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3283_, 0, v_a_3276_);
    crate::leanh::lean_closure_set(v___f_3283_, 1, v_toPure_3281_);
    v___x_3284_ = crate::leanh::lean_apply_4(
        v_toBind_3280_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3282_,
        v___f_3283_,
    );
    return v___x_3284_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3(
    mut v_00_u03b1_3285_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3286_: *mut crate::leanh::LeanObject,
    mut v_m_3287_: *mut crate::leanh::LeanObject,
    mut v_inst_3288_: *mut crate::leanh::LeanObject,
    mut v_inst_3289_: *mut crate::leanh::LeanObject,
    mut v_inst_3290_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3291_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3292_: *mut crate::leanh::LeanObject,
    mut v_a_3293_: *mut crate::leanh::LeanObject,
    mut v_a_3294_: *mut crate::leanh::LeanObject,
    mut v_a_3295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3296_ = crate::leanh::lean_ctor_get(v_inst_3290_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3296_);
    v_toBind_3297_ = crate::leanh::lean_ctor_get(v_inst_3290_, 1);
    crate::leanh::lean_inc(v_toBind_3297_);
    crate::leanh::lean_dec_ref(v_inst_3290_);
    v_toPure_3298_ = crate::leanh::lean_ctor_get(v_toApplicative_3296_, 1);
    crate::leanh::lean_inc(v_toPure_3298_);
    crate::leanh::lean_dec_ref(v_toApplicative_3296_);
    v___x_3299_ = crate::leanh::lean_apply_1(v_a_3294_, v_a_3295_);
    v___f_3300_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3300_, 0, v_a_3293_);
    crate::leanh::lean_closure_set(v___f_3300_, 1, v_toPure_3298_);
    v___x_3301_ = crate::leanh::lean_apply_4(
        v_toBind_3297_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3299_,
        v___f_3300_,
    );
    return v___x_3301_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3___boxed(
    mut v_00_u03b1_3302_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3303_: *mut crate::leanh::LeanObject,
    mut v_m_3304_: *mut crate::leanh::LeanObject,
    mut v_inst_3305_: *mut crate::leanh::LeanObject,
    mut v_inst_3306_: *mut crate::leanh::LeanObject,
    mut v_inst_3307_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3308_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
    mut v_a_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3313_ = l_Lean_MonadStateCacheT_instMonad___aux__3(
        v_00_u03b1_3302_,
        v_00_u03b2_3303_,
        v_m_3304_,
        v_inst_3305_,
        v_inst_3306_,
        v_inst_3307_,
        v_00_u03b1_3308_,
        v_00_u03b2_3309_,
        v_a_3310_,
        v_a_3311_,
        v_a_3312_,
    );
    crate::leanh::lean_dec_ref(v_inst_3306_);
    crate::leanh::lean_dec_ref(v_inst_3305_);
    return v_res_3313_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__5___redArg(
    mut v_inst_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
    mut v_a_3316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3320_: u8 = 0;
    let mut v_toPure_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut v_unused_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3317_ = crate::leanh::lean_ctor_get(v_inst_3314_, 0);
                v_isSharedCheck_3326_ = (!crate::leanh::lean_is_exclusive(v_inst_3314_)) as u8;
                if v_isSharedCheck_3326_ == 0 {
                    v_unused_3327_ = crate::leanh::lean_ctor_get(v_inst_3314_, 1);
                    crate::leanh::lean_dec(v_unused_3327_);
                    v___x_3319_ = v_inst_3314_;
                    v_isShared_3320_ = v_isSharedCheck_3326_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3317_);
                    crate::leanh::lean_dec(v_inst_3314_);
                    v___x_3319_ = crate::leanh::lean_box(0);
                    v_isShared_3320_ = v_isSharedCheck_3326_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3321_ = crate::leanh::lean_ctor_get(v_toApplicative_3317_, 1);
                crate::leanh::lean_inc(v_toPure_3321_);
                crate::leanh::lean_dec_ref(v_toApplicative_3317_);
                if v_isShared_3320_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3319_, 1, v_a_3316_);
                    crate::leanh::lean_ctor_set(v___x_3319_, 0, v_a_3315_);
                    v___x_3323_ = v___x_3319_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3325_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_a_3316_);
                    v___x_3323_ = v_reuseFailAlloc_3325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3324_ = crate::leanh::lean_apply_2(
                    v_toPure_3321_,
                    crate::leanh::lean_box(0),
                    v___x_3323_,
                );
                return v___x_3324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__5(
    mut v_00_u03b1_3328_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3329_: *mut crate::leanh::LeanObject,
    mut v_m_3330_: *mut crate::leanh::LeanObject,
    mut v_inst_3331_: *mut crate::leanh::LeanObject,
    mut v_inst_3332_: *mut crate::leanh::LeanObject,
    mut v_inst_3333_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v_toPure_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_unused_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3337_ = crate::leanh::lean_ctor_get(v_inst_3333_, 0);
                v_isSharedCheck_3346_ = (!crate::leanh::lean_is_exclusive(v_inst_3333_)) as u8;
                if v_isSharedCheck_3346_ == 0 {
                    v_unused_3347_ = crate::leanh::lean_ctor_get(v_inst_3333_, 1);
                    crate::leanh::lean_dec(v_unused_3347_);
                    v___x_3339_ = v_inst_3333_;
                    v_isShared_3340_ = v_isSharedCheck_3346_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3337_);
                    crate::leanh::lean_dec(v_inst_3333_);
                    v___x_3339_ = crate::leanh::lean_box(0);
                    v_isShared_3340_ = v_isSharedCheck_3346_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3341_ = crate::leanh::lean_ctor_get(v_toApplicative_3337_, 1);
                crate::leanh::lean_inc(v_toPure_3341_);
                crate::leanh::lean_dec_ref(v_toApplicative_3337_);
                if v_isShared_3340_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3339_, 1, v_a_3336_);
                    crate::leanh::lean_ctor_set(v___x_3339_, 0, v_a_3335_);
                    v___x_3343_ = v___x_3339_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3335_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_a_3336_);
                    v___x_3343_ = v_reuseFailAlloc_3345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3344_ = crate::leanh::lean_apply_2(
                    v_toPure_3341_,
                    crate::leanh::lean_box(0),
                    v___x_3343_,
                );
                return v___x_3344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__5___boxed(
    mut v_00_u03b1_3348_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3349_: *mut crate::leanh::LeanObject,
    mut v_m_3350_: *mut crate::leanh::LeanObject,
    mut v_inst_3351_: *mut crate::leanh::LeanObject,
    mut v_inst_3352_: *mut crate::leanh::LeanObject,
    mut v_inst_3353_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3357_ = l_Lean_MonadStateCacheT_instMonad___aux__5(
        v_00_u03b1_3348_,
        v_00_u03b2_3349_,
        v_m_3350_,
        v_inst_3351_,
        v_inst_3352_,
        v_inst_3353_,
        v_00_u03b1_3354_,
        v_a_3355_,
        v_a_3356_,
    );
    crate::leanh::lean_dec_ref(v_inst_3352_);
    crate::leanh::lean_dec_ref(v_inst_3351_);
    return v_res_3357_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0(
    mut v_fst_3358_: *mut crate::leanh::LeanObject,
    mut v_toPure_3359_: *mut crate::leanh::LeanObject,
    mut v_____x_3360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3365_: u8 = 0;
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3361_ = crate::leanh::lean_ctor_get(v_____x_3360_, 0);
                v_snd_3362_ = crate::leanh::lean_ctor_get(v_____x_3360_, 1);
                v_isSharedCheck_3371_ = (!crate::leanh::lean_is_exclusive(v_____x_3360_)) as u8;
                if v_isSharedCheck_3371_ == 0 {
                    v___x_3364_ = v_____x_3360_;
                    v_isShared_3365_ = v_isSharedCheck_3371_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3362_);
                    crate::leanh::lean_inc(v_fst_3361_);
                    crate::leanh::lean_dec(v_____x_3360_);
                    v___x_3364_ = crate::leanh::lean_box(0);
                    v_isShared_3365_ = v_isSharedCheck_3371_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3366_ = crate::leanh::lean_apply_1(v_fst_3358_, v_fst_3361_);
                if v_isShared_3365_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3364_, 0, v___x_3366_);
                    v___x_3368_ = v___x_3364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3370_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_snd_3362_);
                    v___x_3368_ = v_reuseFailAlloc_3370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3369_ = crate::leanh::lean_apply_2(
                    v_toPure_3359_,
                    crate::leanh::lean_box(0),
                    v___x_3368_,
                );
                return v___x_3369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1(
    mut v_toApplicative_3372_: *mut crate::leanh::LeanObject,
    mut v_x_3373_: *mut crate::leanh::LeanObject,
    mut v_toBind_3374_: *mut crate::leanh::LeanObject,
    mut v_____x_3375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3376_ = crate::leanh::lean_ctor_get(v_____x_3375_, 0);
    crate::leanh::lean_inc(v_fst_3376_);
    v_snd_3377_ = crate::leanh::lean_ctor_get(v_____x_3375_, 1);
    crate::leanh::lean_inc(v_snd_3377_);
    crate::leanh::lean_dec_ref(v_____x_3375_);
    v_toPure_3378_ = crate::leanh::lean_ctor_get(v_toApplicative_3372_, 1);
    crate::leanh::lean_inc(v_toPure_3378_);
    crate::leanh::lean_dec_ref(v_toApplicative_3372_);
    v___x_3379_ = crate::leanh::lean_box(0);
    v___x_3380_ = crate::leanh::lean_apply_2(v_x_3373_, v___x_3379_, v_snd_3377_);
    v___f_3381_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3381_, 0, v_fst_3376_);
    crate::leanh::lean_closure_set(v___f_3381_, 1, v_toPure_3378_);
    v___x_3382_ = crate::leanh::lean_apply_4(
        v_toBind_3374_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3380_,
        v___f_3381_,
    );
    return v___x_3382_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___redArg(
    mut v_inst_3383_: *mut crate::leanh::LeanObject,
    mut v_f_3384_: *mut crate::leanh::LeanObject,
    mut v_x_3385_: *mut crate::leanh::LeanObject,
    mut v_a_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3387_ = crate::leanh::lean_ctor_get(v_inst_3383_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3387_);
    v_toBind_3388_ = crate::leanh::lean_ctor_get(v_inst_3383_, 1);
    crate::leanh::lean_inc_n(v_toBind_3388_, 2);
    crate::leanh::lean_dec_ref(v_inst_3383_);
    v___f_3389_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3389_, 0, v_toApplicative_3387_);
    crate::leanh::lean_closure_set(v___f_3389_, 1, v_x_3385_);
    crate::leanh::lean_closure_set(v___f_3389_, 2, v_toBind_3388_);
    v___x_3390_ = crate::leanh::lean_apply_1(v_f_3384_, v_a_3386_);
    v___x_3391_ = crate::leanh::lean_apply_4(
        v_toBind_3388_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3390_,
        v___f_3389_,
    );
    return v___x_3391_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7(
    mut v_00_u03b1_3392_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3393_: *mut crate::leanh::LeanObject,
    mut v_m_3394_: *mut crate::leanh::LeanObject,
    mut v_inst_3395_: *mut crate::leanh::LeanObject,
    mut v_inst_3396_: *mut crate::leanh::LeanObject,
    mut v_inst_3397_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3398_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3399_: *mut crate::leanh::LeanObject,
    mut v_f_3400_: *mut crate::leanh::LeanObject,
    mut v_x_3401_: *mut crate::leanh::LeanObject,
    mut v_a_3402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3403_ = crate::leanh::lean_ctor_get(v_inst_3397_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3403_);
    v_toBind_3404_ = crate::leanh::lean_ctor_get(v_inst_3397_, 1);
    crate::leanh::lean_inc_n(v_toBind_3404_, 2);
    crate::leanh::lean_dec_ref(v_inst_3397_);
    v___f_3405_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3405_, 0, v_toApplicative_3403_);
    crate::leanh::lean_closure_set(v___f_3405_, 1, v_x_3401_);
    crate::leanh::lean_closure_set(v___f_3405_, 2, v_toBind_3404_);
    v___x_3406_ = crate::leanh::lean_apply_1(v_f_3400_, v_a_3402_);
    v___x_3407_ = crate::leanh::lean_apply_4(
        v_toBind_3404_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3406_,
        v___f_3405_,
    );
    return v___x_3407_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___boxed(
    mut v_00_u03b1_3408_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3409_: *mut crate::leanh::LeanObject,
    mut v_m_3410_: *mut crate::leanh::LeanObject,
    mut v_inst_3411_: *mut crate::leanh::LeanObject,
    mut v_inst_3412_: *mut crate::leanh::LeanObject,
    mut v_inst_3413_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3414_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3415_: *mut crate::leanh::LeanObject,
    mut v_f_3416_: *mut crate::leanh::LeanObject,
    mut v_x_3417_: *mut crate::leanh::LeanObject,
    mut v_a_3418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3419_ = l_Lean_MonadStateCacheT_instMonad___aux__7(
        v_00_u03b1_3408_,
        v_00_u03b2_3409_,
        v_m_3410_,
        v_inst_3411_,
        v_inst_3412_,
        v_inst_3413_,
        v_00_u03b1_3414_,
        v_00_u03b2_3415_,
        v_f_3416_,
        v_x_3417_,
        v_a_3418_,
    );
    crate::leanh::lean_dec_ref(v_inst_3412_);
    crate::leanh::lean_dec_ref(v_inst_3411_);
    return v_res_3419_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0(
    mut v_toApplicative_3420_: *mut crate::leanh::LeanObject,
    mut v_fst_3421_: *mut crate::leanh::LeanObject,
    mut v_____x_3422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3426_: u8 = 0;
    let mut v_toPure_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3432_: u8 = 0;
    let mut v_unused_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3423_ = crate::leanh::lean_ctor_get(v_____x_3422_, 1);
                v_isSharedCheck_3432_ = (!crate::leanh::lean_is_exclusive(v_____x_3422_)) as u8;
                if v_isSharedCheck_3432_ == 0 {
                    v_unused_3433_ = crate::leanh::lean_ctor_get(v_____x_3422_, 0);
                    crate::leanh::lean_dec(v_unused_3433_);
                    v___x_3425_ = v_____x_3422_;
                    v_isShared_3426_ = v_isSharedCheck_3432_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3423_);
                    crate::leanh::lean_dec(v_____x_3422_);
                    v___x_3425_ = crate::leanh::lean_box(0);
                    v_isShared_3426_ = v_isSharedCheck_3432_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3427_ = crate::leanh::lean_ctor_get(v_toApplicative_3420_, 1);
                crate::leanh::lean_inc(v_toPure_3427_);
                crate::leanh::lean_dec_ref(v_toApplicative_3420_);
                if v_isShared_3426_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3425_, 0, v_fst_3421_);
                    v___x_3429_ = v___x_3425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3431_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_fst_3421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_snd_3423_);
                    v___x_3429_ = v_reuseFailAlloc_3431_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3430_ = crate::leanh::lean_apply_2(
                    v_toPure_3427_,
                    crate::leanh::lean_box(0),
                    v___x_3429_,
                );
                return v___x_3430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1(
    mut v_toApplicative_3434_: *mut crate::leanh::LeanObject,
    mut v_y_3435_: *mut crate::leanh::LeanObject,
    mut v_toBind_3436_: *mut crate::leanh::LeanObject,
    mut v_____x_3437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3438_ = crate::leanh::lean_ctor_get(v_____x_3437_, 0);
    crate::leanh::lean_inc(v_fst_3438_);
    v_snd_3439_ = crate::leanh::lean_ctor_get(v_____x_3437_, 1);
    crate::leanh::lean_inc(v_snd_3439_);
    crate::leanh::lean_dec_ref(v_____x_3437_);
    v___f_3440_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3440_, 0, v_toApplicative_3434_);
    crate::leanh::lean_closure_set(v___f_3440_, 1, v_fst_3438_);
    v___x_3441_ = crate::leanh::lean_box(0);
    v___x_3442_ = crate::leanh::lean_apply_2(v_y_3435_, v___x_3441_, v_snd_3439_);
    v___x_3443_ = crate::leanh::lean_apply_4(
        v_toBind_3436_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3442_,
        v___f_3440_,
    );
    return v___x_3443_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___redArg(
    mut v_inst_3444_: *mut crate::leanh::LeanObject,
    mut v_x_3445_: *mut crate::leanh::LeanObject,
    mut v_y_3446_: *mut crate::leanh::LeanObject,
    mut v_a_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3448_ = crate::leanh::lean_ctor_get(v_inst_3444_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3448_);
    v_toBind_3449_ = crate::leanh::lean_ctor_get(v_inst_3444_, 1);
    crate::leanh::lean_inc_n(v_toBind_3449_, 2);
    crate::leanh::lean_dec_ref(v_inst_3444_);
    v___f_3450_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3450_, 0, v_toApplicative_3448_);
    crate::leanh::lean_closure_set(v___f_3450_, 1, v_y_3446_);
    crate::leanh::lean_closure_set(v___f_3450_, 2, v_toBind_3449_);
    v___x_3451_ = crate::leanh::lean_apply_1(v_x_3445_, v_a_3447_);
    v___x_3452_ = crate::leanh::lean_apply_4(
        v_toBind_3449_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3451_,
        v___f_3450_,
    );
    return v___x_3452_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9(
    mut v_00_u03b1_3453_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3454_: *mut crate::leanh::LeanObject,
    mut v_m_3455_: *mut crate::leanh::LeanObject,
    mut v_inst_3456_: *mut crate::leanh::LeanObject,
    mut v_inst_3457_: *mut crate::leanh::LeanObject,
    mut v_inst_3458_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3459_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3460_: *mut crate::leanh::LeanObject,
    mut v_x_3461_: *mut crate::leanh::LeanObject,
    mut v_y_3462_: *mut crate::leanh::LeanObject,
    mut v_a_3463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3464_ = crate::leanh::lean_ctor_get(v_inst_3458_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3464_);
    v_toBind_3465_ = crate::leanh::lean_ctor_get(v_inst_3458_, 1);
    crate::leanh::lean_inc_n(v_toBind_3465_, 2);
    crate::leanh::lean_dec_ref(v_inst_3458_);
    v___f_3466_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3466_, 0, v_toApplicative_3464_);
    crate::leanh::lean_closure_set(v___f_3466_, 1, v_y_3462_);
    crate::leanh::lean_closure_set(v___f_3466_, 2, v_toBind_3465_);
    v___x_3467_ = crate::leanh::lean_apply_1(v_x_3461_, v_a_3463_);
    v___x_3468_ = crate::leanh::lean_apply_4(
        v_toBind_3465_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3467_,
        v___f_3466_,
    );
    return v___x_3468_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___boxed(
    mut v_00_u03b1_3469_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3470_: *mut crate::leanh::LeanObject,
    mut v_m_3471_: *mut crate::leanh::LeanObject,
    mut v_inst_3472_: *mut crate::leanh::LeanObject,
    mut v_inst_3473_: *mut crate::leanh::LeanObject,
    mut v_inst_3474_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3475_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3476_: *mut crate::leanh::LeanObject,
    mut v_x_3477_: *mut crate::leanh::LeanObject,
    mut v_y_3478_: *mut crate::leanh::LeanObject,
    mut v_a_3479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_Lean_MonadStateCacheT_instMonad___aux__9(
        v_00_u03b1_3469_,
        v_00_u03b2_3470_,
        v_m_3471_,
        v_inst_3472_,
        v_inst_3473_,
        v_inst_3474_,
        v_00_u03b1_3475_,
        v_00_u03b2_3476_,
        v_x_3477_,
        v_y_3478_,
        v_a_3479_,
    );
    crate::leanh::lean_dec_ref(v_inst_3473_);
    crate::leanh::lean_dec_ref(v_inst_3472_);
    return v_res_3480_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0(
    mut v_y_3481_: *mut crate::leanh::LeanObject,
    mut v_____x_3482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_3483_ = crate::leanh::lean_ctor_get(v_____x_3482_, 1);
    crate::leanh::lean_inc(v_snd_3483_);
    crate::leanh::lean_dec_ref(v_____x_3482_);
    v___x_3484_ = crate::leanh::lean_box(0);
    v___x_3485_ = crate::leanh::lean_apply_2(v_y_3481_, v___x_3484_, v_snd_3483_);
    return v___x_3485_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11___redArg(
    mut v_inst_3486_: *mut crate::leanh::LeanObject,
    mut v_x_3487_: *mut crate::leanh::LeanObject,
    mut v_y_3488_: *mut crate::leanh::LeanObject,
    mut v_a_3489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_3490_ = crate::leanh::lean_ctor_get(v_inst_3486_, 1);
    crate::leanh::lean_inc(v_toBind_3490_);
    crate::leanh::lean_dec_ref(v_inst_3486_);
    v___f_3491_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3491_, 0, v_y_3488_);
    v___x_3492_ = crate::leanh::lean_apply_1(v_x_3487_, v_a_3489_);
    v___x_3493_ = crate::leanh::lean_apply_4(
        v_toBind_3490_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3492_,
        v___f_3491_,
    );
    return v___x_3493_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11(
    mut v_00_u03b1_3494_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3495_: *mut crate::leanh::LeanObject,
    mut v_m_3496_: *mut crate::leanh::LeanObject,
    mut v_inst_3497_: *mut crate::leanh::LeanObject,
    mut v_inst_3498_: *mut crate::leanh::LeanObject,
    mut v_inst_3499_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3500_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3501_: *mut crate::leanh::LeanObject,
    mut v_x_3502_: *mut crate::leanh::LeanObject,
    mut v_y_3503_: *mut crate::leanh::LeanObject,
    mut v_a_3504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_3505_ = crate::leanh::lean_ctor_get(v_inst_3499_, 1);
    crate::leanh::lean_inc(v_toBind_3505_);
    crate::leanh::lean_dec_ref(v_inst_3499_);
    v___f_3506_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3506_, 0, v_y_3503_);
    v___x_3507_ = crate::leanh::lean_apply_1(v_x_3502_, v_a_3504_);
    v___x_3508_ = crate::leanh::lean_apply_4(
        v_toBind_3505_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3507_,
        v___f_3506_,
    );
    return v___x_3508_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11___boxed(
    mut v_00_u03b1_3509_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3510_: *mut crate::leanh::LeanObject,
    mut v_m_3511_: *mut crate::leanh::LeanObject,
    mut v_inst_3512_: *mut crate::leanh::LeanObject,
    mut v_inst_3513_: *mut crate::leanh::LeanObject,
    mut v_inst_3514_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3515_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3516_: *mut crate::leanh::LeanObject,
    mut v_x_3517_: *mut crate::leanh::LeanObject,
    mut v_y_3518_: *mut crate::leanh::LeanObject,
    mut v_a_3519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3520_ = l_Lean_MonadStateCacheT_instMonad___aux__11(
        v_00_u03b1_3509_,
        v_00_u03b2_3510_,
        v_m_3511_,
        v_inst_3512_,
        v_inst_3513_,
        v_inst_3514_,
        v_00_u03b1_3515_,
        v_00_u03b2_3516_,
        v_x_3517_,
        v_y_3518_,
        v_a_3519_,
    );
    crate::leanh::lean_dec_ref(v_inst_3513_);
    crate::leanh::lean_dec_ref(v_inst_3512_);
    return v_res_3520_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0(
    mut v_f_3521_: *mut crate::leanh::LeanObject,
    mut v_____x_3522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3523_ = crate::leanh::lean_ctor_get(v_____x_3522_, 0);
    crate::leanh::lean_inc(v_fst_3523_);
    v_snd_3524_ = crate::leanh::lean_ctor_get(v_____x_3522_, 1);
    crate::leanh::lean_inc(v_snd_3524_);
    crate::leanh::lean_dec_ref(v_____x_3522_);
    v___x_3525_ = crate::leanh::lean_apply_2(v_f_3521_, v_fst_3523_, v_snd_3524_);
    return v___x_3525_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13___redArg(
    mut v_inst_3526_: *mut crate::leanh::LeanObject,
    mut v_x_3527_: *mut crate::leanh::LeanObject,
    mut v_f_3528_: *mut crate::leanh::LeanObject,
    mut v_a_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_3530_ = crate::leanh::lean_ctor_get(v_inst_3526_, 1);
    crate::leanh::lean_inc(v_toBind_3530_);
    crate::leanh::lean_dec_ref(v_inst_3526_);
    v___f_3531_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3531_, 0, v_f_3528_);
    v___x_3532_ = crate::leanh::lean_apply_1(v_x_3527_, v_a_3529_);
    v___x_3533_ = crate::leanh::lean_apply_4(
        v_toBind_3530_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3532_,
        v___f_3531_,
    );
    return v___x_3533_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13(
    mut v_00_u03b1_3534_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3535_: *mut crate::leanh::LeanObject,
    mut v_m_3536_: *mut crate::leanh::LeanObject,
    mut v_inst_3537_: *mut crate::leanh::LeanObject,
    mut v_inst_3538_: *mut crate::leanh::LeanObject,
    mut v_inst_3539_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3540_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3541_: *mut crate::leanh::LeanObject,
    mut v_x_3542_: *mut crate::leanh::LeanObject,
    mut v_f_3543_: *mut crate::leanh::LeanObject,
    mut v_a_3544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_3545_ = crate::leanh::lean_ctor_get(v_inst_3539_, 1);
    crate::leanh::lean_inc(v_toBind_3545_);
    crate::leanh::lean_dec_ref(v_inst_3539_);
    v___f_3546_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3546_, 0, v_f_3543_);
    v___x_3547_ = crate::leanh::lean_apply_1(v_x_3542_, v_a_3544_);
    v___x_3548_ = crate::leanh::lean_apply_4(
        v_toBind_3545_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3547_,
        v___f_3546_,
    );
    return v___x_3548_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13___boxed(
    mut v_00_u03b1_3549_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3550_: *mut crate::leanh::LeanObject,
    mut v_m_3551_: *mut crate::leanh::LeanObject,
    mut v_inst_3552_: *mut crate::leanh::LeanObject,
    mut v_inst_3553_: *mut crate::leanh::LeanObject,
    mut v_inst_3554_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3555_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3556_: *mut crate::leanh::LeanObject,
    mut v_x_3557_: *mut crate::leanh::LeanObject,
    mut v_f_3558_: *mut crate::leanh::LeanObject,
    mut v_a_3559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3560_ = l_Lean_MonadStateCacheT_instMonad___aux__13(
        v_00_u03b1_3549_,
        v_00_u03b2_3550_,
        v_m_3551_,
        v_inst_3552_,
        v_inst_3553_,
        v_inst_3554_,
        v_00_u03b1_3555_,
        v_00_u03b2_3556_,
        v_x_3557_,
        v_f_3558_,
        v_a_3559_,
    );
    crate::leanh::lean_dec_ref(v_inst_3553_);
    crate::leanh::lean_dec_ref(v_inst_3552_);
    return v_res_3560_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___redArg(
    mut v_inst_3561_: *mut crate::leanh::LeanObject,
    mut v_inst_3562_: *mut crate::leanh::LeanObject,
    mut v_inst_3563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_3563_, 6);
    crate::leanh::lean_inc_ref_n(v_inst_3562_, 6);
    crate::leanh::lean_inc_ref_n(v_inst_3561_, 6);
    v___x_3564_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__1___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3564_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3564_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3564_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3564_, 3, v_inst_3561_);
    crate::leanh::lean_closure_set(v___x_3564_, 4, v_inst_3562_);
    crate::leanh::lean_closure_set(v___x_3564_, 5, v_inst_3563_);
    v___x_3565_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__3___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3565_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3565_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3565_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3565_, 3, v_inst_3561_);
    crate::leanh::lean_closure_set(v___x_3565_, 4, v_inst_3562_);
    crate::leanh::lean_closure_set(v___x_3565_, 5, v_inst_3563_);
    v___x_3566_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3566_, 0, v___x_3564_);
    crate::leanh::lean_ctor_set(v___x_3566_, 1, v___x_3565_);
    v___x_3567_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__5___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3567_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3567_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3567_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3567_, 3, v_inst_3561_);
    crate::leanh::lean_closure_set(v___x_3567_, 4, v_inst_3562_);
    crate::leanh::lean_closure_set(v___x_3567_, 5, v_inst_3563_);
    v___x_3568_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3568_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3568_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3568_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3568_, 3, v_inst_3561_);
    crate::leanh::lean_closure_set(v___x_3568_, 4, v_inst_3562_);
    crate::leanh::lean_closure_set(v___x_3568_, 5, v_inst_3563_);
    v___x_3569_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3569_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3569_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3569_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3569_, 3, v_inst_3561_);
    crate::leanh::lean_closure_set(v___x_3569_, 4, v_inst_3562_);
    crate::leanh::lean_closure_set(v___x_3569_, 5, v_inst_3563_);
    v___x_3570_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__11___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3570_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3570_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3570_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3570_, 3, v_inst_3561_);
    crate::leanh::lean_closure_set(v___x_3570_, 4, v_inst_3562_);
    crate::leanh::lean_closure_set(v___x_3570_, 5, v_inst_3563_);
    v___x_3571_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3571_, 0, v___x_3566_);
    crate::leanh::lean_ctor_set(v___x_3571_, 1, v___x_3567_);
    crate::leanh::lean_ctor_set(v___x_3571_, 2, v___x_3568_);
    crate::leanh::lean_ctor_set(v___x_3571_, 3, v___x_3569_);
    crate::leanh::lean_ctor_set(v___x_3571_, 4, v___x_3570_);
    v___x_3572_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3572_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3572_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3572_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3572_, 3, v_inst_3561_);
    crate::leanh::lean_closure_set(v___x_3572_, 4, v_inst_3562_);
    crate::leanh::lean_closure_set(v___x_3572_, 5, v_inst_3563_);
    v___x_3573_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3573_, 0, v___x_3571_);
    crate::leanh::lean_ctor_set(v___x_3573_, 1, v___x_3572_);
    return v___x_3573_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad(
    mut v_00_u03b1_3574_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3575_: *mut crate::leanh::LeanObject,
    mut v_m_3576_: *mut crate::leanh::LeanObject,
    mut v_inst_3577_: *mut crate::leanh::LeanObject,
    mut v_inst_3578_: *mut crate::leanh::LeanObject,
    mut v_inst_3579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3580_ =
        l_Lean_MonadStateCacheT_instMonad___redArg(v_inst_3577_, v_inst_3578_, v_inst_3579_);
    return v___x_3580_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0(
    mut v_a_3581_: *mut crate::leanh::LeanObject,
    mut v_toPure_3582_: *mut crate::leanh::LeanObject,
    mut v_a_3583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3584_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3584_, 0, v_a_3583_);
    crate::leanh::lean_ctor_set(v___x_3584_, 1, v_a_3581_);
    v___x_3585_ =
        crate::leanh::lean_apply_2(v_toPure_3582_, crate::leanh::lean_box(0), v___x_3584_);
    return v___x_3585_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg(
    mut v_inst_3586_: *mut crate::leanh::LeanObject,
    mut v_t_3587_: *mut crate::leanh::LeanObject,
    mut v_a_3588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3589_ = crate::leanh::lean_ctor_get(v_inst_3586_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3589_);
    v_toBind_3590_ = crate::leanh::lean_ctor_get(v_inst_3586_, 1);
    crate::leanh::lean_inc(v_toBind_3590_);
    crate::leanh::lean_dec_ref(v_inst_3586_);
    v_toPure_3591_ = crate::leanh::lean_ctor_get(v_toApplicative_3589_, 1);
    crate::leanh::lean_inc(v_toPure_3591_);
    crate::leanh::lean_dec_ref(v_toApplicative_3589_);
    v___f_3592_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3592_, 0, v_a_3588_);
    crate::leanh::lean_closure_set(v___f_3592_, 1, v_toPure_3591_);
    v___x_3593_ = crate::leanh::lean_apply_4(
        v_toBind_3590_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_t_3587_,
        v___f_3592_,
    );
    return v___x_3593_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1(
    mut v_00_u03b1_3594_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3595_: *mut crate::leanh::LeanObject,
    mut v_m_3596_: *mut crate::leanh::LeanObject,
    mut v_inst_3597_: *mut crate::leanh::LeanObject,
    mut v_inst_3598_: *mut crate::leanh::LeanObject,
    mut v_inst_3599_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3600_: *mut crate::leanh::LeanObject,
    mut v_t_3601_: *mut crate::leanh::LeanObject,
    mut v_a_3602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3603_ = crate::leanh::lean_ctor_get(v_inst_3599_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3603_);
    v_toBind_3604_ = crate::leanh::lean_ctor_get(v_inst_3599_, 1);
    crate::leanh::lean_inc(v_toBind_3604_);
    crate::leanh::lean_dec_ref(v_inst_3599_);
    v_toPure_3605_ = crate::leanh::lean_ctor_get(v_toApplicative_3603_, 1);
    crate::leanh::lean_inc(v_toPure_3605_);
    crate::leanh::lean_dec_ref(v_toApplicative_3603_);
    v___f_3606_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3606_, 0, v_a_3602_);
    crate::leanh::lean_closure_set(v___f_3606_, 1, v_toPure_3605_);
    v___x_3607_ = crate::leanh::lean_apply_4(
        v_toBind_3604_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_t_3601_,
        v___f_3606_,
    );
    return v___x_3607_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed(
    mut v_00_u03b1_3608_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3609_: *mut crate::leanh::LeanObject,
    mut v_m_3610_: *mut crate::leanh::LeanObject,
    mut v_inst_3611_: *mut crate::leanh::LeanObject,
    mut v_inst_3612_: *mut crate::leanh::LeanObject,
    mut v_inst_3613_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3614_: *mut crate::leanh::LeanObject,
    mut v_t_3615_: *mut crate::leanh::LeanObject,
    mut v_a_3616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3617_ = l_Lean_MonadStateCacheT_instMonadLift___aux__1(
        v_00_u03b1_3608_,
        v_00_u03b2_3609_,
        v_m_3610_,
        v_inst_3611_,
        v_inst_3612_,
        v_inst_3613_,
        v_00_u03b1_3614_,
        v_t_3615_,
        v_a_3616_,
    );
    crate::leanh::lean_dec_ref(v_inst_3612_);
    crate::leanh::lean_dec_ref(v_inst_3611_);
    return v_res_3617_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___redArg(
    mut v_inst_3618_: *mut crate::leanh::LeanObject,
    mut v_inst_3619_: *mut crate::leanh::LeanObject,
    mut v_inst_3620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3621_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3621_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3621_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3621_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3621_, 3, v_inst_3618_);
    crate::leanh::lean_closure_set(v___x_3621_, 4, v_inst_3619_);
    crate::leanh::lean_closure_set(v___x_3621_, 5, v_inst_3620_);
    return v___x_3621_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift(
    mut v_00_u03b1_3622_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3623_: *mut crate::leanh::LeanObject,
    mut v_m_3624_: *mut crate::leanh::LeanObject,
    mut v_inst_3625_: *mut crate::leanh::LeanObject,
    mut v_inst_3626_: *mut crate::leanh::LeanObject,
    mut v_inst_3627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3628_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3628_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3628_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3628_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3628_, 3, v_inst_3625_);
    crate::leanh::lean_closure_set(v___x_3628_, 4, v_inst_3626_);
    crate::leanh::lean_closure_set(v___x_3628_, 5, v_inst_3627_);
    return v___x_3628_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___redArg(
    mut v_inst_3629_: *mut crate::leanh::LeanObject,
    mut v_inst_3630_: *mut crate::leanh::LeanObject,
    mut v_a_3631_: *mut crate::leanh::LeanObject,
    mut v_a_3632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_throw_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3633_ = crate::leanh::lean_ctor_get(v_inst_3629_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3633_);
    v_throw_3634_ = crate::leanh::lean_ctor_get(v_inst_3630_, 0);
    crate::leanh::lean_inc(v_throw_3634_);
    crate::leanh::lean_dec_ref(v_inst_3630_);
    v_toBind_3635_ = crate::leanh::lean_ctor_get(v_inst_3629_, 1);
    crate::leanh::lean_inc(v_toBind_3635_);
    crate::leanh::lean_dec_ref(v_inst_3629_);
    v_toPure_3636_ = crate::leanh::lean_ctor_get(v_toApplicative_3633_, 1);
    crate::leanh::lean_inc(v_toPure_3636_);
    crate::leanh::lean_dec_ref(v_toApplicative_3633_);
    v___x_3637_ = crate::leanh::lean_apply_2(v_throw_3634_, crate::leanh::lean_box(0), v_a_3631_);
    v___f_3638_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3638_, 0, v_a_3632_);
    crate::leanh::lean_closure_set(v___f_3638_, 1, v_toPure_3636_);
    v___x_3639_ = crate::leanh::lean_apply_4(
        v_toBind_3635_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3637_,
        v___f_3638_,
    );
    return v___x_3639_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1(
    mut v_00_u03b1_3640_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3641_: *mut crate::leanh::LeanObject,
    mut v_m_3642_: *mut crate::leanh::LeanObject,
    mut v_inst_3643_: *mut crate::leanh::LeanObject,
    mut v_inst_3644_: *mut crate::leanh::LeanObject,
    mut v_inst_3645_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_3646_: *mut crate::leanh::LeanObject,
    mut v_inst_3647_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3648_: *mut crate::leanh::LeanObject,
    mut v_a_3649_: *mut crate::leanh::LeanObject,
    mut v_a_3650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_throw_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3651_ = crate::leanh::lean_ctor_get(v_inst_3645_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3651_);
    v_throw_3652_ = crate::leanh::lean_ctor_get(v_inst_3647_, 0);
    crate::leanh::lean_inc(v_throw_3652_);
    crate::leanh::lean_dec_ref(v_inst_3647_);
    v_toBind_3653_ = crate::leanh::lean_ctor_get(v_inst_3645_, 1);
    crate::leanh::lean_inc(v_toBind_3653_);
    crate::leanh::lean_dec_ref(v_inst_3645_);
    v_toPure_3654_ = crate::leanh::lean_ctor_get(v_toApplicative_3651_, 1);
    crate::leanh::lean_inc(v_toPure_3654_);
    crate::leanh::lean_dec_ref(v_toApplicative_3651_);
    v___x_3655_ = crate::leanh::lean_apply_2(v_throw_3652_, crate::leanh::lean_box(0), v_a_3649_);
    v___f_3656_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3656_, 0, v_a_3650_);
    crate::leanh::lean_closure_set(v___f_3656_, 1, v_toPure_3654_);
    v___x_3657_ = crate::leanh::lean_apply_4(
        v_toBind_3653_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3655_,
        v___f_3656_,
    );
    return v___x_3657_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed(
    mut v_00_u03b1_3658_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3659_: *mut crate::leanh::LeanObject,
    mut v_m_3660_: *mut crate::leanh::LeanObject,
    mut v_inst_3661_: *mut crate::leanh::LeanObject,
    mut v_inst_3662_: *mut crate::leanh::LeanObject,
    mut v_inst_3663_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_3664_: *mut crate::leanh::LeanObject,
    mut v_inst_3665_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3666_: *mut crate::leanh::LeanObject,
    mut v_a_3667_: *mut crate::leanh::LeanObject,
    mut v_a_3668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3669_ = l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1(
        v_00_u03b1_3658_,
        v_00_u03b2_3659_,
        v_m_3660_,
        v_inst_3661_,
        v_inst_3662_,
        v_inst_3663_,
        v_00_u03b5_3664_,
        v_inst_3665_,
        v_00_u03b1_3666_,
        v_a_3667_,
        v_a_3668_,
    );
    crate::leanh::lean_dec_ref(v_inst_3662_);
    crate::leanh::lean_dec_ref(v_inst_3661_);
    return v_res_3669_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0(
    mut v_c_3670_: *mut crate::leanh::LeanObject,
    mut v_s_3671_: *mut crate::leanh::LeanObject,
    mut v_e_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3673_ = crate::leanh::lean_apply_2(v_c_3670_, v_e_3672_, v_s_3671_);
    return v___x_3673_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg(
    mut v_inst_3674_: *mut crate::leanh::LeanObject,
    mut v_x_3675_: *mut crate::leanh::LeanObject,
    mut v_c_3676_: *mut crate::leanh::LeanObject,
    mut v_s_3677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_3678_ = crate::leanh::lean_ctor_get(v_inst_3674_, 1);
    crate::leanh::lean_inc(v_tryCatch_3678_);
    crate::leanh::lean_dec_ref(v_inst_3674_);
    crate::leanh::lean_inc_ref(v_s_3677_);
    v___f_3679_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3679_, 0, v_c_3676_);
    crate::leanh::lean_closure_set(v___f_3679_, 1, v_s_3677_);
    v___x_3680_ = crate::leanh::lean_apply_1(v_x_3675_, v_s_3677_);
    v___x_3681_ = crate::leanh::lean_apply_3(
        v_tryCatch_3678_,
        crate::leanh::lean_box(0),
        v___x_3680_,
        v___f_3679_,
    );
    return v___x_3681_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3(
    mut v_00_u03b1_3682_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3683_: *mut crate::leanh::LeanObject,
    mut v_m_3684_: *mut crate::leanh::LeanObject,
    mut v_inst_3685_: *mut crate::leanh::LeanObject,
    mut v_inst_3686_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_3687_: *mut crate::leanh::LeanObject,
    mut v_inst_3688_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3689_: *mut crate::leanh::LeanObject,
    mut v_x_3690_: *mut crate::leanh::LeanObject,
    mut v_c_3691_: *mut crate::leanh::LeanObject,
    mut v_s_3692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_3693_ = crate::leanh::lean_ctor_get(v_inst_3688_, 1);
    crate::leanh::lean_inc(v_tryCatch_3693_);
    crate::leanh::lean_dec_ref(v_inst_3688_);
    crate::leanh::lean_inc_ref(v_s_3692_);
    v___f_3694_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3694_, 0, v_c_3691_);
    crate::leanh::lean_closure_set(v___f_3694_, 1, v_s_3692_);
    v___x_3695_ = crate::leanh::lean_apply_1(v_x_3690_, v_s_3692_);
    v___x_3696_ = crate::leanh::lean_apply_3(
        v_tryCatch_3693_,
        crate::leanh::lean_box(0),
        v___x_3695_,
        v___f_3694_,
    );
    return v___x_3696_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed(
    mut v_00_u03b1_3697_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3698_: *mut crate::leanh::LeanObject,
    mut v_m_3699_: *mut crate::leanh::LeanObject,
    mut v_inst_3700_: *mut crate::leanh::LeanObject,
    mut v_inst_3701_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_3702_: *mut crate::leanh::LeanObject,
    mut v_inst_3703_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3704_: *mut crate::leanh::LeanObject,
    mut v_x_3705_: *mut crate::leanh::LeanObject,
    mut v_c_3706_: *mut crate::leanh::LeanObject,
    mut v_s_3707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3708_ = l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3(
        v_00_u03b1_3697_,
        v_00_u03b2_3698_,
        v_m_3699_,
        v_inst_3700_,
        v_inst_3701_,
        v_00_u03b5_3702_,
        v_inst_3703_,
        v_00_u03b1_3704_,
        v_x_3705_,
        v_c_3706_,
        v_s_3707_,
    );
    crate::leanh::lean_dec_ref(v_inst_3701_);
    crate::leanh::lean_dec_ref(v_inst_3700_);
    return v_res_3708_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(
    mut v_inst_3709_: *mut crate::leanh::LeanObject,
    mut v_inst_3710_: *mut crate::leanh::LeanObject,
    mut v_inst_3711_: *mut crate::leanh::LeanObject,
    mut v_inst_3712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_3712_);
    crate::leanh::lean_inc_ref(v_inst_3710_);
    crate::leanh::lean_inc_ref(v_inst_3709_);
    v___x_3713_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed as *mut core::ffi::c_void,
        11,
        8,
    );
    crate::leanh::lean_closure_set(v___x_3713_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3713_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3713_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3713_, 3, v_inst_3709_);
    crate::leanh::lean_closure_set(v___x_3713_, 4, v_inst_3710_);
    crate::leanh::lean_closure_set(v___x_3713_, 5, v_inst_3711_);
    crate::leanh::lean_closure_set(v___x_3713_, 6, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3713_, 7, v_inst_3712_);
    v___x_3714_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed as *mut core::ffi::c_void,
        11,
        7,
    );
    crate::leanh::lean_closure_set(v___x_3714_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3714_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3714_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3714_, 3, v_inst_3709_);
    crate::leanh::lean_closure_set(v___x_3714_, 4, v_inst_3710_);
    crate::leanh::lean_closure_set(v___x_3714_, 5, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3714_, 6, v_inst_3712_);
    v___x_3715_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3715_, 0, v___x_3713_);
    crate::leanh::lean_ctor_set(v___x_3715_, 1, v___x_3714_);
    return v___x_3715_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf(
    mut v_00_u03b1_3716_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3717_: *mut crate::leanh::LeanObject,
    mut v_m_3718_: *mut crate::leanh::LeanObject,
    mut v_inst_3719_: *mut crate::leanh::LeanObject,
    mut v_inst_3720_: *mut crate::leanh::LeanObject,
    mut v_inst_3721_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_3722_: *mut crate::leanh::LeanObject,
    mut v_inst_3723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3724_ = l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(
        v_inst_3719_,
        v_inst_3720_,
        v_inst_3721_,
        v_inst_3723_,
    );
    return v___x_3724_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0(
    mut v_fst_3725_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3726_: *mut crate::leanh::LeanObject,
    mut v_x_3727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3728_ = crate::leanh::lean_apply_1(v_x_3727_, v_fst_3725_);
    return v___x_3728_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1(
    mut v_snd_3729_: *mut crate::leanh::LeanObject,
    mut v_toPure_3730_: *mut crate::leanh::LeanObject,
    mut v_a_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3732_, 0, v_a_3731_);
    crate::leanh::lean_ctor_set(v___x_3732_, 1, v_snd_3729_);
    v___x_3733_ =
        crate::leanh::lean_apply_2(v_toPure_3730_, crate::leanh::lean_box(0), v___x_3732_);
    return v___x_3733_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2(
    mut v_f_3734_: *mut crate::leanh::LeanObject,
    mut v_toPure_3735_: *mut crate::leanh::LeanObject,
    mut v_toBind_3736_: *mut crate::leanh::LeanObject,
    mut v_____x_3737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3738_ = crate::leanh::lean_ctor_get(v_____x_3737_, 0);
    crate::leanh::lean_inc(v_fst_3738_);
    v_snd_3739_ = crate::leanh::lean_ctor_get(v_____x_3737_, 1);
    crate::leanh::lean_inc(v_snd_3739_);
    crate::leanh::lean_dec_ref(v_____x_3737_);
    v___f_3740_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3740_, 0, v_fst_3738_);
    v___x_3741_ = crate::leanh::lean_apply_1(v_f_3734_, v___f_3740_);
    v___f_3742_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3742_, 0, v_snd_3739_);
    crate::leanh::lean_closure_set(v___f_3742_, 1, v_toPure_3735_);
    v___x_3743_ = crate::leanh::lean_apply_4(
        v_toBind_3736_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3741_,
        v___f_3742_,
    );
    return v___x_3743_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg(
    mut v_inst_3744_: *mut crate::leanh::LeanObject,
    mut v_f_3745_: *mut crate::leanh::LeanObject,
    mut v_a_3746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3751_: u8 = 0;
    let mut v_toPure_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3747_ = crate::leanh::lean_ctor_get(v_inst_3744_, 0);
                v_toBind_3748_ = crate::leanh::lean_ctor_get(v_inst_3744_, 1);
                v_isSharedCheck_3759_ = (!crate::leanh::lean_is_exclusive(v_inst_3744_)) as u8;
                if v_isSharedCheck_3759_ == 0 {
                    v___x_3750_ = v_inst_3744_;
                    v_isShared_3751_ = v_isSharedCheck_3759_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toBind_3748_);
                    crate::leanh::lean_inc(v_toApplicative_3747_);
                    crate::leanh::lean_dec(v_inst_3744_);
                    v___x_3750_ = crate::leanh::lean_box(0);
                    v_isShared_3751_ = v_isSharedCheck_3759_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3752_ = crate::leanh::lean_ctor_get(v_toApplicative_3747_, 1);
                crate::leanh::lean_inc_n(v_toPure_3752_, 2);
                crate::leanh::lean_dec_ref(v_toApplicative_3747_);
                crate::leanh::lean_inc(v_toBind_3748_);
                v___f_3753_ = crate::leanh::lean_alloc_closure(
                    l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3753_, 0, v_f_3745_);
                crate::leanh::lean_closure_set(v___f_3753_, 1, v_toPure_3752_);
                crate::leanh::lean_closure_set(v___f_3753_, 2, v_toBind_3748_);
                crate::leanh::lean_inc_ref(v_a_3746_);
                if v_isShared_3751_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3750_, 1, v_a_3746_);
                    crate::leanh::lean_ctor_set(v___x_3750_, 0, v_a_3746_);
                    v___x_3755_ = v___x_3750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3758_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_a_3746_);
                    v___x_3755_ = v_reuseFailAlloc_3758_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3756_ = crate::leanh::lean_apply_2(
                    v_toPure_3752_,
                    crate::leanh::lean_box(0),
                    v___x_3755_,
                );
                v___x_3757_ = crate::leanh::lean_apply_4(
                    v_toBind_3748_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3756_,
                    v___f_3753_,
                );
                return v___x_3757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1(
    mut v_00_u03b1_3760_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3761_: *mut crate::leanh::LeanObject,
    mut v_m_3762_: *mut crate::leanh::LeanObject,
    mut v_inst_3763_: *mut crate::leanh::LeanObject,
    mut v_inst_3764_: *mut crate::leanh::LeanObject,
    mut v_inst_3765_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3766_: *mut crate::leanh::LeanObject,
    mut v_f_3767_: *mut crate::leanh::LeanObject,
    mut v_a_3768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3773_: u8 = 0;
    let mut v_toPure_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3769_ = crate::leanh::lean_ctor_get(v_inst_3765_, 0);
                v_toBind_3770_ = crate::leanh::lean_ctor_get(v_inst_3765_, 1);
                v_isSharedCheck_3781_ = (!crate::leanh::lean_is_exclusive(v_inst_3765_)) as u8;
                if v_isSharedCheck_3781_ == 0 {
                    v___x_3772_ = v_inst_3765_;
                    v_isShared_3773_ = v_isSharedCheck_3781_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toBind_3770_);
                    crate::leanh::lean_inc(v_toApplicative_3769_);
                    crate::leanh::lean_dec(v_inst_3765_);
                    v___x_3772_ = crate::leanh::lean_box(0);
                    v_isShared_3773_ = v_isSharedCheck_3781_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3774_ = crate::leanh::lean_ctor_get(v_toApplicative_3769_, 1);
                crate::leanh::lean_inc_n(v_toPure_3774_, 2);
                crate::leanh::lean_dec_ref(v_toApplicative_3769_);
                crate::leanh::lean_inc(v_toBind_3770_);
                v___f_3775_ = crate::leanh::lean_alloc_closure(
                    l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3775_, 0, v_f_3767_);
                crate::leanh::lean_closure_set(v___f_3775_, 1, v_toPure_3774_);
                crate::leanh::lean_closure_set(v___f_3775_, 2, v_toBind_3770_);
                crate::leanh::lean_inc_ref(v_a_3768_);
                if v_isShared_3773_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3772_, 1, v_a_3768_);
                    crate::leanh::lean_ctor_set(v___x_3772_, 0, v_a_3768_);
                    v___x_3777_ = v___x_3772_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_a_3768_);
                    v___x_3777_ = v_reuseFailAlloc_3780_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3778_ = crate::leanh::lean_apply_2(
                    v_toPure_3774_,
                    crate::leanh::lean_box(0),
                    v___x_3777_,
                );
                v___x_3779_ = crate::leanh::lean_apply_4(
                    v_toBind_3770_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3778_,
                    v___f_3775_,
                );
                return v___x_3779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___boxed(
    mut v_00_u03b1_3782_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3783_: *mut crate::leanh::LeanObject,
    mut v_m_3784_: *mut crate::leanh::LeanObject,
    mut v_inst_3785_: *mut crate::leanh::LeanObject,
    mut v_inst_3786_: *mut crate::leanh::LeanObject,
    mut v_inst_3787_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3788_: *mut crate::leanh::LeanObject,
    mut v_f_3789_: *mut crate::leanh::LeanObject,
    mut v_a_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Lean_MonadStateCacheT_instMonadControl___aux__1(
        v_00_u03b1_3782_,
        v_00_u03b2_3783_,
        v_m_3784_,
        v_inst_3785_,
        v_inst_3786_,
        v_inst_3787_,
        v_00_u03b1_3788_,
        v_f_3789_,
        v_a_3790_,
    );
    crate::leanh::lean_dec_ref(v_inst_3786_);
    crate::leanh::lean_dec_ref(v_inst_3785_);
    return v_res_3791_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0(
    mut v_fst_3792_: *mut crate::leanh::LeanObject,
    mut v_toPure_3793_: *mut crate::leanh::LeanObject,
    mut v_____x_3794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3798_: u8 = 0;
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_unused_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3795_ = crate::leanh::lean_ctor_get(v_____x_3794_, 1);
                v_isSharedCheck_3803_ = (!crate::leanh::lean_is_exclusive(v_____x_3794_)) as u8;
                if v_isSharedCheck_3803_ == 0 {
                    v_unused_3804_ = crate::leanh::lean_ctor_get(v_____x_3794_, 0);
                    crate::leanh::lean_dec(v_unused_3804_);
                    v___x_3797_ = v_____x_3794_;
                    v_isShared_3798_ = v_isSharedCheck_3803_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3795_);
                    crate::leanh::lean_dec(v_____x_3794_);
                    v___x_3797_ = crate::leanh::lean_box(0);
                    v_isShared_3798_ = v_isSharedCheck_3803_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3798_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3797_, 0, v_fst_3792_);
                    v___x_3800_ = v___x_3797_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_fst_3792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_snd_3795_);
                    v___x_3800_ = v_reuseFailAlloc_3802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3801_ = crate::leanh::lean_apply_2(
                    v_toPure_3793_,
                    crate::leanh::lean_box(0),
                    v___x_3800_,
                );
                return v___x_3801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1(
    mut v_toPure_3805_: *mut crate::leanh::LeanObject,
    mut v_toBind_3806_: *mut crate::leanh::LeanObject,
    mut v_____x_3807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3813_: u8 = 0;
    let mut v___f_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3808_ = crate::leanh::lean_ctor_get(v_____x_3807_, 0);
                crate::leanh::lean_inc(v_fst_3808_);
                crate::leanh::lean_dec_ref(v_____x_3807_);
                v_fst_3809_ = crate::leanh::lean_ctor_get(v_fst_3808_, 0);
                v_snd_3810_ = crate::leanh::lean_ctor_get(v_fst_3808_, 1);
                v_isSharedCheck_3821_ = (!crate::leanh::lean_is_exclusive(v_fst_3808_)) as u8;
                if v_isSharedCheck_3821_ == 0 {
                    v___x_3812_ = v_fst_3808_;
                    v_isShared_3813_ = v_isSharedCheck_3821_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3810_);
                    crate::leanh::lean_inc(v_fst_3809_);
                    crate::leanh::lean_dec(v_fst_3808_);
                    v___x_3812_ = crate::leanh::lean_box(0);
                    v_isShared_3813_ = v_isSharedCheck_3821_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_toPure_3805_);
                v___f_3814_ = crate::leanh::lean_alloc_closure(
                    l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3814_, 0, v_fst_3809_);
                crate::leanh::lean_closure_set(v___f_3814_, 1, v_toPure_3805_);
                v___x_3815_ = crate::leanh::lean_box(0);
                if v_isShared_3813_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3812_, 0, v___x_3815_);
                    v___x_3817_ = v___x_3812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_snd_3810_);
                    v___x_3817_ = v_reuseFailAlloc_3820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3818_ = crate::leanh::lean_apply_2(
                    v_toPure_3805_,
                    crate::leanh::lean_box(0),
                    v___x_3817_,
                );
                v___x_3819_ = crate::leanh::lean_apply_4(
                    v_toBind_3806_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3818_,
                    v___f_3814_,
                );
                return v___x_3819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2(
    mut v_a_3822_: *mut crate::leanh::LeanObject,
    mut v_toPure_3823_: *mut crate::leanh::LeanObject,
    mut v_a_3824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3825_, 0, v_a_3824_);
    crate::leanh::lean_ctor_set(v___x_3825_, 1, v_a_3822_);
    v___x_3826_ =
        crate::leanh::lean_apply_2(v_toPure_3823_, crate::leanh::lean_box(0), v___x_3825_);
    return v___x_3826_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg(
    mut v_inst_3827_: *mut crate::leanh::LeanObject,
    mut v_x_3828_: *mut crate::leanh::LeanObject,
    mut v_a_3829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3830_ = crate::leanh::lean_ctor_get(v_inst_3827_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3830_);
    v_toBind_3831_ = crate::leanh::lean_ctor_get(v_inst_3827_, 1);
    crate::leanh::lean_inc_n(v_toBind_3831_, 3);
    crate::leanh::lean_dec_ref(v_inst_3827_);
    v_toPure_3832_ = crate::leanh::lean_ctor_get(v_toApplicative_3830_, 1);
    crate::leanh::lean_inc_n(v_toPure_3832_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3830_);
    v___f_3833_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3833_, 0, v_toPure_3832_);
    crate::leanh::lean_closure_set(v___f_3833_, 1, v_toBind_3831_);
    v___f_3834_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3834_, 0, v_a_3829_);
    crate::leanh::lean_closure_set(v___f_3834_, 1, v_toPure_3832_);
    v___x_3835_ = crate::leanh::lean_apply_4(
        v_toBind_3831_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_3828_,
        v___f_3834_,
    );
    v___x_3836_ = crate::leanh::lean_apply_4(
        v_toBind_3831_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3835_,
        v___f_3833_,
    );
    return v___x_3836_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3(
    mut v_00_u03b1_3837_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3838_: *mut crate::leanh::LeanObject,
    mut v_m_3839_: *mut crate::leanh::LeanObject,
    mut v_inst_3840_: *mut crate::leanh::LeanObject,
    mut v_inst_3841_: *mut crate::leanh::LeanObject,
    mut v_inst_3842_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3843_: *mut crate::leanh::LeanObject,
    mut v_x_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3846_ = crate::leanh::lean_ctor_get(v_inst_3842_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3846_);
    v_toBind_3847_ = crate::leanh::lean_ctor_get(v_inst_3842_, 1);
    crate::leanh::lean_inc_n(v_toBind_3847_, 3);
    crate::leanh::lean_dec_ref(v_inst_3842_);
    v_toPure_3848_ = crate::leanh::lean_ctor_get(v_toApplicative_3846_, 1);
    crate::leanh::lean_inc_n(v_toPure_3848_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_3846_);
    v___f_3849_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3849_, 0, v_toPure_3848_);
    crate::leanh::lean_closure_set(v___f_3849_, 1, v_toBind_3847_);
    v___f_3850_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3850_, 0, v_a_3845_);
    crate::leanh::lean_closure_set(v___f_3850_, 1, v_toPure_3848_);
    v___x_3851_ = crate::leanh::lean_apply_4(
        v_toBind_3847_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_3844_,
        v___f_3850_,
    );
    v___x_3852_ = crate::leanh::lean_apply_4(
        v_toBind_3847_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3851_,
        v___f_3849_,
    );
    return v___x_3852_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed(
    mut v_00_u03b1_3853_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3854_: *mut crate::leanh::LeanObject,
    mut v_m_3855_: *mut crate::leanh::LeanObject,
    mut v_inst_3856_: *mut crate::leanh::LeanObject,
    mut v_inst_3857_: *mut crate::leanh::LeanObject,
    mut v_inst_3858_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3859_: *mut crate::leanh::LeanObject,
    mut v_x_3860_: *mut crate::leanh::LeanObject,
    mut v_a_3861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3862_ = l_Lean_MonadStateCacheT_instMonadControl___aux__3(
        v_00_u03b1_3853_,
        v_00_u03b2_3854_,
        v_m_3855_,
        v_inst_3856_,
        v_inst_3857_,
        v_inst_3858_,
        v_00_u03b1_3859_,
        v_x_3860_,
        v_a_3861_,
    );
    crate::leanh::lean_dec_ref(v_inst_3857_);
    crate::leanh::lean_dec_ref(v_inst_3856_);
    return v_res_3862_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___redArg(
    mut v_inst_3863_: *mut crate::leanh::LeanObject,
    mut v_inst_3864_: *mut crate::leanh::LeanObject,
    mut v_inst_3865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_3865_);
    crate::leanh::lean_inc_ref(v_inst_3864_);
    crate::leanh::lean_inc_ref(v_inst_3863_);
    v___x_3866_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__1___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3866_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3866_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3866_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3866_, 3, v_inst_3863_);
    crate::leanh::lean_closure_set(v___x_3866_, 4, v_inst_3864_);
    crate::leanh::lean_closure_set(v___x_3866_, 5, v_inst_3865_);
    v___x_3867_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___x_3867_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3867_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3867_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3867_, 3, v_inst_3863_);
    crate::leanh::lean_closure_set(v___x_3867_, 4, v_inst_3864_);
    crate::leanh::lean_closure_set(v___x_3867_, 5, v_inst_3865_);
    v___x_3868_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3868_, 0, v___x_3866_);
    crate::leanh::lean_ctor_set(v___x_3868_, 1, v___x_3867_);
    return v___x_3868_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl(
    mut v_00_u03b1_3869_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3870_: *mut crate::leanh::LeanObject,
    mut v_m_3871_: *mut crate::leanh::LeanObject,
    mut v_inst_3872_: *mut crate::leanh::LeanObject,
    mut v_inst_3873_: *mut crate::leanh::LeanObject,
    mut v_inst_3874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3875_ =
        l_Lean_MonadStateCacheT_instMonadControl___redArg(v_inst_3872_, v_inst_3873_, v_inst_3874_);
    return v___x_3875_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0(
    mut v_h_3876_: *mut crate::leanh::LeanObject,
    mut v_s_3877_: *mut crate::leanh::LeanObject,
    mut v_x_3878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3884_: u8 = 0;
    let mut v_fst_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3878_) == 0 {
                    v___x_3879_ = crate::leanh::lean_box(0);
                    v___x_3880_ = crate::leanh::lean_apply_2(v_h_3876_, v___x_3879_, v_s_3877_);
                    return v___x_3880_;
                } else {
                    crate::leanh::lean_dec_ref(v_s_3877_);
                    v_val_3881_ = crate::leanh::lean_ctor_get(v_x_3878_, 0);
                    v_isSharedCheck_3891_ = (!crate::leanh::lean_is_exclusive(v_x_3878_)) as u8;
                    if v_isSharedCheck_3891_ == 0 {
                        v___x_3883_ = v_x_3878_;
                        v_isShared_3884_ = v_isSharedCheck_3891_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3881_);
                        crate::leanh::lean_dec(v_x_3878_);
                        v___x_3883_ = crate::leanh::lean_box(0);
                        v_isShared_3884_ = v_isSharedCheck_3891_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3885_ = crate::leanh::lean_ctor_get(v_val_3881_, 0);
                crate::leanh::lean_inc(v_fst_3885_);
                v_snd_3886_ = crate::leanh::lean_ctor_get(v_val_3881_, 1);
                crate::leanh::lean_inc(v_snd_3886_);
                crate::leanh::lean_dec(v_val_3881_);
                if v_isShared_3884_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3883_, 0, v_fst_3885_);
                    v___x_3888_ = v___x_3883_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3890_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_fst_3885_);
                    v___x_3888_ = v_reuseFailAlloc_3890_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3889_ = crate::leanh::lean_apply_2(v_h_3876_, v___x_3888_, v_snd_3886_);
                return v___x_3889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1(
    mut v_toPure_3892_: *mut crate::leanh::LeanObject,
    mut v_____x_3893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v_fst_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3904_: u8 = 0;
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3912_: u8 = 0;
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_unused_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3894_ = crate::leanh::lean_ctor_get(v_____x_3893_, 0);
                crate::leanh::lean_inc(v_fst_3894_);
                v_snd_3895_ = crate::leanh::lean_ctor_get(v_____x_3893_, 1);
                crate::leanh::lean_inc(v_snd_3895_);
                crate::leanh::lean_dec_ref(v_____x_3893_);
                v_fst_3896_ = crate::leanh::lean_ctor_get(v_fst_3894_, 0);
                v_isSharedCheck_3913_ = (!crate::leanh::lean_is_exclusive(v_fst_3894_)) as u8;
                if v_isSharedCheck_3913_ == 0 {
                    v_unused_3914_ = crate::leanh::lean_ctor_get(v_fst_3894_, 1);
                    crate::leanh::lean_dec(v_unused_3914_);
                    v___x_3898_ = v_fst_3894_;
                    v_isShared_3899_ = v_isSharedCheck_3913_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3896_);
                    crate::leanh::lean_dec(v_fst_3894_);
                    v___x_3898_ = crate::leanh::lean_box(0);
                    v_isShared_3899_ = v_isSharedCheck_3913_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3900_ = crate::leanh::lean_ctor_get(v_snd_3895_, 0);
                v_snd_3901_ = crate::leanh::lean_ctor_get(v_snd_3895_, 1);
                v_isSharedCheck_3912_ = (!crate::leanh::lean_is_exclusive(v_snd_3895_)) as u8;
                if v_isSharedCheck_3912_ == 0 {
                    v___x_3903_ = v_snd_3895_;
                    v_isShared_3904_ = v_isSharedCheck_3912_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3901_);
                    crate::leanh::lean_inc(v_fst_3900_);
                    crate::leanh::lean_dec(v_snd_3895_);
                    v___x_3903_ = crate::leanh::lean_box(0);
                    v_isShared_3904_ = v_isSharedCheck_3912_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3904_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3903_, 1, v_fst_3900_);
                    crate::leanh::lean_ctor_set(v___x_3903_, 0, v_fst_3896_);
                    v___x_3906_ = v___x_3903_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3911_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_fst_3896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_fst_3900_);
                    v___x_3906_ = v_reuseFailAlloc_3911_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3898_, 1, v_snd_3901_);
                    crate::leanh::lean_ctor_set(v___x_3898_, 0, v___x_3906_);
                    v___x_3908_ = v___x_3898_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3910_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3910_, 1, v_snd_3901_);
                    v___x_3908_ = v_reuseFailAlloc_3910_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3909_ = crate::leanh::lean_apply_2(
                    v_toPure_3892_,
                    crate::leanh::lean_box(0),
                    v___x_3908_,
                );
                return v___x_3909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg(
    mut v_inst_3915_: *mut crate::leanh::LeanObject,
    mut v_inst_3916_: *mut crate::leanh::LeanObject,
    mut v_x_3917_: *mut crate::leanh::LeanObject,
    mut v_h_3918_: *mut crate::leanh::LeanObject,
    mut v_s_3919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3920_ = crate::leanh::lean_ctor_get(v_inst_3915_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3920_);
    v_toBind_3921_ = crate::leanh::lean_ctor_get(v_inst_3915_, 1);
    crate::leanh::lean_inc(v_toBind_3921_);
    crate::leanh::lean_dec_ref(v_inst_3915_);
    v_toPure_3922_ = crate::leanh::lean_ctor_get(v_toApplicative_3920_, 1);
    crate::leanh::lean_inc(v_toPure_3922_);
    crate::leanh::lean_dec_ref(v_toApplicative_3920_);
    crate::leanh::lean_inc_ref(v_s_3919_);
    v___f_3923_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3923_, 0, v_h_3918_);
    crate::leanh::lean_closure_set(v___f_3923_, 1, v_s_3919_);
    v___x_3924_ = crate::leanh::lean_apply_1(v_x_3917_, v_s_3919_);
    v___f_3925_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3925_, 0, v_toPure_3922_);
    v___x_3926_ = crate::leanh::lean_apply_4(
        v_inst_3916_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3924_,
        v___f_3923_,
    );
    v___x_3927_ = crate::leanh::lean_apply_4(
        v_toBind_3921_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3926_,
        v___f_3925_,
    );
    return v___x_3927_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1(
    mut v_00_u03b1_3928_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3929_: *mut crate::leanh::LeanObject,
    mut v_m_3930_: *mut crate::leanh::LeanObject,
    mut v_inst_3931_: *mut crate::leanh::LeanObject,
    mut v_inst_3932_: *mut crate::leanh::LeanObject,
    mut v_inst_3933_: *mut crate::leanh::LeanObject,
    mut v_inst_3934_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3935_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3936_: *mut crate::leanh::LeanObject,
    mut v_x_3937_: *mut crate::leanh::LeanObject,
    mut v_h_3938_: *mut crate::leanh::LeanObject,
    mut v_s_3939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3940_ = crate::leanh::lean_ctor_get(v_inst_3933_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3940_);
    v_toBind_3941_ = crate::leanh::lean_ctor_get(v_inst_3933_, 1);
    crate::leanh::lean_inc(v_toBind_3941_);
    crate::leanh::lean_dec_ref(v_inst_3933_);
    v_toPure_3942_ = crate::leanh::lean_ctor_get(v_toApplicative_3940_, 1);
    crate::leanh::lean_inc(v_toPure_3942_);
    crate::leanh::lean_dec_ref(v_toApplicative_3940_);
    crate::leanh::lean_inc_ref(v_s_3939_);
    v___f_3943_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3943_, 0, v_h_3938_);
    crate::leanh::lean_closure_set(v___f_3943_, 1, v_s_3939_);
    v___x_3944_ = crate::leanh::lean_apply_1(v_x_3937_, v_s_3939_);
    v___f_3945_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3945_, 0, v_toPure_3942_);
    v___x_3946_ = crate::leanh::lean_apply_4(
        v_inst_3934_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3944_,
        v___f_3943_,
    );
    v___x_3947_ = crate::leanh::lean_apply_4(
        v_toBind_3941_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3946_,
        v___f_3945_,
    );
    return v___x_3947_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed(
    mut v_00_u03b1_3948_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3949_: *mut crate::leanh::LeanObject,
    mut v_m_3950_: *mut crate::leanh::LeanObject,
    mut v_inst_3951_: *mut crate::leanh::LeanObject,
    mut v_inst_3952_: *mut crate::leanh::LeanObject,
    mut v_inst_3953_: *mut crate::leanh::LeanObject,
    mut v_inst_3954_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3955_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3956_: *mut crate::leanh::LeanObject,
    mut v_x_3957_: *mut crate::leanh::LeanObject,
    mut v_h_3958_: *mut crate::leanh::LeanObject,
    mut v_s_3959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3960_ = l_Lean_MonadStateCacheT_instMonadFinally___aux__1(
        v_00_u03b1_3948_,
        v_00_u03b2_3949_,
        v_m_3950_,
        v_inst_3951_,
        v_inst_3952_,
        v_inst_3953_,
        v_inst_3954_,
        v_00_u03b1_3955_,
        v_00_u03b2_3956_,
        v_x_3957_,
        v_h_3958_,
        v_s_3959_,
    );
    crate::leanh::lean_dec_ref(v_inst_3952_);
    crate::leanh::lean_dec_ref(v_inst_3951_);
    return v_res_3960_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___redArg(
    mut v_inst_3961_: *mut crate::leanh::LeanObject,
    mut v_inst_3962_: *mut crate::leanh::LeanObject,
    mut v_inst_3963_: *mut crate::leanh::LeanObject,
    mut v_inst_3964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3965_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    crate::leanh::lean_closure_set(v___x_3965_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3965_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3965_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3965_, 3, v_inst_3961_);
    crate::leanh::lean_closure_set(v___x_3965_, 4, v_inst_3962_);
    crate::leanh::lean_closure_set(v___x_3965_, 5, v_inst_3963_);
    crate::leanh::lean_closure_set(v___x_3965_, 6, v_inst_3964_);
    return v___x_3965_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally(
    mut v_00_u03b1_3966_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3967_: *mut crate::leanh::LeanObject,
    mut v_m_3968_: *mut crate::leanh::LeanObject,
    mut v_inst_3969_: *mut crate::leanh::LeanObject,
    mut v_inst_3970_: *mut crate::leanh::LeanObject,
    mut v_inst_3971_: *mut crate::leanh::LeanObject,
    mut v_inst_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3973_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    crate::leanh::lean_closure_set(v___x_3973_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3973_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3973_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3973_, 3, v_inst_3969_);
    crate::leanh::lean_closure_set(v___x_3973_, 4, v_inst_3970_);
    crate::leanh::lean_closure_set(v___x_3973_, 5, v_inst_3971_);
    crate::leanh::lean_closure_set(v___x_3973_, 6, v_inst_3972_);
    return v___x_3973_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0(
    mut v_a_3974_: *mut crate::leanh::LeanObject,
    mut v_toPure_3975_: *mut crate::leanh::LeanObject,
    mut v_a_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3977_, 0, v_a_3976_);
    crate::leanh::lean_ctor_set(v___x_3977_, 1, v_a_3974_);
    v___x_3978_ =
        crate::leanh::lean_apply_2(v_toPure_3975_, crate::leanh::lean_box(0), v___x_3977_);
    return v___x_3978_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg(
    mut v_inst_3979_: *mut crate::leanh::LeanObject,
    mut v_inst_3980_: *mut crate::leanh::LeanObject,
    mut v_a_3981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3982_ = crate::leanh::lean_ctor_get(v_inst_3979_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3982_);
    v_getRef_3983_ = crate::leanh::lean_ctor_get(v_inst_3980_, 0);
    crate::leanh::lean_inc(v_getRef_3983_);
    crate::leanh::lean_dec_ref(v_inst_3980_);
    v_toBind_3984_ = crate::leanh::lean_ctor_get(v_inst_3979_, 1);
    crate::leanh::lean_inc(v_toBind_3984_);
    crate::leanh::lean_dec_ref(v_inst_3979_);
    v_toPure_3985_ = crate::leanh::lean_ctor_get(v_toApplicative_3982_, 1);
    crate::leanh::lean_inc(v_toPure_3985_);
    crate::leanh::lean_dec_ref(v_toApplicative_3982_);
    v___f_3986_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3986_, 0, v_a_3981_);
    crate::leanh::lean_closure_set(v___f_3986_, 1, v_toPure_3985_);
    v___x_3987_ = crate::leanh::lean_apply_4(
        v_toBind_3984_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_3983_,
        v___f_3986_,
    );
    return v___x_3987_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1(
    mut v_00_u03b1_3988_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3989_: *mut crate::leanh::LeanObject,
    mut v_m_3990_: *mut crate::leanh::LeanObject,
    mut v_inst_3991_: *mut crate::leanh::LeanObject,
    mut v_inst_3992_: *mut crate::leanh::LeanObject,
    mut v_inst_3993_: *mut crate::leanh::LeanObject,
    mut v_inst_3994_: *mut crate::leanh::LeanObject,
    mut v_a_3995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3996_ = crate::leanh::lean_ctor_get(v_inst_3993_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3996_);
    v_getRef_3997_ = crate::leanh::lean_ctor_get(v_inst_3994_, 0);
    crate::leanh::lean_inc(v_getRef_3997_);
    crate::leanh::lean_dec_ref(v_inst_3994_);
    v_toBind_3998_ = crate::leanh::lean_ctor_get(v_inst_3993_, 1);
    crate::leanh::lean_inc(v_toBind_3998_);
    crate::leanh::lean_dec_ref(v_inst_3993_);
    v_toPure_3999_ = crate::leanh::lean_ctor_get(v_toApplicative_3996_, 1);
    crate::leanh::lean_inc(v_toPure_3999_);
    crate::leanh::lean_dec_ref(v_toApplicative_3996_);
    v___f_4000_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4000_, 0, v_a_3995_);
    crate::leanh::lean_closure_set(v___f_4000_, 1, v_toPure_3999_);
    v___x_4001_ = crate::leanh::lean_apply_4(
        v_toBind_3998_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_3997_,
        v___f_4000_,
    );
    return v___x_4001_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed(
    mut v_00_u03b1_4002_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4003_: *mut crate::leanh::LeanObject,
    mut v_m_4004_: *mut crate::leanh::LeanObject,
    mut v_inst_4005_: *mut crate::leanh::LeanObject,
    mut v_inst_4006_: *mut crate::leanh::LeanObject,
    mut v_inst_4007_: *mut crate::leanh::LeanObject,
    mut v_inst_4008_: *mut crate::leanh::LeanObject,
    mut v_a_4009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4010_ = l_Lean_MonadStateCacheT_instMonadRef___aux__1(
        v_00_u03b1_4002_,
        v_00_u03b2_4003_,
        v_m_4004_,
        v_inst_4005_,
        v_inst_4006_,
        v_inst_4007_,
        v_inst_4008_,
        v_a_4009_,
    );
    crate::leanh::lean_dec_ref(v_inst_4006_);
    crate::leanh::lean_dec_ref(v_inst_4005_);
    return v_res_4010_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__3___redArg(
    mut v_inst_4011_: *mut crate::leanh::LeanObject,
    mut v_ref_4012_: *mut crate::leanh::LeanObject,
    mut v_x_4013_: *mut crate::leanh::LeanObject,
    mut v_a_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_withRef_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_withRef_4015_ = crate::leanh::lean_ctor_get(v_inst_4011_, 1);
    crate::leanh::lean_inc(v_withRef_4015_);
    crate::leanh::lean_dec_ref(v_inst_4011_);
    v___x_4016_ = crate::leanh::lean_apply_1(v_x_4013_, v_a_4014_);
    v___x_4017_ = crate::leanh::lean_apply_3(
        v_withRef_4015_,
        crate::leanh::lean_box(0),
        v_ref_4012_,
        v___x_4016_,
    );
    return v___x_4017_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__3(
    mut v_00_u03b1_4018_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4019_: *mut crate::leanh::LeanObject,
    mut v_m_4020_: *mut crate::leanh::LeanObject,
    mut v_inst_4021_: *mut crate::leanh::LeanObject,
    mut v_inst_4022_: *mut crate::leanh::LeanObject,
    mut v_inst_4023_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4024_: *mut crate::leanh::LeanObject,
    mut v_ref_4025_: *mut crate::leanh::LeanObject,
    mut v_x_4026_: *mut crate::leanh::LeanObject,
    mut v_a_4027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_withRef_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_withRef_4028_ = crate::leanh::lean_ctor_get(v_inst_4023_, 1);
    crate::leanh::lean_inc(v_withRef_4028_);
    crate::leanh::lean_dec_ref(v_inst_4023_);
    v___x_4029_ = crate::leanh::lean_apply_1(v_x_4026_, v_a_4027_);
    v___x_4030_ = crate::leanh::lean_apply_3(
        v_withRef_4028_,
        crate::leanh::lean_box(0),
        v_ref_4025_,
        v___x_4029_,
    );
    return v___x_4030_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed(
    mut v_00_u03b1_4031_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4032_: *mut crate::leanh::LeanObject,
    mut v_m_4033_: *mut crate::leanh::LeanObject,
    mut v_inst_4034_: *mut crate::leanh::LeanObject,
    mut v_inst_4035_: *mut crate::leanh::LeanObject,
    mut v_inst_4036_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4037_: *mut crate::leanh::LeanObject,
    mut v_ref_4038_: *mut crate::leanh::LeanObject,
    mut v_x_4039_: *mut crate::leanh::LeanObject,
    mut v_a_4040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4041_ = l_Lean_MonadStateCacheT_instMonadRef___aux__3(
        v_00_u03b1_4031_,
        v_00_u03b2_4032_,
        v_m_4033_,
        v_inst_4034_,
        v_inst_4035_,
        v_inst_4036_,
        v_00_u03b1_4037_,
        v_ref_4038_,
        v_x_4039_,
        v_a_4040_,
    );
    crate::leanh::lean_dec_ref(v_inst_4035_);
    crate::leanh::lean_dec_ref(v_inst_4034_);
    return v_res_4041_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___redArg(
    mut v_inst_4042_: *mut crate::leanh::LeanObject,
    mut v_inst_4043_: *mut crate::leanh::LeanObject,
    mut v_inst_4044_: *mut crate::leanh::LeanObject,
    mut v_inst_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_4045_);
    crate::leanh::lean_inc_ref(v_inst_4043_);
    crate::leanh::lean_inc_ref(v_inst_4042_);
    v___x_4046_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___x_4046_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4046_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4046_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4046_, 3, v_inst_4042_);
    crate::leanh::lean_closure_set(v___x_4046_, 4, v_inst_4043_);
    crate::leanh::lean_closure_set(v___x_4046_, 5, v_inst_4044_);
    crate::leanh::lean_closure_set(v___x_4046_, 6, v_inst_4045_);
    v___x_4047_ = crate::leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed as *mut core::ffi::c_void,
        10,
        6,
    );
    crate::leanh::lean_closure_set(v___x_4047_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4047_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4047_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4047_, 3, v_inst_4042_);
    crate::leanh::lean_closure_set(v___x_4047_, 4, v_inst_4043_);
    crate::leanh::lean_closure_set(v___x_4047_, 5, v_inst_4045_);
    v___x_4048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4048_, 0, v___x_4046_);
    crate::leanh::lean_ctor_set(v___x_4048_, 1, v___x_4047_);
    return v___x_4048_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef(
    mut v_00_u03b1_4049_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4050_: *mut crate::leanh::LeanObject,
    mut v_m_4051_: *mut crate::leanh::LeanObject,
    mut v_inst_4052_: *mut crate::leanh::LeanObject,
    mut v_inst_4053_: *mut crate::leanh::LeanObject,
    mut v_inst_4054_: *mut crate::leanh::LeanObject,
    mut v_inst_4055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4056_ = l_Lean_MonadStateCacheT_instMonadRef___redArg(
        v_inst_4052_,
        v_inst_4053_,
        v_inst_4054_,
        v_inst_4055_,
    );
    return v___x_4056_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_MonadCache(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_MonadCache(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_MonadCache(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_MonadCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_MonadCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_MonadCache(builtin);
}
