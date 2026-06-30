// Lean compiler output
// Module: Lean.Util.MonadCache
// Imports: Std.Data.HashMap.Basic
use crate::ffi::lean_mk_array;
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
pub static l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__2 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MonadCacheT_run___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadCacheT_run___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadCacheT_run___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadCacheT_run___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MonadCacheT_run___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MonadCacheT_run___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MonadStateCacheT_run___redArg___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_MonadStateCacheT_run___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MonadStateCacheT_run___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_checkCache___redArg___lam__0(
    mut v_toPure_2029_: *mut leanh::LeanObject,
    mut v_b_2030_: *mut leanh::LeanObject,
    mut v_____r_2031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2032_ = leanh::lean_apply_2(v_toPure_2029_, leanh::lean_box(0), v_b_2030_);
    return v___x_2032_;
}
pub unsafe fn l_Lean_checkCache___redArg___lam__1(
    mut v_toPure_2033_: *mut leanh::LeanObject,
    mut v_cache_2034_: *mut leanh::LeanObject,
    mut v_a_2035_: *mut leanh::LeanObject,
    mut v_toBind_2036_: *mut leanh::LeanObject,
    mut v_b_2037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_b_2037_);
    v___f_2038_ = leanh::lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2038_, 0, v_toPure_2033_);
    leanh::lean_closure_set(v___f_2038_, 1, v_b_2037_);
    v___x_2039_ = leanh::lean_apply_2(v_cache_2034_, v_a_2035_, v_b_2037_);
    v___x_2040_ = leanh::lean_apply_4(
        v_toBind_2036_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2039_,
        v___f_2038_,
    );
    return v___x_2040_;
}
pub unsafe fn l_Lean_checkCache___redArg___lam__2(
    mut v_f_2041_: *mut leanh::LeanObject,
    mut v_toBind_2042_: *mut leanh::LeanObject,
    mut v___f_2043_: *mut leanh::LeanObject,
    mut v_toPure_2044_: *mut leanh::LeanObject,
    mut v_____do__lift_2045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_2045_) == 0 {
        let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2044_);
        v___x_2046_ = leanh::lean_box(0);
        v___x_2047_ = leanh::lean_apply_1(v_f_2041_, v___x_2046_);
        v___x_2048_ = leanh::lean_apply_4(
            v_toBind_2042_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2047_,
            v___f_2043_,
        );
        return v___x_2048_;
    } else {
        let mut v_val_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2043_);
        leanh::lean_dec(v_toBind_2042_);
        leanh::lean_dec(v_f_2041_);
        v_val_2049_ = leanh::lean_ctor_get(v_____do__lift_2045_, 0);
        leanh::lean_inc(v_val_2049_);
        leanh::lean_dec_ref_known(v_____do__lift_2045_, 1);
        v___x_2050_ =
            leanh::lean_apply_2(v_toPure_2044_, leanh::lean_box(0), v_val_2049_);
        return v___x_2050_;
    }
}
pub unsafe fn l_Lean_checkCache___redArg(
    mut v_inst_2051_: *mut leanh::LeanObject,
    mut v_inst_2052_: *mut leanh::LeanObject,
    mut v_a_2053_: *mut leanh::LeanObject,
    mut v_f_2054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_findCached_x3f_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2055_ = leanh::lean_ctor_get(v_inst_2052_, 0);
    leanh::lean_inc_ref(v_toApplicative_2055_);
    v_toBind_2056_ = leanh::lean_ctor_get(v_inst_2052_, 1);
    leanh::lean_inc_n(v_toBind_2056_, 3);
    leanh::lean_dec_ref(v_inst_2052_);
    v_findCached_x3f_2057_ = leanh::lean_ctor_get(v_inst_2051_, 0);
    leanh::lean_inc(v_findCached_x3f_2057_);
    v_cache_2058_ = leanh::lean_ctor_get(v_inst_2051_, 1);
    leanh::lean_inc(v_cache_2058_);
    leanh::lean_dec_ref(v_inst_2051_);
    v_toPure_2059_ = leanh::lean_ctor_get(v_toApplicative_2055_, 1);
    leanh::lean_inc_n(v_toPure_2059_, 2);
    leanh::lean_dec_ref(v_toApplicative_2055_);
    leanh::lean_inc(v_a_2053_);
    v___x_2060_ = leanh::lean_apply_1(v_findCached_x3f_2057_, v_a_2053_);
    v___f_2061_ = leanh::lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2061_, 0, v_toPure_2059_);
    leanh::lean_closure_set(v___f_2061_, 1, v_cache_2058_);
    leanh::lean_closure_set(v___f_2061_, 2, v_a_2053_);
    leanh::lean_closure_set(v___f_2061_, 3, v_toBind_2056_);
    v___f_2062_ = leanh::lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2062_, 0, v_f_2054_);
    leanh::lean_closure_set(v___f_2062_, 1, v_toBind_2056_);
    leanh::lean_closure_set(v___f_2062_, 2, v___f_2061_);
    leanh::lean_closure_set(v___f_2062_, 3, v_toPure_2059_);
    v___x_2063_ = leanh::lean_apply_4(
        v_toBind_2056_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2060_,
        v___f_2062_,
    );
    return v___x_2063_;
}
pub unsafe fn l_Lean_checkCache(
    mut v_00_u03b1_2064_: *mut leanh::LeanObject,
    mut v_00_u03b2_2065_: *mut leanh::LeanObject,
    mut v_m_2066_: *mut leanh::LeanObject,
    mut v_inst_2067_: *mut leanh::LeanObject,
    mut v_inst_2068_: *mut leanh::LeanObject,
    mut v_a_2069_: *mut leanh::LeanObject,
    mut v_f_2070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_findCached_x3f_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2071_ = leanh::lean_ctor_get(v_inst_2068_, 0);
    leanh::lean_inc_ref(v_toApplicative_2071_);
    v_toBind_2072_ = leanh::lean_ctor_get(v_inst_2068_, 1);
    leanh::lean_inc_n(v_toBind_2072_, 3);
    leanh::lean_dec_ref(v_inst_2068_);
    v_findCached_x3f_2073_ = leanh::lean_ctor_get(v_inst_2067_, 0);
    leanh::lean_inc(v_findCached_x3f_2073_);
    v_cache_2074_ = leanh::lean_ctor_get(v_inst_2067_, 1);
    leanh::lean_inc(v_cache_2074_);
    leanh::lean_dec_ref(v_inst_2067_);
    v_toPure_2075_ = leanh::lean_ctor_get(v_toApplicative_2071_, 1);
    leanh::lean_inc_n(v_toPure_2075_, 2);
    leanh::lean_dec_ref(v_toApplicative_2071_);
    leanh::lean_inc(v_a_2069_);
    v___x_2076_ = leanh::lean_apply_1(v_findCached_x3f_2073_, v_a_2069_);
    v___f_2077_ = leanh::lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2077_, 0, v_toPure_2075_);
    leanh::lean_closure_set(v___f_2077_, 1, v_cache_2074_);
    leanh::lean_closure_set(v___f_2077_, 2, v_a_2069_);
    leanh::lean_closure_set(v___f_2077_, 3, v_toBind_2072_);
    v___f_2078_ = leanh::lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2078_, 0, v_f_2070_);
    leanh::lean_closure_set(v___f_2078_, 1, v_toBind_2072_);
    leanh::lean_closure_set(v___f_2078_, 2, v___f_2077_);
    leanh::lean_closure_set(v___f_2078_, 3, v_toPure_2075_);
    v___x_2079_ = leanh::lean_apply_4(
        v_toBind_2072_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2076_,
        v___f_2078_,
    );
    return v___x_2079_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__0(
    mut v_inst_2080_: *mut leanh::LeanObject,
    mut v_a_2081_: *mut leanh::LeanObject,
    mut v_x_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_findCached_x3f_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_findCached_x3f_2083_ = leanh::lean_ctor_get(v_inst_2080_, 0);
    leanh::lean_inc(v_findCached_x3f_2083_);
    leanh::lean_dec_ref(v_inst_2080_);
    v___x_2084_ = leanh::lean_apply_1(v_findCached_x3f_2083_, v_a_2081_);
    return v___x_2084_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__0___boxed(
    mut v_inst_2085_: *mut leanh::LeanObject,
    mut v_a_2086_: *mut leanh::LeanObject,
    mut v_x_2087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2088_ =
        l_Lean_instMonadCacheReaderT___redArg___lam__0(v_inst_2085_, v_a_2086_, v_x_2087_);
    leanh::lean_dec(v_x_2087_);
    return v_res_2088_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__1(
    mut v_inst_2089_: *mut leanh::LeanObject,
    mut v_a_2090_: *mut leanh::LeanObject,
    mut v_b_2091_: *mut leanh::LeanObject,
    mut v_x_2092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cache_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cache_2093_ = leanh::lean_ctor_get(v_inst_2089_, 1);
    leanh::lean_inc(v_cache_2093_);
    leanh::lean_dec_ref(v_inst_2089_);
    v___x_2094_ = leanh::lean_apply_2(v_cache_2093_, v_a_2090_, v_b_2091_);
    return v___x_2094_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__1___boxed(
    mut v_inst_2095_: *mut leanh::LeanObject,
    mut v_a_2096_: *mut leanh::LeanObject,
    mut v_b_2097_: *mut leanh::LeanObject,
    mut v_x_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2099_ = l_Lean_instMonadCacheReaderT___redArg___lam__1(
        v_inst_2095_,
        v_a_2096_,
        v_b_2097_,
        v_x_2098_,
    );
    leanh::lean_dec(v_x_2098_);
    return v_res_2099_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg(
    mut v_inst_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2100_);
    v___f_2101_ = leanh::lean_alloc_closure(
        l_Lean_instMonadCacheReaderT___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2101_, 0, v_inst_2100_);
    v___f_2102_ = leanh::lean_alloc_closure(
        l_Lean_instMonadCacheReaderT___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2102_, 0, v_inst_2100_);
    v___x_2103_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2103_, 0, v___f_2101_);
    leanh::lean_ctor_set(v___x_2103_, 1, v___f_2102_);
    return v___x_2103_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT(
    mut v_00_u03b1_2104_: *mut leanh::LeanObject,
    mut v_00_u03b2_2105_: *mut leanh::LeanObject,
    mut v_00_u03c1_2106_: *mut leanh::LeanObject,
    mut v_m_2107_: *mut leanh::LeanObject,
    mut v_inst_2108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2109_ = l_Lean_instMonadCacheReaderT___redArg(v_inst_2108_);
    return v___x_2109_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__0(
    mut v_a_2110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2111_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2111_, 0, v_a_2110_);
    return v___x_2111_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1(
    mut v_inst_2112_: *mut leanh::LeanObject,
    mut v_inst_2113_: *mut leanh::LeanObject,
    mut v___f_2114_: *mut leanh::LeanObject,
    mut v_a_2115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_findCached_x3f_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2116_ = leanh::lean_ctor_get(v_inst_2113_, 0);
    leanh::lean_inc_ref(v_toApplicative_2116_);
    leanh::lean_dec_ref(v_inst_2113_);
    v_toFunctor_2117_ = leanh::lean_ctor_get(v_toApplicative_2116_, 0);
    leanh::lean_inc_ref(v_toFunctor_2117_);
    leanh::lean_dec_ref(v_toApplicative_2116_);
    v_findCached_x3f_2118_ = leanh::lean_ctor_get(v_inst_2112_, 0);
    leanh::lean_inc(v_findCached_x3f_2118_);
    leanh::lean_dec_ref(v_inst_2112_);
    v_map_2119_ = leanh::lean_ctor_get(v_toFunctor_2117_, 0);
    leanh::lean_inc(v_map_2119_);
    leanh::lean_dec_ref(v_toFunctor_2117_);
    v___x_2120_ = leanh::lean_apply_1(v_findCached_x3f_2118_, v_a_2115_);
    v___x_2121_ = leanh::lean_apply_4(
        v_map_2119_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2114_,
        v___x_2120_,
    );
    return v___x_2121_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__2(
    mut v_a_2122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2123_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2123_, 0, v_a_2122_);
    return v___x_2123_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3(
    mut v_inst_2124_: *mut leanh::LeanObject,
    mut v_inst_2125_: *mut leanh::LeanObject,
    mut v___f_2126_: *mut leanh::LeanObject,
    mut v_a_2127_: *mut leanh::LeanObject,
    mut v_b_2128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2129_ = leanh::lean_ctor_get(v_inst_2125_, 0);
    leanh::lean_inc_ref(v_toApplicative_2129_);
    leanh::lean_dec_ref(v_inst_2125_);
    v_toFunctor_2130_ = leanh::lean_ctor_get(v_toApplicative_2129_, 0);
    leanh::lean_inc_ref(v_toFunctor_2130_);
    leanh::lean_dec_ref(v_toApplicative_2129_);
    v_cache_2131_ = leanh::lean_ctor_get(v_inst_2124_, 1);
    leanh::lean_inc(v_cache_2131_);
    leanh::lean_dec_ref(v_inst_2124_);
    v_map_2132_ = leanh::lean_ctor_get(v_toFunctor_2130_, 0);
    leanh::lean_inc(v_map_2132_);
    leanh::lean_dec_ref(v_toFunctor_2130_);
    v___x_2133_ = leanh::lean_apply_2(v_cache_2131_, v_a_2127_, v_b_2128_);
    v___x_2134_ = leanh::lean_apply_4(
        v_map_2132_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2126_,
        v___x_2133_,
    );
    return v___x_2134_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg(
    mut v_inst_2137_: *mut leanh::LeanObject,
    mut v_inst_2138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2139_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0;
    leanh::lean_inc_ref(v_inst_2138_);
    leanh::lean_inc_ref(v_inst_2137_);
    v___f_2140_ = leanh::lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2140_, 0, v_inst_2137_);
    leanh::lean_closure_set(v___f_2140_, 1, v_inst_2138_);
    leanh::lean_closure_set(v___f_2140_, 2, v___f_2139_);
    v___f_2141_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1;
    v___f_2142_ = leanh::lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_2142_, 0, v_inst_2137_);
    leanh::lean_closure_set(v___f_2142_, 1, v_inst_2138_);
    leanh::lean_closure_set(v___f_2142_, 2, v___f_2141_);
    v___x_2143_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2143_, 0, v___f_2140_);
    leanh::lean_ctor_set(v___x_2143_, 1, v___f_2142_);
    return v___x_2143_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad(
    mut v_00_u03b1_2144_: *mut leanh::LeanObject,
    mut v_00_u03b2_2145_: *mut leanh::LeanObject,
    mut v_00_u03b5_2146_: *mut leanh::LeanObject,
    mut v_m_2147_: *mut leanh::LeanObject,
    mut v_inst_2148_: *mut leanh::LeanObject,
    mut v_inst_2149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2150_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0;
    leanh::lean_inc_ref(v_inst_2149_);
    leanh::lean_inc_ref(v_inst_2148_);
    v___f_2151_ = leanh::lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2151_, 0, v_inst_2148_);
    leanh::lean_closure_set(v___f_2151_, 1, v_inst_2149_);
    leanh::lean_closure_set(v___f_2151_, 2, v___f_2150_);
    v___f_2152_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1;
    v___f_2153_ = leanh::lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_2153_, 0, v_inst_2148_);
    leanh::lean_closure_set(v___f_2153_, 1, v_inst_2149_);
    leanh::lean_closure_set(v___f_2153_, 2, v___f_2152_);
    v___x_2154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2154_, 0, v___f_2151_);
    leanh::lean_ctor_set(v___x_2154_, 1, v___f_2153_);
    return v___x_2154_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0(
    mut v_inst_2155_: *mut leanh::LeanObject,
    mut v_inst_2156_: *mut leanh::LeanObject,
    mut v_a_2157_: *mut leanh::LeanObject,
    mut v_toPure_2158_: *mut leanh::LeanObject,
    mut v_c_2159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2160_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_inst_2155_,
        v_inst_2156_,
        v_c_2159_,
        v_a_2157_,
    );
    v___x_2161_ =
        leanh::lean_apply_2(v_toPure_2158_, leanh::lean_box(0), v___x_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed(
    mut v_inst_2162_: *mut leanh::LeanObject,
    mut v_inst_2163_: *mut leanh::LeanObject,
    mut v_a_2164_: *mut leanh::LeanObject,
    mut v_toPure_2165_: *mut leanh::LeanObject,
    mut v_c_2166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2167_ = l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0(
        v_inst_2162_,
        v_inst_2163_,
        v_a_2164_,
        v_toPure_2165_,
        v_c_2166_,
    );
    leanh::lean_dec_ref(v_c_2166_);
    return v_res_2167_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg(
    mut v_inst_2168_: *mut leanh::LeanObject,
    mut v_inst_2169_: *mut leanh::LeanObject,
    mut v_inst_2170_: *mut leanh::LeanObject,
    mut v_inst_2171_: *mut leanh::LeanObject,
    mut v_a_2172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCache_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2173_ = leanh::lean_ctor_get(v_inst_2170_, 0);
    leanh::lean_inc_ref(v_toApplicative_2173_);
    v_toBind_2174_ = leanh::lean_ctor_get(v_inst_2170_, 1);
    leanh::lean_inc(v_toBind_2174_);
    leanh::lean_dec_ref(v_inst_2170_);
    v_getCache_2175_ = leanh::lean_ctor_get(v_inst_2171_, 0);
    leanh::lean_inc(v_getCache_2175_);
    leanh::lean_dec_ref(v_inst_2171_);
    v_toPure_2176_ = leanh::lean_ctor_get(v_toApplicative_2173_, 1);
    leanh::lean_inc(v_toPure_2176_);
    leanh::lean_dec_ref(v_toApplicative_2173_);
    v___f_2177_ = leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2177_, 0, v_inst_2168_);
    leanh::lean_closure_set(v___f_2177_, 1, v_inst_2169_);
    leanh::lean_closure_set(v___f_2177_, 2, v_a_2172_);
    leanh::lean_closure_set(v___f_2177_, 3, v_toPure_2176_);
    v___x_2178_ = leanh::lean_apply_4(
        v_toBind_2174_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCache_2175_,
        v___f_2177_,
    );
    return v___x_2178_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f(
    mut v_00_u03b1_2179_: *mut leanh::LeanObject,
    mut v_00_u03b2_2180_: *mut leanh::LeanObject,
    mut v_m_2181_: *mut leanh::LeanObject,
    mut v_inst_2182_: *mut leanh::LeanObject,
    mut v_inst_2183_: *mut leanh::LeanObject,
    mut v_inst_2184_: *mut leanh::LeanObject,
    mut v_inst_2185_: *mut leanh::LeanObject,
    mut v_a_2186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCache_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2187_ = leanh::lean_ctor_get(v_inst_2184_, 0);
    leanh::lean_inc_ref(v_toApplicative_2187_);
    v_toBind_2188_ = leanh::lean_ctor_get(v_inst_2184_, 1);
    leanh::lean_inc(v_toBind_2188_);
    leanh::lean_dec_ref(v_inst_2184_);
    v_getCache_2189_ = leanh::lean_ctor_get(v_inst_2185_, 0);
    leanh::lean_inc(v_getCache_2189_);
    leanh::lean_dec_ref(v_inst_2185_);
    v_toPure_2190_ = leanh::lean_ctor_get(v_toApplicative_2187_, 1);
    leanh::lean_inc(v_toPure_2190_);
    leanh::lean_dec_ref(v_toApplicative_2187_);
    v___f_2191_ = leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2191_, 0, v_inst_2182_);
    leanh::lean_closure_set(v___f_2191_, 1, v_inst_2183_);
    leanh::lean_closure_set(v___f_2191_, 2, v_a_2186_);
    leanh::lean_closure_set(v___f_2191_, 3, v_toPure_2190_);
    v___x_2192_ = leanh::lean_apply_4(
        v_toBind_2188_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCache_2189_,
        v___f_2191_,
    );
    return v___x_2192_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0(
    mut v_inst_2193_: *mut leanh::LeanObject,
    mut v_inst_2194_: *mut leanh::LeanObject,
    mut v_a_2195_: *mut leanh::LeanObject,
    mut v_b_2196_: *mut leanh::LeanObject,
    mut v_s_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2199_: *mut leanh::LeanObject,
    mut v_inst_2200_: *mut leanh::LeanObject,
    mut v_inst_2201_: *mut leanh::LeanObject,
    mut v_a_2202_: *mut leanh::LeanObject,
    mut v_b_2203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyCache_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyCache_2204_ = leanh::lean_ctor_get(v_inst_2201_, 1);
    leanh::lean_inc(v_modifyCache_2204_);
    leanh::lean_dec_ref(v_inst_2201_);
    v___f_2205_ = leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2205_, 0, v_inst_2199_);
    leanh::lean_closure_set(v___f_2205_, 1, v_inst_2200_);
    leanh::lean_closure_set(v___f_2205_, 2, v_a_2202_);
    leanh::lean_closure_set(v___f_2205_, 3, v_b_2203_);
    v___x_2206_ = leanh::lean_apply_1(v_modifyCache_2204_, v___f_2205_);
    return v___x_2206_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_cache(
    mut v_00_u03b1_2207_: *mut leanh::LeanObject,
    mut v_00_u03b2_2208_: *mut leanh::LeanObject,
    mut v_m_2209_: *mut leanh::LeanObject,
    mut v_inst_2210_: *mut leanh::LeanObject,
    mut v_inst_2211_: *mut leanh::LeanObject,
    mut v_inst_2212_: *mut leanh::LeanObject,
    mut v_a_2213_: *mut leanh::LeanObject,
    mut v_b_2214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyCache_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyCache_2215_ = leanh::lean_ctor_get(v_inst_2212_, 1);
    leanh::lean_inc(v_modifyCache_2215_);
    leanh::lean_dec_ref(v_inst_2212_);
    v___f_2216_ = leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2216_, 0, v_inst_2210_);
    leanh::lean_closure_set(v___f_2216_, 1, v_inst_2211_);
    leanh::lean_closure_set(v___f_2216_, 2, v_a_2213_);
    leanh::lean_closure_set(v___f_2216_, 3, v_b_2214_);
    v___x_2217_ = leanh::lean_apply_1(v_modifyCache_2215_, v___f_2216_);
    return v___x_2217_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad___redArg(
    mut v_inst_2218_: *mut leanh::LeanObject,
    mut v_inst_2219_: *mut leanh::LeanObject,
    mut v_inst_2220_: *mut leanh::LeanObject,
    mut v_inst_2221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2221_);
    leanh::lean_inc_ref(v_inst_2219_);
    leanh::lean_inc_ref(v_inst_2218_);
    v___x_2222_ = leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_findCached_x3f as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___x_2222_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2222_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2222_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2222_, 3, v_inst_2218_);
    leanh::lean_closure_set(v___x_2222_, 4, v_inst_2219_);
    leanh::lean_closure_set(v___x_2222_, 5, v_inst_2220_);
    leanh::lean_closure_set(v___x_2222_, 6, v_inst_2221_);
    v___x_2223_ = leanh::lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_cache as *mut core::ffi::c_void,
        8,
        6,
    );
    leanh::lean_closure_set(v___x_2223_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2223_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2223_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2223_, 3, v_inst_2218_);
    leanh::lean_closure_set(v___x_2223_, 4, v_inst_2219_);
    leanh::lean_closure_set(v___x_2223_, 5, v_inst_2221_);
    v___x_2224_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2224_, 0, v___x_2222_);
    leanh::lean_ctor_set(v___x_2224_, 1, v___x_2223_);
    return v___x_2224_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad(
    mut v_00_u03b1_2225_: *mut leanh::LeanObject,
    mut v_00_u03b2_2226_: *mut leanh::LeanObject,
    mut v_m_2227_: *mut leanh::LeanObject,
    mut v_inst_2228_: *mut leanh::LeanObject,
    mut v_inst_2229_: *mut leanh::LeanObject,
    mut v_inst_2230_: *mut leanh::LeanObject,
    mut v_inst_2231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2232_ = l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad___redArg(
        v_inst_2228_,
        v_inst_2229_,
        v_inst_2230_,
        v_inst_2231_,
    );
    return v___x_2232_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(
    mut v_f_2233_: *mut leanh::LeanObject,
    mut v_s_2234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2235_ = leanh::lean_box(0);
    v___x_2236_ = leanh::lean_apply_1(v_f_2233_, v_s_2234_);
    v___x_2237_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2237_, 0, v___x_2235_);
    leanh::lean_ctor_set(v___x_2237_, 1, v___x_2236_);
    return v___x_2237_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1(
    mut v_inst_2238_: *mut leanh::LeanObject,
    mut v_f_2239_: *mut leanh::LeanObject,
    mut v___y_2240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2241_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2241_, 0, v_f_2239_);
    leanh::lean_inc(v___y_2240_);
    v___x_2242_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_2242_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2242_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2242_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2242_, 3, v___y_2240_);
    leanh::lean_closure_set(v___x_2242_, 4, v___f_2241_);
    v___x_2243_ = leanh::lean_apply_2(v_inst_2238_, leanh::lean_box(0), v___x_2242_);
    return v___x_2243_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1___boxed(
    mut v_inst_2244_: *mut leanh::LeanObject,
    mut v_f_2245_: *mut leanh::LeanObject,
    mut v___y_2246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2247_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1(
        v_inst_2244_,
        v_f_2245_,
        v___y_2246_,
    );
    leanh::lean_dec(v___y_2246_);
    return v_res_2247_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(
    mut v_inst_2248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_inst_2248_);
    v___f_2249_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2249_, 0, v_inst_2248_);
    v___x_2250_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_get___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_2250_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2250_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2250_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2250_, 3, v_inst_2248_);
    v___x_2251_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2251_, 0, v___x_2250_);
    leanh::lean_ctor_set(v___x_2251_, 1, v___f_2249_);
    return v___x_2251_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter(
    mut v_00_u03c9_2252_: *mut leanh::LeanObject,
    mut v_00_u03b1_2253_: *mut leanh::LeanObject,
    mut v_00_u03b2_2254_: *mut leanh::LeanObject,
    mut v_m_2255_: *mut leanh::LeanObject,
    mut v_inst_2256_: *mut leanh::LeanObject,
    mut v_inst_2257_: *mut leanh::LeanObject,
    mut v_inst_2258_: *mut leanh::LeanObject,
    mut v_inst_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2260_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_2259_);
    return v___x_2260_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___boxed(
    mut v_00_u03c9_2261_: *mut leanh::LeanObject,
    mut v_00_u03b1_2262_: *mut leanh::LeanObject,
    mut v_00_u03b2_2263_: *mut leanh::LeanObject,
    mut v_m_2264_: *mut leanh::LeanObject,
    mut v_inst_2265_: *mut leanh::LeanObject,
    mut v_inst_2266_: *mut leanh::LeanObject,
    mut v_inst_2267_: *mut leanh::LeanObject,
    mut v_inst_2268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_2267_);
    leanh::lean_dec_ref(v_inst_2266_);
    return v_res_2269_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__0(
    mut v_a_2270_: *mut leanh::LeanObject,
    mut v_toPure_2271_: *mut leanh::LeanObject,
    mut v_s_2272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2273_, 0, v_a_2270_);
    leanh::lean_ctor_set(v___x_2273_, 1, v_s_2272_);
    v___x_2274_ =
        leanh::lean_apply_2(v_toPure_2271_, leanh::lean_box(0), v___x_2273_);
    return v___x_2274_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__1(
    mut v_toPure_2275_: *mut leanh::LeanObject,
    mut v_ref_2276_: *mut leanh::LeanObject,
    mut v_inst_2277_: *mut leanh::LeanObject,
    mut v_toBind_2278_: *mut leanh::LeanObject,
    mut v_a_2279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2280_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2280_, 0, v_a_2279_);
    leanh::lean_closure_set(v___f_2280_, 1, v_toPure_2275_);
    v___x_2281_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_2281_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2281_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2281_, 2, v_ref_2276_);
    v___x_2282_ = leanh::lean_apply_2(v_inst_2277_, leanh::lean_box(0), v___x_2281_);
    v___x_2283_ = leanh::lean_apply_4(
        v_toBind_2278_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2282_,
        v___f_2280_,
    );
    return v___x_2283_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__2(
    mut v_toPure_2284_: *mut leanh::LeanObject,
    mut v_inst_2285_: *mut leanh::LeanObject,
    mut v_toBind_2286_: *mut leanh::LeanObject,
    mut v_x_2287_: *mut leanh::LeanObject,
    mut v_ref_2288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_2286_);
    leanh::lean_inc(v_ref_2288_);
    v___f_2289_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2289_, 0, v_toPure_2284_);
    leanh::lean_closure_set(v___f_2289_, 1, v_ref_2288_);
    leanh::lean_closure_set(v___f_2289_, 2, v_inst_2285_);
    leanh::lean_closure_set(v___f_2289_, 3, v_toBind_2286_);
    v___x_2290_ = leanh::lean_apply_1(v_x_2287_, v_ref_2288_);
    v___x_2291_ = leanh::lean_apply_4(
        v_toBind_2286_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2290_,
        v___f_2289_,
    );
    return v___x_2291_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__3(
    mut v_toPure_2292_: *mut leanh::LeanObject,
    mut v_____x_2293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2294_ = leanh::lean_ctor_get(v_____x_2293_, 0);
    leanh::lean_inc(v_fst_2294_);
    leanh::lean_dec_ref(v_____x_2293_);
    v___x_2295_ =
        leanh::lean_apply_2(v_toPure_2292_, leanh::lean_box(0), v_fst_2294_);
    return v___x_2295_;
}
pub unsafe fn _init_l_Lean_MonadCacheT_run___redArg___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2296_ = leanh::lean_box(0);
    v___x_2297_ = leanh::lean_unsigned_to_nat(16);
    v___x_2298_ = lean_mk_array(v___x_2297_, v___x_2296_);
    return v___x_2298_;
}
pub unsafe fn _init_l_Lean_MonadCacheT_run___redArg___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__0_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__0,
    );
    v___x_2300_ = leanh::lean_unsigned_to_nat(0);
    v___x_2301_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2301_, 0, v___x_2300_);
    leanh::lean_ctor_set(v___x_2301_, 1, v___x_2299_);
    return v___x_2301_;
}
pub unsafe fn _init_l_Lean_MonadCacheT_run___redArg___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__1,
    );
    v___x_2303_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_2303_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2303_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2303_, 2, v___x_2302_);
    return v___x_2303_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg(
    mut v_inst_2304_: *mut leanh::LeanObject,
    mut v_inst_2305_: *mut leanh::LeanObject,
    mut v_x_2306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2307_ = leanh::lean_ctor_get(v_inst_2305_, 0);
    leanh::lean_inc_ref(v_toApplicative_2307_);
    v_toBind_2308_ = leanh::lean_ctor_get(v_inst_2305_, 1);
    leanh::lean_inc_n(v_toBind_2308_, 3);
    leanh::lean_dec_ref(v_inst_2305_);
    v_toPure_2309_ = leanh::lean_ctor_get(v_toApplicative_2307_, 1);
    leanh::lean_inc_n(v_toPure_2309_, 2);
    leanh::lean_dec_ref(v_toApplicative_2307_);
    v___x_2310_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__2,
    );
    leanh::lean_inc(v_inst_2304_);
    v___x_2311_ = leanh::lean_apply_2(v_inst_2304_, leanh::lean_box(0), v___x_2310_);
    v___f_2312_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2312_, 0, v_toPure_2309_);
    leanh::lean_closure_set(v___f_2312_, 1, v_inst_2304_);
    leanh::lean_closure_set(v___f_2312_, 2, v_toBind_2308_);
    leanh::lean_closure_set(v___f_2312_, 3, v_x_2306_);
    v___f_2313_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2313_, 0, v_toPure_2309_);
    v___x_2314_ = leanh::lean_apply_4(
        v_toBind_2308_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2311_,
        v___f_2312_,
    );
    v___x_2315_ = leanh::lean_apply_4(
        v_toBind_2308_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2314_,
        v___f_2313_,
    );
    return v___x_2315_;
}
pub unsafe fn l_Lean_MonadCacheT_run(
    mut v_00_u03c9_2316_: *mut leanh::LeanObject,
    mut v_00_u03b1_2317_: *mut leanh::LeanObject,
    mut v_00_u03b2_2318_: *mut leanh::LeanObject,
    mut v_m_2319_: *mut leanh::LeanObject,
    mut v_inst_2320_: *mut leanh::LeanObject,
    mut v_inst_2321_: *mut leanh::LeanObject,
    mut v_inst_2322_: *mut leanh::LeanObject,
    mut v_inst_2323_: *mut leanh::LeanObject,
    mut v_inst_2324_: *mut leanh::LeanObject,
    mut v_00_u03c3_2325_: *mut leanh::LeanObject,
    mut v_x_2326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2327_ = leanh::lean_ctor_get(v_inst_2324_, 0);
    leanh::lean_inc_ref(v_toApplicative_2327_);
    v_toBind_2328_ = leanh::lean_ctor_get(v_inst_2324_, 1);
    leanh::lean_inc_n(v_toBind_2328_, 3);
    leanh::lean_dec_ref(v_inst_2324_);
    v_toPure_2329_ = leanh::lean_ctor_get(v_toApplicative_2327_, 1);
    leanh::lean_inc_n(v_toPure_2329_, 2);
    leanh::lean_dec_ref(v_toApplicative_2327_);
    v___x_2330_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__2,
    );
    leanh::lean_inc(v_inst_2323_);
    v___x_2331_ = leanh::lean_apply_2(v_inst_2323_, leanh::lean_box(0), v___x_2330_);
    v___f_2332_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2332_, 0, v_toPure_2329_);
    leanh::lean_closure_set(v___f_2332_, 1, v_inst_2323_);
    leanh::lean_closure_set(v___f_2332_, 2, v_toBind_2328_);
    leanh::lean_closure_set(v___f_2332_, 3, v_x_2326_);
    v___f_2333_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2333_, 0, v_toPure_2329_);
    v___x_2334_ = leanh::lean_apply_4(
        v_toBind_2328_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2331_,
        v___f_2332_,
    );
    v___x_2335_ = leanh::lean_apply_4(
        v_toBind_2328_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2334_,
        v___f_2333_,
    );
    return v___x_2335_;
}
pub unsafe fn l_Lean_MonadCacheT_run___boxed(
    mut v_00_u03c9_2336_: *mut leanh::LeanObject,
    mut v_00_u03b1_2337_: *mut leanh::LeanObject,
    mut v_00_u03b2_2338_: *mut leanh::LeanObject,
    mut v_m_2339_: *mut leanh::LeanObject,
    mut v_inst_2340_: *mut leanh::LeanObject,
    mut v_inst_2341_: *mut leanh::LeanObject,
    mut v_inst_2342_: *mut leanh::LeanObject,
    mut v_inst_2343_: *mut leanh::LeanObject,
    mut v_inst_2344_: *mut leanh::LeanObject,
    mut v_00_u03c3_2345_: *mut leanh::LeanObject,
    mut v_x_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_2342_);
    leanh::lean_dec_ref(v_inst_2341_);
    return v_res_2347_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1___redArg(
    mut v_inst_2348_: *mut leanh::LeanObject,
    mut v_a_2349_: *mut leanh::LeanObject,
    mut v_a_2350_: *mut leanh::LeanObject,
    mut v_a_2351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2352_ = leanh::lean_ctor_get(v_inst_2348_, 0);
    leanh::lean_inc_ref(v_toApplicative_2352_);
    leanh::lean_dec_ref(v_inst_2348_);
    v_toFunctor_2353_ = leanh::lean_ctor_get(v_toApplicative_2352_, 0);
    leanh::lean_inc_ref(v_toFunctor_2353_);
    leanh::lean_dec_ref(v_toApplicative_2352_);
    v_map_2354_ = leanh::lean_ctor_get(v_toFunctor_2353_, 0);
    leanh::lean_inc(v_map_2354_);
    leanh::lean_dec_ref(v_toFunctor_2353_);
    leanh::lean_inc(v_a_2351_);
    v___x_2355_ = leanh::lean_apply_1(v_a_2350_, v_a_2351_);
    v___x_2356_ = leanh::lean_apply_4(
        v_map_2354_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_a_2349_,
        v___x_2355_,
    );
    return v___x_2356_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1___redArg___boxed(
    mut v_inst_2357_: *mut leanh::LeanObject,
    mut v_a_2358_: *mut leanh::LeanObject,
    mut v_a_2359_: *mut leanh::LeanObject,
    mut v_a_2360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2361_ = l_Lean_MonadCacheT_instMonad___aux__1___redArg(
        v_inst_2357_,
        v_a_2358_,
        v_a_2359_,
        v_a_2360_,
    );
    leanh::lean_dec(v_a_2360_);
    return v_res_2361_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1(
    mut v_00_u03c9_2362_: *mut leanh::LeanObject,
    mut v_00_u03b1_2363_: *mut leanh::LeanObject,
    mut v_00_u03b2_2364_: *mut leanh::LeanObject,
    mut v_m_2365_: *mut leanh::LeanObject,
    mut v_inst_2366_: *mut leanh::LeanObject,
    mut v_inst_2367_: *mut leanh::LeanObject,
    mut v_inst_2368_: *mut leanh::LeanObject,
    mut v_inst_2369_: *mut leanh::LeanObject,
    mut v_00_u03b1_2370_: *mut leanh::LeanObject,
    mut v_00_u03b2_2371_: *mut leanh::LeanObject,
    mut v_a_2372_: *mut leanh::LeanObject,
    mut v_a_2373_: *mut leanh::LeanObject,
    mut v_a_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2375_ = leanh::lean_ctor_get(v_inst_2369_, 0);
    leanh::lean_inc_ref(v_toApplicative_2375_);
    leanh::lean_dec_ref(v_inst_2369_);
    v_toFunctor_2376_ = leanh::lean_ctor_get(v_toApplicative_2375_, 0);
    leanh::lean_inc_ref(v_toFunctor_2376_);
    leanh::lean_dec_ref(v_toApplicative_2375_);
    v_map_2377_ = leanh::lean_ctor_get(v_toFunctor_2376_, 0);
    leanh::lean_inc(v_map_2377_);
    leanh::lean_dec_ref(v_toFunctor_2376_);
    leanh::lean_inc(v_a_2374_);
    v___x_2378_ = leanh::lean_apply_1(v_a_2373_, v_a_2374_);
    v___x_2379_ = leanh::lean_apply_4(
        v_map_2377_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_a_2372_,
        v___x_2378_,
    );
    return v___x_2379_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1___boxed(
    mut v_00_u03c9_2380_: *mut leanh::LeanObject,
    mut v_00_u03b1_2381_: *mut leanh::LeanObject,
    mut v_00_u03b2_2382_: *mut leanh::LeanObject,
    mut v_m_2383_: *mut leanh::LeanObject,
    mut v_inst_2384_: *mut leanh::LeanObject,
    mut v_inst_2385_: *mut leanh::LeanObject,
    mut v_inst_2386_: *mut leanh::LeanObject,
    mut v_inst_2387_: *mut leanh::LeanObject,
    mut v_00_u03b1_2388_: *mut leanh::LeanObject,
    mut v_00_u03b2_2389_: *mut leanh::LeanObject,
    mut v_a_2390_: *mut leanh::LeanObject,
    mut v_a_2391_: *mut leanh::LeanObject,
    mut v_a_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2392_);
    leanh::lean_dec_ref(v_inst_2386_);
    leanh::lean_dec_ref(v_inst_2385_);
    return v_res_2393_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3___redArg(
    mut v_inst_2394_: *mut leanh::LeanObject,
    mut v_a_2395_: *mut leanh::LeanObject,
    mut v_a_2396_: *mut leanh::LeanObject,
    mut v_a_2397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapConst_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2398_ = leanh::lean_ctor_get(v_inst_2394_, 0);
    leanh::lean_inc_ref(v_toApplicative_2398_);
    leanh::lean_dec_ref(v_inst_2394_);
    v_toFunctor_2399_ = leanh::lean_ctor_get(v_toApplicative_2398_, 0);
    leanh::lean_inc_ref(v_toFunctor_2399_);
    leanh::lean_dec_ref(v_toApplicative_2398_);
    v_mapConst_2400_ = leanh::lean_ctor_get(v_toFunctor_2399_, 1);
    leanh::lean_inc(v_mapConst_2400_);
    leanh::lean_dec_ref(v_toFunctor_2399_);
    leanh::lean_inc(v_a_2397_);
    v___x_2401_ = leanh::lean_apply_1(v_a_2396_, v_a_2397_);
    v___x_2402_ = leanh::lean_apply_4(
        v_mapConst_2400_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_a_2395_,
        v___x_2401_,
    );
    return v___x_2402_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3___redArg___boxed(
    mut v_inst_2403_: *mut leanh::LeanObject,
    mut v_a_2404_: *mut leanh::LeanObject,
    mut v_a_2405_: *mut leanh::LeanObject,
    mut v_a_2406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_Lean_MonadCacheT_instMonad___aux__3___redArg(
        v_inst_2403_,
        v_a_2404_,
        v_a_2405_,
        v_a_2406_,
    );
    leanh::lean_dec(v_a_2406_);
    return v_res_2407_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3(
    mut v_00_u03c9_2408_: *mut leanh::LeanObject,
    mut v_00_u03b1_2409_: *mut leanh::LeanObject,
    mut v_00_u03b2_2410_: *mut leanh::LeanObject,
    mut v_m_2411_: *mut leanh::LeanObject,
    mut v_inst_2412_: *mut leanh::LeanObject,
    mut v_inst_2413_: *mut leanh::LeanObject,
    mut v_inst_2414_: *mut leanh::LeanObject,
    mut v_inst_2415_: *mut leanh::LeanObject,
    mut v_00_u03b1_2416_: *mut leanh::LeanObject,
    mut v_00_u03b2_2417_: *mut leanh::LeanObject,
    mut v_a_2418_: *mut leanh::LeanObject,
    mut v_a_2419_: *mut leanh::LeanObject,
    mut v_a_2420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapConst_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2421_ = leanh::lean_ctor_get(v_inst_2415_, 0);
    leanh::lean_inc_ref(v_toApplicative_2421_);
    leanh::lean_dec_ref(v_inst_2415_);
    v_toFunctor_2422_ = leanh::lean_ctor_get(v_toApplicative_2421_, 0);
    leanh::lean_inc_ref(v_toFunctor_2422_);
    leanh::lean_dec_ref(v_toApplicative_2421_);
    v_mapConst_2423_ = leanh::lean_ctor_get(v_toFunctor_2422_, 1);
    leanh::lean_inc(v_mapConst_2423_);
    leanh::lean_dec_ref(v_toFunctor_2422_);
    leanh::lean_inc(v_a_2420_);
    v___x_2424_ = leanh::lean_apply_1(v_a_2419_, v_a_2420_);
    v___x_2425_ = leanh::lean_apply_4(
        v_mapConst_2423_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_a_2418_,
        v___x_2424_,
    );
    return v___x_2425_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3___boxed(
    mut v_00_u03c9_2426_: *mut leanh::LeanObject,
    mut v_00_u03b1_2427_: *mut leanh::LeanObject,
    mut v_00_u03b2_2428_: *mut leanh::LeanObject,
    mut v_m_2429_: *mut leanh::LeanObject,
    mut v_inst_2430_: *mut leanh::LeanObject,
    mut v_inst_2431_: *mut leanh::LeanObject,
    mut v_inst_2432_: *mut leanh::LeanObject,
    mut v_inst_2433_: *mut leanh::LeanObject,
    mut v_00_u03b1_2434_: *mut leanh::LeanObject,
    mut v_00_u03b2_2435_: *mut leanh::LeanObject,
    mut v_a_2436_: *mut leanh::LeanObject,
    mut v_a_2437_: *mut leanh::LeanObject,
    mut v_a_2438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2438_);
    leanh::lean_dec_ref(v_inst_2432_);
    leanh::lean_dec_ref(v_inst_2431_);
    return v_res_2439_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__5___redArg(
    mut v_inst_2440_: *mut leanh::LeanObject,
    mut v_a_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2442_ = leanh::lean_ctor_get(v_inst_2440_, 0);
    leanh::lean_inc_ref(v_toApplicative_2442_);
    leanh::lean_dec_ref(v_inst_2440_);
    v_toPure_2443_ = leanh::lean_ctor_get(v_toApplicative_2442_, 1);
    leanh::lean_inc(v_toPure_2443_);
    leanh::lean_dec_ref(v_toApplicative_2442_);
    v___x_2444_ = leanh::lean_apply_2(v_toPure_2443_, leanh::lean_box(0), v_a_2441_);
    return v___x_2444_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__5(
    mut v_00_u03c9_2445_: *mut leanh::LeanObject,
    mut v_00_u03b1_2446_: *mut leanh::LeanObject,
    mut v_00_u03b2_2447_: *mut leanh::LeanObject,
    mut v_m_2448_: *mut leanh::LeanObject,
    mut v_inst_2449_: *mut leanh::LeanObject,
    mut v_inst_2450_: *mut leanh::LeanObject,
    mut v_inst_2451_: *mut leanh::LeanObject,
    mut v_inst_2452_: *mut leanh::LeanObject,
    mut v_00_u03b1_2453_: *mut leanh::LeanObject,
    mut v_a_2454_: *mut leanh::LeanObject,
    mut v_a_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2456_ = leanh::lean_ctor_get(v_inst_2452_, 0);
    leanh::lean_inc_ref(v_toApplicative_2456_);
    leanh::lean_dec_ref(v_inst_2452_);
    v_toPure_2457_ = leanh::lean_ctor_get(v_toApplicative_2456_, 1);
    leanh::lean_inc(v_toPure_2457_);
    leanh::lean_dec_ref(v_toApplicative_2456_);
    v___x_2458_ = leanh::lean_apply_2(v_toPure_2457_, leanh::lean_box(0), v_a_2454_);
    return v___x_2458_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__5___boxed(
    mut v_00_u03c9_2459_: *mut leanh::LeanObject,
    mut v_00_u03b1_2460_: *mut leanh::LeanObject,
    mut v_00_u03b2_2461_: *mut leanh::LeanObject,
    mut v_m_2462_: *mut leanh::LeanObject,
    mut v_inst_2463_: *mut leanh::LeanObject,
    mut v_inst_2464_: *mut leanh::LeanObject,
    mut v_inst_2465_: *mut leanh::LeanObject,
    mut v_inst_2466_: *mut leanh::LeanObject,
    mut v_00_u03b1_2467_: *mut leanh::LeanObject,
    mut v_a_2468_: *mut leanh::LeanObject,
    mut v_a_2469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2469_);
    leanh::lean_dec_ref(v_inst_2465_);
    leanh::lean_dec_ref(v_inst_2464_);
    return v_res_2470_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0(
    mut v_a_2471_: *mut leanh::LeanObject,
    mut v_a_2472_: *mut leanh::LeanObject,
    mut v_x_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = leanh::lean_box(0);
    leanh::lean_inc(v_a_2472_);
    v___x_2475_ = leanh::lean_apply_2(v_a_2471_, v___x_2474_, v_a_2472_);
    return v___x_2475_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed(
    mut v_a_2476_: *mut leanh::LeanObject,
    mut v_a_2477_: *mut leanh::LeanObject,
    mut v_x_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2479_ =
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0(v_a_2476_, v_a_2477_, v_x_2478_);
    leanh::lean_dec(v_a_2477_);
    return v_res_2479_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg(
    mut v_inst_2480_: *mut leanh::LeanObject,
    mut v_a_2481_: *mut leanh::LeanObject,
    mut v_a_2482_: *mut leanh::LeanObject,
    mut v_a_2483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2484_ = leanh::lean_ctor_get(v_inst_2480_, 0);
    leanh::lean_inc_ref(v_toApplicative_2484_);
    leanh::lean_dec_ref(v_inst_2480_);
    v_toSeq_2485_ = leanh::lean_ctor_get(v_toApplicative_2484_, 2);
    leanh::lean_inc(v_toSeq_2485_);
    leanh::lean_dec_ref(v_toApplicative_2484_);
    leanh::lean_inc_n(v_a_2483_, 2);
    v___f_2486_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2486_, 0, v_a_2482_);
    leanh::lean_closure_set(v___f_2486_, 1, v_a_2483_);
    v___x_2487_ = leanh::lean_apply_1(v_a_2481_, v_a_2483_);
    v___x_2488_ = leanh::lean_apply_4(
        v_toSeq_2485_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2487_,
        v___f_2486_,
    );
    return v___x_2488_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg___boxed(
    mut v_inst_2489_: *mut leanh::LeanObject,
    mut v_a_2490_: *mut leanh::LeanObject,
    mut v_a_2491_: *mut leanh::LeanObject,
    mut v_a_2492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2493_ = l_Lean_MonadCacheT_instMonad___aux__7___redArg(
        v_inst_2489_,
        v_a_2490_,
        v_a_2491_,
        v_a_2492_,
    );
    leanh::lean_dec(v_a_2492_);
    return v_res_2493_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7(
    mut v_00_u03c9_2494_: *mut leanh::LeanObject,
    mut v_00_u03b1_2495_: *mut leanh::LeanObject,
    mut v_00_u03b2_2496_: *mut leanh::LeanObject,
    mut v_m_2497_: *mut leanh::LeanObject,
    mut v_inst_2498_: *mut leanh::LeanObject,
    mut v_inst_2499_: *mut leanh::LeanObject,
    mut v_inst_2500_: *mut leanh::LeanObject,
    mut v_inst_2501_: *mut leanh::LeanObject,
    mut v_00_u03b1_2502_: *mut leanh::LeanObject,
    mut v_00_u03b2_2503_: *mut leanh::LeanObject,
    mut v_a_2504_: *mut leanh::LeanObject,
    mut v_a_2505_: *mut leanh::LeanObject,
    mut v_a_2506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2507_ = leanh::lean_ctor_get(v_inst_2501_, 0);
    leanh::lean_inc_ref(v_toApplicative_2507_);
    leanh::lean_dec_ref(v_inst_2501_);
    v_toSeq_2508_ = leanh::lean_ctor_get(v_toApplicative_2507_, 2);
    leanh::lean_inc(v_toSeq_2508_);
    leanh::lean_dec_ref(v_toApplicative_2507_);
    leanh::lean_inc_n(v_a_2506_, 2);
    v___f_2509_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2509_, 0, v_a_2505_);
    leanh::lean_closure_set(v___f_2509_, 1, v_a_2506_);
    v___x_2510_ = leanh::lean_apply_1(v_a_2504_, v_a_2506_);
    v___x_2511_ = leanh::lean_apply_4(
        v_toSeq_2508_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2510_,
        v___f_2509_,
    );
    return v___x_2511_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___boxed(
    mut v_00_u03c9_2512_: *mut leanh::LeanObject,
    mut v_00_u03b1_2513_: *mut leanh::LeanObject,
    mut v_00_u03b2_2514_: *mut leanh::LeanObject,
    mut v_m_2515_: *mut leanh::LeanObject,
    mut v_inst_2516_: *mut leanh::LeanObject,
    mut v_inst_2517_: *mut leanh::LeanObject,
    mut v_inst_2518_: *mut leanh::LeanObject,
    mut v_inst_2519_: *mut leanh::LeanObject,
    mut v_00_u03b1_2520_: *mut leanh::LeanObject,
    mut v_00_u03b2_2521_: *mut leanh::LeanObject,
    mut v_a_2522_: *mut leanh::LeanObject,
    mut v_a_2523_: *mut leanh::LeanObject,
    mut v_a_2524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2524_);
    leanh::lean_dec_ref(v_inst_2518_);
    leanh::lean_dec_ref(v_inst_2517_);
    return v_res_2525_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9___redArg(
    mut v_inst_2526_: *mut leanh::LeanObject,
    mut v_a_2527_: *mut leanh::LeanObject,
    mut v_a_2528_: *mut leanh::LeanObject,
    mut v_a_2529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2530_ = leanh::lean_ctor_get(v_inst_2526_, 0);
    leanh::lean_inc_ref(v_toApplicative_2530_);
    leanh::lean_dec_ref(v_inst_2526_);
    v_toSeqLeft_2531_ = leanh::lean_ctor_get(v_toApplicative_2530_, 3);
    leanh::lean_inc(v_toSeqLeft_2531_);
    leanh::lean_dec_ref(v_toApplicative_2530_);
    leanh::lean_inc_n(v_a_2529_, 2);
    v___f_2532_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2532_, 0, v_a_2528_);
    leanh::lean_closure_set(v___f_2532_, 1, v_a_2529_);
    v___x_2533_ = leanh::lean_apply_1(v_a_2527_, v_a_2529_);
    v___x_2534_ = leanh::lean_apply_4(
        v_toSeqLeft_2531_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2533_,
        v___f_2532_,
    );
    return v___x_2534_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9___redArg___boxed(
    mut v_inst_2535_: *mut leanh::LeanObject,
    mut v_a_2536_: *mut leanh::LeanObject,
    mut v_a_2537_: *mut leanh::LeanObject,
    mut v_a_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Lean_MonadCacheT_instMonad___aux__9___redArg(
        v_inst_2535_,
        v_a_2536_,
        v_a_2537_,
        v_a_2538_,
    );
    leanh::lean_dec(v_a_2538_);
    return v_res_2539_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9(
    mut v_00_u03c9_2540_: *mut leanh::LeanObject,
    mut v_00_u03b1_2541_: *mut leanh::LeanObject,
    mut v_00_u03b2_2542_: *mut leanh::LeanObject,
    mut v_m_2543_: *mut leanh::LeanObject,
    mut v_inst_2544_: *mut leanh::LeanObject,
    mut v_inst_2545_: *mut leanh::LeanObject,
    mut v_inst_2546_: *mut leanh::LeanObject,
    mut v_inst_2547_: *mut leanh::LeanObject,
    mut v_00_u03b1_2548_: *mut leanh::LeanObject,
    mut v_00_u03b2_2549_: *mut leanh::LeanObject,
    mut v_a_2550_: *mut leanh::LeanObject,
    mut v_a_2551_: *mut leanh::LeanObject,
    mut v_a_2552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2553_ = leanh::lean_ctor_get(v_inst_2547_, 0);
    leanh::lean_inc_ref(v_toApplicative_2553_);
    leanh::lean_dec_ref(v_inst_2547_);
    v_toSeqLeft_2554_ = leanh::lean_ctor_get(v_toApplicative_2553_, 3);
    leanh::lean_inc(v_toSeqLeft_2554_);
    leanh::lean_dec_ref(v_toApplicative_2553_);
    leanh::lean_inc_n(v_a_2552_, 2);
    v___f_2555_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2555_, 0, v_a_2551_);
    leanh::lean_closure_set(v___f_2555_, 1, v_a_2552_);
    v___x_2556_ = leanh::lean_apply_1(v_a_2550_, v_a_2552_);
    v___x_2557_ = leanh::lean_apply_4(
        v_toSeqLeft_2554_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2556_,
        v___f_2555_,
    );
    return v___x_2557_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9___boxed(
    mut v_00_u03c9_2558_: *mut leanh::LeanObject,
    mut v_00_u03b1_2559_: *mut leanh::LeanObject,
    mut v_00_u03b2_2560_: *mut leanh::LeanObject,
    mut v_m_2561_: *mut leanh::LeanObject,
    mut v_inst_2562_: *mut leanh::LeanObject,
    mut v_inst_2563_: *mut leanh::LeanObject,
    mut v_inst_2564_: *mut leanh::LeanObject,
    mut v_inst_2565_: *mut leanh::LeanObject,
    mut v_00_u03b1_2566_: *mut leanh::LeanObject,
    mut v_00_u03b2_2567_: *mut leanh::LeanObject,
    mut v_a_2568_: *mut leanh::LeanObject,
    mut v_a_2569_: *mut leanh::LeanObject,
    mut v_a_2570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2570_);
    leanh::lean_dec_ref(v_inst_2564_);
    leanh::lean_dec_ref(v_inst_2563_);
    return v_res_2571_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11___redArg(
    mut v_inst_2572_: *mut leanh::LeanObject,
    mut v_a_2573_: *mut leanh::LeanObject,
    mut v_a_2574_: *mut leanh::LeanObject,
    mut v_a_2575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2576_ = leanh::lean_ctor_get(v_inst_2572_, 0);
    leanh::lean_inc_ref(v_toApplicative_2576_);
    leanh::lean_dec_ref(v_inst_2572_);
    v_toSeqRight_2577_ = leanh::lean_ctor_get(v_toApplicative_2576_, 4);
    leanh::lean_inc(v_toSeqRight_2577_);
    leanh::lean_dec_ref(v_toApplicative_2576_);
    leanh::lean_inc_n(v_a_2575_, 2);
    v___f_2578_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2578_, 0, v_a_2574_);
    leanh::lean_closure_set(v___f_2578_, 1, v_a_2575_);
    v___x_2579_ = leanh::lean_apply_1(v_a_2573_, v_a_2575_);
    v___x_2580_ = leanh::lean_apply_4(
        v_toSeqRight_2577_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2579_,
        v___f_2578_,
    );
    return v___x_2580_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11___redArg___boxed(
    mut v_inst_2581_: *mut leanh::LeanObject,
    mut v_a_2582_: *mut leanh::LeanObject,
    mut v_a_2583_: *mut leanh::LeanObject,
    mut v_a_2584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2585_ = l_Lean_MonadCacheT_instMonad___aux__11___redArg(
        v_inst_2581_,
        v_a_2582_,
        v_a_2583_,
        v_a_2584_,
    );
    leanh::lean_dec(v_a_2584_);
    return v_res_2585_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11(
    mut v_00_u03c9_2586_: *mut leanh::LeanObject,
    mut v_00_u03b1_2587_: *mut leanh::LeanObject,
    mut v_00_u03b2_2588_: *mut leanh::LeanObject,
    mut v_m_2589_: *mut leanh::LeanObject,
    mut v_inst_2590_: *mut leanh::LeanObject,
    mut v_inst_2591_: *mut leanh::LeanObject,
    mut v_inst_2592_: *mut leanh::LeanObject,
    mut v_inst_2593_: *mut leanh::LeanObject,
    mut v_00_u03b1_2594_: *mut leanh::LeanObject,
    mut v_00_u03b2_2595_: *mut leanh::LeanObject,
    mut v_a_2596_: *mut leanh::LeanObject,
    mut v_a_2597_: *mut leanh::LeanObject,
    mut v_a_2598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2599_ = leanh::lean_ctor_get(v_inst_2593_, 0);
    leanh::lean_inc_ref(v_toApplicative_2599_);
    leanh::lean_dec_ref(v_inst_2593_);
    v_toSeqRight_2600_ = leanh::lean_ctor_get(v_toApplicative_2599_, 4);
    leanh::lean_inc(v_toSeqRight_2600_);
    leanh::lean_dec_ref(v_toApplicative_2599_);
    leanh::lean_inc_n(v_a_2598_, 2);
    v___f_2601_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2601_, 0, v_a_2597_);
    leanh::lean_closure_set(v___f_2601_, 1, v_a_2598_);
    v___x_2602_ = leanh::lean_apply_1(v_a_2596_, v_a_2598_);
    v___x_2603_ = leanh::lean_apply_4(
        v_toSeqRight_2600_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2602_,
        v___f_2601_,
    );
    return v___x_2603_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11___boxed(
    mut v_00_u03c9_2604_: *mut leanh::LeanObject,
    mut v_00_u03b1_2605_: *mut leanh::LeanObject,
    mut v_00_u03b2_2606_: *mut leanh::LeanObject,
    mut v_m_2607_: *mut leanh::LeanObject,
    mut v_inst_2608_: *mut leanh::LeanObject,
    mut v_inst_2609_: *mut leanh::LeanObject,
    mut v_inst_2610_: *mut leanh::LeanObject,
    mut v_inst_2611_: *mut leanh::LeanObject,
    mut v_00_u03b1_2612_: *mut leanh::LeanObject,
    mut v_00_u03b2_2613_: *mut leanh::LeanObject,
    mut v_a_2614_: *mut leanh::LeanObject,
    mut v_a_2615_: *mut leanh::LeanObject,
    mut v_a_2616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2616_);
    leanh::lean_dec_ref(v_inst_2610_);
    leanh::lean_dec_ref(v_inst_2609_);
    return v_res_2617_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(
    mut v_a_2618_: *mut leanh::LeanObject,
    mut v_a_2619_: *mut leanh::LeanObject,
    mut v_a_2620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2619_);
    v___x_2621_ = leanh::lean_apply_2(v_a_2618_, v_a_2620_, v_a_2619_);
    return v___x_2621_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed(
    mut v_a_2622_: *mut leanh::LeanObject,
    mut v_a_2623_: *mut leanh::LeanObject,
    mut v_a_2624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2625_ =
        l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(v_a_2622_, v_a_2623_, v_a_2624_);
    leanh::lean_dec(v_a_2623_);
    return v_res_2625_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg(
    mut v_inst_2626_: *mut leanh::LeanObject,
    mut v_a_2627_: *mut leanh::LeanObject,
    mut v_a_2628_: *mut leanh::LeanObject,
    mut v_a_2629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2630_ = leanh::lean_ctor_get(v_inst_2626_, 1);
    leanh::lean_inc(v_toBind_2630_);
    leanh::lean_dec_ref(v_inst_2626_);
    leanh::lean_inc_n(v_a_2629_, 2);
    v___f_2631_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2631_, 0, v_a_2628_);
    leanh::lean_closure_set(v___f_2631_, 1, v_a_2629_);
    v___x_2632_ = leanh::lean_apply_1(v_a_2627_, v_a_2629_);
    v___x_2633_ = leanh::lean_apply_4(
        v_toBind_2630_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2632_,
        v___f_2631_,
    );
    return v___x_2633_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg___boxed(
    mut v_inst_2634_: *mut leanh::LeanObject,
    mut v_a_2635_: *mut leanh::LeanObject,
    mut v_a_2636_: *mut leanh::LeanObject,
    mut v_a_2637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2638_ = l_Lean_MonadCacheT_instMonad___aux__13___redArg(
        v_inst_2634_,
        v_a_2635_,
        v_a_2636_,
        v_a_2637_,
    );
    leanh::lean_dec(v_a_2637_);
    return v_res_2638_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13(
    mut v_00_u03c9_2639_: *mut leanh::LeanObject,
    mut v_00_u03b1_2640_: *mut leanh::LeanObject,
    mut v_00_u03b2_2641_: *mut leanh::LeanObject,
    mut v_m_2642_: *mut leanh::LeanObject,
    mut v_inst_2643_: *mut leanh::LeanObject,
    mut v_inst_2644_: *mut leanh::LeanObject,
    mut v_inst_2645_: *mut leanh::LeanObject,
    mut v_inst_2646_: *mut leanh::LeanObject,
    mut v_00_u03b1_2647_: *mut leanh::LeanObject,
    mut v_00_u03b2_2648_: *mut leanh::LeanObject,
    mut v_a_2649_: *mut leanh::LeanObject,
    mut v_a_2650_: *mut leanh::LeanObject,
    mut v_a_2651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2652_ = leanh::lean_ctor_get(v_inst_2646_, 1);
    leanh::lean_inc(v_toBind_2652_);
    leanh::lean_dec_ref(v_inst_2646_);
    leanh::lean_inc_n(v_a_2651_, 2);
    v___f_2653_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2653_, 0, v_a_2650_);
    leanh::lean_closure_set(v___f_2653_, 1, v_a_2651_);
    v___x_2654_ = leanh::lean_apply_1(v_a_2649_, v_a_2651_);
    v___x_2655_ = leanh::lean_apply_4(
        v_toBind_2652_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2654_,
        v___f_2653_,
    );
    return v___x_2655_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___boxed(
    mut v_00_u03c9_2656_: *mut leanh::LeanObject,
    mut v_00_u03b1_2657_: *mut leanh::LeanObject,
    mut v_00_u03b2_2658_: *mut leanh::LeanObject,
    mut v_m_2659_: *mut leanh::LeanObject,
    mut v_inst_2660_: *mut leanh::LeanObject,
    mut v_inst_2661_: *mut leanh::LeanObject,
    mut v_inst_2662_: *mut leanh::LeanObject,
    mut v_inst_2663_: *mut leanh::LeanObject,
    mut v_00_u03b1_2664_: *mut leanh::LeanObject,
    mut v_00_u03b2_2665_: *mut leanh::LeanObject,
    mut v_a_2666_: *mut leanh::LeanObject,
    mut v_a_2667_: *mut leanh::LeanObject,
    mut v_a_2668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2668_);
    leanh::lean_dec_ref(v_inst_2662_);
    leanh::lean_dec_ref(v_inst_2661_);
    return v_res_2669_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___redArg(
    mut v_inst_2670_: *mut leanh::LeanObject,
    mut v_inst_2671_: *mut leanh::LeanObject,
    mut v_inst_2672_: *mut leanh::LeanObject,
    mut v_inst_2673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_2673_, 6);
    leanh::lean_inc_ref_n(v_inst_2672_, 6);
    leanh::lean_inc_ref_n(v_inst_2671_, 6);
    v___x_2674_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__1___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    leanh::lean_closure_set(v___x_2674_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2674_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2674_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2674_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2674_, 4, v_inst_2670_);
    leanh::lean_closure_set(v___x_2674_, 5, v_inst_2671_);
    leanh::lean_closure_set(v___x_2674_, 6, v_inst_2672_);
    leanh::lean_closure_set(v___x_2674_, 7, v_inst_2673_);
    v___x_2675_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__3___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    leanh::lean_closure_set(v___x_2675_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2675_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2675_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2675_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2675_, 4, v_inst_2670_);
    leanh::lean_closure_set(v___x_2675_, 5, v_inst_2671_);
    leanh::lean_closure_set(v___x_2675_, 6, v_inst_2672_);
    leanh::lean_closure_set(v___x_2675_, 7, v_inst_2673_);
    v___x_2676_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2676_, 0, v___x_2674_);
    leanh::lean_ctor_set(v___x_2676_, 1, v___x_2675_);
    v___x_2677_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__5___boxed as *mut core::ffi::c_void,
        11,
        8,
    );
    leanh::lean_closure_set(v___x_2677_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2677_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2677_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2677_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2677_, 4, v_inst_2670_);
    leanh::lean_closure_set(v___x_2677_, 5, v_inst_2671_);
    leanh::lean_closure_set(v___x_2677_, 6, v_inst_2672_);
    leanh::lean_closure_set(v___x_2677_, 7, v_inst_2673_);
    v___x_2678_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    leanh::lean_closure_set(v___x_2678_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2678_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2678_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2678_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2678_, 4, v_inst_2670_);
    leanh::lean_closure_set(v___x_2678_, 5, v_inst_2671_);
    leanh::lean_closure_set(v___x_2678_, 6, v_inst_2672_);
    leanh::lean_closure_set(v___x_2678_, 7, v_inst_2673_);
    v___x_2679_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__9___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    leanh::lean_closure_set(v___x_2679_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2679_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2679_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2679_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2679_, 4, v_inst_2670_);
    leanh::lean_closure_set(v___x_2679_, 5, v_inst_2671_);
    leanh::lean_closure_set(v___x_2679_, 6, v_inst_2672_);
    leanh::lean_closure_set(v___x_2679_, 7, v_inst_2673_);
    v___x_2680_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__11___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    leanh::lean_closure_set(v___x_2680_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2680_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2680_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2680_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2680_, 4, v_inst_2670_);
    leanh::lean_closure_set(v___x_2680_, 5, v_inst_2671_);
    leanh::lean_closure_set(v___x_2680_, 6, v_inst_2672_);
    leanh::lean_closure_set(v___x_2680_, 7, v_inst_2673_);
    v___x_2681_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2681_, 0, v___x_2676_);
    leanh::lean_ctor_set(v___x_2681_, 1, v___x_2677_);
    leanh::lean_ctor_set(v___x_2681_, 2, v___x_2678_);
    leanh::lean_ctor_set(v___x_2681_, 3, v___x_2679_);
    leanh::lean_ctor_set(v___x_2681_, 4, v___x_2680_);
    v___x_2682_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    leanh::lean_closure_set(v___x_2682_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2682_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2682_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2682_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2682_, 4, v_inst_2670_);
    leanh::lean_closure_set(v___x_2682_, 5, v_inst_2671_);
    leanh::lean_closure_set(v___x_2682_, 6, v_inst_2672_);
    leanh::lean_closure_set(v___x_2682_, 7, v_inst_2673_);
    v___x_2683_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2683_, 0, v___x_2681_);
    leanh::lean_ctor_set(v___x_2683_, 1, v___x_2682_);
    return v___x_2683_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad(
    mut v_00_u03c9_2684_: *mut leanh::LeanObject,
    mut v_00_u03b1_2685_: *mut leanh::LeanObject,
    mut v_00_u03b2_2686_: *mut leanh::LeanObject,
    mut v_m_2687_: *mut leanh::LeanObject,
    mut v_inst_2688_: *mut leanh::LeanObject,
    mut v_inst_2689_: *mut leanh::LeanObject,
    mut v_inst_2690_: *mut leanh::LeanObject,
    mut v_inst_2691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2692_ = l_Lean_MonadCacheT_instMonad___redArg(
        v_inst_2688_,
        v_inst_2689_,
        v_inst_2690_,
        v_inst_2691_,
    );
    return v___x_2692_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1___redArg(
    mut v_x_2693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_2693_);
    return v_x_2693_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1___redArg___boxed(
    mut v_x_2694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2695_ = l_Lean_MonadCacheT_instMonadLift___aux__1___redArg(v_x_2694_);
    leanh::lean_dec(v_x_2694_);
    return v_res_2695_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1(
    mut v_00_u03c9_2696_: *mut leanh::LeanObject,
    mut v_00_u03b1_2697_: *mut leanh::LeanObject,
    mut v_00_u03b2_2698_: *mut leanh::LeanObject,
    mut v_m_2699_: *mut leanh::LeanObject,
    mut v_inst_2700_: *mut leanh::LeanObject,
    mut v_inst_2701_: *mut leanh::LeanObject,
    mut v_inst_2702_: *mut leanh::LeanObject,
    mut v_00_u03b1_2703_: *mut leanh::LeanObject,
    mut v_x_2704_: *mut leanh::LeanObject,
    mut v_a_2705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_2704_);
    return v_x_2704_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1___boxed(
    mut v_00_u03c9_2706_: *mut leanh::LeanObject,
    mut v_00_u03b1_2707_: *mut leanh::LeanObject,
    mut v_00_u03b2_2708_: *mut leanh::LeanObject,
    mut v_m_2709_: *mut leanh::LeanObject,
    mut v_inst_2710_: *mut leanh::LeanObject,
    mut v_inst_2711_: *mut leanh::LeanObject,
    mut v_inst_2712_: *mut leanh::LeanObject,
    mut v_00_u03b1_2713_: *mut leanh::LeanObject,
    mut v_x_2714_: *mut leanh::LeanObject,
    mut v_a_2715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2715_);
    leanh::lean_dec(v_x_2714_);
    leanh::lean_dec_ref(v_inst_2712_);
    leanh::lean_dec_ref(v_inst_2711_);
    return v_res_2716_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___redArg(
    mut v_inst_2717_: *mut leanh::LeanObject,
    mut v_inst_2718_: *mut leanh::LeanObject,
    mut v_inst_2719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2720_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    leanh::lean_closure_set(v___x_2720_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2720_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2720_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2720_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2720_, 4, v_inst_2717_);
    leanh::lean_closure_set(v___x_2720_, 5, v_inst_2718_);
    leanh::lean_closure_set(v___x_2720_, 6, v_inst_2719_);
    return v___x_2720_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift(
    mut v_00_u03c9_2721_: *mut leanh::LeanObject,
    mut v_00_u03b1_2722_: *mut leanh::LeanObject,
    mut v_00_u03b2_2723_: *mut leanh::LeanObject,
    mut v_m_2724_: *mut leanh::LeanObject,
    mut v_inst_2725_: *mut leanh::LeanObject,
    mut v_inst_2726_: *mut leanh::LeanObject,
    mut v_inst_2727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2728_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    leanh::lean_closure_set(v___x_2728_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2728_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2728_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2728_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2728_, 4, v_inst_2725_);
    leanh::lean_closure_set(v___x_2728_, 5, v_inst_2726_);
    leanh::lean_closure_set(v___x_2728_, 6, v_inst_2727_);
    return v___x_2728_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__1___redArg(
    mut v_inst_2729_: *mut leanh::LeanObject,
    mut v_a_2730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_2731_ = leanh::lean_ctor_get(v_inst_2729_, 0);
    leanh::lean_inc(v_throw_2731_);
    leanh::lean_dec_ref(v_inst_2729_);
    v___x_2732_ = leanh::lean_apply_2(v_throw_2731_, leanh::lean_box(0), v_a_2730_);
    return v___x_2732_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__1(
    mut v_00_u03c9_2733_: *mut leanh::LeanObject,
    mut v_00_u03b1_2734_: *mut leanh::LeanObject,
    mut v_00_u03b2_2735_: *mut leanh::LeanObject,
    mut v_m_2736_: *mut leanh::LeanObject,
    mut v_inst_2737_: *mut leanh::LeanObject,
    mut v_inst_2738_: *mut leanh::LeanObject,
    mut v_inst_2739_: *mut leanh::LeanObject,
    mut v_00_u03b5_2740_: *mut leanh::LeanObject,
    mut v_inst_2741_: *mut leanh::LeanObject,
    mut v_00_u03b1_2742_: *mut leanh::LeanObject,
    mut v_a_2743_: *mut leanh::LeanObject,
    mut v_a_2744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_2745_ = leanh::lean_ctor_get(v_inst_2741_, 0);
    leanh::lean_inc(v_throw_2745_);
    leanh::lean_dec_ref(v_inst_2741_);
    v___x_2746_ = leanh::lean_apply_2(v_throw_2745_, leanh::lean_box(0), v_a_2743_);
    return v___x_2746_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__1___boxed(
    mut v_00_u03c9_2747_: *mut leanh::LeanObject,
    mut v_00_u03b1_2748_: *mut leanh::LeanObject,
    mut v_00_u03b2_2749_: *mut leanh::LeanObject,
    mut v_m_2750_: *mut leanh::LeanObject,
    mut v_inst_2751_: *mut leanh::LeanObject,
    mut v_inst_2752_: *mut leanh::LeanObject,
    mut v_inst_2753_: *mut leanh::LeanObject,
    mut v_00_u03b5_2754_: *mut leanh::LeanObject,
    mut v_inst_2755_: *mut leanh::LeanObject,
    mut v_00_u03b1_2756_: *mut leanh::LeanObject,
    mut v_a_2757_: *mut leanh::LeanObject,
    mut v_a_2758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2758_);
    leanh::lean_dec_ref(v_inst_2753_);
    leanh::lean_dec_ref(v_inst_2752_);
    return v_res_2759_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0(
    mut v_c_2760_: *mut leanh::LeanObject,
    mut v_s_2761_: *mut leanh::LeanObject,
    mut v_e_2762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_s_2761_);
    v___x_2763_ = leanh::lean_apply_2(v_c_2760_, v_e_2762_, v_s_2761_);
    return v___x_2763_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed(
    mut v_c_2764_: *mut leanh::LeanObject,
    mut v_s_2765_: *mut leanh::LeanObject,
    mut v_e_2766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0(
        v_c_2764_, v_s_2765_, v_e_2766_,
    );
    leanh::lean_dec(v_s_2765_);
    return v_res_2767_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg(
    mut v_inst_2768_: *mut leanh::LeanObject,
    mut v_x_2769_: *mut leanh::LeanObject,
    mut v_c_2770_: *mut leanh::LeanObject,
    mut v_s_2771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_2772_ = leanh::lean_ctor_get(v_inst_2768_, 1);
    leanh::lean_inc(v_tryCatch_2772_);
    leanh::lean_dec_ref(v_inst_2768_);
    leanh::lean_inc_n(v_s_2771_, 2);
    v___f_2773_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2773_, 0, v_c_2770_);
    leanh::lean_closure_set(v___f_2773_, 1, v_s_2771_);
    v___x_2774_ = leanh::lean_apply_1(v_x_2769_, v_s_2771_);
    v___x_2775_ = leanh::lean_apply_3(
        v_tryCatch_2772_,
        leanh::lean_box(0),
        v___x_2774_,
        v___f_2773_,
    );
    return v___x_2775_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___boxed(
    mut v_inst_2776_: *mut leanh::LeanObject,
    mut v_x_2777_: *mut leanh::LeanObject,
    mut v_c_2778_: *mut leanh::LeanObject,
    mut v_s_2779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2780_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg(
        v_inst_2776_,
        v_x_2777_,
        v_c_2778_,
        v_s_2779_,
    );
    leanh::lean_dec(v_s_2779_);
    return v_res_2780_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3(
    mut v_00_u03c9_2781_: *mut leanh::LeanObject,
    mut v_00_u03b1_2782_: *mut leanh::LeanObject,
    mut v_00_u03b2_2783_: *mut leanh::LeanObject,
    mut v_m_2784_: *mut leanh::LeanObject,
    mut v_inst_2785_: *mut leanh::LeanObject,
    mut v_inst_2786_: *mut leanh::LeanObject,
    mut v_inst_2787_: *mut leanh::LeanObject,
    mut v_00_u03b5_2788_: *mut leanh::LeanObject,
    mut v_inst_2789_: *mut leanh::LeanObject,
    mut v_00_u03b1_2790_: *mut leanh::LeanObject,
    mut v_x_2791_: *mut leanh::LeanObject,
    mut v_c_2792_: *mut leanh::LeanObject,
    mut v_s_2793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_2794_ = leanh::lean_ctor_get(v_inst_2789_, 1);
    leanh::lean_inc(v_tryCatch_2794_);
    leanh::lean_dec_ref(v_inst_2789_);
    leanh::lean_inc_n(v_s_2793_, 2);
    v___f_2795_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2795_, 0, v_c_2792_);
    leanh::lean_closure_set(v___f_2795_, 1, v_s_2793_);
    v___x_2796_ = leanh::lean_apply_1(v_x_2791_, v_s_2793_);
    v___x_2797_ = leanh::lean_apply_3(
        v_tryCatch_2794_,
        leanh::lean_box(0),
        v___x_2796_,
        v___f_2795_,
    );
    return v___x_2797_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___boxed(
    mut v_00_u03c9_2798_: *mut leanh::LeanObject,
    mut v_00_u03b1_2799_: *mut leanh::LeanObject,
    mut v_00_u03b2_2800_: *mut leanh::LeanObject,
    mut v_m_2801_: *mut leanh::LeanObject,
    mut v_inst_2802_: *mut leanh::LeanObject,
    mut v_inst_2803_: *mut leanh::LeanObject,
    mut v_inst_2804_: *mut leanh::LeanObject,
    mut v_00_u03b5_2805_: *mut leanh::LeanObject,
    mut v_inst_2806_: *mut leanh::LeanObject,
    mut v_00_u03b1_2807_: *mut leanh::LeanObject,
    mut v_x_2808_: *mut leanh::LeanObject,
    mut v_c_2809_: *mut leanh::LeanObject,
    mut v_s_2810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_s_2810_);
    leanh::lean_dec_ref(v_inst_2804_);
    leanh::lean_dec_ref(v_inst_2803_);
    return v_res_2811_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___redArg(
    mut v_inst_2812_: *mut leanh::LeanObject,
    mut v_inst_2813_: *mut leanh::LeanObject,
    mut v_inst_2814_: *mut leanh::LeanObject,
    mut v_inst_2815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2815_);
    leanh::lean_inc_ref(v_inst_2814_);
    leanh::lean_inc_ref(v_inst_2813_);
    v___x_2816_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__1___boxed as *mut core::ffi::c_void,
        12,
        9,
    );
    leanh::lean_closure_set(v___x_2816_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2816_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2816_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2816_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2816_, 4, v_inst_2812_);
    leanh::lean_closure_set(v___x_2816_, 5, v_inst_2813_);
    leanh::lean_closure_set(v___x_2816_, 6, v_inst_2814_);
    leanh::lean_closure_set(v___x_2816_, 7, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2816_, 8, v_inst_2815_);
    v___x_2817_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__3___boxed as *mut core::ffi::c_void,
        13,
        9,
    );
    leanh::lean_closure_set(v___x_2817_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2817_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2817_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2817_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2817_, 4, v_inst_2812_);
    leanh::lean_closure_set(v___x_2817_, 5, v_inst_2813_);
    leanh::lean_closure_set(v___x_2817_, 6, v_inst_2814_);
    leanh::lean_closure_set(v___x_2817_, 7, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2817_, 8, v_inst_2815_);
    v___x_2818_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2818_, 0, v___x_2816_);
    leanh::lean_ctor_set(v___x_2818_, 1, v___x_2817_);
    return v___x_2818_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf(
    mut v_00_u03c9_2819_: *mut leanh::LeanObject,
    mut v_00_u03b1_2820_: *mut leanh::LeanObject,
    mut v_00_u03b2_2821_: *mut leanh::LeanObject,
    mut v_m_2822_: *mut leanh::LeanObject,
    mut v_inst_2823_: *mut leanh::LeanObject,
    mut v_inst_2824_: *mut leanh::LeanObject,
    mut v_inst_2825_: *mut leanh::LeanObject,
    mut v_00_u03b5_2826_: *mut leanh::LeanObject,
    mut v_inst_2827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2828_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(
        v_inst_2823_,
        v_inst_2824_,
        v_inst_2825_,
        v_inst_2827_,
    );
    return v___x_2828_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0(
    mut v_a_2829_: *mut leanh::LeanObject,
    mut v_00_u03b2_2830_: *mut leanh::LeanObject,
    mut v_x_2831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2829_);
    v___x_2832_ = leanh::lean_apply_1(v_x_2831_, v_a_2829_);
    return v___x_2832_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed(
    mut v_a_2833_: *mut leanh::LeanObject,
    mut v_00_u03b2_2834_: *mut leanh::LeanObject,
    mut v_x_2835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2836_ = l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0(
        v_a_2833_,
        v_00_u03b2_2834_,
        v_x_2835_,
    );
    leanh::lean_dec(v_a_2833_);
    return v_res_2836_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg(
    mut v_a_2837_: *mut leanh::LeanObject,
    mut v_a_2838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2838_);
    v___f_2839_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2839_, 0, v_a_2838_);
    v___x_2840_ = leanh::lean_apply_1(v_a_2837_, v___f_2839_);
    return v___x_2840_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___boxed(
    mut v_a_2841_: *mut leanh::LeanObject,
    mut v_a_2842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2843_ = l_Lean_MonadCacheT_instMonadControl___aux__1___redArg(v_a_2841_, v_a_2842_);
    leanh::lean_dec(v_a_2842_);
    return v_res_2843_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1(
    mut v_00_u03c9_2844_: *mut leanh::LeanObject,
    mut v_00_u03b1_2845_: *mut leanh::LeanObject,
    mut v_00_u03b2_2846_: *mut leanh::LeanObject,
    mut v_m_2847_: *mut leanh::LeanObject,
    mut v_inst_2848_: *mut leanh::LeanObject,
    mut v_inst_2849_: *mut leanh::LeanObject,
    mut v_inst_2850_: *mut leanh::LeanObject,
    mut v_00_u03b1_2851_: *mut leanh::LeanObject,
    mut v_a_2852_: *mut leanh::LeanObject,
    mut v_a_2853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2853_);
    v___f_2854_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2854_, 0, v_a_2853_);
    v___x_2855_ = leanh::lean_apply_1(v_a_2852_, v___f_2854_);
    return v___x_2855_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___boxed(
    mut v_00_u03c9_2856_: *mut leanh::LeanObject,
    mut v_00_u03b1_2857_: *mut leanh::LeanObject,
    mut v_00_u03b2_2858_: *mut leanh::LeanObject,
    mut v_m_2859_: *mut leanh::LeanObject,
    mut v_inst_2860_: *mut leanh::LeanObject,
    mut v_inst_2861_: *mut leanh::LeanObject,
    mut v_inst_2862_: *mut leanh::LeanObject,
    mut v_00_u03b1_2863_: *mut leanh::LeanObject,
    mut v_a_2864_: *mut leanh::LeanObject,
    mut v_a_2865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2865_);
    leanh::lean_dec_ref(v_inst_2862_);
    leanh::lean_dec_ref(v_inst_2861_);
    return v_res_2866_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3___redArg(
    mut v_a_2867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_a_2867_);
    return v_a_2867_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3___redArg___boxed(
    mut v_a_2868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2869_ = l_Lean_MonadCacheT_instMonadControl___aux__3___redArg(v_a_2868_);
    leanh::lean_dec(v_a_2868_);
    return v_res_2869_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3(
    mut v_00_u03c9_2870_: *mut leanh::LeanObject,
    mut v_00_u03b1_2871_: *mut leanh::LeanObject,
    mut v_00_u03b2_2872_: *mut leanh::LeanObject,
    mut v_m_2873_: *mut leanh::LeanObject,
    mut v_inst_2874_: *mut leanh::LeanObject,
    mut v_inst_2875_: *mut leanh::LeanObject,
    mut v_inst_2876_: *mut leanh::LeanObject,
    mut v_00_u03b1_2877_: *mut leanh::LeanObject,
    mut v_a_2878_: *mut leanh::LeanObject,
    mut v_a_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_a_2878_);
    return v_a_2878_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3___boxed(
    mut v_00_u03c9_2880_: *mut leanh::LeanObject,
    mut v_00_u03b1_2881_: *mut leanh::LeanObject,
    mut v_00_u03b2_2882_: *mut leanh::LeanObject,
    mut v_m_2883_: *mut leanh::LeanObject,
    mut v_inst_2884_: *mut leanh::LeanObject,
    mut v_inst_2885_: *mut leanh::LeanObject,
    mut v_inst_2886_: *mut leanh::LeanObject,
    mut v_00_u03b1_2887_: *mut leanh::LeanObject,
    mut v_a_2888_: *mut leanh::LeanObject,
    mut v_a_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2889_);
    leanh::lean_dec(v_a_2888_);
    leanh::lean_dec_ref(v_inst_2886_);
    leanh::lean_dec_ref(v_inst_2885_);
    return v_res_2890_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___redArg(
    mut v_inst_2891_: *mut leanh::LeanObject,
    mut v_inst_2892_: *mut leanh::LeanObject,
    mut v_inst_2893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2893_);
    leanh::lean_inc_ref(v_inst_2892_);
    v___x_2894_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__1___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    leanh::lean_closure_set(v___x_2894_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2894_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2894_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2894_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2894_, 4, v_inst_2891_);
    leanh::lean_closure_set(v___x_2894_, 5, v_inst_2892_);
    leanh::lean_closure_set(v___x_2894_, 6, v_inst_2893_);
    v___x_2895_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__3___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    leanh::lean_closure_set(v___x_2895_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2895_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2895_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2895_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2895_, 4, v_inst_2891_);
    leanh::lean_closure_set(v___x_2895_, 5, v_inst_2892_);
    leanh::lean_closure_set(v___x_2895_, 6, v_inst_2893_);
    v___x_2896_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2896_, 0, v___x_2894_);
    leanh::lean_ctor_set(v___x_2896_, 1, v___x_2895_);
    return v___x_2896_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl(
    mut v_00_u03c9_2897_: *mut leanh::LeanObject,
    mut v_00_u03b1_2898_: *mut leanh::LeanObject,
    mut v_00_u03b2_2899_: *mut leanh::LeanObject,
    mut v_m_2900_: *mut leanh::LeanObject,
    mut v_inst_2901_: *mut leanh::LeanObject,
    mut v_inst_2902_: *mut leanh::LeanObject,
    mut v_inst_2903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2904_ =
        l_Lean_MonadCacheT_instMonadControl___redArg(v_inst_2901_, v_inst_2902_, v_inst_2903_);
    return v___x_2904_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0(
    mut v_f_2905_: *mut leanh::LeanObject,
    mut v_a_2906_: *mut leanh::LeanObject,
    mut v_a_x3f_2907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2906_);
    v___x_2908_ = leanh::lean_apply_2(v_f_2905_, v_a_x3f_2907_, v_a_2906_);
    return v___x_2908_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed(
    mut v_f_2909_: *mut leanh::LeanObject,
    mut v_a_2910_: *mut leanh::LeanObject,
    mut v_a_x3f_2911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2912_ = l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0(
        v_f_2909_,
        v_a_2910_,
        v_a_x3f_2911_,
    );
    leanh::lean_dec(v_a_2910_);
    return v_res_2912_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg(
    mut v_inst_2913_: *mut leanh::LeanObject,
    mut v_x_2914_: *mut leanh::LeanObject,
    mut v_f_2915_: *mut leanh::LeanObject,
    mut v_a_2916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_a_2916_, 2);
    v___f_2917_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2917_, 0, v_f_2915_);
    leanh::lean_closure_set(v___f_2917_, 1, v_a_2916_);
    v___x_2918_ = leanh::lean_apply_1(v_x_2914_, v_a_2916_);
    v___x_2919_ = leanh::lean_apply_4(
        v_inst_2913_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2918_,
        v___f_2917_,
    );
    return v___x_2919_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___boxed(
    mut v_inst_2920_: *mut leanh::LeanObject,
    mut v_x_2921_: *mut leanh::LeanObject,
    mut v_f_2922_: *mut leanh::LeanObject,
    mut v_a_2923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2924_ = l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg(
        v_inst_2920_,
        v_x_2921_,
        v_f_2922_,
        v_a_2923_,
    );
    leanh::lean_dec(v_a_2923_);
    return v_res_2924_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1(
    mut v_00_u03c9_2925_: *mut leanh::LeanObject,
    mut v_00_u03b1_2926_: *mut leanh::LeanObject,
    mut v_00_u03b2_2927_: *mut leanh::LeanObject,
    mut v_m_2928_: *mut leanh::LeanObject,
    mut v_inst_2929_: *mut leanh::LeanObject,
    mut v_inst_2930_: *mut leanh::LeanObject,
    mut v_inst_2931_: *mut leanh::LeanObject,
    mut v_inst_2932_: *mut leanh::LeanObject,
    mut v_00_u03b1_2933_: *mut leanh::LeanObject,
    mut v_00_u03b2_2934_: *mut leanh::LeanObject,
    mut v_x_2935_: *mut leanh::LeanObject,
    mut v_f_2936_: *mut leanh::LeanObject,
    mut v_a_2937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_a_2937_, 2);
    v___f_2938_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2938_, 0, v_f_2936_);
    leanh::lean_closure_set(v___f_2938_, 1, v_a_2937_);
    v___x_2939_ = leanh::lean_apply_1(v_x_2935_, v_a_2937_);
    v___x_2940_ = leanh::lean_apply_4(
        v_inst_2932_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2939_,
        v___f_2938_,
    );
    return v___x_2940_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed(
    mut v_00_u03c9_2941_: *mut leanh::LeanObject,
    mut v_00_u03b1_2942_: *mut leanh::LeanObject,
    mut v_00_u03b2_2943_: *mut leanh::LeanObject,
    mut v_m_2944_: *mut leanh::LeanObject,
    mut v_inst_2945_: *mut leanh::LeanObject,
    mut v_inst_2946_: *mut leanh::LeanObject,
    mut v_inst_2947_: *mut leanh::LeanObject,
    mut v_inst_2948_: *mut leanh::LeanObject,
    mut v_00_u03b1_2949_: *mut leanh::LeanObject,
    mut v_00_u03b2_2950_: *mut leanh::LeanObject,
    mut v_x_2951_: *mut leanh::LeanObject,
    mut v_f_2952_: *mut leanh::LeanObject,
    mut v_a_2953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2953_);
    leanh::lean_dec_ref(v_inst_2947_);
    leanh::lean_dec_ref(v_inst_2946_);
    return v_res_2954_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___redArg(
    mut v_inst_2955_: *mut leanh::LeanObject,
    mut v_inst_2956_: *mut leanh::LeanObject,
    mut v_inst_2957_: *mut leanh::LeanObject,
    mut v_inst_2958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2959_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    leanh::lean_closure_set(v___x_2959_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2959_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2959_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2959_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2959_, 4, v_inst_2955_);
    leanh::lean_closure_set(v___x_2959_, 5, v_inst_2956_);
    leanh::lean_closure_set(v___x_2959_, 6, v_inst_2957_);
    leanh::lean_closure_set(v___x_2959_, 7, v_inst_2958_);
    return v___x_2959_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally(
    mut v_00_u03c9_2960_: *mut leanh::LeanObject,
    mut v_00_u03b1_2961_: *mut leanh::LeanObject,
    mut v_00_u03b2_2962_: *mut leanh::LeanObject,
    mut v_m_2963_: *mut leanh::LeanObject,
    mut v_inst_2964_: *mut leanh::LeanObject,
    mut v_inst_2965_: *mut leanh::LeanObject,
    mut v_inst_2966_: *mut leanh::LeanObject,
    mut v_inst_2967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2968_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    leanh::lean_closure_set(v___x_2968_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2968_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2968_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2968_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2968_, 4, v_inst_2964_);
    leanh::lean_closure_set(v___x_2968_, 5, v_inst_2965_);
    leanh::lean_closure_set(v___x_2968_, 6, v_inst_2966_);
    leanh::lean_closure_set(v___x_2968_, 7, v_inst_2967_);
    return v___x_2968_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1___redArg(
    mut v_inst_2969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRef_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRef_2970_ = leanh::lean_ctor_get(v_inst_2969_, 0);
    leanh::lean_inc(v_getRef_2970_);
    return v_getRef_2970_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1___redArg___boxed(
    mut v_inst_2971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2972_ = l_Lean_MonadCacheT_instMonadRef___aux__1___redArg(v_inst_2971_);
    leanh::lean_dec_ref(v_inst_2971_);
    return v_res_2972_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1(
    mut v_00_u03c9_2973_: *mut leanh::LeanObject,
    mut v_00_u03b1_2974_: *mut leanh::LeanObject,
    mut v_00_u03b2_2975_: *mut leanh::LeanObject,
    mut v_m_2976_: *mut leanh::LeanObject,
    mut v_inst_2977_: *mut leanh::LeanObject,
    mut v_inst_2978_: *mut leanh::LeanObject,
    mut v_inst_2979_: *mut leanh::LeanObject,
    mut v_inst_2980_: *mut leanh::LeanObject,
    mut v_a_2981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRef_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRef_2982_ = leanh::lean_ctor_get(v_inst_2980_, 0);
    leanh::lean_inc(v_getRef_2982_);
    return v_getRef_2982_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1___boxed(
    mut v_00_u03c9_2983_: *mut leanh::LeanObject,
    mut v_00_u03b1_2984_: *mut leanh::LeanObject,
    mut v_00_u03b2_2985_: *mut leanh::LeanObject,
    mut v_m_2986_: *mut leanh::LeanObject,
    mut v_inst_2987_: *mut leanh::LeanObject,
    mut v_inst_2988_: *mut leanh::LeanObject,
    mut v_inst_2989_: *mut leanh::LeanObject,
    mut v_inst_2990_: *mut leanh::LeanObject,
    mut v_a_2991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2991_);
    leanh::lean_dec_ref(v_inst_2990_);
    leanh::lean_dec_ref(v_inst_2989_);
    leanh::lean_dec_ref(v_inst_2988_);
    return v_res_2992_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3___redArg(
    mut v_inst_2993_: *mut leanh::LeanObject,
    mut v_ref_2994_: *mut leanh::LeanObject,
    mut v_x_2995_: *mut leanh::LeanObject,
    mut v_a_2996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withRef_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withRef_2997_ = leanh::lean_ctor_get(v_inst_2993_, 1);
    leanh::lean_inc(v_withRef_2997_);
    leanh::lean_dec_ref(v_inst_2993_);
    leanh::lean_inc(v_a_2996_);
    v___x_2998_ = leanh::lean_apply_1(v_x_2995_, v_a_2996_);
    v___x_2999_ = leanh::lean_apply_3(
        v_withRef_2997_,
        leanh::lean_box(0),
        v_ref_2994_,
        v___x_2998_,
    );
    return v___x_2999_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3___redArg___boxed(
    mut v_inst_3000_: *mut leanh::LeanObject,
    mut v_ref_3001_: *mut leanh::LeanObject,
    mut v_x_3002_: *mut leanh::LeanObject,
    mut v_a_3003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3004_ = l_Lean_MonadCacheT_instMonadRef___aux__3___redArg(
        v_inst_3000_,
        v_ref_3001_,
        v_x_3002_,
        v_a_3003_,
    );
    leanh::lean_dec(v_a_3003_);
    return v_res_3004_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3(
    mut v_00_u03c9_3005_: *mut leanh::LeanObject,
    mut v_00_u03b1_3006_: *mut leanh::LeanObject,
    mut v_00_u03b2_3007_: *mut leanh::LeanObject,
    mut v_m_3008_: *mut leanh::LeanObject,
    mut v_inst_3009_: *mut leanh::LeanObject,
    mut v_inst_3010_: *mut leanh::LeanObject,
    mut v_inst_3011_: *mut leanh::LeanObject,
    mut v_inst_3012_: *mut leanh::LeanObject,
    mut v_00_u03b1_3013_: *mut leanh::LeanObject,
    mut v_ref_3014_: *mut leanh::LeanObject,
    mut v_x_3015_: *mut leanh::LeanObject,
    mut v_a_3016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withRef_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withRef_3017_ = leanh::lean_ctor_get(v_inst_3012_, 1);
    leanh::lean_inc(v_withRef_3017_);
    leanh::lean_dec_ref(v_inst_3012_);
    leanh::lean_inc(v_a_3016_);
    v___x_3018_ = leanh::lean_apply_1(v_x_3015_, v_a_3016_);
    v___x_3019_ = leanh::lean_apply_3(
        v_withRef_3017_,
        leanh::lean_box(0),
        v_ref_3014_,
        v___x_3018_,
    );
    return v___x_3019_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3___boxed(
    mut v_00_u03c9_3020_: *mut leanh::LeanObject,
    mut v_00_u03b1_3021_: *mut leanh::LeanObject,
    mut v_00_u03b2_3022_: *mut leanh::LeanObject,
    mut v_m_3023_: *mut leanh::LeanObject,
    mut v_inst_3024_: *mut leanh::LeanObject,
    mut v_inst_3025_: *mut leanh::LeanObject,
    mut v_inst_3026_: *mut leanh::LeanObject,
    mut v_inst_3027_: *mut leanh::LeanObject,
    mut v_00_u03b1_3028_: *mut leanh::LeanObject,
    mut v_ref_3029_: *mut leanh::LeanObject,
    mut v_x_3030_: *mut leanh::LeanObject,
    mut v_a_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3031_);
    leanh::lean_dec_ref(v_inst_3026_);
    leanh::lean_dec_ref(v_inst_3025_);
    return v_res_3032_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___redArg(
    mut v_inst_3033_: *mut leanh::LeanObject,
    mut v_inst_3034_: *mut leanh::LeanObject,
    mut v_inst_3035_: *mut leanh::LeanObject,
    mut v_inst_3036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_3036_);
    leanh::lean_inc_ref(v_inst_3035_);
    leanh::lean_inc_ref(v_inst_3034_);
    v___x_3037_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadRef___aux__1___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___x_3037_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3037_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3037_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3037_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3037_, 4, v_inst_3033_);
    leanh::lean_closure_set(v___x_3037_, 5, v_inst_3034_);
    leanh::lean_closure_set(v___x_3037_, 6, v_inst_3035_);
    leanh::lean_closure_set(v___x_3037_, 7, v_inst_3036_);
    v___x_3038_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadRef___aux__3___boxed as *mut core::ffi::c_void,
        12,
        8,
    );
    leanh::lean_closure_set(v___x_3038_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3038_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3038_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3038_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3038_, 4, v_inst_3033_);
    leanh::lean_closure_set(v___x_3038_, 5, v_inst_3034_);
    leanh::lean_closure_set(v___x_3038_, 6, v_inst_3035_);
    leanh::lean_closure_set(v___x_3038_, 7, v_inst_3036_);
    v___x_3039_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3039_, 0, v___x_3037_);
    leanh::lean_ctor_set(v___x_3039_, 1, v___x_3038_);
    return v___x_3039_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef(
    mut v_00_u03c9_3040_: *mut leanh::LeanObject,
    mut v_00_u03b1_3041_: *mut leanh::LeanObject,
    mut v_00_u03b2_3042_: *mut leanh::LeanObject,
    mut v_m_3043_: *mut leanh::LeanObject,
    mut v_inst_3044_: *mut leanh::LeanObject,
    mut v_inst_3045_: *mut leanh::LeanObject,
    mut v_inst_3046_: *mut leanh::LeanObject,
    mut v_inst_3047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = l_Lean_MonadCacheT_instMonadRef___redArg(
        v_inst_3044_,
        v_inst_3045_,
        v_inst_3046_,
        v_inst_3047_,
    );
    return v___x_3048_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__1___redArg(
    mut v_inst_3049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failure_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failure_3050_ = leanh::lean_ctor_get(v_inst_3049_, 1);
    leanh::lean_inc(v_failure_3050_);
    leanh::lean_dec_ref(v_inst_3049_);
    v___x_3051_ = leanh::lean_apply_1(v_failure_3050_, leanh::lean_box(0));
    return v___x_3051_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__1(
    mut v_00_u03c9_3052_: *mut leanh::LeanObject,
    mut v_00_u03b1_3053_: *mut leanh::LeanObject,
    mut v_00_u03b2_3054_: *mut leanh::LeanObject,
    mut v_m_3055_: *mut leanh::LeanObject,
    mut v_inst_3056_: *mut leanh::LeanObject,
    mut v_inst_3057_: *mut leanh::LeanObject,
    mut v_inst_3058_: *mut leanh::LeanObject,
    mut v_inst_3059_: *mut leanh::LeanObject,
    mut v_00_u03b1_3060_: *mut leanh::LeanObject,
    mut v_a_3061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failure_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failure_3062_ = leanh::lean_ctor_get(v_inst_3059_, 1);
    leanh::lean_inc(v_failure_3062_);
    leanh::lean_dec_ref(v_inst_3059_);
    v___x_3063_ = leanh::lean_apply_1(v_failure_3062_, leanh::lean_box(0));
    return v___x_3063_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__1___boxed(
    mut v_00_u03c9_3064_: *mut leanh::LeanObject,
    mut v_00_u03b1_3065_: *mut leanh::LeanObject,
    mut v_00_u03b2_3066_: *mut leanh::LeanObject,
    mut v_m_3067_: *mut leanh::LeanObject,
    mut v_inst_3068_: *mut leanh::LeanObject,
    mut v_inst_3069_: *mut leanh::LeanObject,
    mut v_inst_3070_: *mut leanh::LeanObject,
    mut v_inst_3071_: *mut leanh::LeanObject,
    mut v_00_u03b1_3072_: *mut leanh::LeanObject,
    mut v_a_3073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3073_);
    leanh::lean_dec_ref(v_inst_3070_);
    leanh::lean_dec_ref(v_inst_3069_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3___redArg(
    mut v_inst_3075_: *mut leanh::LeanObject,
    mut v_a_3076_: *mut leanh::LeanObject,
    mut v_a_3077_: *mut leanh::LeanObject,
    mut v_a_3078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_3079_ = leanh::lean_ctor_get(v_inst_3075_, 2);
    leanh::lean_inc(v_orElse_3079_);
    leanh::lean_dec_ref(v_inst_3075_);
    leanh::lean_inc_n(v_a_3078_, 2);
    v___f_3080_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3080_, 0, v_a_3077_);
    leanh::lean_closure_set(v___f_3080_, 1, v_a_3078_);
    v___x_3081_ = leanh::lean_apply_1(v_a_3076_, v_a_3078_);
    v___x_3082_ = leanh::lean_apply_3(
        v_orElse_3079_,
        leanh::lean_box(0),
        v___x_3081_,
        v___f_3080_,
    );
    return v___x_3082_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3___redArg___boxed(
    mut v_inst_3083_: *mut leanh::LeanObject,
    mut v_a_3084_: *mut leanh::LeanObject,
    mut v_a_3085_: *mut leanh::LeanObject,
    mut v_a_3086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3087_ = l_Lean_MonadCacheT_instAlternative___aux__3___redArg(
        v_inst_3083_,
        v_a_3084_,
        v_a_3085_,
        v_a_3086_,
    );
    leanh::lean_dec(v_a_3086_);
    return v_res_3087_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3(
    mut v_00_u03c9_3088_: *mut leanh::LeanObject,
    mut v_00_u03b1_3089_: *mut leanh::LeanObject,
    mut v_00_u03b2_3090_: *mut leanh::LeanObject,
    mut v_m_3091_: *mut leanh::LeanObject,
    mut v_inst_3092_: *mut leanh::LeanObject,
    mut v_inst_3093_: *mut leanh::LeanObject,
    mut v_inst_3094_: *mut leanh::LeanObject,
    mut v_inst_3095_: *mut leanh::LeanObject,
    mut v_00_u03b1_3096_: *mut leanh::LeanObject,
    mut v_a_3097_: *mut leanh::LeanObject,
    mut v_a_3098_: *mut leanh::LeanObject,
    mut v_a_3099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_3100_ = leanh::lean_ctor_get(v_inst_3095_, 2);
    leanh::lean_inc(v_orElse_3100_);
    leanh::lean_dec_ref(v_inst_3095_);
    leanh::lean_inc_n(v_a_3099_, 2);
    v___f_3101_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3101_, 0, v_a_3098_);
    leanh::lean_closure_set(v___f_3101_, 1, v_a_3099_);
    v___x_3102_ = leanh::lean_apply_1(v_a_3097_, v_a_3099_);
    v___x_3103_ = leanh::lean_apply_3(
        v_orElse_3100_,
        leanh::lean_box(0),
        v___x_3102_,
        v___f_3101_,
    );
    return v___x_3103_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3___boxed(
    mut v_00_u03c9_3104_: *mut leanh::LeanObject,
    mut v_00_u03b1_3105_: *mut leanh::LeanObject,
    mut v_00_u03b2_3106_: *mut leanh::LeanObject,
    mut v_m_3107_: *mut leanh::LeanObject,
    mut v_inst_3108_: *mut leanh::LeanObject,
    mut v_inst_3109_: *mut leanh::LeanObject,
    mut v_inst_3110_: *mut leanh::LeanObject,
    mut v_inst_3111_: *mut leanh::LeanObject,
    mut v_00_u03b1_3112_: *mut leanh::LeanObject,
    mut v_a_3113_: *mut leanh::LeanObject,
    mut v_a_3114_: *mut leanh::LeanObject,
    mut v_a_3115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3115_);
    leanh::lean_dec_ref(v_inst_3110_);
    leanh::lean_dec_ref(v_inst_3109_);
    return v_res_3116_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___redArg(
    mut v_inst_3117_: *mut leanh::LeanObject,
    mut v_inst_3118_: *mut leanh::LeanObject,
    mut v_inst_3119_: *mut leanh::LeanObject,
    mut v_inst_3120_: *mut leanh::LeanObject,
    mut v_inst_3121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_3119_, 2);
    leanh::lean_inc_ref_n(v_inst_3118_, 2);
    v___x_3122_ = l_Lean_MonadCacheT_instMonad___redArg(
        v_inst_3117_,
        v_inst_3118_,
        v_inst_3119_,
        v_inst_3120_,
    );
    v_toApplicative_3123_ = leanh::lean_ctor_get(v___x_3122_, 0);
    leanh::lean_inc_ref(v_toApplicative_3123_);
    leanh::lean_dec_ref(v___x_3122_);
    leanh::lean_inc_ref(v_inst_3121_);
    v___x_3124_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instAlternative___aux__1___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    leanh::lean_closure_set(v___x_3124_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3124_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3124_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3124_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3124_, 4, v_inst_3117_);
    leanh::lean_closure_set(v___x_3124_, 5, v_inst_3118_);
    leanh::lean_closure_set(v___x_3124_, 6, v_inst_3119_);
    leanh::lean_closure_set(v___x_3124_, 7, v_inst_3121_);
    v___x_3125_ = leanh::lean_alloc_closure(
        l_Lean_MonadCacheT_instAlternative___aux__3___boxed as *mut core::ffi::c_void,
        12,
        8,
    );
    leanh::lean_closure_set(v___x_3125_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3125_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3125_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3125_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3125_, 4, v_inst_3117_);
    leanh::lean_closure_set(v___x_3125_, 5, v_inst_3118_);
    leanh::lean_closure_set(v___x_3125_, 6, v_inst_3119_);
    leanh::lean_closure_set(v___x_3125_, 7, v_inst_3121_);
    v___x_3126_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3126_, 0, v_toApplicative_3123_);
    leanh::lean_ctor_set(v___x_3126_, 1, v___x_3124_);
    leanh::lean_ctor_set(v___x_3126_, 2, v___x_3125_);
    return v___x_3126_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative(
    mut v_00_u03c9_3127_: *mut leanh::LeanObject,
    mut v_00_u03b1_3128_: *mut leanh::LeanObject,
    mut v_00_u03b2_3129_: *mut leanh::LeanObject,
    mut v_m_3130_: *mut leanh::LeanObject,
    mut v_inst_3131_: *mut leanh::LeanObject,
    mut v_inst_3132_: *mut leanh::LeanObject,
    mut v_inst_3133_: *mut leanh::LeanObject,
    mut v_inst_3134_: *mut leanh::LeanObject,
    mut v_inst_3135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3137_: *mut leanh::LeanObject,
    mut v_f_3138_: *mut leanh::LeanObject,
    mut v___y_3139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3143_: u8 = 0;
    let mut v_toPure_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut v_unused_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3140_ = leanh::lean_ctor_get(v_inst_3137_, 0);
                v_isSharedCheck_3151_ = (!leanh::lean_is_exclusive(v_inst_3137_)) as u8;
                if v_isSharedCheck_3151_ == 0 {
                    v_unused_3152_ = leanh::lean_ctor_get(v_inst_3137_, 1);
                    leanh::lean_dec(v_unused_3152_);
                    v___x_3142_ = v_inst_3137_;
                    v_isShared_3143_ = v_isSharedCheck_3151_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3140_);
                    leanh::lean_dec(v_inst_3137_);
                    v___x_3142_ = leanh::lean_box(0);
                    v_isShared_3143_ = v_isSharedCheck_3151_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3144_ = leanh::lean_ctor_get(v_toApplicative_3140_, 1);
                leanh::lean_inc(v_toPure_3144_);
                leanh::lean_dec_ref(v_toApplicative_3140_);
                v___x_3145_ = leanh::lean_box(0);
                v___x_3146_ = leanh::lean_apply_1(v_f_3138_, v___y_3139_);
                if v_isShared_3143_ == 0 {
                    leanh::lean_ctor_set(v___x_3142_, 1, v___x_3146_);
                    leanh::lean_ctor_set(v___x_3142_, 0, v___x_3145_);
                    v___x_3148_ = v___x_3142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_3146_);
                    v___x_3148_ = v_reuseFailAlloc_3150_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3149_ = leanh::lean_apply_2(
                    v_toPure_3144_,
                    leanh::lean_box(0),
                    v___x_3148_,
                );
                return v___x_3149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(
    mut v_inst_3153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_3153_);
    v___f_3154_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3154_, 0, v_inst_3153_);
    v___x_3155_ = leanh::lean_alloc_closure(l_StateT_get as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_3155_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3155_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3155_, 2, v_inst_3153_);
    v___x_3156_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3156_, 0, v___x_3155_);
    leanh::lean_ctor_set(v___x_3156_, 1, v___f_3154_);
    return v___x_3156_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(
    mut v_00_u03b1_3157_: *mut leanh::LeanObject,
    mut v_00_u03b2_3158_: *mut leanh::LeanObject,
    mut v_m_3159_: *mut leanh::LeanObject,
    mut v_inst_3160_: *mut leanh::LeanObject,
    mut v_inst_3161_: *mut leanh::LeanObject,
    mut v_inst_3162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3163_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_3162_);
    return v___x_3163_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___boxed(
    mut v_00_u03b1_3164_: *mut leanh::LeanObject,
    mut v_00_u03b2_3165_: *mut leanh::LeanObject,
    mut v_m_3166_: *mut leanh::LeanObject,
    mut v_inst_3167_: *mut leanh::LeanObject,
    mut v_inst_3168_: *mut leanh::LeanObject,
    mut v_inst_3169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3170_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(
        v_00_u03b1_3164_,
        v_00_u03b2_3165_,
        v_m_3166_,
        v_inst_3167_,
        v_inst_3168_,
        v_inst_3169_,
    );
    leanh::lean_dec_ref(v_inst_3168_);
    leanh::lean_dec_ref(v_inst_3167_);
    return v_res_3170_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___redArg___lam__0(
    mut v_x_3171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_3172_ = leanh::lean_ctor_get(v_x_3171_, 0);
    leanh::lean_inc(v_fst_3172_);
    return v_fst_3172_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed(
    mut v_x_3173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3174_ = l_Lean_MonadStateCacheT_run___redArg___lam__0(v_x_3173_);
    leanh::lean_dec_ref(v_x_3173_);
    return v_res_3174_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___redArg(
    mut v_inst_3176_: *mut leanh::LeanObject,
    mut v_x_3177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3178_ = leanh::lean_ctor_get(v_inst_3176_, 0);
    leanh::lean_inc_ref(v_toApplicative_3178_);
    leanh::lean_dec_ref(v_inst_3176_);
    v_toFunctor_3179_ = leanh::lean_ctor_get(v_toApplicative_3178_, 0);
    leanh::lean_inc_ref(v_toFunctor_3179_);
    leanh::lean_dec_ref(v_toApplicative_3178_);
    v_map_3180_ = leanh::lean_ctor_get(v_toFunctor_3179_, 0);
    leanh::lean_inc(v_map_3180_);
    leanh::lean_dec_ref(v_toFunctor_3179_);
    v___f_3181_ = l_Lean_MonadStateCacheT_run___redArg___closed__0;
    v___x_3182_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__1,
    );
    v___x_3183_ = leanh::lean_apply_1(v_x_3177_, v___x_3182_);
    v___x_3184_ = leanh::lean_apply_4(
        v_map_3180_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_3181_,
        v___x_3183_,
    );
    return v___x_3184_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run(
    mut v_00_u03b1_3185_: *mut leanh::LeanObject,
    mut v_00_u03b2_3186_: *mut leanh::LeanObject,
    mut v_m_3187_: *mut leanh::LeanObject,
    mut v_inst_3188_: *mut leanh::LeanObject,
    mut v_inst_3189_: *mut leanh::LeanObject,
    mut v_inst_3190_: *mut leanh::LeanObject,
    mut v_00_u03c3_3191_: *mut leanh::LeanObject,
    mut v_x_3192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3193_ = leanh::lean_ctor_get(v_inst_3190_, 0);
    leanh::lean_inc_ref(v_toApplicative_3193_);
    leanh::lean_dec_ref(v_inst_3190_);
    v_toFunctor_3194_ = leanh::lean_ctor_get(v_toApplicative_3193_, 0);
    leanh::lean_inc_ref(v_toFunctor_3194_);
    leanh::lean_dec_ref(v_toApplicative_3193_);
    v_map_3195_ = leanh::lean_ctor_get(v_toFunctor_3194_, 0);
    leanh::lean_inc(v_map_3195_);
    leanh::lean_dec_ref(v_toFunctor_3194_);
    v___f_3196_ = l_Lean_MonadStateCacheT_run___redArg___closed__0;
    v___x_3197_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__1,
    );
    v___x_3198_ = leanh::lean_apply_1(v_x_3192_, v___x_3197_);
    v___x_3199_ = leanh::lean_apply_4(
        v_map_3195_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_3196_,
        v___x_3198_,
    );
    return v___x_3199_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___boxed(
    mut v_00_u03b1_3200_: *mut leanh::LeanObject,
    mut v_00_u03b2_3201_: *mut leanh::LeanObject,
    mut v_m_3202_: *mut leanh::LeanObject,
    mut v_inst_3203_: *mut leanh::LeanObject,
    mut v_inst_3204_: *mut leanh::LeanObject,
    mut v_inst_3205_: *mut leanh::LeanObject,
    mut v_00_u03c3_3206_: *mut leanh::LeanObject,
    mut v_x_3207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3204_);
    leanh::lean_dec_ref(v_inst_3203_);
    return v_res_3208_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0(
    mut v_f_3209_: *mut leanh::LeanObject,
    mut v_toPure_3210_: *mut leanh::LeanObject,
    mut v_____x_3211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3212_ = leanh::lean_ctor_get(v_____x_3211_, 0);
                v_snd_3213_ = leanh::lean_ctor_get(v_____x_3211_, 1);
                v_isSharedCheck_3222_ = (!leanh::lean_is_exclusive(v_____x_3211_)) as u8;
                if v_isSharedCheck_3222_ == 0 {
                    v___x_3215_ = v_____x_3211_;
                    v_isShared_3216_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3213_);
                    leanh::lean_inc(v_fst_3212_);
                    leanh::lean_dec(v_____x_3211_);
                    v___x_3215_ = leanh::lean_box(0);
                    v_isShared_3216_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3217_ = leanh::lean_apply_1(v_f_3209_, v_fst_3212_);
                if v_isShared_3216_ == 0 {
                    leanh::lean_ctor_set(v___x_3215_, 0, v___x_3217_);
                    v___x_3219_ = v___x_3215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_snd_3213_);
                    v___x_3219_ = v_reuseFailAlloc_3221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3220_ = leanh::lean_apply_2(
                    v_toPure_3210_,
                    leanh::lean_box(0),
                    v___x_3219_,
                );
                return v___x_3220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1___redArg(
    mut v_inst_3223_: *mut leanh::LeanObject,
    mut v_f_3224_: *mut leanh::LeanObject,
    mut v_x_3225_: *mut leanh::LeanObject,
    mut v_a_3226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3227_ = leanh::lean_ctor_get(v_inst_3223_, 0);
    leanh::lean_inc_ref(v_toApplicative_3227_);
    v_toBind_3228_ = leanh::lean_ctor_get(v_inst_3223_, 1);
    leanh::lean_inc(v_toBind_3228_);
    leanh::lean_dec_ref(v_inst_3223_);
    v_toPure_3229_ = leanh::lean_ctor_get(v_toApplicative_3227_, 1);
    leanh::lean_inc(v_toPure_3229_);
    leanh::lean_dec_ref(v_toApplicative_3227_);
    v___x_3230_ = leanh::lean_apply_1(v_x_3225_, v_a_3226_);
    v___f_3231_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3231_, 0, v_f_3224_);
    leanh::lean_closure_set(v___f_3231_, 1, v_toPure_3229_);
    v___x_3232_ = leanh::lean_apply_4(
        v_toBind_3228_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3230_,
        v___f_3231_,
    );
    return v___x_3232_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1(
    mut v_00_u03b1_3233_: *mut leanh::LeanObject,
    mut v_00_u03b2_3234_: *mut leanh::LeanObject,
    mut v_m_3235_: *mut leanh::LeanObject,
    mut v_inst_3236_: *mut leanh::LeanObject,
    mut v_inst_3237_: *mut leanh::LeanObject,
    mut v_inst_3238_: *mut leanh::LeanObject,
    mut v_00_u03b1_3239_: *mut leanh::LeanObject,
    mut v_00_u03b2_3240_: *mut leanh::LeanObject,
    mut v_f_3241_: *mut leanh::LeanObject,
    mut v_x_3242_: *mut leanh::LeanObject,
    mut v_a_3243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3244_ = leanh::lean_ctor_get(v_inst_3238_, 0);
    leanh::lean_inc_ref(v_toApplicative_3244_);
    v_toBind_3245_ = leanh::lean_ctor_get(v_inst_3238_, 1);
    leanh::lean_inc(v_toBind_3245_);
    leanh::lean_dec_ref(v_inst_3238_);
    v_toPure_3246_ = leanh::lean_ctor_get(v_toApplicative_3244_, 1);
    leanh::lean_inc(v_toPure_3246_);
    leanh::lean_dec_ref(v_toApplicative_3244_);
    v___x_3247_ = leanh::lean_apply_1(v_x_3242_, v_a_3243_);
    v___f_3248_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3248_, 0, v_f_3241_);
    leanh::lean_closure_set(v___f_3248_, 1, v_toPure_3246_);
    v___x_3249_ = leanh::lean_apply_4(
        v_toBind_3245_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3247_,
        v___f_3248_,
    );
    return v___x_3249_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1___boxed(
    mut v_00_u03b1_3250_: *mut leanh::LeanObject,
    mut v_00_u03b2_3251_: *mut leanh::LeanObject,
    mut v_m_3252_: *mut leanh::LeanObject,
    mut v_inst_3253_: *mut leanh::LeanObject,
    mut v_inst_3254_: *mut leanh::LeanObject,
    mut v_inst_3255_: *mut leanh::LeanObject,
    mut v_00_u03b1_3256_: *mut leanh::LeanObject,
    mut v_00_u03b2_3257_: *mut leanh::LeanObject,
    mut v_f_3258_: *mut leanh::LeanObject,
    mut v_x_3259_: *mut leanh::LeanObject,
    mut v_a_3260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3254_);
    leanh::lean_dec_ref(v_inst_3253_);
    return v_res_3261_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0(
    mut v_a_3262_: *mut leanh::LeanObject,
    mut v_toPure_3263_: *mut leanh::LeanObject,
    mut v_____x_3264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_unused_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3265_ = leanh::lean_ctor_get(v_____x_3264_, 1);
                v_isSharedCheck_3273_ = (!leanh::lean_is_exclusive(v_____x_3264_)) as u8;
                if v_isSharedCheck_3273_ == 0 {
                    v_unused_3274_ = leanh::lean_ctor_get(v_____x_3264_, 0);
                    leanh::lean_dec(v_unused_3274_);
                    v___x_3267_ = v_____x_3264_;
                    v_isShared_3268_ = v_isSharedCheck_3273_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3265_);
                    leanh::lean_dec(v_____x_3264_);
                    v___x_3267_ = leanh::lean_box(0);
                    v_isShared_3268_ = v_isSharedCheck_3273_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3268_ == 0 {
                    leanh::lean_ctor_set(v___x_3267_, 0, v_a_3262_);
                    v___x_3270_ = v___x_3267_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3272_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_snd_3265_);
                    v___x_3270_ = v_reuseFailAlloc_3272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3271_ = leanh::lean_apply_2(
                    v_toPure_3263_,
                    leanh::lean_box(0),
                    v___x_3270_,
                );
                return v___x_3271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3___redArg(
    mut v_inst_3275_: *mut leanh::LeanObject,
    mut v_a_3276_: *mut leanh::LeanObject,
    mut v_a_3277_: *mut leanh::LeanObject,
    mut v_a_3278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3279_ = leanh::lean_ctor_get(v_inst_3275_, 0);
    leanh::lean_inc_ref(v_toApplicative_3279_);
    v_toBind_3280_ = leanh::lean_ctor_get(v_inst_3275_, 1);
    leanh::lean_inc(v_toBind_3280_);
    leanh::lean_dec_ref(v_inst_3275_);
    v_toPure_3281_ = leanh::lean_ctor_get(v_toApplicative_3279_, 1);
    leanh::lean_inc(v_toPure_3281_);
    leanh::lean_dec_ref(v_toApplicative_3279_);
    v___x_3282_ = leanh::lean_apply_1(v_a_3277_, v_a_3278_);
    v___f_3283_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3283_, 0, v_a_3276_);
    leanh::lean_closure_set(v___f_3283_, 1, v_toPure_3281_);
    v___x_3284_ = leanh::lean_apply_4(
        v_toBind_3280_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3282_,
        v___f_3283_,
    );
    return v___x_3284_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3(
    mut v_00_u03b1_3285_: *mut leanh::LeanObject,
    mut v_00_u03b2_3286_: *mut leanh::LeanObject,
    mut v_m_3287_: *mut leanh::LeanObject,
    mut v_inst_3288_: *mut leanh::LeanObject,
    mut v_inst_3289_: *mut leanh::LeanObject,
    mut v_inst_3290_: *mut leanh::LeanObject,
    mut v_00_u03b1_3291_: *mut leanh::LeanObject,
    mut v_00_u03b2_3292_: *mut leanh::LeanObject,
    mut v_a_3293_: *mut leanh::LeanObject,
    mut v_a_3294_: *mut leanh::LeanObject,
    mut v_a_3295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3296_ = leanh::lean_ctor_get(v_inst_3290_, 0);
    leanh::lean_inc_ref(v_toApplicative_3296_);
    v_toBind_3297_ = leanh::lean_ctor_get(v_inst_3290_, 1);
    leanh::lean_inc(v_toBind_3297_);
    leanh::lean_dec_ref(v_inst_3290_);
    v_toPure_3298_ = leanh::lean_ctor_get(v_toApplicative_3296_, 1);
    leanh::lean_inc(v_toPure_3298_);
    leanh::lean_dec_ref(v_toApplicative_3296_);
    v___x_3299_ = leanh::lean_apply_1(v_a_3294_, v_a_3295_);
    v___f_3300_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3300_, 0, v_a_3293_);
    leanh::lean_closure_set(v___f_3300_, 1, v_toPure_3298_);
    v___x_3301_ = leanh::lean_apply_4(
        v_toBind_3297_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3299_,
        v___f_3300_,
    );
    return v___x_3301_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3___boxed(
    mut v_00_u03b1_3302_: *mut leanh::LeanObject,
    mut v_00_u03b2_3303_: *mut leanh::LeanObject,
    mut v_m_3304_: *mut leanh::LeanObject,
    mut v_inst_3305_: *mut leanh::LeanObject,
    mut v_inst_3306_: *mut leanh::LeanObject,
    mut v_inst_3307_: *mut leanh::LeanObject,
    mut v_00_u03b1_3308_: *mut leanh::LeanObject,
    mut v_00_u03b2_3309_: *mut leanh::LeanObject,
    mut v_a_3310_: *mut leanh::LeanObject,
    mut v_a_3311_: *mut leanh::LeanObject,
    mut v_a_3312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3306_);
    leanh::lean_dec_ref(v_inst_3305_);
    return v_res_3313_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__5___redArg(
    mut v_inst_3314_: *mut leanh::LeanObject,
    mut v_a_3315_: *mut leanh::LeanObject,
    mut v_a_3316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3320_: u8 = 0;
    let mut v_toPure_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut v_unused_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3317_ = leanh::lean_ctor_get(v_inst_3314_, 0);
                v_isSharedCheck_3326_ = (!leanh::lean_is_exclusive(v_inst_3314_)) as u8;
                if v_isSharedCheck_3326_ == 0 {
                    v_unused_3327_ = leanh::lean_ctor_get(v_inst_3314_, 1);
                    leanh::lean_dec(v_unused_3327_);
                    v___x_3319_ = v_inst_3314_;
                    v_isShared_3320_ = v_isSharedCheck_3326_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3317_);
                    leanh::lean_dec(v_inst_3314_);
                    v___x_3319_ = leanh::lean_box(0);
                    v_isShared_3320_ = v_isSharedCheck_3326_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3321_ = leanh::lean_ctor_get(v_toApplicative_3317_, 1);
                leanh::lean_inc(v_toPure_3321_);
                leanh::lean_dec_ref(v_toApplicative_3317_);
                if v_isShared_3320_ == 0 {
                    leanh::lean_ctor_set(v___x_3319_, 1, v_a_3316_);
                    leanh::lean_ctor_set(v___x_3319_, 0, v_a_3315_);
                    v___x_3323_ = v___x_3319_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3325_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_a_3316_);
                    v___x_3323_ = v_reuseFailAlloc_3325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3324_ = leanh::lean_apply_2(
                    v_toPure_3321_,
                    leanh::lean_box(0),
                    v___x_3323_,
                );
                return v___x_3324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__5(
    mut v_00_u03b1_3328_: *mut leanh::LeanObject,
    mut v_00_u03b2_3329_: *mut leanh::LeanObject,
    mut v_m_3330_: *mut leanh::LeanObject,
    mut v_inst_3331_: *mut leanh::LeanObject,
    mut v_inst_3332_: *mut leanh::LeanObject,
    mut v_inst_3333_: *mut leanh::LeanObject,
    mut v_00_u03b1_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
    mut v_a_3336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v_toPure_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_unused_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3337_ = leanh::lean_ctor_get(v_inst_3333_, 0);
                v_isSharedCheck_3346_ = (!leanh::lean_is_exclusive(v_inst_3333_)) as u8;
                if v_isSharedCheck_3346_ == 0 {
                    v_unused_3347_ = leanh::lean_ctor_get(v_inst_3333_, 1);
                    leanh::lean_dec(v_unused_3347_);
                    v___x_3339_ = v_inst_3333_;
                    v_isShared_3340_ = v_isSharedCheck_3346_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3337_);
                    leanh::lean_dec(v_inst_3333_);
                    v___x_3339_ = leanh::lean_box(0);
                    v_isShared_3340_ = v_isSharedCheck_3346_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3341_ = leanh::lean_ctor_get(v_toApplicative_3337_, 1);
                leanh::lean_inc(v_toPure_3341_);
                leanh::lean_dec_ref(v_toApplicative_3337_);
                if v_isShared_3340_ == 0 {
                    leanh::lean_ctor_set(v___x_3339_, 1, v_a_3336_);
                    leanh::lean_ctor_set(v___x_3339_, 0, v_a_3335_);
                    v___x_3343_ = v___x_3339_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3335_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_a_3336_);
                    v___x_3343_ = v_reuseFailAlloc_3345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3344_ = leanh::lean_apply_2(
                    v_toPure_3341_,
                    leanh::lean_box(0),
                    v___x_3343_,
                );
                return v___x_3344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__5___boxed(
    mut v_00_u03b1_3348_: *mut leanh::LeanObject,
    mut v_00_u03b2_3349_: *mut leanh::LeanObject,
    mut v_m_3350_: *mut leanh::LeanObject,
    mut v_inst_3351_: *mut leanh::LeanObject,
    mut v_inst_3352_: *mut leanh::LeanObject,
    mut v_inst_3353_: *mut leanh::LeanObject,
    mut v_00_u03b1_3354_: *mut leanh::LeanObject,
    mut v_a_3355_: *mut leanh::LeanObject,
    mut v_a_3356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3352_);
    leanh::lean_dec_ref(v_inst_3351_);
    return v_res_3357_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0(
    mut v_fst_3358_: *mut leanh::LeanObject,
    mut v_toPure_3359_: *mut leanh::LeanObject,
    mut v_____x_3360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3365_: u8 = 0;
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3361_ = leanh::lean_ctor_get(v_____x_3360_, 0);
                v_snd_3362_ = leanh::lean_ctor_get(v_____x_3360_, 1);
                v_isSharedCheck_3371_ = (!leanh::lean_is_exclusive(v_____x_3360_)) as u8;
                if v_isSharedCheck_3371_ == 0 {
                    v___x_3364_ = v_____x_3360_;
                    v_isShared_3365_ = v_isSharedCheck_3371_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3362_);
                    leanh::lean_inc(v_fst_3361_);
                    leanh::lean_dec(v_____x_3360_);
                    v___x_3364_ = leanh::lean_box(0);
                    v_isShared_3365_ = v_isSharedCheck_3371_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3366_ = leanh::lean_apply_1(v_fst_3358_, v_fst_3361_);
                if v_isShared_3365_ == 0 {
                    leanh::lean_ctor_set(v___x_3364_, 0, v___x_3366_);
                    v___x_3368_ = v___x_3364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3370_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3366_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_snd_3362_);
                    v___x_3368_ = v_reuseFailAlloc_3370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3369_ = leanh::lean_apply_2(
                    v_toPure_3359_,
                    leanh::lean_box(0),
                    v___x_3368_,
                );
                return v___x_3369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1(
    mut v_toApplicative_3372_: *mut leanh::LeanObject,
    mut v_x_3373_: *mut leanh::LeanObject,
    mut v_toBind_3374_: *mut leanh::LeanObject,
    mut v_____x_3375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_3376_ = leanh::lean_ctor_get(v_____x_3375_, 0);
    leanh::lean_inc(v_fst_3376_);
    v_snd_3377_ = leanh::lean_ctor_get(v_____x_3375_, 1);
    leanh::lean_inc(v_snd_3377_);
    leanh::lean_dec_ref(v_____x_3375_);
    v_toPure_3378_ = leanh::lean_ctor_get(v_toApplicative_3372_, 1);
    leanh::lean_inc(v_toPure_3378_);
    leanh::lean_dec_ref(v_toApplicative_3372_);
    v___x_3379_ = leanh::lean_box(0);
    v___x_3380_ = leanh::lean_apply_2(v_x_3373_, v___x_3379_, v_snd_3377_);
    v___f_3381_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3381_, 0, v_fst_3376_);
    leanh::lean_closure_set(v___f_3381_, 1, v_toPure_3378_);
    v___x_3382_ = leanh::lean_apply_4(
        v_toBind_3374_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3380_,
        v___f_3381_,
    );
    return v___x_3382_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___redArg(
    mut v_inst_3383_: *mut leanh::LeanObject,
    mut v_f_3384_: *mut leanh::LeanObject,
    mut v_x_3385_: *mut leanh::LeanObject,
    mut v_a_3386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3387_ = leanh::lean_ctor_get(v_inst_3383_, 0);
    leanh::lean_inc_ref(v_toApplicative_3387_);
    v_toBind_3388_ = leanh::lean_ctor_get(v_inst_3383_, 1);
    leanh::lean_inc_n(v_toBind_3388_, 2);
    leanh::lean_dec_ref(v_inst_3383_);
    v___f_3389_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3389_, 0, v_toApplicative_3387_);
    leanh::lean_closure_set(v___f_3389_, 1, v_x_3385_);
    leanh::lean_closure_set(v___f_3389_, 2, v_toBind_3388_);
    v___x_3390_ = leanh::lean_apply_1(v_f_3384_, v_a_3386_);
    v___x_3391_ = leanh::lean_apply_4(
        v_toBind_3388_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3390_,
        v___f_3389_,
    );
    return v___x_3391_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7(
    mut v_00_u03b1_3392_: *mut leanh::LeanObject,
    mut v_00_u03b2_3393_: *mut leanh::LeanObject,
    mut v_m_3394_: *mut leanh::LeanObject,
    mut v_inst_3395_: *mut leanh::LeanObject,
    mut v_inst_3396_: *mut leanh::LeanObject,
    mut v_inst_3397_: *mut leanh::LeanObject,
    mut v_00_u03b1_3398_: *mut leanh::LeanObject,
    mut v_00_u03b2_3399_: *mut leanh::LeanObject,
    mut v_f_3400_: *mut leanh::LeanObject,
    mut v_x_3401_: *mut leanh::LeanObject,
    mut v_a_3402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3403_ = leanh::lean_ctor_get(v_inst_3397_, 0);
    leanh::lean_inc_ref(v_toApplicative_3403_);
    v_toBind_3404_ = leanh::lean_ctor_get(v_inst_3397_, 1);
    leanh::lean_inc_n(v_toBind_3404_, 2);
    leanh::lean_dec_ref(v_inst_3397_);
    v___f_3405_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3405_, 0, v_toApplicative_3403_);
    leanh::lean_closure_set(v___f_3405_, 1, v_x_3401_);
    leanh::lean_closure_set(v___f_3405_, 2, v_toBind_3404_);
    v___x_3406_ = leanh::lean_apply_1(v_f_3400_, v_a_3402_);
    v___x_3407_ = leanh::lean_apply_4(
        v_toBind_3404_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3406_,
        v___f_3405_,
    );
    return v___x_3407_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___boxed(
    mut v_00_u03b1_3408_: *mut leanh::LeanObject,
    mut v_00_u03b2_3409_: *mut leanh::LeanObject,
    mut v_m_3410_: *mut leanh::LeanObject,
    mut v_inst_3411_: *mut leanh::LeanObject,
    mut v_inst_3412_: *mut leanh::LeanObject,
    mut v_inst_3413_: *mut leanh::LeanObject,
    mut v_00_u03b1_3414_: *mut leanh::LeanObject,
    mut v_00_u03b2_3415_: *mut leanh::LeanObject,
    mut v_f_3416_: *mut leanh::LeanObject,
    mut v_x_3417_: *mut leanh::LeanObject,
    mut v_a_3418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3412_);
    leanh::lean_dec_ref(v_inst_3411_);
    return v_res_3419_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0(
    mut v_toApplicative_3420_: *mut leanh::LeanObject,
    mut v_fst_3421_: *mut leanh::LeanObject,
    mut v_____x_3422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3426_: u8 = 0;
    let mut v_toPure_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3432_: u8 = 0;
    let mut v_unused_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3423_ = leanh::lean_ctor_get(v_____x_3422_, 1);
                v_isSharedCheck_3432_ = (!leanh::lean_is_exclusive(v_____x_3422_)) as u8;
                if v_isSharedCheck_3432_ == 0 {
                    v_unused_3433_ = leanh::lean_ctor_get(v_____x_3422_, 0);
                    leanh::lean_dec(v_unused_3433_);
                    v___x_3425_ = v_____x_3422_;
                    v_isShared_3426_ = v_isSharedCheck_3432_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3423_);
                    leanh::lean_dec(v_____x_3422_);
                    v___x_3425_ = leanh::lean_box(0);
                    v_isShared_3426_ = v_isSharedCheck_3432_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3427_ = leanh::lean_ctor_get(v_toApplicative_3420_, 1);
                leanh::lean_inc(v_toPure_3427_);
                leanh::lean_dec_ref(v_toApplicative_3420_);
                if v_isShared_3426_ == 0 {
                    leanh::lean_ctor_set(v___x_3425_, 0, v_fst_3421_);
                    v___x_3429_ = v___x_3425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3431_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_fst_3421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_snd_3423_);
                    v___x_3429_ = v_reuseFailAlloc_3431_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3430_ = leanh::lean_apply_2(
                    v_toPure_3427_,
                    leanh::lean_box(0),
                    v___x_3429_,
                );
                return v___x_3430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1(
    mut v_toApplicative_3434_: *mut leanh::LeanObject,
    mut v_y_3435_: *mut leanh::LeanObject,
    mut v_toBind_3436_: *mut leanh::LeanObject,
    mut v_____x_3437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_3438_ = leanh::lean_ctor_get(v_____x_3437_, 0);
    leanh::lean_inc(v_fst_3438_);
    v_snd_3439_ = leanh::lean_ctor_get(v_____x_3437_, 1);
    leanh::lean_inc(v_snd_3439_);
    leanh::lean_dec_ref(v_____x_3437_);
    v___f_3440_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3440_, 0, v_toApplicative_3434_);
    leanh::lean_closure_set(v___f_3440_, 1, v_fst_3438_);
    v___x_3441_ = leanh::lean_box(0);
    v___x_3442_ = leanh::lean_apply_2(v_y_3435_, v___x_3441_, v_snd_3439_);
    v___x_3443_ = leanh::lean_apply_4(
        v_toBind_3436_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3442_,
        v___f_3440_,
    );
    return v___x_3443_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___redArg(
    mut v_inst_3444_: *mut leanh::LeanObject,
    mut v_x_3445_: *mut leanh::LeanObject,
    mut v_y_3446_: *mut leanh::LeanObject,
    mut v_a_3447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3448_ = leanh::lean_ctor_get(v_inst_3444_, 0);
    leanh::lean_inc_ref(v_toApplicative_3448_);
    v_toBind_3449_ = leanh::lean_ctor_get(v_inst_3444_, 1);
    leanh::lean_inc_n(v_toBind_3449_, 2);
    leanh::lean_dec_ref(v_inst_3444_);
    v___f_3450_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3450_, 0, v_toApplicative_3448_);
    leanh::lean_closure_set(v___f_3450_, 1, v_y_3446_);
    leanh::lean_closure_set(v___f_3450_, 2, v_toBind_3449_);
    v___x_3451_ = leanh::lean_apply_1(v_x_3445_, v_a_3447_);
    v___x_3452_ = leanh::lean_apply_4(
        v_toBind_3449_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3451_,
        v___f_3450_,
    );
    return v___x_3452_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9(
    mut v_00_u03b1_3453_: *mut leanh::LeanObject,
    mut v_00_u03b2_3454_: *mut leanh::LeanObject,
    mut v_m_3455_: *mut leanh::LeanObject,
    mut v_inst_3456_: *mut leanh::LeanObject,
    mut v_inst_3457_: *mut leanh::LeanObject,
    mut v_inst_3458_: *mut leanh::LeanObject,
    mut v_00_u03b1_3459_: *mut leanh::LeanObject,
    mut v_00_u03b2_3460_: *mut leanh::LeanObject,
    mut v_x_3461_: *mut leanh::LeanObject,
    mut v_y_3462_: *mut leanh::LeanObject,
    mut v_a_3463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3464_ = leanh::lean_ctor_get(v_inst_3458_, 0);
    leanh::lean_inc_ref(v_toApplicative_3464_);
    v_toBind_3465_ = leanh::lean_ctor_get(v_inst_3458_, 1);
    leanh::lean_inc_n(v_toBind_3465_, 2);
    leanh::lean_dec_ref(v_inst_3458_);
    v___f_3466_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3466_, 0, v_toApplicative_3464_);
    leanh::lean_closure_set(v___f_3466_, 1, v_y_3462_);
    leanh::lean_closure_set(v___f_3466_, 2, v_toBind_3465_);
    v___x_3467_ = leanh::lean_apply_1(v_x_3461_, v_a_3463_);
    v___x_3468_ = leanh::lean_apply_4(
        v_toBind_3465_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3467_,
        v___f_3466_,
    );
    return v___x_3468_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___boxed(
    mut v_00_u03b1_3469_: *mut leanh::LeanObject,
    mut v_00_u03b2_3470_: *mut leanh::LeanObject,
    mut v_m_3471_: *mut leanh::LeanObject,
    mut v_inst_3472_: *mut leanh::LeanObject,
    mut v_inst_3473_: *mut leanh::LeanObject,
    mut v_inst_3474_: *mut leanh::LeanObject,
    mut v_00_u03b1_3475_: *mut leanh::LeanObject,
    mut v_00_u03b2_3476_: *mut leanh::LeanObject,
    mut v_x_3477_: *mut leanh::LeanObject,
    mut v_y_3478_: *mut leanh::LeanObject,
    mut v_a_3479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3473_);
    leanh::lean_dec_ref(v_inst_3472_);
    return v_res_3480_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0(
    mut v_y_3481_: *mut leanh::LeanObject,
    mut v_____x_3482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_3483_ = leanh::lean_ctor_get(v_____x_3482_, 1);
    leanh::lean_inc(v_snd_3483_);
    leanh::lean_dec_ref(v_____x_3482_);
    v___x_3484_ = leanh::lean_box(0);
    v___x_3485_ = leanh::lean_apply_2(v_y_3481_, v___x_3484_, v_snd_3483_);
    return v___x_3485_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11___redArg(
    mut v_inst_3486_: *mut leanh::LeanObject,
    mut v_x_3487_: *mut leanh::LeanObject,
    mut v_y_3488_: *mut leanh::LeanObject,
    mut v_a_3489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_3490_ = leanh::lean_ctor_get(v_inst_3486_, 1);
    leanh::lean_inc(v_toBind_3490_);
    leanh::lean_dec_ref(v_inst_3486_);
    v___f_3491_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3491_, 0, v_y_3488_);
    v___x_3492_ = leanh::lean_apply_1(v_x_3487_, v_a_3489_);
    v___x_3493_ = leanh::lean_apply_4(
        v_toBind_3490_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3492_,
        v___f_3491_,
    );
    return v___x_3493_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11(
    mut v_00_u03b1_3494_: *mut leanh::LeanObject,
    mut v_00_u03b2_3495_: *mut leanh::LeanObject,
    mut v_m_3496_: *mut leanh::LeanObject,
    mut v_inst_3497_: *mut leanh::LeanObject,
    mut v_inst_3498_: *mut leanh::LeanObject,
    mut v_inst_3499_: *mut leanh::LeanObject,
    mut v_00_u03b1_3500_: *mut leanh::LeanObject,
    mut v_00_u03b2_3501_: *mut leanh::LeanObject,
    mut v_x_3502_: *mut leanh::LeanObject,
    mut v_y_3503_: *mut leanh::LeanObject,
    mut v_a_3504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_3505_ = leanh::lean_ctor_get(v_inst_3499_, 1);
    leanh::lean_inc(v_toBind_3505_);
    leanh::lean_dec_ref(v_inst_3499_);
    v___f_3506_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3506_, 0, v_y_3503_);
    v___x_3507_ = leanh::lean_apply_1(v_x_3502_, v_a_3504_);
    v___x_3508_ = leanh::lean_apply_4(
        v_toBind_3505_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3507_,
        v___f_3506_,
    );
    return v___x_3508_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11___boxed(
    mut v_00_u03b1_3509_: *mut leanh::LeanObject,
    mut v_00_u03b2_3510_: *mut leanh::LeanObject,
    mut v_m_3511_: *mut leanh::LeanObject,
    mut v_inst_3512_: *mut leanh::LeanObject,
    mut v_inst_3513_: *mut leanh::LeanObject,
    mut v_inst_3514_: *mut leanh::LeanObject,
    mut v_00_u03b1_3515_: *mut leanh::LeanObject,
    mut v_00_u03b2_3516_: *mut leanh::LeanObject,
    mut v_x_3517_: *mut leanh::LeanObject,
    mut v_y_3518_: *mut leanh::LeanObject,
    mut v_a_3519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3513_);
    leanh::lean_dec_ref(v_inst_3512_);
    return v_res_3520_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0(
    mut v_f_3521_: *mut leanh::LeanObject,
    mut v_____x_3522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_3523_ = leanh::lean_ctor_get(v_____x_3522_, 0);
    leanh::lean_inc(v_fst_3523_);
    v_snd_3524_ = leanh::lean_ctor_get(v_____x_3522_, 1);
    leanh::lean_inc(v_snd_3524_);
    leanh::lean_dec_ref(v_____x_3522_);
    v___x_3525_ = leanh::lean_apply_2(v_f_3521_, v_fst_3523_, v_snd_3524_);
    return v___x_3525_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13___redArg(
    mut v_inst_3526_: *mut leanh::LeanObject,
    mut v_x_3527_: *mut leanh::LeanObject,
    mut v_f_3528_: *mut leanh::LeanObject,
    mut v_a_3529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_3530_ = leanh::lean_ctor_get(v_inst_3526_, 1);
    leanh::lean_inc(v_toBind_3530_);
    leanh::lean_dec_ref(v_inst_3526_);
    v___f_3531_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3531_, 0, v_f_3528_);
    v___x_3532_ = leanh::lean_apply_1(v_x_3527_, v_a_3529_);
    v___x_3533_ = leanh::lean_apply_4(
        v_toBind_3530_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3532_,
        v___f_3531_,
    );
    return v___x_3533_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13(
    mut v_00_u03b1_3534_: *mut leanh::LeanObject,
    mut v_00_u03b2_3535_: *mut leanh::LeanObject,
    mut v_m_3536_: *mut leanh::LeanObject,
    mut v_inst_3537_: *mut leanh::LeanObject,
    mut v_inst_3538_: *mut leanh::LeanObject,
    mut v_inst_3539_: *mut leanh::LeanObject,
    mut v_00_u03b1_3540_: *mut leanh::LeanObject,
    mut v_00_u03b2_3541_: *mut leanh::LeanObject,
    mut v_x_3542_: *mut leanh::LeanObject,
    mut v_f_3543_: *mut leanh::LeanObject,
    mut v_a_3544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_3545_ = leanh::lean_ctor_get(v_inst_3539_, 1);
    leanh::lean_inc(v_toBind_3545_);
    leanh::lean_dec_ref(v_inst_3539_);
    v___f_3546_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3546_, 0, v_f_3543_);
    v___x_3547_ = leanh::lean_apply_1(v_x_3542_, v_a_3544_);
    v___x_3548_ = leanh::lean_apply_4(
        v_toBind_3545_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3547_,
        v___f_3546_,
    );
    return v___x_3548_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13___boxed(
    mut v_00_u03b1_3549_: *mut leanh::LeanObject,
    mut v_00_u03b2_3550_: *mut leanh::LeanObject,
    mut v_m_3551_: *mut leanh::LeanObject,
    mut v_inst_3552_: *mut leanh::LeanObject,
    mut v_inst_3553_: *mut leanh::LeanObject,
    mut v_inst_3554_: *mut leanh::LeanObject,
    mut v_00_u03b1_3555_: *mut leanh::LeanObject,
    mut v_00_u03b2_3556_: *mut leanh::LeanObject,
    mut v_x_3557_: *mut leanh::LeanObject,
    mut v_f_3558_: *mut leanh::LeanObject,
    mut v_a_3559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3553_);
    leanh::lean_dec_ref(v_inst_3552_);
    return v_res_3560_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___redArg(
    mut v_inst_3561_: *mut leanh::LeanObject,
    mut v_inst_3562_: *mut leanh::LeanObject,
    mut v_inst_3563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_3563_, 6);
    leanh::lean_inc_ref_n(v_inst_3562_, 6);
    leanh::lean_inc_ref_n(v_inst_3561_, 6);
    v___x_3564_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__1___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    leanh::lean_closure_set(v___x_3564_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3564_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3564_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3564_, 3, v_inst_3561_);
    leanh::lean_closure_set(v___x_3564_, 4, v_inst_3562_);
    leanh::lean_closure_set(v___x_3564_, 5, v_inst_3563_);
    v___x_3565_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__3___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    leanh::lean_closure_set(v___x_3565_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3565_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3565_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3565_, 3, v_inst_3561_);
    leanh::lean_closure_set(v___x_3565_, 4, v_inst_3562_);
    leanh::lean_closure_set(v___x_3565_, 5, v_inst_3563_);
    v___x_3566_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3566_, 0, v___x_3564_);
    leanh::lean_ctor_set(v___x_3566_, 1, v___x_3565_);
    v___x_3567_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__5___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    leanh::lean_closure_set(v___x_3567_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3567_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3567_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3567_, 3, v_inst_3561_);
    leanh::lean_closure_set(v___x_3567_, 4, v_inst_3562_);
    leanh::lean_closure_set(v___x_3567_, 5, v_inst_3563_);
    v___x_3568_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    leanh::lean_closure_set(v___x_3568_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3568_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3568_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3568_, 3, v_inst_3561_);
    leanh::lean_closure_set(v___x_3568_, 4, v_inst_3562_);
    leanh::lean_closure_set(v___x_3568_, 5, v_inst_3563_);
    v___x_3569_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    leanh::lean_closure_set(v___x_3569_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3569_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3569_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3569_, 3, v_inst_3561_);
    leanh::lean_closure_set(v___x_3569_, 4, v_inst_3562_);
    leanh::lean_closure_set(v___x_3569_, 5, v_inst_3563_);
    v___x_3570_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__11___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    leanh::lean_closure_set(v___x_3570_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3570_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3570_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3570_, 3, v_inst_3561_);
    leanh::lean_closure_set(v___x_3570_, 4, v_inst_3562_);
    leanh::lean_closure_set(v___x_3570_, 5, v_inst_3563_);
    v___x_3571_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3571_, 0, v___x_3566_);
    leanh::lean_ctor_set(v___x_3571_, 1, v___x_3567_);
    leanh::lean_ctor_set(v___x_3571_, 2, v___x_3568_);
    leanh::lean_ctor_set(v___x_3571_, 3, v___x_3569_);
    leanh::lean_ctor_set(v___x_3571_, 4, v___x_3570_);
    v___x_3572_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    leanh::lean_closure_set(v___x_3572_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3572_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3572_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3572_, 3, v_inst_3561_);
    leanh::lean_closure_set(v___x_3572_, 4, v_inst_3562_);
    leanh::lean_closure_set(v___x_3572_, 5, v_inst_3563_);
    v___x_3573_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3573_, 0, v___x_3571_);
    leanh::lean_ctor_set(v___x_3573_, 1, v___x_3572_);
    return v___x_3573_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad(
    mut v_00_u03b1_3574_: *mut leanh::LeanObject,
    mut v_00_u03b2_3575_: *mut leanh::LeanObject,
    mut v_m_3576_: *mut leanh::LeanObject,
    mut v_inst_3577_: *mut leanh::LeanObject,
    mut v_inst_3578_: *mut leanh::LeanObject,
    mut v_inst_3579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3580_ =
        l_Lean_MonadStateCacheT_instMonad___redArg(v_inst_3577_, v_inst_3578_, v_inst_3579_);
    return v___x_3580_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0(
    mut v_a_3581_: *mut leanh::LeanObject,
    mut v_toPure_3582_: *mut leanh::LeanObject,
    mut v_a_3583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3584_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3584_, 0, v_a_3583_);
    leanh::lean_ctor_set(v___x_3584_, 1, v_a_3581_);
    v___x_3585_ =
        leanh::lean_apply_2(v_toPure_3582_, leanh::lean_box(0), v___x_3584_);
    return v___x_3585_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg(
    mut v_inst_3586_: *mut leanh::LeanObject,
    mut v_t_3587_: *mut leanh::LeanObject,
    mut v_a_3588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3589_ = leanh::lean_ctor_get(v_inst_3586_, 0);
    leanh::lean_inc_ref(v_toApplicative_3589_);
    v_toBind_3590_ = leanh::lean_ctor_get(v_inst_3586_, 1);
    leanh::lean_inc(v_toBind_3590_);
    leanh::lean_dec_ref(v_inst_3586_);
    v_toPure_3591_ = leanh::lean_ctor_get(v_toApplicative_3589_, 1);
    leanh::lean_inc(v_toPure_3591_);
    leanh::lean_dec_ref(v_toApplicative_3589_);
    v___f_3592_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3592_, 0, v_a_3588_);
    leanh::lean_closure_set(v___f_3592_, 1, v_toPure_3591_);
    v___x_3593_ = leanh::lean_apply_4(
        v_toBind_3590_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_t_3587_,
        v___f_3592_,
    );
    return v___x_3593_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1(
    mut v_00_u03b1_3594_: *mut leanh::LeanObject,
    mut v_00_u03b2_3595_: *mut leanh::LeanObject,
    mut v_m_3596_: *mut leanh::LeanObject,
    mut v_inst_3597_: *mut leanh::LeanObject,
    mut v_inst_3598_: *mut leanh::LeanObject,
    mut v_inst_3599_: *mut leanh::LeanObject,
    mut v_00_u03b1_3600_: *mut leanh::LeanObject,
    mut v_t_3601_: *mut leanh::LeanObject,
    mut v_a_3602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3603_ = leanh::lean_ctor_get(v_inst_3599_, 0);
    leanh::lean_inc_ref(v_toApplicative_3603_);
    v_toBind_3604_ = leanh::lean_ctor_get(v_inst_3599_, 1);
    leanh::lean_inc(v_toBind_3604_);
    leanh::lean_dec_ref(v_inst_3599_);
    v_toPure_3605_ = leanh::lean_ctor_get(v_toApplicative_3603_, 1);
    leanh::lean_inc(v_toPure_3605_);
    leanh::lean_dec_ref(v_toApplicative_3603_);
    v___f_3606_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3606_, 0, v_a_3602_);
    leanh::lean_closure_set(v___f_3606_, 1, v_toPure_3605_);
    v___x_3607_ = leanh::lean_apply_4(
        v_toBind_3604_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_t_3601_,
        v___f_3606_,
    );
    return v___x_3607_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed(
    mut v_00_u03b1_3608_: *mut leanh::LeanObject,
    mut v_00_u03b2_3609_: *mut leanh::LeanObject,
    mut v_m_3610_: *mut leanh::LeanObject,
    mut v_inst_3611_: *mut leanh::LeanObject,
    mut v_inst_3612_: *mut leanh::LeanObject,
    mut v_inst_3613_: *mut leanh::LeanObject,
    mut v_00_u03b1_3614_: *mut leanh::LeanObject,
    mut v_t_3615_: *mut leanh::LeanObject,
    mut v_a_3616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3612_);
    leanh::lean_dec_ref(v_inst_3611_);
    return v_res_3617_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___redArg(
    mut v_inst_3618_: *mut leanh::LeanObject,
    mut v_inst_3619_: *mut leanh::LeanObject,
    mut v_inst_3620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3621_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    leanh::lean_closure_set(v___x_3621_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3621_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3621_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3621_, 3, v_inst_3618_);
    leanh::lean_closure_set(v___x_3621_, 4, v_inst_3619_);
    leanh::lean_closure_set(v___x_3621_, 5, v_inst_3620_);
    return v___x_3621_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift(
    mut v_00_u03b1_3622_: *mut leanh::LeanObject,
    mut v_00_u03b2_3623_: *mut leanh::LeanObject,
    mut v_m_3624_: *mut leanh::LeanObject,
    mut v_inst_3625_: *mut leanh::LeanObject,
    mut v_inst_3626_: *mut leanh::LeanObject,
    mut v_inst_3627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3628_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    leanh::lean_closure_set(v___x_3628_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3628_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3628_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3628_, 3, v_inst_3625_);
    leanh::lean_closure_set(v___x_3628_, 4, v_inst_3626_);
    leanh::lean_closure_set(v___x_3628_, 5, v_inst_3627_);
    return v___x_3628_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___redArg(
    mut v_inst_3629_: *mut leanh::LeanObject,
    mut v_inst_3630_: *mut leanh::LeanObject,
    mut v_a_3631_: *mut leanh::LeanObject,
    mut v_a_3632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_throw_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3633_ = leanh::lean_ctor_get(v_inst_3629_, 0);
    leanh::lean_inc_ref(v_toApplicative_3633_);
    v_throw_3634_ = leanh::lean_ctor_get(v_inst_3630_, 0);
    leanh::lean_inc(v_throw_3634_);
    leanh::lean_dec_ref(v_inst_3630_);
    v_toBind_3635_ = leanh::lean_ctor_get(v_inst_3629_, 1);
    leanh::lean_inc(v_toBind_3635_);
    leanh::lean_dec_ref(v_inst_3629_);
    v_toPure_3636_ = leanh::lean_ctor_get(v_toApplicative_3633_, 1);
    leanh::lean_inc(v_toPure_3636_);
    leanh::lean_dec_ref(v_toApplicative_3633_);
    v___x_3637_ = leanh::lean_apply_2(v_throw_3634_, leanh::lean_box(0), v_a_3631_);
    v___f_3638_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3638_, 0, v_a_3632_);
    leanh::lean_closure_set(v___f_3638_, 1, v_toPure_3636_);
    v___x_3639_ = leanh::lean_apply_4(
        v_toBind_3635_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3637_,
        v___f_3638_,
    );
    return v___x_3639_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1(
    mut v_00_u03b1_3640_: *mut leanh::LeanObject,
    mut v_00_u03b2_3641_: *mut leanh::LeanObject,
    mut v_m_3642_: *mut leanh::LeanObject,
    mut v_inst_3643_: *mut leanh::LeanObject,
    mut v_inst_3644_: *mut leanh::LeanObject,
    mut v_inst_3645_: *mut leanh::LeanObject,
    mut v_00_u03b5_3646_: *mut leanh::LeanObject,
    mut v_inst_3647_: *mut leanh::LeanObject,
    mut v_00_u03b1_3648_: *mut leanh::LeanObject,
    mut v_a_3649_: *mut leanh::LeanObject,
    mut v_a_3650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_throw_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3651_ = leanh::lean_ctor_get(v_inst_3645_, 0);
    leanh::lean_inc_ref(v_toApplicative_3651_);
    v_throw_3652_ = leanh::lean_ctor_get(v_inst_3647_, 0);
    leanh::lean_inc(v_throw_3652_);
    leanh::lean_dec_ref(v_inst_3647_);
    v_toBind_3653_ = leanh::lean_ctor_get(v_inst_3645_, 1);
    leanh::lean_inc(v_toBind_3653_);
    leanh::lean_dec_ref(v_inst_3645_);
    v_toPure_3654_ = leanh::lean_ctor_get(v_toApplicative_3651_, 1);
    leanh::lean_inc(v_toPure_3654_);
    leanh::lean_dec_ref(v_toApplicative_3651_);
    v___x_3655_ = leanh::lean_apply_2(v_throw_3652_, leanh::lean_box(0), v_a_3649_);
    v___f_3656_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3656_, 0, v_a_3650_);
    leanh::lean_closure_set(v___f_3656_, 1, v_toPure_3654_);
    v___x_3657_ = leanh::lean_apply_4(
        v_toBind_3653_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3655_,
        v___f_3656_,
    );
    return v___x_3657_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed(
    mut v_00_u03b1_3658_: *mut leanh::LeanObject,
    mut v_00_u03b2_3659_: *mut leanh::LeanObject,
    mut v_m_3660_: *mut leanh::LeanObject,
    mut v_inst_3661_: *mut leanh::LeanObject,
    mut v_inst_3662_: *mut leanh::LeanObject,
    mut v_inst_3663_: *mut leanh::LeanObject,
    mut v_00_u03b5_3664_: *mut leanh::LeanObject,
    mut v_inst_3665_: *mut leanh::LeanObject,
    mut v_00_u03b1_3666_: *mut leanh::LeanObject,
    mut v_a_3667_: *mut leanh::LeanObject,
    mut v_a_3668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3662_);
    leanh::lean_dec_ref(v_inst_3661_);
    return v_res_3669_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0(
    mut v_c_3670_: *mut leanh::LeanObject,
    mut v_s_3671_: *mut leanh::LeanObject,
    mut v_e_3672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3673_ = leanh::lean_apply_2(v_c_3670_, v_e_3672_, v_s_3671_);
    return v___x_3673_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg(
    mut v_inst_3674_: *mut leanh::LeanObject,
    mut v_x_3675_: *mut leanh::LeanObject,
    mut v_c_3676_: *mut leanh::LeanObject,
    mut v_s_3677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_3678_ = leanh::lean_ctor_get(v_inst_3674_, 1);
    leanh::lean_inc(v_tryCatch_3678_);
    leanh::lean_dec_ref(v_inst_3674_);
    leanh::lean_inc_ref(v_s_3677_);
    v___f_3679_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3679_, 0, v_c_3676_);
    leanh::lean_closure_set(v___f_3679_, 1, v_s_3677_);
    v___x_3680_ = leanh::lean_apply_1(v_x_3675_, v_s_3677_);
    v___x_3681_ = leanh::lean_apply_3(
        v_tryCatch_3678_,
        leanh::lean_box(0),
        v___x_3680_,
        v___f_3679_,
    );
    return v___x_3681_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3(
    mut v_00_u03b1_3682_: *mut leanh::LeanObject,
    mut v_00_u03b2_3683_: *mut leanh::LeanObject,
    mut v_m_3684_: *mut leanh::LeanObject,
    mut v_inst_3685_: *mut leanh::LeanObject,
    mut v_inst_3686_: *mut leanh::LeanObject,
    mut v_00_u03b5_3687_: *mut leanh::LeanObject,
    mut v_inst_3688_: *mut leanh::LeanObject,
    mut v_00_u03b1_3689_: *mut leanh::LeanObject,
    mut v_x_3690_: *mut leanh::LeanObject,
    mut v_c_3691_: *mut leanh::LeanObject,
    mut v_s_3692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_3693_ = leanh::lean_ctor_get(v_inst_3688_, 1);
    leanh::lean_inc(v_tryCatch_3693_);
    leanh::lean_dec_ref(v_inst_3688_);
    leanh::lean_inc_ref(v_s_3692_);
    v___f_3694_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3694_, 0, v_c_3691_);
    leanh::lean_closure_set(v___f_3694_, 1, v_s_3692_);
    v___x_3695_ = leanh::lean_apply_1(v_x_3690_, v_s_3692_);
    v___x_3696_ = leanh::lean_apply_3(
        v_tryCatch_3693_,
        leanh::lean_box(0),
        v___x_3695_,
        v___f_3694_,
    );
    return v___x_3696_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed(
    mut v_00_u03b1_3697_: *mut leanh::LeanObject,
    mut v_00_u03b2_3698_: *mut leanh::LeanObject,
    mut v_m_3699_: *mut leanh::LeanObject,
    mut v_inst_3700_: *mut leanh::LeanObject,
    mut v_inst_3701_: *mut leanh::LeanObject,
    mut v_00_u03b5_3702_: *mut leanh::LeanObject,
    mut v_inst_3703_: *mut leanh::LeanObject,
    mut v_00_u03b1_3704_: *mut leanh::LeanObject,
    mut v_x_3705_: *mut leanh::LeanObject,
    mut v_c_3706_: *mut leanh::LeanObject,
    mut v_s_3707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3701_);
    leanh::lean_dec_ref(v_inst_3700_);
    return v_res_3708_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(
    mut v_inst_3709_: *mut leanh::LeanObject,
    mut v_inst_3710_: *mut leanh::LeanObject,
    mut v_inst_3711_: *mut leanh::LeanObject,
    mut v_inst_3712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_3712_);
    leanh::lean_inc_ref(v_inst_3710_);
    leanh::lean_inc_ref(v_inst_3709_);
    v___x_3713_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed as *mut core::ffi::c_void,
        11,
        8,
    );
    leanh::lean_closure_set(v___x_3713_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3713_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3713_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3713_, 3, v_inst_3709_);
    leanh::lean_closure_set(v___x_3713_, 4, v_inst_3710_);
    leanh::lean_closure_set(v___x_3713_, 5, v_inst_3711_);
    leanh::lean_closure_set(v___x_3713_, 6, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3713_, 7, v_inst_3712_);
    v___x_3714_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed as *mut core::ffi::c_void,
        11,
        7,
    );
    leanh::lean_closure_set(v___x_3714_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3714_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3714_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3714_, 3, v_inst_3709_);
    leanh::lean_closure_set(v___x_3714_, 4, v_inst_3710_);
    leanh::lean_closure_set(v___x_3714_, 5, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3714_, 6, v_inst_3712_);
    v___x_3715_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3715_, 0, v___x_3713_);
    leanh::lean_ctor_set(v___x_3715_, 1, v___x_3714_);
    return v___x_3715_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf(
    mut v_00_u03b1_3716_: *mut leanh::LeanObject,
    mut v_00_u03b2_3717_: *mut leanh::LeanObject,
    mut v_m_3718_: *mut leanh::LeanObject,
    mut v_inst_3719_: *mut leanh::LeanObject,
    mut v_inst_3720_: *mut leanh::LeanObject,
    mut v_inst_3721_: *mut leanh::LeanObject,
    mut v_00_u03b5_3722_: *mut leanh::LeanObject,
    mut v_inst_3723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3724_ = l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(
        v_inst_3719_,
        v_inst_3720_,
        v_inst_3721_,
        v_inst_3723_,
    );
    return v___x_3724_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0(
    mut v_fst_3725_: *mut leanh::LeanObject,
    mut v_00_u03b2_3726_: *mut leanh::LeanObject,
    mut v_x_3727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3728_ = leanh::lean_apply_1(v_x_3727_, v_fst_3725_);
    return v___x_3728_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1(
    mut v_snd_3729_: *mut leanh::LeanObject,
    mut v_toPure_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3732_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3732_, 0, v_a_3731_);
    leanh::lean_ctor_set(v___x_3732_, 1, v_snd_3729_);
    v___x_3733_ =
        leanh::lean_apply_2(v_toPure_3730_, leanh::lean_box(0), v___x_3732_);
    return v___x_3733_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2(
    mut v_f_3734_: *mut leanh::LeanObject,
    mut v_toPure_3735_: *mut leanh::LeanObject,
    mut v_toBind_3736_: *mut leanh::LeanObject,
    mut v_____x_3737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_3738_ = leanh::lean_ctor_get(v_____x_3737_, 0);
    leanh::lean_inc(v_fst_3738_);
    v_snd_3739_ = leanh::lean_ctor_get(v_____x_3737_, 1);
    leanh::lean_inc(v_snd_3739_);
    leanh::lean_dec_ref(v_____x_3737_);
    v___f_3740_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3740_, 0, v_fst_3738_);
    v___x_3741_ = leanh::lean_apply_1(v_f_3734_, v___f_3740_);
    v___f_3742_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3742_, 0, v_snd_3739_);
    leanh::lean_closure_set(v___f_3742_, 1, v_toPure_3735_);
    v___x_3743_ = leanh::lean_apply_4(
        v_toBind_3736_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3741_,
        v___f_3742_,
    );
    return v___x_3743_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg(
    mut v_inst_3744_: *mut leanh::LeanObject,
    mut v_f_3745_: *mut leanh::LeanObject,
    mut v_a_3746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3751_: u8 = 0;
    let mut v_toPure_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3747_ = leanh::lean_ctor_get(v_inst_3744_, 0);
                v_toBind_3748_ = leanh::lean_ctor_get(v_inst_3744_, 1);
                v_isSharedCheck_3759_ = (!leanh::lean_is_exclusive(v_inst_3744_)) as u8;
                if v_isSharedCheck_3759_ == 0 {
                    v___x_3750_ = v_inst_3744_;
                    v_isShared_3751_ = v_isSharedCheck_3759_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_3748_);
                    leanh::lean_inc(v_toApplicative_3747_);
                    leanh::lean_dec(v_inst_3744_);
                    v___x_3750_ = leanh::lean_box(0);
                    v_isShared_3751_ = v_isSharedCheck_3759_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3752_ = leanh::lean_ctor_get(v_toApplicative_3747_, 1);
                leanh::lean_inc_n(v_toPure_3752_, 2);
                leanh::lean_dec_ref(v_toApplicative_3747_);
                leanh::lean_inc(v_toBind_3748_);
                v___f_3753_ = leanh::lean_alloc_closure(
                    l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_3753_, 0, v_f_3745_);
                leanh::lean_closure_set(v___f_3753_, 1, v_toPure_3752_);
                leanh::lean_closure_set(v___f_3753_, 2, v_toBind_3748_);
                leanh::lean_inc_ref(v_a_3746_);
                if v_isShared_3751_ == 0 {
                    leanh::lean_ctor_set(v___x_3750_, 1, v_a_3746_);
                    leanh::lean_ctor_set(v___x_3750_, 0, v_a_3746_);
                    v___x_3755_ = v___x_3750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3758_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_a_3746_);
                    v___x_3755_ = v_reuseFailAlloc_3758_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3756_ = leanh::lean_apply_2(
                    v_toPure_3752_,
                    leanh::lean_box(0),
                    v___x_3755_,
                );
                v___x_3757_ = leanh::lean_apply_4(
                    v_toBind_3748_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_00_u03b1_3760_: *mut leanh::LeanObject,
    mut v_00_u03b2_3761_: *mut leanh::LeanObject,
    mut v_m_3762_: *mut leanh::LeanObject,
    mut v_inst_3763_: *mut leanh::LeanObject,
    mut v_inst_3764_: *mut leanh::LeanObject,
    mut v_inst_3765_: *mut leanh::LeanObject,
    mut v_00_u03b1_3766_: *mut leanh::LeanObject,
    mut v_f_3767_: *mut leanh::LeanObject,
    mut v_a_3768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3773_: u8 = 0;
    let mut v_toPure_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3769_ = leanh::lean_ctor_get(v_inst_3765_, 0);
                v_toBind_3770_ = leanh::lean_ctor_get(v_inst_3765_, 1);
                v_isSharedCheck_3781_ = (!leanh::lean_is_exclusive(v_inst_3765_)) as u8;
                if v_isSharedCheck_3781_ == 0 {
                    v___x_3772_ = v_inst_3765_;
                    v_isShared_3773_ = v_isSharedCheck_3781_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_3770_);
                    leanh::lean_inc(v_toApplicative_3769_);
                    leanh::lean_dec(v_inst_3765_);
                    v___x_3772_ = leanh::lean_box(0);
                    v_isShared_3773_ = v_isSharedCheck_3781_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3774_ = leanh::lean_ctor_get(v_toApplicative_3769_, 1);
                leanh::lean_inc_n(v_toPure_3774_, 2);
                leanh::lean_dec_ref(v_toApplicative_3769_);
                leanh::lean_inc(v_toBind_3770_);
                v___f_3775_ = leanh::lean_alloc_closure(
                    l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_3775_, 0, v_f_3767_);
                leanh::lean_closure_set(v___f_3775_, 1, v_toPure_3774_);
                leanh::lean_closure_set(v___f_3775_, 2, v_toBind_3770_);
                leanh::lean_inc_ref(v_a_3768_);
                if v_isShared_3773_ == 0 {
                    leanh::lean_ctor_set(v___x_3772_, 1, v_a_3768_);
                    leanh::lean_ctor_set(v___x_3772_, 0, v_a_3768_);
                    v___x_3777_ = v___x_3772_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3768_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_a_3768_);
                    v___x_3777_ = v_reuseFailAlloc_3780_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3778_ = leanh::lean_apply_2(
                    v_toPure_3774_,
                    leanh::lean_box(0),
                    v___x_3777_,
                );
                v___x_3779_ = leanh::lean_apply_4(
                    v_toBind_3770_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_00_u03b1_3782_: *mut leanh::LeanObject,
    mut v_00_u03b2_3783_: *mut leanh::LeanObject,
    mut v_m_3784_: *mut leanh::LeanObject,
    mut v_inst_3785_: *mut leanh::LeanObject,
    mut v_inst_3786_: *mut leanh::LeanObject,
    mut v_inst_3787_: *mut leanh::LeanObject,
    mut v_00_u03b1_3788_: *mut leanh::LeanObject,
    mut v_f_3789_: *mut leanh::LeanObject,
    mut v_a_3790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3786_);
    leanh::lean_dec_ref(v_inst_3785_);
    return v_res_3791_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0(
    mut v_fst_3792_: *mut leanh::LeanObject,
    mut v_toPure_3793_: *mut leanh::LeanObject,
    mut v_____x_3794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3798_: u8 = 0;
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_unused_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3795_ = leanh::lean_ctor_get(v_____x_3794_, 1);
                v_isSharedCheck_3803_ = (!leanh::lean_is_exclusive(v_____x_3794_)) as u8;
                if v_isSharedCheck_3803_ == 0 {
                    v_unused_3804_ = leanh::lean_ctor_get(v_____x_3794_, 0);
                    leanh::lean_dec(v_unused_3804_);
                    v___x_3797_ = v_____x_3794_;
                    v_isShared_3798_ = v_isSharedCheck_3803_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3795_);
                    leanh::lean_dec(v_____x_3794_);
                    v___x_3797_ = leanh::lean_box(0);
                    v_isShared_3798_ = v_isSharedCheck_3803_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3798_ == 0 {
                    leanh::lean_ctor_set(v___x_3797_, 0, v_fst_3792_);
                    v___x_3800_ = v___x_3797_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3802_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_fst_3792_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_snd_3795_);
                    v___x_3800_ = v_reuseFailAlloc_3802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3801_ = leanh::lean_apply_2(
                    v_toPure_3793_,
                    leanh::lean_box(0),
                    v___x_3800_,
                );
                return v___x_3801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1(
    mut v_toPure_3805_: *mut leanh::LeanObject,
    mut v_toBind_3806_: *mut leanh::LeanObject,
    mut v_____x_3807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3813_: u8 = 0;
    let mut v___f_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3808_ = leanh::lean_ctor_get(v_____x_3807_, 0);
                leanh::lean_inc(v_fst_3808_);
                leanh::lean_dec_ref(v_____x_3807_);
                v_fst_3809_ = leanh::lean_ctor_get(v_fst_3808_, 0);
                v_snd_3810_ = leanh::lean_ctor_get(v_fst_3808_, 1);
                v_isSharedCheck_3821_ = (!leanh::lean_is_exclusive(v_fst_3808_)) as u8;
                if v_isSharedCheck_3821_ == 0 {
                    v___x_3812_ = v_fst_3808_;
                    v_isShared_3813_ = v_isSharedCheck_3821_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3810_);
                    leanh::lean_inc(v_fst_3809_);
                    leanh::lean_dec(v_fst_3808_);
                    v___x_3812_ = leanh::lean_box(0);
                    v_isShared_3813_ = v_isSharedCheck_3821_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_toPure_3805_);
                v___f_3814_ = leanh::lean_alloc_closure(
                    l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_3814_, 0, v_fst_3809_);
                leanh::lean_closure_set(v___f_3814_, 1, v_toPure_3805_);
                v___x_3815_ = leanh::lean_box(0);
                if v_isShared_3813_ == 0 {
                    leanh::lean_ctor_set(v___x_3812_, 0, v___x_3815_);
                    v___x_3817_ = v___x_3812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_snd_3810_);
                    v___x_3817_ = v_reuseFailAlloc_3820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3818_ = leanh::lean_apply_2(
                    v_toPure_3805_,
                    leanh::lean_box(0),
                    v___x_3817_,
                );
                v___x_3819_ = leanh::lean_apply_4(
                    v_toBind_3806_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_a_3822_: *mut leanh::LeanObject,
    mut v_toPure_3823_: *mut leanh::LeanObject,
    mut v_a_3824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3825_, 0, v_a_3824_);
    leanh::lean_ctor_set(v___x_3825_, 1, v_a_3822_);
    v___x_3826_ =
        leanh::lean_apply_2(v_toPure_3823_, leanh::lean_box(0), v___x_3825_);
    return v___x_3826_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg(
    mut v_inst_3827_: *mut leanh::LeanObject,
    mut v_x_3828_: *mut leanh::LeanObject,
    mut v_a_3829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3830_ = leanh::lean_ctor_get(v_inst_3827_, 0);
    leanh::lean_inc_ref(v_toApplicative_3830_);
    v_toBind_3831_ = leanh::lean_ctor_get(v_inst_3827_, 1);
    leanh::lean_inc_n(v_toBind_3831_, 3);
    leanh::lean_dec_ref(v_inst_3827_);
    v_toPure_3832_ = leanh::lean_ctor_get(v_toApplicative_3830_, 1);
    leanh::lean_inc_n(v_toPure_3832_, 2);
    leanh::lean_dec_ref(v_toApplicative_3830_);
    v___f_3833_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3833_, 0, v_toPure_3832_);
    leanh::lean_closure_set(v___f_3833_, 1, v_toBind_3831_);
    v___f_3834_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3834_, 0, v_a_3829_);
    leanh::lean_closure_set(v___f_3834_, 1, v_toPure_3832_);
    v___x_3835_ = leanh::lean_apply_4(
        v_toBind_3831_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_3828_,
        v___f_3834_,
    );
    v___x_3836_ = leanh::lean_apply_4(
        v_toBind_3831_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3835_,
        v___f_3833_,
    );
    return v___x_3836_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3(
    mut v_00_u03b1_3837_: *mut leanh::LeanObject,
    mut v_00_u03b2_3838_: *mut leanh::LeanObject,
    mut v_m_3839_: *mut leanh::LeanObject,
    mut v_inst_3840_: *mut leanh::LeanObject,
    mut v_inst_3841_: *mut leanh::LeanObject,
    mut v_inst_3842_: *mut leanh::LeanObject,
    mut v_00_u03b1_3843_: *mut leanh::LeanObject,
    mut v_x_3844_: *mut leanh::LeanObject,
    mut v_a_3845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3846_ = leanh::lean_ctor_get(v_inst_3842_, 0);
    leanh::lean_inc_ref(v_toApplicative_3846_);
    v_toBind_3847_ = leanh::lean_ctor_get(v_inst_3842_, 1);
    leanh::lean_inc_n(v_toBind_3847_, 3);
    leanh::lean_dec_ref(v_inst_3842_);
    v_toPure_3848_ = leanh::lean_ctor_get(v_toApplicative_3846_, 1);
    leanh::lean_inc_n(v_toPure_3848_, 2);
    leanh::lean_dec_ref(v_toApplicative_3846_);
    v___f_3849_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3849_, 0, v_toPure_3848_);
    leanh::lean_closure_set(v___f_3849_, 1, v_toBind_3847_);
    v___f_3850_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3850_, 0, v_a_3845_);
    leanh::lean_closure_set(v___f_3850_, 1, v_toPure_3848_);
    v___x_3851_ = leanh::lean_apply_4(
        v_toBind_3847_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_3844_,
        v___f_3850_,
    );
    v___x_3852_ = leanh::lean_apply_4(
        v_toBind_3847_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3851_,
        v___f_3849_,
    );
    return v___x_3852_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed(
    mut v_00_u03b1_3853_: *mut leanh::LeanObject,
    mut v_00_u03b2_3854_: *mut leanh::LeanObject,
    mut v_m_3855_: *mut leanh::LeanObject,
    mut v_inst_3856_: *mut leanh::LeanObject,
    mut v_inst_3857_: *mut leanh::LeanObject,
    mut v_inst_3858_: *mut leanh::LeanObject,
    mut v_00_u03b1_3859_: *mut leanh::LeanObject,
    mut v_x_3860_: *mut leanh::LeanObject,
    mut v_a_3861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3857_);
    leanh::lean_dec_ref(v_inst_3856_);
    return v_res_3862_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___redArg(
    mut v_inst_3863_: *mut leanh::LeanObject,
    mut v_inst_3864_: *mut leanh::LeanObject,
    mut v_inst_3865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_3865_);
    leanh::lean_inc_ref(v_inst_3864_);
    leanh::lean_inc_ref(v_inst_3863_);
    v___x_3866_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__1___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    leanh::lean_closure_set(v___x_3866_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3866_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3866_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3866_, 3, v_inst_3863_);
    leanh::lean_closure_set(v___x_3866_, 4, v_inst_3864_);
    leanh::lean_closure_set(v___x_3866_, 5, v_inst_3865_);
    v___x_3867_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    leanh::lean_closure_set(v___x_3867_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3867_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3867_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3867_, 3, v_inst_3863_);
    leanh::lean_closure_set(v___x_3867_, 4, v_inst_3864_);
    leanh::lean_closure_set(v___x_3867_, 5, v_inst_3865_);
    v___x_3868_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3868_, 0, v___x_3866_);
    leanh::lean_ctor_set(v___x_3868_, 1, v___x_3867_);
    return v___x_3868_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl(
    mut v_00_u03b1_3869_: *mut leanh::LeanObject,
    mut v_00_u03b2_3870_: *mut leanh::LeanObject,
    mut v_m_3871_: *mut leanh::LeanObject,
    mut v_inst_3872_: *mut leanh::LeanObject,
    mut v_inst_3873_: *mut leanh::LeanObject,
    mut v_inst_3874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3875_ =
        l_Lean_MonadStateCacheT_instMonadControl___redArg(v_inst_3872_, v_inst_3873_, v_inst_3874_);
    return v___x_3875_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0(
    mut v_h_3876_: *mut leanh::LeanObject,
    mut v_s_3877_: *mut leanh::LeanObject,
    mut v_x_3878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3884_: u8 = 0;
    let mut v_fst_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3878_) == 0 {
                    v___x_3879_ = leanh::lean_box(0);
                    v___x_3880_ = leanh::lean_apply_2(v_h_3876_, v___x_3879_, v_s_3877_);
                    return v___x_3880_;
                } else {
                    leanh::lean_dec_ref(v_s_3877_);
                    v_val_3881_ = leanh::lean_ctor_get(v_x_3878_, 0);
                    v_isSharedCheck_3891_ = (!leanh::lean_is_exclusive(v_x_3878_)) as u8;
                    if v_isSharedCheck_3891_ == 0 {
                        v___x_3883_ = v_x_3878_;
                        v_isShared_3884_ = v_isSharedCheck_3891_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3881_);
                        leanh::lean_dec(v_x_3878_);
                        v___x_3883_ = leanh::lean_box(0);
                        v_isShared_3884_ = v_isSharedCheck_3891_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3885_ = leanh::lean_ctor_get(v_val_3881_, 0);
                leanh::lean_inc(v_fst_3885_);
                v_snd_3886_ = leanh::lean_ctor_get(v_val_3881_, 1);
                leanh::lean_inc(v_snd_3886_);
                leanh::lean_dec(v_val_3881_);
                if v_isShared_3884_ == 0 {
                    leanh::lean_ctor_set(v___x_3883_, 0, v_fst_3885_);
                    v___x_3888_ = v___x_3883_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3890_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_fst_3885_);
                    v___x_3888_ = v_reuseFailAlloc_3890_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3889_ = leanh::lean_apply_2(v_h_3876_, v___x_3888_, v_snd_3886_);
                return v___x_3889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1(
    mut v_toPure_3892_: *mut leanh::LeanObject,
    mut v_____x_3893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v_fst_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3904_: u8 = 0;
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3912_: u8 = 0;
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_unused_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3894_ = leanh::lean_ctor_get(v_____x_3893_, 0);
                leanh::lean_inc(v_fst_3894_);
                v_snd_3895_ = leanh::lean_ctor_get(v_____x_3893_, 1);
                leanh::lean_inc(v_snd_3895_);
                leanh::lean_dec_ref(v_____x_3893_);
                v_fst_3896_ = leanh::lean_ctor_get(v_fst_3894_, 0);
                v_isSharedCheck_3913_ = (!leanh::lean_is_exclusive(v_fst_3894_)) as u8;
                if v_isSharedCheck_3913_ == 0 {
                    v_unused_3914_ = leanh::lean_ctor_get(v_fst_3894_, 1);
                    leanh::lean_dec(v_unused_3914_);
                    v___x_3898_ = v_fst_3894_;
                    v_isShared_3899_ = v_isSharedCheck_3913_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_3896_);
                    leanh::lean_dec(v_fst_3894_);
                    v___x_3898_ = leanh::lean_box(0);
                    v_isShared_3899_ = v_isSharedCheck_3913_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3900_ = leanh::lean_ctor_get(v_snd_3895_, 0);
                v_snd_3901_ = leanh::lean_ctor_get(v_snd_3895_, 1);
                v_isSharedCheck_3912_ = (!leanh::lean_is_exclusive(v_snd_3895_)) as u8;
                if v_isSharedCheck_3912_ == 0 {
                    v___x_3903_ = v_snd_3895_;
                    v_isShared_3904_ = v_isSharedCheck_3912_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3901_);
                    leanh::lean_inc(v_fst_3900_);
                    leanh::lean_dec(v_snd_3895_);
                    v___x_3903_ = leanh::lean_box(0);
                    v_isShared_3904_ = v_isSharedCheck_3912_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3904_ == 0 {
                    leanh::lean_ctor_set(v___x_3903_, 1, v_fst_3900_);
                    leanh::lean_ctor_set(v___x_3903_, 0, v_fst_3896_);
                    v___x_3906_ = v___x_3903_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3911_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_fst_3896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_fst_3900_);
                    v___x_3906_ = v_reuseFailAlloc_3911_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3899_ == 0 {
                    leanh::lean_ctor_set(v___x_3898_, 1, v_snd_3901_);
                    leanh::lean_ctor_set(v___x_3898_, 0, v___x_3906_);
                    v___x_3908_ = v___x_3898_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3910_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3910_, 1, v_snd_3901_);
                    v___x_3908_ = v_reuseFailAlloc_3910_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3909_ = leanh::lean_apply_2(
                    v_toPure_3892_,
                    leanh::lean_box(0),
                    v___x_3908_,
                );
                return v___x_3909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg(
    mut v_inst_3915_: *mut leanh::LeanObject,
    mut v_inst_3916_: *mut leanh::LeanObject,
    mut v_x_3917_: *mut leanh::LeanObject,
    mut v_h_3918_: *mut leanh::LeanObject,
    mut v_s_3919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3920_ = leanh::lean_ctor_get(v_inst_3915_, 0);
    leanh::lean_inc_ref(v_toApplicative_3920_);
    v_toBind_3921_ = leanh::lean_ctor_get(v_inst_3915_, 1);
    leanh::lean_inc(v_toBind_3921_);
    leanh::lean_dec_ref(v_inst_3915_);
    v_toPure_3922_ = leanh::lean_ctor_get(v_toApplicative_3920_, 1);
    leanh::lean_inc(v_toPure_3922_);
    leanh::lean_dec_ref(v_toApplicative_3920_);
    leanh::lean_inc_ref(v_s_3919_);
    v___f_3923_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3923_, 0, v_h_3918_);
    leanh::lean_closure_set(v___f_3923_, 1, v_s_3919_);
    v___x_3924_ = leanh::lean_apply_1(v_x_3917_, v_s_3919_);
    v___f_3925_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3925_, 0, v_toPure_3922_);
    v___x_3926_ = leanh::lean_apply_4(
        v_inst_3916_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3924_,
        v___f_3923_,
    );
    v___x_3927_ = leanh::lean_apply_4(
        v_toBind_3921_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3926_,
        v___f_3925_,
    );
    return v___x_3927_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1(
    mut v_00_u03b1_3928_: *mut leanh::LeanObject,
    mut v_00_u03b2_3929_: *mut leanh::LeanObject,
    mut v_m_3930_: *mut leanh::LeanObject,
    mut v_inst_3931_: *mut leanh::LeanObject,
    mut v_inst_3932_: *mut leanh::LeanObject,
    mut v_inst_3933_: *mut leanh::LeanObject,
    mut v_inst_3934_: *mut leanh::LeanObject,
    mut v_00_u03b1_3935_: *mut leanh::LeanObject,
    mut v_00_u03b2_3936_: *mut leanh::LeanObject,
    mut v_x_3937_: *mut leanh::LeanObject,
    mut v_h_3938_: *mut leanh::LeanObject,
    mut v_s_3939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3940_ = leanh::lean_ctor_get(v_inst_3933_, 0);
    leanh::lean_inc_ref(v_toApplicative_3940_);
    v_toBind_3941_ = leanh::lean_ctor_get(v_inst_3933_, 1);
    leanh::lean_inc(v_toBind_3941_);
    leanh::lean_dec_ref(v_inst_3933_);
    v_toPure_3942_ = leanh::lean_ctor_get(v_toApplicative_3940_, 1);
    leanh::lean_inc(v_toPure_3942_);
    leanh::lean_dec_ref(v_toApplicative_3940_);
    leanh::lean_inc_ref(v_s_3939_);
    v___f_3943_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3943_, 0, v_h_3938_);
    leanh::lean_closure_set(v___f_3943_, 1, v_s_3939_);
    v___x_3944_ = leanh::lean_apply_1(v_x_3937_, v_s_3939_);
    v___f_3945_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3945_, 0, v_toPure_3942_);
    v___x_3946_ = leanh::lean_apply_4(
        v_inst_3934_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3944_,
        v___f_3943_,
    );
    v___x_3947_ = leanh::lean_apply_4(
        v_toBind_3941_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3946_,
        v___f_3945_,
    );
    return v___x_3947_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed(
    mut v_00_u03b1_3948_: *mut leanh::LeanObject,
    mut v_00_u03b2_3949_: *mut leanh::LeanObject,
    mut v_m_3950_: *mut leanh::LeanObject,
    mut v_inst_3951_: *mut leanh::LeanObject,
    mut v_inst_3952_: *mut leanh::LeanObject,
    mut v_inst_3953_: *mut leanh::LeanObject,
    mut v_inst_3954_: *mut leanh::LeanObject,
    mut v_00_u03b1_3955_: *mut leanh::LeanObject,
    mut v_00_u03b2_3956_: *mut leanh::LeanObject,
    mut v_x_3957_: *mut leanh::LeanObject,
    mut v_h_3958_: *mut leanh::LeanObject,
    mut v_s_3959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_3952_);
    leanh::lean_dec_ref(v_inst_3951_);
    return v_res_3960_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___redArg(
    mut v_inst_3961_: *mut leanh::LeanObject,
    mut v_inst_3962_: *mut leanh::LeanObject,
    mut v_inst_3963_: *mut leanh::LeanObject,
    mut v_inst_3964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3965_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    leanh::lean_closure_set(v___x_3965_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3965_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3965_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3965_, 3, v_inst_3961_);
    leanh::lean_closure_set(v___x_3965_, 4, v_inst_3962_);
    leanh::lean_closure_set(v___x_3965_, 5, v_inst_3963_);
    leanh::lean_closure_set(v___x_3965_, 6, v_inst_3964_);
    return v___x_3965_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally(
    mut v_00_u03b1_3966_: *mut leanh::LeanObject,
    mut v_00_u03b2_3967_: *mut leanh::LeanObject,
    mut v_m_3968_: *mut leanh::LeanObject,
    mut v_inst_3969_: *mut leanh::LeanObject,
    mut v_inst_3970_: *mut leanh::LeanObject,
    mut v_inst_3971_: *mut leanh::LeanObject,
    mut v_inst_3972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3973_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    leanh::lean_closure_set(v___x_3973_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3973_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3973_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3973_, 3, v_inst_3969_);
    leanh::lean_closure_set(v___x_3973_, 4, v_inst_3970_);
    leanh::lean_closure_set(v___x_3973_, 5, v_inst_3971_);
    leanh::lean_closure_set(v___x_3973_, 6, v_inst_3972_);
    return v___x_3973_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0(
    mut v_a_3974_: *mut leanh::LeanObject,
    mut v_toPure_3975_: *mut leanh::LeanObject,
    mut v_a_3976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3977_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3977_, 0, v_a_3976_);
    leanh::lean_ctor_set(v___x_3977_, 1, v_a_3974_);
    v___x_3978_ =
        leanh::lean_apply_2(v_toPure_3975_, leanh::lean_box(0), v___x_3977_);
    return v___x_3978_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg(
    mut v_inst_3979_: *mut leanh::LeanObject,
    mut v_inst_3980_: *mut leanh::LeanObject,
    mut v_a_3981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3982_ = leanh::lean_ctor_get(v_inst_3979_, 0);
    leanh::lean_inc_ref(v_toApplicative_3982_);
    v_getRef_3983_ = leanh::lean_ctor_get(v_inst_3980_, 0);
    leanh::lean_inc(v_getRef_3983_);
    leanh::lean_dec_ref(v_inst_3980_);
    v_toBind_3984_ = leanh::lean_ctor_get(v_inst_3979_, 1);
    leanh::lean_inc(v_toBind_3984_);
    leanh::lean_dec_ref(v_inst_3979_);
    v_toPure_3985_ = leanh::lean_ctor_get(v_toApplicative_3982_, 1);
    leanh::lean_inc(v_toPure_3985_);
    leanh::lean_dec_ref(v_toApplicative_3982_);
    v___f_3986_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3986_, 0, v_a_3981_);
    leanh::lean_closure_set(v___f_3986_, 1, v_toPure_3985_);
    v___x_3987_ = leanh::lean_apply_4(
        v_toBind_3984_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_3983_,
        v___f_3986_,
    );
    return v___x_3987_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1(
    mut v_00_u03b1_3988_: *mut leanh::LeanObject,
    mut v_00_u03b2_3989_: *mut leanh::LeanObject,
    mut v_m_3990_: *mut leanh::LeanObject,
    mut v_inst_3991_: *mut leanh::LeanObject,
    mut v_inst_3992_: *mut leanh::LeanObject,
    mut v_inst_3993_: *mut leanh::LeanObject,
    mut v_inst_3994_: *mut leanh::LeanObject,
    mut v_a_3995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3996_ = leanh::lean_ctor_get(v_inst_3993_, 0);
    leanh::lean_inc_ref(v_toApplicative_3996_);
    v_getRef_3997_ = leanh::lean_ctor_get(v_inst_3994_, 0);
    leanh::lean_inc(v_getRef_3997_);
    leanh::lean_dec_ref(v_inst_3994_);
    v_toBind_3998_ = leanh::lean_ctor_get(v_inst_3993_, 1);
    leanh::lean_inc(v_toBind_3998_);
    leanh::lean_dec_ref(v_inst_3993_);
    v_toPure_3999_ = leanh::lean_ctor_get(v_toApplicative_3996_, 1);
    leanh::lean_inc(v_toPure_3999_);
    leanh::lean_dec_ref(v_toApplicative_3996_);
    v___f_4000_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4000_, 0, v_a_3995_);
    leanh::lean_closure_set(v___f_4000_, 1, v_toPure_3999_);
    v___x_4001_ = leanh::lean_apply_4(
        v_toBind_3998_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_3997_,
        v___f_4000_,
    );
    return v___x_4001_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed(
    mut v_00_u03b1_4002_: *mut leanh::LeanObject,
    mut v_00_u03b2_4003_: *mut leanh::LeanObject,
    mut v_m_4004_: *mut leanh::LeanObject,
    mut v_inst_4005_: *mut leanh::LeanObject,
    mut v_inst_4006_: *mut leanh::LeanObject,
    mut v_inst_4007_: *mut leanh::LeanObject,
    mut v_inst_4008_: *mut leanh::LeanObject,
    mut v_a_4009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_4006_);
    leanh::lean_dec_ref(v_inst_4005_);
    return v_res_4010_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__3___redArg(
    mut v_inst_4011_: *mut leanh::LeanObject,
    mut v_ref_4012_: *mut leanh::LeanObject,
    mut v_x_4013_: *mut leanh::LeanObject,
    mut v_a_4014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withRef_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withRef_4015_ = leanh::lean_ctor_get(v_inst_4011_, 1);
    leanh::lean_inc(v_withRef_4015_);
    leanh::lean_dec_ref(v_inst_4011_);
    v___x_4016_ = leanh::lean_apply_1(v_x_4013_, v_a_4014_);
    v___x_4017_ = leanh::lean_apply_3(
        v_withRef_4015_,
        leanh::lean_box(0),
        v_ref_4012_,
        v___x_4016_,
    );
    return v___x_4017_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__3(
    mut v_00_u03b1_4018_: *mut leanh::LeanObject,
    mut v_00_u03b2_4019_: *mut leanh::LeanObject,
    mut v_m_4020_: *mut leanh::LeanObject,
    mut v_inst_4021_: *mut leanh::LeanObject,
    mut v_inst_4022_: *mut leanh::LeanObject,
    mut v_inst_4023_: *mut leanh::LeanObject,
    mut v_00_u03b1_4024_: *mut leanh::LeanObject,
    mut v_ref_4025_: *mut leanh::LeanObject,
    mut v_x_4026_: *mut leanh::LeanObject,
    mut v_a_4027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withRef_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withRef_4028_ = leanh::lean_ctor_get(v_inst_4023_, 1);
    leanh::lean_inc(v_withRef_4028_);
    leanh::lean_dec_ref(v_inst_4023_);
    v___x_4029_ = leanh::lean_apply_1(v_x_4026_, v_a_4027_);
    v___x_4030_ = leanh::lean_apply_3(
        v_withRef_4028_,
        leanh::lean_box(0),
        v_ref_4025_,
        v___x_4029_,
    );
    return v___x_4030_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed(
    mut v_00_u03b1_4031_: *mut leanh::LeanObject,
    mut v_00_u03b2_4032_: *mut leanh::LeanObject,
    mut v_m_4033_: *mut leanh::LeanObject,
    mut v_inst_4034_: *mut leanh::LeanObject,
    mut v_inst_4035_: *mut leanh::LeanObject,
    mut v_inst_4036_: *mut leanh::LeanObject,
    mut v_00_u03b1_4037_: *mut leanh::LeanObject,
    mut v_ref_4038_: *mut leanh::LeanObject,
    mut v_x_4039_: *mut leanh::LeanObject,
    mut v_a_4040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_4035_);
    leanh::lean_dec_ref(v_inst_4034_);
    return v_res_4041_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___redArg(
    mut v_inst_4042_: *mut leanh::LeanObject,
    mut v_inst_4043_: *mut leanh::LeanObject,
    mut v_inst_4044_: *mut leanh::LeanObject,
    mut v_inst_4045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_4045_);
    leanh::lean_inc_ref(v_inst_4043_);
    leanh::lean_inc_ref(v_inst_4042_);
    v___x_4046_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___x_4046_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4046_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4046_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4046_, 3, v_inst_4042_);
    leanh::lean_closure_set(v___x_4046_, 4, v_inst_4043_);
    leanh::lean_closure_set(v___x_4046_, 5, v_inst_4044_);
    leanh::lean_closure_set(v___x_4046_, 6, v_inst_4045_);
    v___x_4047_ = leanh::lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed as *mut core::ffi::c_void,
        10,
        6,
    );
    leanh::lean_closure_set(v___x_4047_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4047_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4047_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4047_, 3, v_inst_4042_);
    leanh::lean_closure_set(v___x_4047_, 4, v_inst_4043_);
    leanh::lean_closure_set(v___x_4047_, 5, v_inst_4045_);
    v___x_4048_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4048_, 0, v___x_4046_);
    leanh::lean_ctor_set(v___x_4048_, 1, v___x_4047_);
    return v___x_4048_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef(
    mut v_00_u03b1_4049_: *mut leanh::LeanObject,
    mut v_00_u03b2_4050_: *mut leanh::LeanObject,
    mut v_m_4051_: *mut leanh::LeanObject,
    mut v_inst_4052_: *mut leanh::LeanObject,
    mut v_inst_4053_: *mut leanh::LeanObject,
    mut v_inst_4054_: *mut leanh::LeanObject,
    mut v_inst_4055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
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
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_MonadCache(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_MonadCache(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_MonadCache(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_MonadCache(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_MonadCache(builtin);
}