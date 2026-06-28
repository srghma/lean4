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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__2 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_MonadCacheT_run___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadCacheT_run___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadCacheT_run___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadCacheT_run___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MonadCacheT_run___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MonadCacheT_run___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MonadStateCacheT_run___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MonadStateCacheT_run___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MonadStateCacheT_run___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_checkCache___redArg___lam__0(
    mut v_toPure_2029_: *mut LeanObject,
    mut v_b_2030_: *mut LeanObject,
    mut v_____r_2031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    v___x_2032_ = lean_apply_2(v_toPure_2029_, lean_box(0), v_b_2030_);
    return v___x_2032_;
}
pub unsafe fn l_Lean_checkCache___redArg___lam__1(
    mut v_toPure_2033_: *mut LeanObject,
    mut v_cache_2034_: *mut LeanObject,
    mut v_a_2035_: *mut LeanObject,
    mut v_toBind_2036_: *mut LeanObject,
    mut v_b_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_b_2037_);
    v___f_2038_ = lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2038_, 0, v_toPure_2033_);
    lean_closure_set(v___f_2038_, 1, v_b_2037_);
    v___x_2039_ = lean_apply_2(v_cache_2034_, v_a_2035_, v_b_2037_);
    v___x_2040_ = lean_apply_4(
        v_toBind_2036_,
        lean_box(0),
        lean_box(0),
        v___x_2039_,
        v___f_2038_,
    );
    return v___x_2040_;
}
pub unsafe fn l_Lean_checkCache___redArg___lam__2(
    mut v_f_2041_: *mut LeanObject,
    mut v_toBind_2042_: *mut LeanObject,
    mut v___f_2043_: *mut LeanObject,
    mut v_toPure_2044_: *mut LeanObject,
    mut v_____do__lift_2045_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2045_) == 0 {
        let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2044_);
        v___x_2046_ = lean_box(0);
        v___x_2047_ = lean_apply_1(v_f_2041_, v___x_2046_);
        v___x_2048_ = lean_apply_4(
            v_toBind_2042_,
            lean_box(0),
            lean_box(0),
            v___x_2047_,
            v___f_2043_,
        );
        return v___x_2048_;
    } else {
        let mut v_val_2049_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2043_);
        lean_dec(v_toBind_2042_);
        lean_dec(v_f_2041_);
        v_val_2049_ = lean_ctor_get(v_____do__lift_2045_, 0);
        lean_inc(v_val_2049_);
        lean_dec_ref_known(v_____do__lift_2045_, 1);
        v___x_2050_ = lean_apply_2(v_toPure_2044_, lean_box(0), v_val_2049_);
        return v___x_2050_;
    }
}
pub unsafe fn l_Lean_checkCache___redArg(
    mut v_inst_2051_: *mut LeanObject,
    mut v_inst_2052_: *mut LeanObject,
    mut v_a_2053_: *mut LeanObject,
    mut v_f_2054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_findCached_x3f_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2055_ = lean_ctor_get(v_inst_2052_, 0);
    lean_inc_ref(v_toApplicative_2055_);
    v_toBind_2056_ = lean_ctor_get(v_inst_2052_, 1);
    lean_inc_n(v_toBind_2056_, 3);
    lean_dec_ref(v_inst_2052_);
    v_findCached_x3f_2057_ = lean_ctor_get(v_inst_2051_, 0);
    lean_inc(v_findCached_x3f_2057_);
    v_cache_2058_ = lean_ctor_get(v_inst_2051_, 1);
    lean_inc(v_cache_2058_);
    lean_dec_ref(v_inst_2051_);
    v_toPure_2059_ = lean_ctor_get(v_toApplicative_2055_, 1);
    lean_inc_n(v_toPure_2059_, 2);
    lean_dec_ref(v_toApplicative_2055_);
    lean_inc(v_a_2053_);
    v___x_2060_ = lean_apply_1(v_findCached_x3f_2057_, v_a_2053_);
    v___f_2061_ = lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2061_, 0, v_toPure_2059_);
    lean_closure_set(v___f_2061_, 1, v_cache_2058_);
    lean_closure_set(v___f_2061_, 2, v_a_2053_);
    lean_closure_set(v___f_2061_, 3, v_toBind_2056_);
    v___f_2062_ = lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2062_, 0, v_f_2054_);
    lean_closure_set(v___f_2062_, 1, v_toBind_2056_);
    lean_closure_set(v___f_2062_, 2, v___f_2061_);
    lean_closure_set(v___f_2062_, 3, v_toPure_2059_);
    v___x_2063_ = lean_apply_4(
        v_toBind_2056_,
        lean_box(0),
        lean_box(0),
        v___x_2060_,
        v___f_2062_,
    );
    return v___x_2063_;
}
pub unsafe fn l_Lean_checkCache(
    mut v_00_u03b1_2064_: *mut LeanObject,
    mut v_00_u03b2_2065_: *mut LeanObject,
    mut v_m_2066_: *mut LeanObject,
    mut v_inst_2067_: *mut LeanObject,
    mut v_inst_2068_: *mut LeanObject,
    mut v_a_2069_: *mut LeanObject,
    mut v_f_2070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_findCached_x3f_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2071_ = lean_ctor_get(v_inst_2068_, 0);
    lean_inc_ref(v_toApplicative_2071_);
    v_toBind_2072_ = lean_ctor_get(v_inst_2068_, 1);
    lean_inc_n(v_toBind_2072_, 3);
    lean_dec_ref(v_inst_2068_);
    v_findCached_x3f_2073_ = lean_ctor_get(v_inst_2067_, 0);
    lean_inc(v_findCached_x3f_2073_);
    v_cache_2074_ = lean_ctor_get(v_inst_2067_, 1);
    lean_inc(v_cache_2074_);
    lean_dec_ref(v_inst_2067_);
    v_toPure_2075_ = lean_ctor_get(v_toApplicative_2071_, 1);
    lean_inc_n(v_toPure_2075_, 2);
    lean_dec_ref(v_toApplicative_2071_);
    lean_inc(v_a_2069_);
    v___x_2076_ = lean_apply_1(v_findCached_x3f_2073_, v_a_2069_);
    v___f_2077_ = lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2077_, 0, v_toPure_2075_);
    lean_closure_set(v___f_2077_, 1, v_cache_2074_);
    lean_closure_set(v___f_2077_, 2, v_a_2069_);
    lean_closure_set(v___f_2077_, 3, v_toBind_2072_);
    v___f_2078_ = lean_alloc_closure(
        l_Lean_checkCache___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2078_, 0, v_f_2070_);
    lean_closure_set(v___f_2078_, 1, v_toBind_2072_);
    lean_closure_set(v___f_2078_, 2, v___f_2077_);
    lean_closure_set(v___f_2078_, 3, v_toPure_2075_);
    v___x_2079_ = lean_apply_4(
        v_toBind_2072_,
        lean_box(0),
        lean_box(0),
        v___x_2076_,
        v___f_2078_,
    );
    return v___x_2079_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__0(
    mut v_inst_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_x_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_findCached_x3f_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    v_findCached_x3f_2083_ = lean_ctor_get(v_inst_2080_, 0);
    lean_inc(v_findCached_x3f_2083_);
    lean_dec_ref(v_inst_2080_);
    v___x_2084_ = lean_apply_1(v_findCached_x3f_2083_, v_a_2081_);
    return v___x_2084_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__0___boxed(
    mut v_inst_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
    mut v_x_2087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2088_: *mut LeanObject = core::ptr::null_mut();
    v_res_2088_ =
        l_Lean_instMonadCacheReaderT___redArg___lam__0(v_inst_2085_, v_a_2086_, v_x_2087_);
    lean_dec(v_x_2087_);
    return v_res_2088_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__1(
    mut v_inst_2089_: *mut LeanObject,
    mut v_a_2090_: *mut LeanObject,
    mut v_b_2091_: *mut LeanObject,
    mut v_x_2092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cache_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    v_cache_2093_ = lean_ctor_get(v_inst_2089_, 1);
    lean_inc(v_cache_2093_);
    lean_dec_ref(v_inst_2089_);
    v___x_2094_ = lean_apply_2(v_cache_2093_, v_a_2090_, v_b_2091_);
    return v___x_2094_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg___lam__1___boxed(
    mut v_inst_2095_: *mut LeanObject,
    mut v_a_2096_: *mut LeanObject,
    mut v_b_2097_: *mut LeanObject,
    mut v_x_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2099_: *mut LeanObject = core::ptr::null_mut();
    v_res_2099_ = l_Lean_instMonadCacheReaderT___redArg___lam__1(
        v_inst_2095_,
        v_a_2096_,
        v_b_2097_,
        v_x_2098_,
    );
    lean_dec(v_x_2098_);
    return v_res_2099_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT___redArg(
    mut v_inst_2100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_2100_);
    v___f_2101_ = lean_alloc_closure(
        l_Lean_instMonadCacheReaderT___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2101_, 0, v_inst_2100_);
    v___f_2102_ = lean_alloc_closure(
        l_Lean_instMonadCacheReaderT___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2102_, 0, v_inst_2100_);
    v___x_2103_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2103_, 0, v___f_2101_);
    lean_ctor_set(v___x_2103_, 1, v___f_2102_);
    return v___x_2103_;
}
pub unsafe fn l_Lean_instMonadCacheReaderT(
    mut v_00_u03b1_2104_: *mut LeanObject,
    mut v_00_u03b2_2105_: *mut LeanObject,
    mut v_00_u03c1_2106_: *mut LeanObject,
    mut v_m_2107_: *mut LeanObject,
    mut v_inst_2108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    v___x_2109_ = l_Lean_instMonadCacheReaderT___redArg(v_inst_2108_);
    return v___x_2109_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__0(
    mut v_a_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    v___x_2111_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2111_, 0, v_a_2110_);
    return v___x_2111_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1(
    mut v_inst_2112_: *mut LeanObject,
    mut v_inst_2113_: *mut LeanObject,
    mut v___f_2114_: *mut LeanObject,
    mut v_a_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_findCached_x3f_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2116_ = lean_ctor_get(v_inst_2113_, 0);
    lean_inc_ref(v_toApplicative_2116_);
    lean_dec_ref(v_inst_2113_);
    v_toFunctor_2117_ = lean_ctor_get(v_toApplicative_2116_, 0);
    lean_inc_ref(v_toFunctor_2117_);
    lean_dec_ref(v_toApplicative_2116_);
    v_findCached_x3f_2118_ = lean_ctor_get(v_inst_2112_, 0);
    lean_inc(v_findCached_x3f_2118_);
    lean_dec_ref(v_inst_2112_);
    v_map_2119_ = lean_ctor_get(v_toFunctor_2117_, 0);
    lean_inc(v_map_2119_);
    lean_dec_ref(v_toFunctor_2117_);
    v___x_2120_ = lean_apply_1(v_findCached_x3f_2118_, v_a_2115_);
    v___x_2121_ = lean_apply_4(
        v_map_2119_,
        lean_box(0),
        lean_box(0),
        v___f_2114_,
        v___x_2120_,
    );
    return v___x_2121_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__2(
    mut v_a_2122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    v___x_2123_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2123_, 0, v_a_2122_);
    return v___x_2123_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3(
    mut v_inst_2124_: *mut LeanObject,
    mut v_inst_2125_: *mut LeanObject,
    mut v___f_2126_: *mut LeanObject,
    mut v_a_2127_: *mut LeanObject,
    mut v_b_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2129_ = lean_ctor_get(v_inst_2125_, 0);
    lean_inc_ref(v_toApplicative_2129_);
    lean_dec_ref(v_inst_2125_);
    v_toFunctor_2130_ = lean_ctor_get(v_toApplicative_2129_, 0);
    lean_inc_ref(v_toFunctor_2130_);
    lean_dec_ref(v_toApplicative_2129_);
    v_cache_2131_ = lean_ctor_get(v_inst_2124_, 1);
    lean_inc(v_cache_2131_);
    lean_dec_ref(v_inst_2124_);
    v_map_2132_ = lean_ctor_get(v_toFunctor_2130_, 0);
    lean_inc(v_map_2132_);
    lean_dec_ref(v_toFunctor_2130_);
    v___x_2133_ = lean_apply_2(v_cache_2131_, v_a_2127_, v_b_2128_);
    v___x_2134_ = lean_apply_4(
        v_map_2132_,
        lean_box(0),
        lean_box(0),
        v___f_2126_,
        v___x_2133_,
    );
    return v___x_2134_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad___redArg(
    mut v_inst_2137_: *mut LeanObject,
    mut v_inst_2138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    v___f_2139_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0;
    lean_inc_ref(v_inst_2138_);
    lean_inc_ref(v_inst_2137_);
    v___f_2140_ = lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2140_, 0, v_inst_2137_);
    lean_closure_set(v___f_2140_, 1, v_inst_2138_);
    lean_closure_set(v___f_2140_, 2, v___f_2139_);
    v___f_2141_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1;
    v___f_2142_ = lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2142_, 0, v_inst_2137_);
    lean_closure_set(v___f_2142_, 1, v_inst_2138_);
    lean_closure_set(v___f_2142_, 2, v___f_2141_);
    v___x_2143_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2143_, 0, v___f_2140_);
    lean_ctor_set(v___x_2143_, 1, v___f_2142_);
    return v___x_2143_;
}
pub unsafe fn l_Lean_instMonadCacheExceptTOfMonad(
    mut v_00_u03b1_2144_: *mut LeanObject,
    mut v_00_u03b2_2145_: *mut LeanObject,
    mut v_00_u03b5_2146_: *mut LeanObject,
    mut v_m_2147_: *mut LeanObject,
    mut v_inst_2148_: *mut LeanObject,
    mut v_inst_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    v___f_2150_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__0;
    lean_inc_ref(v_inst_2149_);
    lean_inc_ref(v_inst_2148_);
    v___f_2151_ = lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2151_, 0, v_inst_2148_);
    lean_closure_set(v___f_2151_, 1, v_inst_2149_);
    lean_closure_set(v___f_2151_, 2, v___f_2150_);
    v___f_2152_ = l_Lean_instMonadCacheExceptTOfMonad___redArg___closed__1;
    v___f_2153_ = lean_alloc_closure(
        l_Lean_instMonadCacheExceptTOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2153_, 0, v_inst_2148_);
    lean_closure_set(v___f_2153_, 1, v_inst_2149_);
    lean_closure_set(v___f_2153_, 2, v___f_2152_);
    v___x_2154_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2154_, 0, v___f_2151_);
    lean_ctor_set(v___x_2154_, 1, v___f_2153_);
    return v___x_2154_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0(
    mut v_inst_2155_: *mut LeanObject,
    mut v_inst_2156_: *mut LeanObject,
    mut v_a_2157_: *mut LeanObject,
    mut v_toPure_2158_: *mut LeanObject,
    mut v_c_2159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    v___x_2160_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_inst_2155_,
        v_inst_2156_,
        v_c_2159_,
        v_a_2157_,
    );
    v___x_2161_ = lean_apply_2(v_toPure_2158_, lean_box(0), v___x_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed(
    mut v_inst_2162_: *mut LeanObject,
    mut v_inst_2163_: *mut LeanObject,
    mut v_a_2164_: *mut LeanObject,
    mut v_toPure_2165_: *mut LeanObject,
    mut v_c_2166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2167_: *mut LeanObject = core::ptr::null_mut();
    v_res_2167_ = l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0(
        v_inst_2162_,
        v_inst_2163_,
        v_a_2164_,
        v_toPure_2165_,
        v_c_2166_,
    );
    lean_dec_ref(v_c_2166_);
    return v_res_2167_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg(
    mut v_inst_2168_: *mut LeanObject,
    mut v_inst_2169_: *mut LeanObject,
    mut v_inst_2170_: *mut LeanObject,
    mut v_inst_2171_: *mut LeanObject,
    mut v_a_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCache_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2173_ = lean_ctor_get(v_inst_2170_, 0);
    lean_inc_ref(v_toApplicative_2173_);
    v_toBind_2174_ = lean_ctor_get(v_inst_2170_, 1);
    lean_inc(v_toBind_2174_);
    lean_dec_ref(v_inst_2170_);
    v_getCache_2175_ = lean_ctor_get(v_inst_2171_, 0);
    lean_inc(v_getCache_2175_);
    lean_dec_ref(v_inst_2171_);
    v_toPure_2176_ = lean_ctor_get(v_toApplicative_2173_, 1);
    lean_inc(v_toPure_2176_);
    lean_dec_ref(v_toApplicative_2173_);
    v___f_2177_ = lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2177_, 0, v_inst_2168_);
    lean_closure_set(v___f_2177_, 1, v_inst_2169_);
    lean_closure_set(v___f_2177_, 2, v_a_2172_);
    lean_closure_set(v___f_2177_, 3, v_toPure_2176_);
    v___x_2178_ = lean_apply_4(
        v_toBind_2174_,
        lean_box(0),
        lean_box(0),
        v_getCache_2175_,
        v___f_2177_,
    );
    return v___x_2178_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_findCached_x3f(
    mut v_00_u03b1_2179_: *mut LeanObject,
    mut v_00_u03b2_2180_: *mut LeanObject,
    mut v_m_2181_: *mut LeanObject,
    mut v_inst_2182_: *mut LeanObject,
    mut v_inst_2183_: *mut LeanObject,
    mut v_inst_2184_: *mut LeanObject,
    mut v_inst_2185_: *mut LeanObject,
    mut v_a_2186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCache_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2187_ = lean_ctor_get(v_inst_2184_, 0);
    lean_inc_ref(v_toApplicative_2187_);
    v_toBind_2188_ = lean_ctor_get(v_inst_2184_, 1);
    lean_inc(v_toBind_2188_);
    lean_dec_ref(v_inst_2184_);
    v_getCache_2189_ = lean_ctor_get(v_inst_2185_, 0);
    lean_inc(v_getCache_2189_);
    lean_dec_ref(v_inst_2185_);
    v_toPure_2190_ = lean_ctor_get(v_toApplicative_2187_, 1);
    lean_inc(v_toPure_2190_);
    lean_dec_ref(v_toApplicative_2187_);
    v___f_2191_ = lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_findCached_x3f___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2191_, 0, v_inst_2182_);
    lean_closure_set(v___f_2191_, 1, v_inst_2183_);
    lean_closure_set(v___f_2191_, 2, v_a_2186_);
    lean_closure_set(v___f_2191_, 3, v_toPure_2190_);
    v___x_2192_ = lean_apply_4(
        v_toBind_2188_,
        lean_box(0),
        lean_box(0),
        v_getCache_2189_,
        v___f_2191_,
    );
    return v___x_2192_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0(
    mut v_inst_2193_: *mut LeanObject,
    mut v_inst_2194_: *mut LeanObject,
    mut v_a_2195_: *mut LeanObject,
    mut v_b_2196_: *mut LeanObject,
    mut v_s_2197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_2199_: *mut LeanObject,
    mut v_inst_2200_: *mut LeanObject,
    mut v_inst_2201_: *mut LeanObject,
    mut v_a_2202_: *mut LeanObject,
    mut v_b_2203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyCache_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    v_modifyCache_2204_ = lean_ctor_get(v_inst_2201_, 1);
    lean_inc(v_modifyCache_2204_);
    lean_dec_ref(v_inst_2201_);
    v___f_2205_ = lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2205_, 0, v_inst_2199_);
    lean_closure_set(v___f_2205_, 1, v_inst_2200_);
    lean_closure_set(v___f_2205_, 2, v_a_2202_);
    lean_closure_set(v___f_2205_, 3, v_b_2203_);
    v___x_2206_ = lean_apply_1(v_modifyCache_2204_, v___f_2205_);
    return v___x_2206_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_cache(
    mut v_00_u03b1_2207_: *mut LeanObject,
    mut v_00_u03b2_2208_: *mut LeanObject,
    mut v_m_2209_: *mut LeanObject,
    mut v_inst_2210_: *mut LeanObject,
    mut v_inst_2211_: *mut LeanObject,
    mut v_inst_2212_: *mut LeanObject,
    mut v_a_2213_: *mut LeanObject,
    mut v_b_2214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyCache_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    v_modifyCache_2215_ = lean_ctor_get(v_inst_2212_, 1);
    lean_inc(v_modifyCache_2215_);
    lean_dec_ref(v_inst_2212_);
    v___f_2216_ = lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_cache___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2216_, 0, v_inst_2210_);
    lean_closure_set(v___f_2216_, 1, v_inst_2211_);
    lean_closure_set(v___f_2216_, 2, v_a_2213_);
    lean_closure_set(v___f_2216_, 3, v_b_2214_);
    v___x_2217_ = lean_apply_1(v_modifyCache_2215_, v___f_2216_);
    return v___x_2217_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad___redArg(
    mut v_inst_2218_: *mut LeanObject,
    mut v_inst_2219_: *mut LeanObject,
    mut v_inst_2220_: *mut LeanObject,
    mut v_inst_2221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_2221_);
    lean_inc_ref(v_inst_2219_);
    lean_inc_ref(v_inst_2218_);
    v___x_2222_ = lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_findCached_x3f as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___x_2222_, 0, lean_box(0));
    lean_closure_set(v___x_2222_, 1, lean_box(0));
    lean_closure_set(v___x_2222_, 2, lean_box(0));
    lean_closure_set(v___x_2222_, 3, v_inst_2218_);
    lean_closure_set(v___x_2222_, 4, v_inst_2219_);
    lean_closure_set(v___x_2222_, 5, v_inst_2220_);
    lean_closure_set(v___x_2222_, 6, v_inst_2221_);
    v___x_2223_ = lean_alloc_closure(
        l_Lean_MonadHashMapCacheAdapter_cache as *mut core::ffi::c_void,
        8,
        6,
    );
    lean_closure_set(v___x_2223_, 0, lean_box(0));
    lean_closure_set(v___x_2223_, 1, lean_box(0));
    lean_closure_set(v___x_2223_, 2, lean_box(0));
    lean_closure_set(v___x_2223_, 3, v_inst_2218_);
    lean_closure_set(v___x_2223_, 4, v_inst_2219_);
    lean_closure_set(v___x_2223_, 5, v_inst_2221_);
    v___x_2224_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2224_, 0, v___x_2222_);
    lean_ctor_set(v___x_2224_, 1, v___x_2223_);
    return v___x_2224_;
}
pub unsafe fn l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad(
    mut v_00_u03b1_2225_: *mut LeanObject,
    mut v_00_u03b2_2226_: *mut LeanObject,
    mut v_m_2227_: *mut LeanObject,
    mut v_inst_2228_: *mut LeanObject,
    mut v_inst_2229_: *mut LeanObject,
    mut v_inst_2230_: *mut LeanObject,
    mut v_inst_2231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    v___x_2232_ = l_Lean_MonadHashMapCacheAdapter_instMonadCacheOfMonad___redArg(
        v_inst_2228_,
        v_inst_2229_,
        v_inst_2230_,
        v_inst_2231_,
    );
    return v___x_2232_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__0(
    mut v_f_2233_: *mut LeanObject,
    mut v_s_2234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    v___x_2235_ = lean_box(0);
    v___x_2236_ = lean_apply_1(v_f_2233_, v_s_2234_);
    v___x_2237_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2237_, 0, v___x_2235_);
    lean_ctor_set(v___x_2237_, 1, v___x_2236_);
    return v___x_2237_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1(
    mut v_inst_2238_: *mut LeanObject,
    mut v_f_2239_: *mut LeanObject,
    mut v___y_2240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    v___f_2241_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2241_, 0, v_f_2239_);
    lean_inc(v___y_2240_);
    v___x_2242_ = lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___x_2242_, 0, lean_box(0));
    lean_closure_set(v___x_2242_, 1, lean_box(0));
    lean_closure_set(v___x_2242_, 2, lean_box(0));
    lean_closure_set(v___x_2242_, 3, v___y_2240_);
    lean_closure_set(v___x_2242_, 4, v___f_2241_);
    v___x_2243_ = lean_apply_2(v_inst_2238_, lean_box(0), v___x_2242_);
    return v___x_2243_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1___boxed(
    mut v_inst_2244_: *mut LeanObject,
    mut v_f_2245_: *mut LeanObject,
    mut v___y_2246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2247_: *mut LeanObject = core::ptr::null_mut();
    v_res_2247_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1(
        v_inst_2244_,
        v_f_2245_,
        v___y_2246_,
    );
    lean_dec(v___y_2246_);
    return v_res_2247_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(
    mut v_inst_2248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_inst_2248_);
    v___f_2249_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2249_, 0, v_inst_2248_);
    v___x_2250_ = lean_alloc_closure(l_StateRefT_x27_get___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_2250_, 0, lean_box(0));
    lean_closure_set(v___x_2250_, 1, lean_box(0));
    lean_closure_set(v___x_2250_, 2, lean_box(0));
    lean_closure_set(v___x_2250_, 3, v_inst_2248_);
    v___x_2251_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2251_, 0, v___x_2250_);
    lean_ctor_set(v___x_2251_, 1, v___f_2249_);
    return v___x_2251_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter(
    mut v_00_u03c9_2252_: *mut LeanObject,
    mut v_00_u03b1_2253_: *mut LeanObject,
    mut v_00_u03b2_2254_: *mut LeanObject,
    mut v_m_2255_: *mut LeanObject,
    mut v_inst_2256_: *mut LeanObject,
    mut v_inst_2257_: *mut LeanObject,
    mut v_inst_2258_: *mut LeanObject,
    mut v_inst_2259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    v___x_2260_ = l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_2259_);
    return v___x_2260_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadHashMapCacheAdapter___boxed(
    mut v_00_u03c9_2261_: *mut LeanObject,
    mut v_00_u03b1_2262_: *mut LeanObject,
    mut v_00_u03b2_2263_: *mut LeanObject,
    mut v_m_2264_: *mut LeanObject,
    mut v_inst_2265_: *mut LeanObject,
    mut v_inst_2266_: *mut LeanObject,
    mut v_inst_2267_: *mut LeanObject,
    mut v_inst_2268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2269_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_2267_);
    lean_dec_ref(v_inst_2266_);
    return v_res_2269_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__0(
    mut v_a_2270_: *mut LeanObject,
    mut v_toPure_2271_: *mut LeanObject,
    mut v_s_2272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    v___x_2273_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2273_, 0, v_a_2270_);
    lean_ctor_set(v___x_2273_, 1, v_s_2272_);
    v___x_2274_ = lean_apply_2(v_toPure_2271_, lean_box(0), v___x_2273_);
    return v___x_2274_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__1(
    mut v_toPure_2275_: *mut LeanObject,
    mut v_ref_2276_: *mut LeanObject,
    mut v_inst_2277_: *mut LeanObject,
    mut v_toBind_2278_: *mut LeanObject,
    mut v_a_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    v___f_2280_ = lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2280_, 0, v_a_2279_);
    lean_closure_set(v___f_2280_, 1, v_toPure_2275_);
    v___x_2281_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_2281_, 0, lean_box(0));
    lean_closure_set(v___x_2281_, 1, lean_box(0));
    lean_closure_set(v___x_2281_, 2, v_ref_2276_);
    v___x_2282_ = lean_apply_2(v_inst_2277_, lean_box(0), v___x_2281_);
    v___x_2283_ = lean_apply_4(
        v_toBind_2278_,
        lean_box(0),
        lean_box(0),
        v___x_2282_,
        v___f_2280_,
    );
    return v___x_2283_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__2(
    mut v_toPure_2284_: *mut LeanObject,
    mut v_inst_2285_: *mut LeanObject,
    mut v_toBind_2286_: *mut LeanObject,
    mut v_x_2287_: *mut LeanObject,
    mut v_ref_2288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_2286_);
    lean_inc(v_ref_2288_);
    v___f_2289_ = lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2289_, 0, v_toPure_2284_);
    lean_closure_set(v___f_2289_, 1, v_ref_2288_);
    lean_closure_set(v___f_2289_, 2, v_inst_2285_);
    lean_closure_set(v___f_2289_, 3, v_toBind_2286_);
    v___x_2290_ = lean_apply_1(v_x_2287_, v_ref_2288_);
    v___x_2291_ = lean_apply_4(
        v_toBind_2286_,
        lean_box(0),
        lean_box(0),
        v___x_2290_,
        v___f_2289_,
    );
    return v___x_2291_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg___lam__3(
    mut v_toPure_2292_: *mut LeanObject,
    mut v_____x_2293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2294_ = lean_ctor_get(v_____x_2293_, 0);
    lean_inc(v_fst_2294_);
    lean_dec_ref(v_____x_2293_);
    v___x_2295_ = lean_apply_2(v_toPure_2292_, lean_box(0), v_fst_2294_);
    return v___x_2295_;
}
pub unsafe fn _init_l_Lean_MonadCacheT_run___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    v___x_2296_ = lean_box(0);
    v___x_2297_ = lean_unsigned_to_nat(16);
    v___x_2298_ = lean_mk_array(v___x_2297_, v___x_2296_);
    return v___x_2298_;
}
pub unsafe fn _init_l_Lean_MonadCacheT_run___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    v___x_2299_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__0_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__0,
    );
    v___x_2300_ = lean_unsigned_to_nat(0);
    v___x_2301_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2301_, 0, v___x_2300_);
    lean_ctor_set(v___x_2301_, 1, v___x_2299_);
    return v___x_2301_;
}
pub unsafe fn _init_l_Lean_MonadCacheT_run___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    v___x_2302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__1,
    );
    v___x_2303_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_2303_, 0, lean_box(0));
    lean_closure_set(v___x_2303_, 1, lean_box(0));
    lean_closure_set(v___x_2303_, 2, v___x_2302_);
    return v___x_2303_;
}
pub unsafe fn l_Lean_MonadCacheT_run___redArg(
    mut v_inst_2304_: *mut LeanObject,
    mut v_inst_2305_: *mut LeanObject,
    mut v_x_2306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2307_ = lean_ctor_get(v_inst_2305_, 0);
    lean_inc_ref(v_toApplicative_2307_);
    v_toBind_2308_ = lean_ctor_get(v_inst_2305_, 1);
    lean_inc_n(v_toBind_2308_, 3);
    lean_dec_ref(v_inst_2305_);
    v_toPure_2309_ = lean_ctor_get(v_toApplicative_2307_, 1);
    lean_inc_n(v_toPure_2309_, 2);
    lean_dec_ref(v_toApplicative_2307_);
    v___x_2310_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__2,
    );
    lean_inc(v_inst_2304_);
    v___x_2311_ = lean_apply_2(v_inst_2304_, lean_box(0), v___x_2310_);
    v___f_2312_ = lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2312_, 0, v_toPure_2309_);
    lean_closure_set(v___f_2312_, 1, v_inst_2304_);
    lean_closure_set(v___f_2312_, 2, v_toBind_2308_);
    lean_closure_set(v___f_2312_, 3, v_x_2306_);
    v___f_2313_ = lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2313_, 0, v_toPure_2309_);
    v___x_2314_ = lean_apply_4(
        v_toBind_2308_,
        lean_box(0),
        lean_box(0),
        v___x_2311_,
        v___f_2312_,
    );
    v___x_2315_ = lean_apply_4(
        v_toBind_2308_,
        lean_box(0),
        lean_box(0),
        v___x_2314_,
        v___f_2313_,
    );
    return v___x_2315_;
}
pub unsafe fn l_Lean_MonadCacheT_run(
    mut v_00_u03c9_2316_: *mut LeanObject,
    mut v_00_u03b1_2317_: *mut LeanObject,
    mut v_00_u03b2_2318_: *mut LeanObject,
    mut v_m_2319_: *mut LeanObject,
    mut v_inst_2320_: *mut LeanObject,
    mut v_inst_2321_: *mut LeanObject,
    mut v_inst_2322_: *mut LeanObject,
    mut v_inst_2323_: *mut LeanObject,
    mut v_inst_2324_: *mut LeanObject,
    mut v_00_u03c3_2325_: *mut LeanObject,
    mut v_x_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2327_ = lean_ctor_get(v_inst_2324_, 0);
    lean_inc_ref(v_toApplicative_2327_);
    v_toBind_2328_ = lean_ctor_get(v_inst_2324_, 1);
    lean_inc_n(v_toBind_2328_, 3);
    lean_dec_ref(v_inst_2324_);
    v_toPure_2329_ = lean_ctor_get(v_toApplicative_2327_, 1);
    lean_inc_n(v_toPure_2329_, 2);
    lean_dec_ref(v_toApplicative_2327_);
    v___x_2330_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__2_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__2,
    );
    lean_inc(v_inst_2323_);
    v___x_2331_ = lean_apply_2(v_inst_2323_, lean_box(0), v___x_2330_);
    v___f_2332_ = lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2332_, 0, v_toPure_2329_);
    lean_closure_set(v___f_2332_, 1, v_inst_2323_);
    lean_closure_set(v___f_2332_, 2, v_toBind_2328_);
    lean_closure_set(v___f_2332_, 3, v_x_2326_);
    v___f_2333_ = lean_alloc_closure(
        l_Lean_MonadCacheT_run___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2333_, 0, v_toPure_2329_);
    v___x_2334_ = lean_apply_4(
        v_toBind_2328_,
        lean_box(0),
        lean_box(0),
        v___x_2331_,
        v___f_2332_,
    );
    v___x_2335_ = lean_apply_4(
        v_toBind_2328_,
        lean_box(0),
        lean_box(0),
        v___x_2334_,
        v___f_2333_,
    );
    return v___x_2335_;
}
pub unsafe fn l_Lean_MonadCacheT_run___boxed(
    mut v_00_u03c9_2336_: *mut LeanObject,
    mut v_00_u03b1_2337_: *mut LeanObject,
    mut v_00_u03b2_2338_: *mut LeanObject,
    mut v_m_2339_: *mut LeanObject,
    mut v_inst_2340_: *mut LeanObject,
    mut v_inst_2341_: *mut LeanObject,
    mut v_inst_2342_: *mut LeanObject,
    mut v_inst_2343_: *mut LeanObject,
    mut v_inst_2344_: *mut LeanObject,
    mut v_00_u03c3_2345_: *mut LeanObject,
    mut v_x_2346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2347_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_2342_);
    lean_dec_ref(v_inst_2341_);
    return v_res_2347_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1___redArg(
    mut v_inst_2348_: *mut LeanObject,
    mut v_a_2349_: *mut LeanObject,
    mut v_a_2350_: *mut LeanObject,
    mut v_a_2351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2352_ = lean_ctor_get(v_inst_2348_, 0);
    lean_inc_ref(v_toApplicative_2352_);
    lean_dec_ref(v_inst_2348_);
    v_toFunctor_2353_ = lean_ctor_get(v_toApplicative_2352_, 0);
    lean_inc_ref(v_toFunctor_2353_);
    lean_dec_ref(v_toApplicative_2352_);
    v_map_2354_ = lean_ctor_get(v_toFunctor_2353_, 0);
    lean_inc(v_map_2354_);
    lean_dec_ref(v_toFunctor_2353_);
    lean_inc(v_a_2351_);
    v___x_2355_ = lean_apply_1(v_a_2350_, v_a_2351_);
    v___x_2356_ = lean_apply_4(
        v_map_2354_,
        lean_box(0),
        lean_box(0),
        v_a_2349_,
        v___x_2355_,
    );
    return v___x_2356_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1___redArg___boxed(
    mut v_inst_2357_: *mut LeanObject,
    mut v_a_2358_: *mut LeanObject,
    mut v_a_2359_: *mut LeanObject,
    mut v_a_2360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2361_: *mut LeanObject = core::ptr::null_mut();
    v_res_2361_ = l_Lean_MonadCacheT_instMonad___aux__1___redArg(
        v_inst_2357_,
        v_a_2358_,
        v_a_2359_,
        v_a_2360_,
    );
    lean_dec(v_a_2360_);
    return v_res_2361_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1(
    mut v_00_u03c9_2362_: *mut LeanObject,
    mut v_00_u03b1_2363_: *mut LeanObject,
    mut v_00_u03b2_2364_: *mut LeanObject,
    mut v_m_2365_: *mut LeanObject,
    mut v_inst_2366_: *mut LeanObject,
    mut v_inst_2367_: *mut LeanObject,
    mut v_inst_2368_: *mut LeanObject,
    mut v_inst_2369_: *mut LeanObject,
    mut v_00_u03b1_2370_: *mut LeanObject,
    mut v_00_u03b2_2371_: *mut LeanObject,
    mut v_a_2372_: *mut LeanObject,
    mut v_a_2373_: *mut LeanObject,
    mut v_a_2374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2375_ = lean_ctor_get(v_inst_2369_, 0);
    lean_inc_ref(v_toApplicative_2375_);
    lean_dec_ref(v_inst_2369_);
    v_toFunctor_2376_ = lean_ctor_get(v_toApplicative_2375_, 0);
    lean_inc_ref(v_toFunctor_2376_);
    lean_dec_ref(v_toApplicative_2375_);
    v_map_2377_ = lean_ctor_get(v_toFunctor_2376_, 0);
    lean_inc(v_map_2377_);
    lean_dec_ref(v_toFunctor_2376_);
    lean_inc(v_a_2374_);
    v___x_2378_ = lean_apply_1(v_a_2373_, v_a_2374_);
    v___x_2379_ = lean_apply_4(
        v_map_2377_,
        lean_box(0),
        lean_box(0),
        v_a_2372_,
        v___x_2378_,
    );
    return v___x_2379_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__1___boxed(
    mut v_00_u03c9_2380_: *mut LeanObject,
    mut v_00_u03b1_2381_: *mut LeanObject,
    mut v_00_u03b2_2382_: *mut LeanObject,
    mut v_m_2383_: *mut LeanObject,
    mut v_inst_2384_: *mut LeanObject,
    mut v_inst_2385_: *mut LeanObject,
    mut v_inst_2386_: *mut LeanObject,
    mut v_inst_2387_: *mut LeanObject,
    mut v_00_u03b1_2388_: *mut LeanObject,
    mut v_00_u03b2_2389_: *mut LeanObject,
    mut v_a_2390_: *mut LeanObject,
    mut v_a_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2393_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2392_);
    lean_dec_ref(v_inst_2386_);
    lean_dec_ref(v_inst_2385_);
    return v_res_2393_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3___redArg(
    mut v_inst_2394_: *mut LeanObject,
    mut v_a_2395_: *mut LeanObject,
    mut v_a_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2398_ = lean_ctor_get(v_inst_2394_, 0);
    lean_inc_ref(v_toApplicative_2398_);
    lean_dec_ref(v_inst_2394_);
    v_toFunctor_2399_ = lean_ctor_get(v_toApplicative_2398_, 0);
    lean_inc_ref(v_toFunctor_2399_);
    lean_dec_ref(v_toApplicative_2398_);
    v_mapConst_2400_ = lean_ctor_get(v_toFunctor_2399_, 1);
    lean_inc(v_mapConst_2400_);
    lean_dec_ref(v_toFunctor_2399_);
    lean_inc(v_a_2397_);
    v___x_2401_ = lean_apply_1(v_a_2396_, v_a_2397_);
    v___x_2402_ = lean_apply_4(
        v_mapConst_2400_,
        lean_box(0),
        lean_box(0),
        v_a_2395_,
        v___x_2401_,
    );
    return v___x_2402_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3___redArg___boxed(
    mut v_inst_2403_: *mut LeanObject,
    mut v_a_2404_: *mut LeanObject,
    mut v_a_2405_: *mut LeanObject,
    mut v_a_2406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2407_: *mut LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_Lean_MonadCacheT_instMonad___aux__3___redArg(
        v_inst_2403_,
        v_a_2404_,
        v_a_2405_,
        v_a_2406_,
    );
    lean_dec(v_a_2406_);
    return v_res_2407_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3(
    mut v_00_u03c9_2408_: *mut LeanObject,
    mut v_00_u03b1_2409_: *mut LeanObject,
    mut v_00_u03b2_2410_: *mut LeanObject,
    mut v_m_2411_: *mut LeanObject,
    mut v_inst_2412_: *mut LeanObject,
    mut v_inst_2413_: *mut LeanObject,
    mut v_inst_2414_: *mut LeanObject,
    mut v_inst_2415_: *mut LeanObject,
    mut v_00_u03b1_2416_: *mut LeanObject,
    mut v_00_u03b2_2417_: *mut LeanObject,
    mut v_a_2418_: *mut LeanObject,
    mut v_a_2419_: *mut LeanObject,
    mut v_a_2420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2421_ = lean_ctor_get(v_inst_2415_, 0);
    lean_inc_ref(v_toApplicative_2421_);
    lean_dec_ref(v_inst_2415_);
    v_toFunctor_2422_ = lean_ctor_get(v_toApplicative_2421_, 0);
    lean_inc_ref(v_toFunctor_2422_);
    lean_dec_ref(v_toApplicative_2421_);
    v_mapConst_2423_ = lean_ctor_get(v_toFunctor_2422_, 1);
    lean_inc(v_mapConst_2423_);
    lean_dec_ref(v_toFunctor_2422_);
    lean_inc(v_a_2420_);
    v___x_2424_ = lean_apply_1(v_a_2419_, v_a_2420_);
    v___x_2425_ = lean_apply_4(
        v_mapConst_2423_,
        lean_box(0),
        lean_box(0),
        v_a_2418_,
        v___x_2424_,
    );
    return v___x_2425_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__3___boxed(
    mut v_00_u03c9_2426_: *mut LeanObject,
    mut v_00_u03b1_2427_: *mut LeanObject,
    mut v_00_u03b2_2428_: *mut LeanObject,
    mut v_m_2429_: *mut LeanObject,
    mut v_inst_2430_: *mut LeanObject,
    mut v_inst_2431_: *mut LeanObject,
    mut v_inst_2432_: *mut LeanObject,
    mut v_inst_2433_: *mut LeanObject,
    mut v_00_u03b1_2434_: *mut LeanObject,
    mut v_00_u03b2_2435_: *mut LeanObject,
    mut v_a_2436_: *mut LeanObject,
    mut v_a_2437_: *mut LeanObject,
    mut v_a_2438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2439_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2438_);
    lean_dec_ref(v_inst_2432_);
    lean_dec_ref(v_inst_2431_);
    return v_res_2439_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__5___redArg(
    mut v_inst_2440_: *mut LeanObject,
    mut v_a_2441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2442_ = lean_ctor_get(v_inst_2440_, 0);
    lean_inc_ref(v_toApplicative_2442_);
    lean_dec_ref(v_inst_2440_);
    v_toPure_2443_ = lean_ctor_get(v_toApplicative_2442_, 1);
    lean_inc(v_toPure_2443_);
    lean_dec_ref(v_toApplicative_2442_);
    v___x_2444_ = lean_apply_2(v_toPure_2443_, lean_box(0), v_a_2441_);
    return v___x_2444_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__5(
    mut v_00_u03c9_2445_: *mut LeanObject,
    mut v_00_u03b1_2446_: *mut LeanObject,
    mut v_00_u03b2_2447_: *mut LeanObject,
    mut v_m_2448_: *mut LeanObject,
    mut v_inst_2449_: *mut LeanObject,
    mut v_inst_2450_: *mut LeanObject,
    mut v_inst_2451_: *mut LeanObject,
    mut v_inst_2452_: *mut LeanObject,
    mut v_00_u03b1_2453_: *mut LeanObject,
    mut v_a_2454_: *mut LeanObject,
    mut v_a_2455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2456_ = lean_ctor_get(v_inst_2452_, 0);
    lean_inc_ref(v_toApplicative_2456_);
    lean_dec_ref(v_inst_2452_);
    v_toPure_2457_ = lean_ctor_get(v_toApplicative_2456_, 1);
    lean_inc(v_toPure_2457_);
    lean_dec_ref(v_toApplicative_2456_);
    v___x_2458_ = lean_apply_2(v_toPure_2457_, lean_box(0), v_a_2454_);
    return v___x_2458_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__5___boxed(
    mut v_00_u03c9_2459_: *mut LeanObject,
    mut v_00_u03b1_2460_: *mut LeanObject,
    mut v_00_u03b2_2461_: *mut LeanObject,
    mut v_m_2462_: *mut LeanObject,
    mut v_inst_2463_: *mut LeanObject,
    mut v_inst_2464_: *mut LeanObject,
    mut v_inst_2465_: *mut LeanObject,
    mut v_inst_2466_: *mut LeanObject,
    mut v_00_u03b1_2467_: *mut LeanObject,
    mut v_a_2468_: *mut LeanObject,
    mut v_a_2469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2470_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2469_);
    lean_dec_ref(v_inst_2465_);
    lean_dec_ref(v_inst_2464_);
    return v_res_2470_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0(
    mut v_a_2471_: *mut LeanObject,
    mut v_a_2472_: *mut LeanObject,
    mut v_x_2473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    v___x_2474_ = lean_box(0);
    lean_inc(v_a_2472_);
    v___x_2475_ = lean_apply_2(v_a_2471_, v___x_2474_, v_a_2472_);
    return v___x_2475_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed(
    mut v_a_2476_: *mut LeanObject,
    mut v_a_2477_: *mut LeanObject,
    mut v_x_2478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2479_: *mut LeanObject = core::ptr::null_mut();
    v_res_2479_ =
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0(v_a_2476_, v_a_2477_, v_x_2478_);
    lean_dec(v_a_2477_);
    return v_res_2479_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg(
    mut v_inst_2480_: *mut LeanObject,
    mut v_a_2481_: *mut LeanObject,
    mut v_a_2482_: *mut LeanObject,
    mut v_a_2483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2484_ = lean_ctor_get(v_inst_2480_, 0);
    lean_inc_ref(v_toApplicative_2484_);
    lean_dec_ref(v_inst_2480_);
    v_toSeq_2485_ = lean_ctor_get(v_toApplicative_2484_, 2);
    lean_inc(v_toSeq_2485_);
    lean_dec_ref(v_toApplicative_2484_);
    lean_inc_n(v_a_2483_, 2);
    v___f_2486_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2486_, 0, v_a_2482_);
    lean_closure_set(v___f_2486_, 1, v_a_2483_);
    v___x_2487_ = lean_apply_1(v_a_2481_, v_a_2483_);
    v___x_2488_ = lean_apply_4(
        v_toSeq_2485_,
        lean_box(0),
        lean_box(0),
        v___x_2487_,
        v___f_2486_,
    );
    return v___x_2488_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___redArg___boxed(
    mut v_inst_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
    mut v_a_2491_: *mut LeanObject,
    mut v_a_2492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2493_: *mut LeanObject = core::ptr::null_mut();
    v_res_2493_ = l_Lean_MonadCacheT_instMonad___aux__7___redArg(
        v_inst_2489_,
        v_a_2490_,
        v_a_2491_,
        v_a_2492_,
    );
    lean_dec(v_a_2492_);
    return v_res_2493_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7(
    mut v_00_u03c9_2494_: *mut LeanObject,
    mut v_00_u03b1_2495_: *mut LeanObject,
    mut v_00_u03b2_2496_: *mut LeanObject,
    mut v_m_2497_: *mut LeanObject,
    mut v_inst_2498_: *mut LeanObject,
    mut v_inst_2499_: *mut LeanObject,
    mut v_inst_2500_: *mut LeanObject,
    mut v_inst_2501_: *mut LeanObject,
    mut v_00_u03b1_2502_: *mut LeanObject,
    mut v_00_u03b2_2503_: *mut LeanObject,
    mut v_a_2504_: *mut LeanObject,
    mut v_a_2505_: *mut LeanObject,
    mut v_a_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2507_ = lean_ctor_get(v_inst_2501_, 0);
    lean_inc_ref(v_toApplicative_2507_);
    lean_dec_ref(v_inst_2501_);
    v_toSeq_2508_ = lean_ctor_get(v_toApplicative_2507_, 2);
    lean_inc(v_toSeq_2508_);
    lean_dec_ref(v_toApplicative_2507_);
    lean_inc_n(v_a_2506_, 2);
    v___f_2509_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2509_, 0, v_a_2505_);
    lean_closure_set(v___f_2509_, 1, v_a_2506_);
    v___x_2510_ = lean_apply_1(v_a_2504_, v_a_2506_);
    v___x_2511_ = lean_apply_4(
        v_toSeq_2508_,
        lean_box(0),
        lean_box(0),
        v___x_2510_,
        v___f_2509_,
    );
    return v___x_2511_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__7___boxed(
    mut v_00_u03c9_2512_: *mut LeanObject,
    mut v_00_u03b1_2513_: *mut LeanObject,
    mut v_00_u03b2_2514_: *mut LeanObject,
    mut v_m_2515_: *mut LeanObject,
    mut v_inst_2516_: *mut LeanObject,
    mut v_inst_2517_: *mut LeanObject,
    mut v_inst_2518_: *mut LeanObject,
    mut v_inst_2519_: *mut LeanObject,
    mut v_00_u03b1_2520_: *mut LeanObject,
    mut v_00_u03b2_2521_: *mut LeanObject,
    mut v_a_2522_: *mut LeanObject,
    mut v_a_2523_: *mut LeanObject,
    mut v_a_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2525_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2524_);
    lean_dec_ref(v_inst_2518_);
    lean_dec_ref(v_inst_2517_);
    return v_res_2525_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9___redArg(
    mut v_inst_2526_: *mut LeanObject,
    mut v_a_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
    mut v_a_2529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2530_ = lean_ctor_get(v_inst_2526_, 0);
    lean_inc_ref(v_toApplicative_2530_);
    lean_dec_ref(v_inst_2526_);
    v_toSeqLeft_2531_ = lean_ctor_get(v_toApplicative_2530_, 3);
    lean_inc(v_toSeqLeft_2531_);
    lean_dec_ref(v_toApplicative_2530_);
    lean_inc_n(v_a_2529_, 2);
    v___f_2532_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2532_, 0, v_a_2528_);
    lean_closure_set(v___f_2532_, 1, v_a_2529_);
    v___x_2533_ = lean_apply_1(v_a_2527_, v_a_2529_);
    v___x_2534_ = lean_apply_4(
        v_toSeqLeft_2531_,
        lean_box(0),
        lean_box(0),
        v___x_2533_,
        v___f_2532_,
    );
    return v___x_2534_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9___redArg___boxed(
    mut v_inst_2535_: *mut LeanObject,
    mut v_a_2536_: *mut LeanObject,
    mut v_a_2537_: *mut LeanObject,
    mut v_a_2538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2539_: *mut LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Lean_MonadCacheT_instMonad___aux__9___redArg(
        v_inst_2535_,
        v_a_2536_,
        v_a_2537_,
        v_a_2538_,
    );
    lean_dec(v_a_2538_);
    return v_res_2539_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9(
    mut v_00_u03c9_2540_: *mut LeanObject,
    mut v_00_u03b1_2541_: *mut LeanObject,
    mut v_00_u03b2_2542_: *mut LeanObject,
    mut v_m_2543_: *mut LeanObject,
    mut v_inst_2544_: *mut LeanObject,
    mut v_inst_2545_: *mut LeanObject,
    mut v_inst_2546_: *mut LeanObject,
    mut v_inst_2547_: *mut LeanObject,
    mut v_00_u03b1_2548_: *mut LeanObject,
    mut v_00_u03b2_2549_: *mut LeanObject,
    mut v_a_2550_: *mut LeanObject,
    mut v_a_2551_: *mut LeanObject,
    mut v_a_2552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2553_ = lean_ctor_get(v_inst_2547_, 0);
    lean_inc_ref(v_toApplicative_2553_);
    lean_dec_ref(v_inst_2547_);
    v_toSeqLeft_2554_ = lean_ctor_get(v_toApplicative_2553_, 3);
    lean_inc(v_toSeqLeft_2554_);
    lean_dec_ref(v_toApplicative_2553_);
    lean_inc_n(v_a_2552_, 2);
    v___f_2555_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2555_, 0, v_a_2551_);
    lean_closure_set(v___f_2555_, 1, v_a_2552_);
    v___x_2556_ = lean_apply_1(v_a_2550_, v_a_2552_);
    v___x_2557_ = lean_apply_4(
        v_toSeqLeft_2554_,
        lean_box(0),
        lean_box(0),
        v___x_2556_,
        v___f_2555_,
    );
    return v___x_2557_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__9___boxed(
    mut v_00_u03c9_2558_: *mut LeanObject,
    mut v_00_u03b1_2559_: *mut LeanObject,
    mut v_00_u03b2_2560_: *mut LeanObject,
    mut v_m_2561_: *mut LeanObject,
    mut v_inst_2562_: *mut LeanObject,
    mut v_inst_2563_: *mut LeanObject,
    mut v_inst_2564_: *mut LeanObject,
    mut v_inst_2565_: *mut LeanObject,
    mut v_00_u03b1_2566_: *mut LeanObject,
    mut v_00_u03b2_2567_: *mut LeanObject,
    mut v_a_2568_: *mut LeanObject,
    mut v_a_2569_: *mut LeanObject,
    mut v_a_2570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2571_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2570_);
    lean_dec_ref(v_inst_2564_);
    lean_dec_ref(v_inst_2563_);
    return v_res_2571_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11___redArg(
    mut v_inst_2572_: *mut LeanObject,
    mut v_a_2573_: *mut LeanObject,
    mut v_a_2574_: *mut LeanObject,
    mut v_a_2575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2576_ = lean_ctor_get(v_inst_2572_, 0);
    lean_inc_ref(v_toApplicative_2576_);
    lean_dec_ref(v_inst_2572_);
    v_toSeqRight_2577_ = lean_ctor_get(v_toApplicative_2576_, 4);
    lean_inc(v_toSeqRight_2577_);
    lean_dec_ref(v_toApplicative_2576_);
    lean_inc_n(v_a_2575_, 2);
    v___f_2578_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2578_, 0, v_a_2574_);
    lean_closure_set(v___f_2578_, 1, v_a_2575_);
    v___x_2579_ = lean_apply_1(v_a_2573_, v_a_2575_);
    v___x_2580_ = lean_apply_4(
        v_toSeqRight_2577_,
        lean_box(0),
        lean_box(0),
        v___x_2579_,
        v___f_2578_,
    );
    return v___x_2580_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11___redArg___boxed(
    mut v_inst_2581_: *mut LeanObject,
    mut v_a_2582_: *mut LeanObject,
    mut v_a_2583_: *mut LeanObject,
    mut v_a_2584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2585_: *mut LeanObject = core::ptr::null_mut();
    v_res_2585_ = l_Lean_MonadCacheT_instMonad___aux__11___redArg(
        v_inst_2581_,
        v_a_2582_,
        v_a_2583_,
        v_a_2584_,
    );
    lean_dec(v_a_2584_);
    return v_res_2585_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11(
    mut v_00_u03c9_2586_: *mut LeanObject,
    mut v_00_u03b1_2587_: *mut LeanObject,
    mut v_00_u03b2_2588_: *mut LeanObject,
    mut v_m_2589_: *mut LeanObject,
    mut v_inst_2590_: *mut LeanObject,
    mut v_inst_2591_: *mut LeanObject,
    mut v_inst_2592_: *mut LeanObject,
    mut v_inst_2593_: *mut LeanObject,
    mut v_00_u03b1_2594_: *mut LeanObject,
    mut v_00_u03b2_2595_: *mut LeanObject,
    mut v_a_2596_: *mut LeanObject,
    mut v_a_2597_: *mut LeanObject,
    mut v_a_2598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2599_ = lean_ctor_get(v_inst_2593_, 0);
    lean_inc_ref(v_toApplicative_2599_);
    lean_dec_ref(v_inst_2593_);
    v_toSeqRight_2600_ = lean_ctor_get(v_toApplicative_2599_, 4);
    lean_inc(v_toSeqRight_2600_);
    lean_dec_ref(v_toApplicative_2599_);
    lean_inc_n(v_a_2598_, 2);
    v___f_2601_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2601_, 0, v_a_2597_);
    lean_closure_set(v___f_2601_, 1, v_a_2598_);
    v___x_2602_ = lean_apply_1(v_a_2596_, v_a_2598_);
    v___x_2603_ = lean_apply_4(
        v_toSeqRight_2600_,
        lean_box(0),
        lean_box(0),
        v___x_2602_,
        v___f_2601_,
    );
    return v___x_2603_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__11___boxed(
    mut v_00_u03c9_2604_: *mut LeanObject,
    mut v_00_u03b1_2605_: *mut LeanObject,
    mut v_00_u03b2_2606_: *mut LeanObject,
    mut v_m_2607_: *mut LeanObject,
    mut v_inst_2608_: *mut LeanObject,
    mut v_inst_2609_: *mut LeanObject,
    mut v_inst_2610_: *mut LeanObject,
    mut v_inst_2611_: *mut LeanObject,
    mut v_00_u03b1_2612_: *mut LeanObject,
    mut v_00_u03b2_2613_: *mut LeanObject,
    mut v_a_2614_: *mut LeanObject,
    mut v_a_2615_: *mut LeanObject,
    mut v_a_2616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2617_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2616_);
    lean_dec_ref(v_inst_2610_);
    lean_dec_ref(v_inst_2609_);
    return v_res_2617_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(
    mut v_a_2618_: *mut LeanObject,
    mut v_a_2619_: *mut LeanObject,
    mut v_a_2620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2619_);
    v___x_2621_ = lean_apply_2(v_a_2618_, v_a_2620_, v_a_2619_);
    return v___x_2621_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed(
    mut v_a_2622_: *mut LeanObject,
    mut v_a_2623_: *mut LeanObject,
    mut v_a_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2625_: *mut LeanObject = core::ptr::null_mut();
    v_res_2625_ =
        l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0(v_a_2622_, v_a_2623_, v_a_2624_);
    lean_dec(v_a_2623_);
    return v_res_2625_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg(
    mut v_inst_2626_: *mut LeanObject,
    mut v_a_2627_: *mut LeanObject,
    mut v_a_2628_: *mut LeanObject,
    mut v_a_2629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2630_ = lean_ctor_get(v_inst_2626_, 1);
    lean_inc(v_toBind_2630_);
    lean_dec_ref(v_inst_2626_);
    lean_inc_n(v_a_2629_, 2);
    v___f_2631_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2631_, 0, v_a_2628_);
    lean_closure_set(v___f_2631_, 1, v_a_2629_);
    v___x_2632_ = lean_apply_1(v_a_2627_, v_a_2629_);
    v___x_2633_ = lean_apply_4(
        v_toBind_2630_,
        lean_box(0),
        lean_box(0),
        v___x_2632_,
        v___f_2631_,
    );
    return v___x_2633_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___redArg___boxed(
    mut v_inst_2634_: *mut LeanObject,
    mut v_a_2635_: *mut LeanObject,
    mut v_a_2636_: *mut LeanObject,
    mut v_a_2637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2638_: *mut LeanObject = core::ptr::null_mut();
    v_res_2638_ = l_Lean_MonadCacheT_instMonad___aux__13___redArg(
        v_inst_2634_,
        v_a_2635_,
        v_a_2636_,
        v_a_2637_,
    );
    lean_dec(v_a_2637_);
    return v_res_2638_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13(
    mut v_00_u03c9_2639_: *mut LeanObject,
    mut v_00_u03b1_2640_: *mut LeanObject,
    mut v_00_u03b2_2641_: *mut LeanObject,
    mut v_m_2642_: *mut LeanObject,
    mut v_inst_2643_: *mut LeanObject,
    mut v_inst_2644_: *mut LeanObject,
    mut v_inst_2645_: *mut LeanObject,
    mut v_inst_2646_: *mut LeanObject,
    mut v_00_u03b1_2647_: *mut LeanObject,
    mut v_00_u03b2_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
    mut v_a_2651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2652_ = lean_ctor_get(v_inst_2646_, 1);
    lean_inc(v_toBind_2652_);
    lean_dec_ref(v_inst_2646_);
    lean_inc_n(v_a_2651_, 2);
    v___f_2653_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__13___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2653_, 0, v_a_2650_);
    lean_closure_set(v___f_2653_, 1, v_a_2651_);
    v___x_2654_ = lean_apply_1(v_a_2649_, v_a_2651_);
    v___x_2655_ = lean_apply_4(
        v_toBind_2652_,
        lean_box(0),
        lean_box(0),
        v___x_2654_,
        v___f_2653_,
    );
    return v___x_2655_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___aux__13___boxed(
    mut v_00_u03c9_2656_: *mut LeanObject,
    mut v_00_u03b1_2657_: *mut LeanObject,
    mut v_00_u03b2_2658_: *mut LeanObject,
    mut v_m_2659_: *mut LeanObject,
    mut v_inst_2660_: *mut LeanObject,
    mut v_inst_2661_: *mut LeanObject,
    mut v_inst_2662_: *mut LeanObject,
    mut v_inst_2663_: *mut LeanObject,
    mut v_00_u03b1_2664_: *mut LeanObject,
    mut v_00_u03b2_2665_: *mut LeanObject,
    mut v_a_2666_: *mut LeanObject,
    mut v_a_2667_: *mut LeanObject,
    mut v_a_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2669_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2668_);
    lean_dec_ref(v_inst_2662_);
    lean_dec_ref(v_inst_2661_);
    return v_res_2669_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad___redArg(
    mut v_inst_2670_: *mut LeanObject,
    mut v_inst_2671_: *mut LeanObject,
    mut v_inst_2672_: *mut LeanObject,
    mut v_inst_2673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_2673_, 6);
    lean_inc_ref_n(v_inst_2672_, 6);
    lean_inc_ref_n(v_inst_2671_, 6);
    v___x_2674_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__1___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    lean_closure_set(v___x_2674_, 0, lean_box(0));
    lean_closure_set(v___x_2674_, 1, lean_box(0));
    lean_closure_set(v___x_2674_, 2, lean_box(0));
    lean_closure_set(v___x_2674_, 3, lean_box(0));
    lean_closure_set(v___x_2674_, 4, v_inst_2670_);
    lean_closure_set(v___x_2674_, 5, v_inst_2671_);
    lean_closure_set(v___x_2674_, 6, v_inst_2672_);
    lean_closure_set(v___x_2674_, 7, v_inst_2673_);
    v___x_2675_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__3___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    lean_closure_set(v___x_2675_, 0, lean_box(0));
    lean_closure_set(v___x_2675_, 1, lean_box(0));
    lean_closure_set(v___x_2675_, 2, lean_box(0));
    lean_closure_set(v___x_2675_, 3, lean_box(0));
    lean_closure_set(v___x_2675_, 4, v_inst_2670_);
    lean_closure_set(v___x_2675_, 5, v_inst_2671_);
    lean_closure_set(v___x_2675_, 6, v_inst_2672_);
    lean_closure_set(v___x_2675_, 7, v_inst_2673_);
    v___x_2676_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2676_, 0, v___x_2674_);
    lean_ctor_set(v___x_2676_, 1, v___x_2675_);
    v___x_2677_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__5___boxed as *mut core::ffi::c_void,
        11,
        8,
    );
    lean_closure_set(v___x_2677_, 0, lean_box(0));
    lean_closure_set(v___x_2677_, 1, lean_box(0));
    lean_closure_set(v___x_2677_, 2, lean_box(0));
    lean_closure_set(v___x_2677_, 3, lean_box(0));
    lean_closure_set(v___x_2677_, 4, v_inst_2670_);
    lean_closure_set(v___x_2677_, 5, v_inst_2671_);
    lean_closure_set(v___x_2677_, 6, v_inst_2672_);
    lean_closure_set(v___x_2677_, 7, v_inst_2673_);
    v___x_2678_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    lean_closure_set(v___x_2678_, 0, lean_box(0));
    lean_closure_set(v___x_2678_, 1, lean_box(0));
    lean_closure_set(v___x_2678_, 2, lean_box(0));
    lean_closure_set(v___x_2678_, 3, lean_box(0));
    lean_closure_set(v___x_2678_, 4, v_inst_2670_);
    lean_closure_set(v___x_2678_, 5, v_inst_2671_);
    lean_closure_set(v___x_2678_, 6, v_inst_2672_);
    lean_closure_set(v___x_2678_, 7, v_inst_2673_);
    v___x_2679_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__9___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    lean_closure_set(v___x_2679_, 0, lean_box(0));
    lean_closure_set(v___x_2679_, 1, lean_box(0));
    lean_closure_set(v___x_2679_, 2, lean_box(0));
    lean_closure_set(v___x_2679_, 3, lean_box(0));
    lean_closure_set(v___x_2679_, 4, v_inst_2670_);
    lean_closure_set(v___x_2679_, 5, v_inst_2671_);
    lean_closure_set(v___x_2679_, 6, v_inst_2672_);
    lean_closure_set(v___x_2679_, 7, v_inst_2673_);
    v___x_2680_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__11___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    lean_closure_set(v___x_2680_, 0, lean_box(0));
    lean_closure_set(v___x_2680_, 1, lean_box(0));
    lean_closure_set(v___x_2680_, 2, lean_box(0));
    lean_closure_set(v___x_2680_, 3, lean_box(0));
    lean_closure_set(v___x_2680_, 4, v_inst_2670_);
    lean_closure_set(v___x_2680_, 5, v_inst_2671_);
    lean_closure_set(v___x_2680_, 6, v_inst_2672_);
    lean_closure_set(v___x_2680_, 7, v_inst_2673_);
    v___x_2681_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2681_, 0, v___x_2676_);
    lean_ctor_set(v___x_2681_, 1, v___x_2677_);
    lean_ctor_set(v___x_2681_, 2, v___x_2678_);
    lean_ctor_set(v___x_2681_, 3, v___x_2679_);
    lean_ctor_set(v___x_2681_, 4, v___x_2680_);
    v___x_2682_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    lean_closure_set(v___x_2682_, 0, lean_box(0));
    lean_closure_set(v___x_2682_, 1, lean_box(0));
    lean_closure_set(v___x_2682_, 2, lean_box(0));
    lean_closure_set(v___x_2682_, 3, lean_box(0));
    lean_closure_set(v___x_2682_, 4, v_inst_2670_);
    lean_closure_set(v___x_2682_, 5, v_inst_2671_);
    lean_closure_set(v___x_2682_, 6, v_inst_2672_);
    lean_closure_set(v___x_2682_, 7, v_inst_2673_);
    v___x_2683_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2683_, 0, v___x_2681_);
    lean_ctor_set(v___x_2683_, 1, v___x_2682_);
    return v___x_2683_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonad(
    mut v_00_u03c9_2684_: *mut LeanObject,
    mut v_00_u03b1_2685_: *mut LeanObject,
    mut v_00_u03b2_2686_: *mut LeanObject,
    mut v_m_2687_: *mut LeanObject,
    mut v_inst_2688_: *mut LeanObject,
    mut v_inst_2689_: *mut LeanObject,
    mut v_inst_2690_: *mut LeanObject,
    mut v_inst_2691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    v___x_2692_ = l_Lean_MonadCacheT_instMonad___redArg(
        v_inst_2688_,
        v_inst_2689_,
        v_inst_2690_,
        v_inst_2691_,
    );
    return v___x_2692_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1___redArg(
    mut v_x_2693_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_2693_);
    return v_x_2693_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1___redArg___boxed(
    mut v_x_2694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2695_: *mut LeanObject = core::ptr::null_mut();
    v_res_2695_ = l_Lean_MonadCacheT_instMonadLift___aux__1___redArg(v_x_2694_);
    lean_dec(v_x_2694_);
    return v_res_2695_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1(
    mut v_00_u03c9_2696_: *mut LeanObject,
    mut v_00_u03b1_2697_: *mut LeanObject,
    mut v_00_u03b2_2698_: *mut LeanObject,
    mut v_m_2699_: *mut LeanObject,
    mut v_inst_2700_: *mut LeanObject,
    mut v_inst_2701_: *mut LeanObject,
    mut v_inst_2702_: *mut LeanObject,
    mut v_00_u03b1_2703_: *mut LeanObject,
    mut v_x_2704_: *mut LeanObject,
    mut v_a_2705_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_2704_);
    return v_x_2704_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___aux__1___boxed(
    mut v_00_u03c9_2706_: *mut LeanObject,
    mut v_00_u03b1_2707_: *mut LeanObject,
    mut v_00_u03b2_2708_: *mut LeanObject,
    mut v_m_2709_: *mut LeanObject,
    mut v_inst_2710_: *mut LeanObject,
    mut v_inst_2711_: *mut LeanObject,
    mut v_inst_2712_: *mut LeanObject,
    mut v_00_u03b1_2713_: *mut LeanObject,
    mut v_x_2714_: *mut LeanObject,
    mut v_a_2715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2716_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2715_);
    lean_dec(v_x_2714_);
    lean_dec_ref(v_inst_2712_);
    lean_dec_ref(v_inst_2711_);
    return v_res_2716_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift___redArg(
    mut v_inst_2717_: *mut LeanObject,
    mut v_inst_2718_: *mut LeanObject,
    mut v_inst_2719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    v___x_2720_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    lean_closure_set(v___x_2720_, 0, lean_box(0));
    lean_closure_set(v___x_2720_, 1, lean_box(0));
    lean_closure_set(v___x_2720_, 2, lean_box(0));
    lean_closure_set(v___x_2720_, 3, lean_box(0));
    lean_closure_set(v___x_2720_, 4, v_inst_2717_);
    lean_closure_set(v___x_2720_, 5, v_inst_2718_);
    lean_closure_set(v___x_2720_, 6, v_inst_2719_);
    return v___x_2720_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadLift(
    mut v_00_u03c9_2721_: *mut LeanObject,
    mut v_00_u03b1_2722_: *mut LeanObject,
    mut v_00_u03b2_2723_: *mut LeanObject,
    mut v_m_2724_: *mut LeanObject,
    mut v_inst_2725_: *mut LeanObject,
    mut v_inst_2726_: *mut LeanObject,
    mut v_inst_2727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    v___x_2728_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    lean_closure_set(v___x_2728_, 0, lean_box(0));
    lean_closure_set(v___x_2728_, 1, lean_box(0));
    lean_closure_set(v___x_2728_, 2, lean_box(0));
    lean_closure_set(v___x_2728_, 3, lean_box(0));
    lean_closure_set(v___x_2728_, 4, v_inst_2725_);
    lean_closure_set(v___x_2728_, 5, v_inst_2726_);
    lean_closure_set(v___x_2728_, 6, v_inst_2727_);
    return v___x_2728_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__1___redArg(
    mut v_inst_2729_: *mut LeanObject,
    mut v_a_2730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    v_throw_2731_ = lean_ctor_get(v_inst_2729_, 0);
    lean_inc(v_throw_2731_);
    lean_dec_ref(v_inst_2729_);
    v___x_2732_ = lean_apply_2(v_throw_2731_, lean_box(0), v_a_2730_);
    return v___x_2732_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__1(
    mut v_00_u03c9_2733_: *mut LeanObject,
    mut v_00_u03b1_2734_: *mut LeanObject,
    mut v_00_u03b2_2735_: *mut LeanObject,
    mut v_m_2736_: *mut LeanObject,
    mut v_inst_2737_: *mut LeanObject,
    mut v_inst_2738_: *mut LeanObject,
    mut v_inst_2739_: *mut LeanObject,
    mut v_00_u03b5_2740_: *mut LeanObject,
    mut v_inst_2741_: *mut LeanObject,
    mut v_00_u03b1_2742_: *mut LeanObject,
    mut v_a_2743_: *mut LeanObject,
    mut v_a_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    v_throw_2745_ = lean_ctor_get(v_inst_2741_, 0);
    lean_inc(v_throw_2745_);
    lean_dec_ref(v_inst_2741_);
    v___x_2746_ = lean_apply_2(v_throw_2745_, lean_box(0), v_a_2743_);
    return v___x_2746_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__1___boxed(
    mut v_00_u03c9_2747_: *mut LeanObject,
    mut v_00_u03b1_2748_: *mut LeanObject,
    mut v_00_u03b2_2749_: *mut LeanObject,
    mut v_m_2750_: *mut LeanObject,
    mut v_inst_2751_: *mut LeanObject,
    mut v_inst_2752_: *mut LeanObject,
    mut v_inst_2753_: *mut LeanObject,
    mut v_00_u03b5_2754_: *mut LeanObject,
    mut v_inst_2755_: *mut LeanObject,
    mut v_00_u03b1_2756_: *mut LeanObject,
    mut v_a_2757_: *mut LeanObject,
    mut v_a_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2759_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2758_);
    lean_dec_ref(v_inst_2753_);
    lean_dec_ref(v_inst_2752_);
    return v_res_2759_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0(
    mut v_c_2760_: *mut LeanObject,
    mut v_s_2761_: *mut LeanObject,
    mut v_e_2762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_s_2761_);
    v___x_2763_ = lean_apply_2(v_c_2760_, v_e_2762_, v_s_2761_);
    return v___x_2763_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed(
    mut v_c_2764_: *mut LeanObject,
    mut v_s_2765_: *mut LeanObject,
    mut v_e_2766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2767_: *mut LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0(
        v_c_2764_, v_s_2765_, v_e_2766_,
    );
    lean_dec(v_s_2765_);
    return v_res_2767_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg(
    mut v_inst_2768_: *mut LeanObject,
    mut v_x_2769_: *mut LeanObject,
    mut v_c_2770_: *mut LeanObject,
    mut v_s_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_2772_ = lean_ctor_get(v_inst_2768_, 1);
    lean_inc(v_tryCatch_2772_);
    lean_dec_ref(v_inst_2768_);
    lean_inc_n(v_s_2771_, 2);
    v___f_2773_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2773_, 0, v_c_2770_);
    lean_closure_set(v___f_2773_, 1, v_s_2771_);
    v___x_2774_ = lean_apply_1(v_x_2769_, v_s_2771_);
    v___x_2775_ = lean_apply_3(v_tryCatch_2772_, lean_box(0), v___x_2774_, v___f_2773_);
    return v___x_2775_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___boxed(
    mut v_inst_2776_: *mut LeanObject,
    mut v_x_2777_: *mut LeanObject,
    mut v_c_2778_: *mut LeanObject,
    mut v_s_2779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2780_: *mut LeanObject = core::ptr::null_mut();
    v_res_2780_ = l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg(
        v_inst_2776_,
        v_x_2777_,
        v_c_2778_,
        v_s_2779_,
    );
    lean_dec(v_s_2779_);
    return v_res_2780_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3(
    mut v_00_u03c9_2781_: *mut LeanObject,
    mut v_00_u03b1_2782_: *mut LeanObject,
    mut v_00_u03b2_2783_: *mut LeanObject,
    mut v_m_2784_: *mut LeanObject,
    mut v_inst_2785_: *mut LeanObject,
    mut v_inst_2786_: *mut LeanObject,
    mut v_inst_2787_: *mut LeanObject,
    mut v_00_u03b5_2788_: *mut LeanObject,
    mut v_inst_2789_: *mut LeanObject,
    mut v_00_u03b1_2790_: *mut LeanObject,
    mut v_x_2791_: *mut LeanObject,
    mut v_c_2792_: *mut LeanObject,
    mut v_s_2793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_2794_ = lean_ctor_get(v_inst_2789_, 1);
    lean_inc(v_tryCatch_2794_);
    lean_dec_ref(v_inst_2789_);
    lean_inc_n(v_s_2793_, 2);
    v___f_2795_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__3___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2795_, 0, v_c_2792_);
    lean_closure_set(v___f_2795_, 1, v_s_2793_);
    v___x_2796_ = lean_apply_1(v_x_2791_, v_s_2793_);
    v___x_2797_ = lean_apply_3(v_tryCatch_2794_, lean_box(0), v___x_2796_, v___f_2795_);
    return v___x_2797_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___aux__3___boxed(
    mut v_00_u03c9_2798_: *mut LeanObject,
    mut v_00_u03b1_2799_: *mut LeanObject,
    mut v_00_u03b2_2800_: *mut LeanObject,
    mut v_m_2801_: *mut LeanObject,
    mut v_inst_2802_: *mut LeanObject,
    mut v_inst_2803_: *mut LeanObject,
    mut v_inst_2804_: *mut LeanObject,
    mut v_00_u03b5_2805_: *mut LeanObject,
    mut v_inst_2806_: *mut LeanObject,
    mut v_00_u03b1_2807_: *mut LeanObject,
    mut v_x_2808_: *mut LeanObject,
    mut v_c_2809_: *mut LeanObject,
    mut v_s_2810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2811_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_s_2810_);
    lean_dec_ref(v_inst_2804_);
    lean_dec_ref(v_inst_2803_);
    return v_res_2811_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf___redArg(
    mut v_inst_2812_: *mut LeanObject,
    mut v_inst_2813_: *mut LeanObject,
    mut v_inst_2814_: *mut LeanObject,
    mut v_inst_2815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_2815_);
    lean_inc_ref(v_inst_2814_);
    lean_inc_ref(v_inst_2813_);
    v___x_2816_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__1___boxed as *mut core::ffi::c_void,
        12,
        9,
    );
    lean_closure_set(v___x_2816_, 0, lean_box(0));
    lean_closure_set(v___x_2816_, 1, lean_box(0));
    lean_closure_set(v___x_2816_, 2, lean_box(0));
    lean_closure_set(v___x_2816_, 3, lean_box(0));
    lean_closure_set(v___x_2816_, 4, v_inst_2812_);
    lean_closure_set(v___x_2816_, 5, v_inst_2813_);
    lean_closure_set(v___x_2816_, 6, v_inst_2814_);
    lean_closure_set(v___x_2816_, 7, lean_box(0));
    lean_closure_set(v___x_2816_, 8, v_inst_2815_);
    v___x_2817_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadExceptOf___aux__3___boxed as *mut core::ffi::c_void,
        13,
        9,
    );
    lean_closure_set(v___x_2817_, 0, lean_box(0));
    lean_closure_set(v___x_2817_, 1, lean_box(0));
    lean_closure_set(v___x_2817_, 2, lean_box(0));
    lean_closure_set(v___x_2817_, 3, lean_box(0));
    lean_closure_set(v___x_2817_, 4, v_inst_2812_);
    lean_closure_set(v___x_2817_, 5, v_inst_2813_);
    lean_closure_set(v___x_2817_, 6, v_inst_2814_);
    lean_closure_set(v___x_2817_, 7, lean_box(0));
    lean_closure_set(v___x_2817_, 8, v_inst_2815_);
    v___x_2818_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2818_, 0, v___x_2816_);
    lean_ctor_set(v___x_2818_, 1, v___x_2817_);
    return v___x_2818_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadExceptOf(
    mut v_00_u03c9_2819_: *mut LeanObject,
    mut v_00_u03b1_2820_: *mut LeanObject,
    mut v_00_u03b2_2821_: *mut LeanObject,
    mut v_m_2822_: *mut LeanObject,
    mut v_inst_2823_: *mut LeanObject,
    mut v_inst_2824_: *mut LeanObject,
    mut v_inst_2825_: *mut LeanObject,
    mut v_00_u03b5_2826_: *mut LeanObject,
    mut v_inst_2827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    v___x_2828_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(
        v_inst_2823_,
        v_inst_2824_,
        v_inst_2825_,
        v_inst_2827_,
    );
    return v___x_2828_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0(
    mut v_a_2829_: *mut LeanObject,
    mut v_00_u03b2_2830_: *mut LeanObject,
    mut v_x_2831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2829_);
    v___x_2832_ = lean_apply_1(v_x_2831_, v_a_2829_);
    return v___x_2832_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed(
    mut v_a_2833_: *mut LeanObject,
    mut v_00_u03b2_2834_: *mut LeanObject,
    mut v_x_2835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2836_: *mut LeanObject = core::ptr::null_mut();
    v_res_2836_ = l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0(
        v_a_2833_,
        v_00_u03b2_2834_,
        v_x_2835_,
    );
    lean_dec(v_a_2833_);
    return v_res_2836_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg(
    mut v_a_2837_: *mut LeanObject,
    mut v_a_2838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2838_);
    v___f_2839_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2839_, 0, v_a_2838_);
    v___x_2840_ = lean_apply_1(v_a_2837_, v___f_2839_);
    return v___x_2840_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___boxed(
    mut v_a_2841_: *mut LeanObject,
    mut v_a_2842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2843_: *mut LeanObject = core::ptr::null_mut();
    v_res_2843_ = l_Lean_MonadCacheT_instMonadControl___aux__1___redArg(v_a_2841_, v_a_2842_);
    lean_dec(v_a_2842_);
    return v_res_2843_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1(
    mut v_00_u03c9_2844_: *mut LeanObject,
    mut v_00_u03b1_2845_: *mut LeanObject,
    mut v_00_u03b2_2846_: *mut LeanObject,
    mut v_m_2847_: *mut LeanObject,
    mut v_inst_2848_: *mut LeanObject,
    mut v_inst_2849_: *mut LeanObject,
    mut v_inst_2850_: *mut LeanObject,
    mut v_00_u03b1_2851_: *mut LeanObject,
    mut v_a_2852_: *mut LeanObject,
    mut v_a_2853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2853_);
    v___f_2854_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2854_, 0, v_a_2853_);
    v___x_2855_ = lean_apply_1(v_a_2852_, v___f_2854_);
    return v___x_2855_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__1___boxed(
    mut v_00_u03c9_2856_: *mut LeanObject,
    mut v_00_u03b1_2857_: *mut LeanObject,
    mut v_00_u03b2_2858_: *mut LeanObject,
    mut v_m_2859_: *mut LeanObject,
    mut v_inst_2860_: *mut LeanObject,
    mut v_inst_2861_: *mut LeanObject,
    mut v_inst_2862_: *mut LeanObject,
    mut v_00_u03b1_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
    mut v_a_2865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2866_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2865_);
    lean_dec_ref(v_inst_2862_);
    lean_dec_ref(v_inst_2861_);
    return v_res_2866_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3___redArg(
    mut v_a_2867_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_2867_);
    return v_a_2867_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3___redArg___boxed(
    mut v_a_2868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2869_: *mut LeanObject = core::ptr::null_mut();
    v_res_2869_ = l_Lean_MonadCacheT_instMonadControl___aux__3___redArg(v_a_2868_);
    lean_dec(v_a_2868_);
    return v_res_2869_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3(
    mut v_00_u03c9_2870_: *mut LeanObject,
    mut v_00_u03b1_2871_: *mut LeanObject,
    mut v_00_u03b2_2872_: *mut LeanObject,
    mut v_m_2873_: *mut LeanObject,
    mut v_inst_2874_: *mut LeanObject,
    mut v_inst_2875_: *mut LeanObject,
    mut v_inst_2876_: *mut LeanObject,
    mut v_00_u03b1_2877_: *mut LeanObject,
    mut v_a_2878_: *mut LeanObject,
    mut v_a_2879_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_2878_);
    return v_a_2878_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___aux__3___boxed(
    mut v_00_u03c9_2880_: *mut LeanObject,
    mut v_00_u03b1_2881_: *mut LeanObject,
    mut v_00_u03b2_2882_: *mut LeanObject,
    mut v_m_2883_: *mut LeanObject,
    mut v_inst_2884_: *mut LeanObject,
    mut v_inst_2885_: *mut LeanObject,
    mut v_inst_2886_: *mut LeanObject,
    mut v_00_u03b1_2887_: *mut LeanObject,
    mut v_a_2888_: *mut LeanObject,
    mut v_a_2889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2890_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2889_);
    lean_dec(v_a_2888_);
    lean_dec_ref(v_inst_2886_);
    lean_dec_ref(v_inst_2885_);
    return v_res_2890_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl___redArg(
    mut v_inst_2891_: *mut LeanObject,
    mut v_inst_2892_: *mut LeanObject,
    mut v_inst_2893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_2893_);
    lean_inc_ref(v_inst_2892_);
    v___x_2894_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__1___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    lean_closure_set(v___x_2894_, 0, lean_box(0));
    lean_closure_set(v___x_2894_, 1, lean_box(0));
    lean_closure_set(v___x_2894_, 2, lean_box(0));
    lean_closure_set(v___x_2894_, 3, lean_box(0));
    lean_closure_set(v___x_2894_, 4, v_inst_2891_);
    lean_closure_set(v___x_2894_, 5, v_inst_2892_);
    lean_closure_set(v___x_2894_, 6, v_inst_2893_);
    v___x_2895_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadControl___aux__3___boxed as *mut core::ffi::c_void,
        10,
        7,
    );
    lean_closure_set(v___x_2895_, 0, lean_box(0));
    lean_closure_set(v___x_2895_, 1, lean_box(0));
    lean_closure_set(v___x_2895_, 2, lean_box(0));
    lean_closure_set(v___x_2895_, 3, lean_box(0));
    lean_closure_set(v___x_2895_, 4, v_inst_2891_);
    lean_closure_set(v___x_2895_, 5, v_inst_2892_);
    lean_closure_set(v___x_2895_, 6, v_inst_2893_);
    v___x_2896_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2896_, 0, v___x_2894_);
    lean_ctor_set(v___x_2896_, 1, v___x_2895_);
    return v___x_2896_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadControl(
    mut v_00_u03c9_2897_: *mut LeanObject,
    mut v_00_u03b1_2898_: *mut LeanObject,
    mut v_00_u03b2_2899_: *mut LeanObject,
    mut v_m_2900_: *mut LeanObject,
    mut v_inst_2901_: *mut LeanObject,
    mut v_inst_2902_: *mut LeanObject,
    mut v_inst_2903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    v___x_2904_ =
        l_Lean_MonadCacheT_instMonadControl___redArg(v_inst_2901_, v_inst_2902_, v_inst_2903_);
    return v___x_2904_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0(
    mut v_f_2905_: *mut LeanObject,
    mut v_a_2906_: *mut LeanObject,
    mut v_a_x3f_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2906_);
    v___x_2908_ = lean_apply_2(v_f_2905_, v_a_x3f_2907_, v_a_2906_);
    return v___x_2908_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed(
    mut v_f_2909_: *mut LeanObject,
    mut v_a_2910_: *mut LeanObject,
    mut v_a_x3f_2911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2912_: *mut LeanObject = core::ptr::null_mut();
    v_res_2912_ = l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0(
        v_f_2909_,
        v_a_2910_,
        v_a_x3f_2911_,
    );
    lean_dec(v_a_2910_);
    return v_res_2912_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg(
    mut v_inst_2913_: *mut LeanObject,
    mut v_x_2914_: *mut LeanObject,
    mut v_f_2915_: *mut LeanObject,
    mut v_a_2916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_a_2916_, 2);
    v___f_2917_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2917_, 0, v_f_2915_);
    lean_closure_set(v___f_2917_, 1, v_a_2916_);
    v___x_2918_ = lean_apply_1(v_x_2914_, v_a_2916_);
    v___x_2919_ = lean_apply_4(
        v_inst_2913_,
        lean_box(0),
        lean_box(0),
        v___x_2918_,
        v___f_2917_,
    );
    return v___x_2919_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___boxed(
    mut v_inst_2920_: *mut LeanObject,
    mut v_x_2921_: *mut LeanObject,
    mut v_f_2922_: *mut LeanObject,
    mut v_a_2923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2924_: *mut LeanObject = core::ptr::null_mut();
    v_res_2924_ = l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg(
        v_inst_2920_,
        v_x_2921_,
        v_f_2922_,
        v_a_2923_,
    );
    lean_dec(v_a_2923_);
    return v_res_2924_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1(
    mut v_00_u03c9_2925_: *mut LeanObject,
    mut v_00_u03b1_2926_: *mut LeanObject,
    mut v_00_u03b2_2927_: *mut LeanObject,
    mut v_m_2928_: *mut LeanObject,
    mut v_inst_2929_: *mut LeanObject,
    mut v_inst_2930_: *mut LeanObject,
    mut v_inst_2931_: *mut LeanObject,
    mut v_inst_2932_: *mut LeanObject,
    mut v_00_u03b1_2933_: *mut LeanObject,
    mut v_00_u03b2_2934_: *mut LeanObject,
    mut v_x_2935_: *mut LeanObject,
    mut v_f_2936_: *mut LeanObject,
    mut v_a_2937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_a_2937_, 2);
    v___f_2938_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2938_, 0, v_f_2936_);
    lean_closure_set(v___f_2938_, 1, v_a_2937_);
    v___x_2939_ = lean_apply_1(v_x_2935_, v_a_2937_);
    v___x_2940_ = lean_apply_4(
        v_inst_2932_,
        lean_box(0),
        lean_box(0),
        v___x_2939_,
        v___f_2938_,
    );
    return v___x_2940_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed(
    mut v_00_u03c9_2941_: *mut LeanObject,
    mut v_00_u03b1_2942_: *mut LeanObject,
    mut v_00_u03b2_2943_: *mut LeanObject,
    mut v_m_2944_: *mut LeanObject,
    mut v_inst_2945_: *mut LeanObject,
    mut v_inst_2946_: *mut LeanObject,
    mut v_inst_2947_: *mut LeanObject,
    mut v_inst_2948_: *mut LeanObject,
    mut v_00_u03b1_2949_: *mut LeanObject,
    mut v_00_u03b2_2950_: *mut LeanObject,
    mut v_x_2951_: *mut LeanObject,
    mut v_f_2952_: *mut LeanObject,
    mut v_a_2953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2954_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2953_);
    lean_dec_ref(v_inst_2947_);
    lean_dec_ref(v_inst_2946_);
    return v_res_2954_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally___redArg(
    mut v_inst_2955_: *mut LeanObject,
    mut v_inst_2956_: *mut LeanObject,
    mut v_inst_2957_: *mut LeanObject,
    mut v_inst_2958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    v___x_2959_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    lean_closure_set(v___x_2959_, 0, lean_box(0));
    lean_closure_set(v___x_2959_, 1, lean_box(0));
    lean_closure_set(v___x_2959_, 2, lean_box(0));
    lean_closure_set(v___x_2959_, 3, lean_box(0));
    lean_closure_set(v___x_2959_, 4, v_inst_2955_);
    lean_closure_set(v___x_2959_, 5, v_inst_2956_);
    lean_closure_set(v___x_2959_, 6, v_inst_2957_);
    lean_closure_set(v___x_2959_, 7, v_inst_2958_);
    return v___x_2959_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadFinally(
    mut v_00_u03c9_2960_: *mut LeanObject,
    mut v_00_u03b1_2961_: *mut LeanObject,
    mut v_00_u03b2_2962_: *mut LeanObject,
    mut v_m_2963_: *mut LeanObject,
    mut v_inst_2964_: *mut LeanObject,
    mut v_inst_2965_: *mut LeanObject,
    mut v_inst_2966_: *mut LeanObject,
    mut v_inst_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    v___x_2968_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        13,
        8,
    );
    lean_closure_set(v___x_2968_, 0, lean_box(0));
    lean_closure_set(v___x_2968_, 1, lean_box(0));
    lean_closure_set(v___x_2968_, 2, lean_box(0));
    lean_closure_set(v___x_2968_, 3, lean_box(0));
    lean_closure_set(v___x_2968_, 4, v_inst_2964_);
    lean_closure_set(v___x_2968_, 5, v_inst_2965_);
    lean_closure_set(v___x_2968_, 6, v_inst_2966_);
    lean_closure_set(v___x_2968_, 7, v_inst_2967_);
    return v___x_2968_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1___redArg(
    mut v_inst_2969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRef_2970_: *mut LeanObject = core::ptr::null_mut();
    v_getRef_2970_ = lean_ctor_get(v_inst_2969_, 0);
    lean_inc(v_getRef_2970_);
    return v_getRef_2970_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1___redArg___boxed(
    mut v_inst_2971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2972_: *mut LeanObject = core::ptr::null_mut();
    v_res_2972_ = l_Lean_MonadCacheT_instMonadRef___aux__1___redArg(v_inst_2971_);
    lean_dec_ref(v_inst_2971_);
    return v_res_2972_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1(
    mut v_00_u03c9_2973_: *mut LeanObject,
    mut v_00_u03b1_2974_: *mut LeanObject,
    mut v_00_u03b2_2975_: *mut LeanObject,
    mut v_m_2976_: *mut LeanObject,
    mut v_inst_2977_: *mut LeanObject,
    mut v_inst_2978_: *mut LeanObject,
    mut v_inst_2979_: *mut LeanObject,
    mut v_inst_2980_: *mut LeanObject,
    mut v_a_2981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRef_2982_: *mut LeanObject = core::ptr::null_mut();
    v_getRef_2982_ = lean_ctor_get(v_inst_2980_, 0);
    lean_inc(v_getRef_2982_);
    return v_getRef_2982_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__1___boxed(
    mut v_00_u03c9_2983_: *mut LeanObject,
    mut v_00_u03b1_2984_: *mut LeanObject,
    mut v_00_u03b2_2985_: *mut LeanObject,
    mut v_m_2986_: *mut LeanObject,
    mut v_inst_2987_: *mut LeanObject,
    mut v_inst_2988_: *mut LeanObject,
    mut v_inst_2989_: *mut LeanObject,
    mut v_inst_2990_: *mut LeanObject,
    mut v_a_2991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2992_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2991_);
    lean_dec_ref(v_inst_2990_);
    lean_dec_ref(v_inst_2989_);
    lean_dec_ref(v_inst_2988_);
    return v_res_2992_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3___redArg(
    mut v_inst_2993_: *mut LeanObject,
    mut v_ref_2994_: *mut LeanObject,
    mut v_x_2995_: *mut LeanObject,
    mut v_a_2996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_withRef_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    v_withRef_2997_ = lean_ctor_get(v_inst_2993_, 1);
    lean_inc(v_withRef_2997_);
    lean_dec_ref(v_inst_2993_);
    lean_inc(v_a_2996_);
    v___x_2998_ = lean_apply_1(v_x_2995_, v_a_2996_);
    v___x_2999_ = lean_apply_3(v_withRef_2997_, lean_box(0), v_ref_2994_, v___x_2998_);
    return v___x_2999_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3___redArg___boxed(
    mut v_inst_3000_: *mut LeanObject,
    mut v_ref_3001_: *mut LeanObject,
    mut v_x_3002_: *mut LeanObject,
    mut v_a_3003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3004_: *mut LeanObject = core::ptr::null_mut();
    v_res_3004_ = l_Lean_MonadCacheT_instMonadRef___aux__3___redArg(
        v_inst_3000_,
        v_ref_3001_,
        v_x_3002_,
        v_a_3003_,
    );
    lean_dec(v_a_3003_);
    return v_res_3004_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3(
    mut v_00_u03c9_3005_: *mut LeanObject,
    mut v_00_u03b1_3006_: *mut LeanObject,
    mut v_00_u03b2_3007_: *mut LeanObject,
    mut v_m_3008_: *mut LeanObject,
    mut v_inst_3009_: *mut LeanObject,
    mut v_inst_3010_: *mut LeanObject,
    mut v_inst_3011_: *mut LeanObject,
    mut v_inst_3012_: *mut LeanObject,
    mut v_00_u03b1_3013_: *mut LeanObject,
    mut v_ref_3014_: *mut LeanObject,
    mut v_x_3015_: *mut LeanObject,
    mut v_a_3016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_withRef_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    v_withRef_3017_ = lean_ctor_get(v_inst_3012_, 1);
    lean_inc(v_withRef_3017_);
    lean_dec_ref(v_inst_3012_);
    lean_inc(v_a_3016_);
    v___x_3018_ = lean_apply_1(v_x_3015_, v_a_3016_);
    v___x_3019_ = lean_apply_3(v_withRef_3017_, lean_box(0), v_ref_3014_, v___x_3018_);
    return v___x_3019_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___aux__3___boxed(
    mut v_00_u03c9_3020_: *mut LeanObject,
    mut v_00_u03b1_3021_: *mut LeanObject,
    mut v_00_u03b2_3022_: *mut LeanObject,
    mut v_m_3023_: *mut LeanObject,
    mut v_inst_3024_: *mut LeanObject,
    mut v_inst_3025_: *mut LeanObject,
    mut v_inst_3026_: *mut LeanObject,
    mut v_inst_3027_: *mut LeanObject,
    mut v_00_u03b1_3028_: *mut LeanObject,
    mut v_ref_3029_: *mut LeanObject,
    mut v_x_3030_: *mut LeanObject,
    mut v_a_3031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3032_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3031_);
    lean_dec_ref(v_inst_3026_);
    lean_dec_ref(v_inst_3025_);
    return v_res_3032_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef___redArg(
    mut v_inst_3033_: *mut LeanObject,
    mut v_inst_3034_: *mut LeanObject,
    mut v_inst_3035_: *mut LeanObject,
    mut v_inst_3036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_3036_);
    lean_inc_ref(v_inst_3035_);
    lean_inc_ref(v_inst_3034_);
    v___x_3037_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadRef___aux__1___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___x_3037_, 0, lean_box(0));
    lean_closure_set(v___x_3037_, 1, lean_box(0));
    lean_closure_set(v___x_3037_, 2, lean_box(0));
    lean_closure_set(v___x_3037_, 3, lean_box(0));
    lean_closure_set(v___x_3037_, 4, v_inst_3033_);
    lean_closure_set(v___x_3037_, 5, v_inst_3034_);
    lean_closure_set(v___x_3037_, 6, v_inst_3035_);
    lean_closure_set(v___x_3037_, 7, v_inst_3036_);
    v___x_3038_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonadRef___aux__3___boxed as *mut core::ffi::c_void,
        12,
        8,
    );
    lean_closure_set(v___x_3038_, 0, lean_box(0));
    lean_closure_set(v___x_3038_, 1, lean_box(0));
    lean_closure_set(v___x_3038_, 2, lean_box(0));
    lean_closure_set(v___x_3038_, 3, lean_box(0));
    lean_closure_set(v___x_3038_, 4, v_inst_3033_);
    lean_closure_set(v___x_3038_, 5, v_inst_3034_);
    lean_closure_set(v___x_3038_, 6, v_inst_3035_);
    lean_closure_set(v___x_3038_, 7, v_inst_3036_);
    v___x_3039_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3039_, 0, v___x_3037_);
    lean_ctor_set(v___x_3039_, 1, v___x_3038_);
    return v___x_3039_;
}
pub unsafe fn l_Lean_MonadCacheT_instMonadRef(
    mut v_00_u03c9_3040_: *mut LeanObject,
    mut v_00_u03b1_3041_: *mut LeanObject,
    mut v_00_u03b2_3042_: *mut LeanObject,
    mut v_m_3043_: *mut LeanObject,
    mut v_inst_3044_: *mut LeanObject,
    mut v_inst_3045_: *mut LeanObject,
    mut v_inst_3046_: *mut LeanObject,
    mut v_inst_3047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    v___x_3048_ = l_Lean_MonadCacheT_instMonadRef___redArg(
        v_inst_3044_,
        v_inst_3045_,
        v_inst_3046_,
        v_inst_3047_,
    );
    return v___x_3048_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__1___redArg(
    mut v_inst_3049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_failure_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    v_failure_3050_ = lean_ctor_get(v_inst_3049_, 1);
    lean_inc(v_failure_3050_);
    lean_dec_ref(v_inst_3049_);
    v___x_3051_ = lean_apply_1(v_failure_3050_, lean_box(0));
    return v___x_3051_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__1(
    mut v_00_u03c9_3052_: *mut LeanObject,
    mut v_00_u03b1_3053_: *mut LeanObject,
    mut v_00_u03b2_3054_: *mut LeanObject,
    mut v_m_3055_: *mut LeanObject,
    mut v_inst_3056_: *mut LeanObject,
    mut v_inst_3057_: *mut LeanObject,
    mut v_inst_3058_: *mut LeanObject,
    mut v_inst_3059_: *mut LeanObject,
    mut v_00_u03b1_3060_: *mut LeanObject,
    mut v_a_3061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_failure_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    v_failure_3062_ = lean_ctor_get(v_inst_3059_, 1);
    lean_inc(v_failure_3062_);
    lean_dec_ref(v_inst_3059_);
    v___x_3063_ = lean_apply_1(v_failure_3062_, lean_box(0));
    return v___x_3063_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__1___boxed(
    mut v_00_u03c9_3064_: *mut LeanObject,
    mut v_00_u03b1_3065_: *mut LeanObject,
    mut v_00_u03b2_3066_: *mut LeanObject,
    mut v_m_3067_: *mut LeanObject,
    mut v_inst_3068_: *mut LeanObject,
    mut v_inst_3069_: *mut LeanObject,
    mut v_inst_3070_: *mut LeanObject,
    mut v_inst_3071_: *mut LeanObject,
    mut v_00_u03b1_3072_: *mut LeanObject,
    mut v_a_3073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3074_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3073_);
    lean_dec_ref(v_inst_3070_);
    lean_dec_ref(v_inst_3069_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3___redArg(
    mut v_inst_3075_: *mut LeanObject,
    mut v_a_3076_: *mut LeanObject,
    mut v_a_3077_: *mut LeanObject,
    mut v_a_3078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_orElse_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    v_orElse_3079_ = lean_ctor_get(v_inst_3075_, 2);
    lean_inc(v_orElse_3079_);
    lean_dec_ref(v_inst_3075_);
    lean_inc_n(v_a_3078_, 2);
    v___f_3080_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3080_, 0, v_a_3077_);
    lean_closure_set(v___f_3080_, 1, v_a_3078_);
    v___x_3081_ = lean_apply_1(v_a_3076_, v_a_3078_);
    v___x_3082_ = lean_apply_3(v_orElse_3079_, lean_box(0), v___x_3081_, v___f_3080_);
    return v___x_3082_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3___redArg___boxed(
    mut v_inst_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3087_: *mut LeanObject = core::ptr::null_mut();
    v_res_3087_ = l_Lean_MonadCacheT_instAlternative___aux__3___redArg(
        v_inst_3083_,
        v_a_3084_,
        v_a_3085_,
        v_a_3086_,
    );
    lean_dec(v_a_3086_);
    return v_res_3087_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3(
    mut v_00_u03c9_3088_: *mut LeanObject,
    mut v_00_u03b1_3089_: *mut LeanObject,
    mut v_00_u03b2_3090_: *mut LeanObject,
    mut v_m_3091_: *mut LeanObject,
    mut v_inst_3092_: *mut LeanObject,
    mut v_inst_3093_: *mut LeanObject,
    mut v_inst_3094_: *mut LeanObject,
    mut v_inst_3095_: *mut LeanObject,
    mut v_00_u03b1_3096_: *mut LeanObject,
    mut v_a_3097_: *mut LeanObject,
    mut v_a_3098_: *mut LeanObject,
    mut v_a_3099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_orElse_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    v_orElse_3100_ = lean_ctor_get(v_inst_3095_, 2);
    lean_inc(v_orElse_3100_);
    lean_dec_ref(v_inst_3095_);
    lean_inc_n(v_a_3099_, 2);
    v___f_3101_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instMonad___aux__7___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3101_, 0, v_a_3098_);
    lean_closure_set(v___f_3101_, 1, v_a_3099_);
    v___x_3102_ = lean_apply_1(v_a_3097_, v_a_3099_);
    v___x_3103_ = lean_apply_3(v_orElse_3100_, lean_box(0), v___x_3102_, v___f_3101_);
    return v___x_3103_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___aux__3___boxed(
    mut v_00_u03c9_3104_: *mut LeanObject,
    mut v_00_u03b1_3105_: *mut LeanObject,
    mut v_00_u03b2_3106_: *mut LeanObject,
    mut v_m_3107_: *mut LeanObject,
    mut v_inst_3108_: *mut LeanObject,
    mut v_inst_3109_: *mut LeanObject,
    mut v_inst_3110_: *mut LeanObject,
    mut v_inst_3111_: *mut LeanObject,
    mut v_00_u03b1_3112_: *mut LeanObject,
    mut v_a_3113_: *mut LeanObject,
    mut v_a_3114_: *mut LeanObject,
    mut v_a_3115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3116_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3115_);
    lean_dec_ref(v_inst_3110_);
    lean_dec_ref(v_inst_3109_);
    return v_res_3116_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative___redArg(
    mut v_inst_3117_: *mut LeanObject,
    mut v_inst_3118_: *mut LeanObject,
    mut v_inst_3119_: *mut LeanObject,
    mut v_inst_3120_: *mut LeanObject,
    mut v_inst_3121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_3119_, 2);
    lean_inc_ref_n(v_inst_3118_, 2);
    v___x_3122_ = l_Lean_MonadCacheT_instMonad___redArg(
        v_inst_3117_,
        v_inst_3118_,
        v_inst_3119_,
        v_inst_3120_,
    );
    v_toApplicative_3123_ = lean_ctor_get(v___x_3122_, 0);
    lean_inc_ref(v_toApplicative_3123_);
    lean_dec_ref(v___x_3122_);
    lean_inc_ref(v_inst_3121_);
    v___x_3124_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instAlternative___aux__1___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    lean_closure_set(v___x_3124_, 0, lean_box(0));
    lean_closure_set(v___x_3124_, 1, lean_box(0));
    lean_closure_set(v___x_3124_, 2, lean_box(0));
    lean_closure_set(v___x_3124_, 3, lean_box(0));
    lean_closure_set(v___x_3124_, 4, v_inst_3117_);
    lean_closure_set(v___x_3124_, 5, v_inst_3118_);
    lean_closure_set(v___x_3124_, 6, v_inst_3119_);
    lean_closure_set(v___x_3124_, 7, v_inst_3121_);
    v___x_3125_ = lean_alloc_closure(
        l_Lean_MonadCacheT_instAlternative___aux__3___boxed as *mut core::ffi::c_void,
        12,
        8,
    );
    lean_closure_set(v___x_3125_, 0, lean_box(0));
    lean_closure_set(v___x_3125_, 1, lean_box(0));
    lean_closure_set(v___x_3125_, 2, lean_box(0));
    lean_closure_set(v___x_3125_, 3, lean_box(0));
    lean_closure_set(v___x_3125_, 4, v_inst_3117_);
    lean_closure_set(v___x_3125_, 5, v_inst_3118_);
    lean_closure_set(v___x_3125_, 6, v_inst_3119_);
    lean_closure_set(v___x_3125_, 7, v_inst_3121_);
    v___x_3126_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3126_, 0, v_toApplicative_3123_);
    lean_ctor_set(v___x_3126_, 1, v___x_3124_);
    lean_ctor_set(v___x_3126_, 2, v___x_3125_);
    return v___x_3126_;
}
pub unsafe fn l_Lean_MonadCacheT_instAlternative(
    mut v_00_u03c9_3127_: *mut LeanObject,
    mut v_00_u03b1_3128_: *mut LeanObject,
    mut v_00_u03b2_3129_: *mut LeanObject,
    mut v_m_3130_: *mut LeanObject,
    mut v_inst_3131_: *mut LeanObject,
    mut v_inst_3132_: *mut LeanObject,
    mut v_inst_3133_: *mut LeanObject,
    mut v_inst_3134_: *mut LeanObject,
    mut v_inst_3135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_3137_: *mut LeanObject,
    mut v_f_3138_: *mut LeanObject,
    mut v___y_3139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3143_: u8 = 0;
    let mut v_toPure_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut v_unused_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3140_ = lean_ctor_get(v_inst_3137_, 0);
                v_isSharedCheck_3151_ = (!lean_is_exclusive(v_inst_3137_)) as u8;
                if v_isSharedCheck_3151_ == 0 {
                    v_unused_3152_ = lean_ctor_get(v_inst_3137_, 1);
                    lean_dec(v_unused_3152_);
                    v___x_3142_ = v_inst_3137_;
                    v_isShared_3143_ = v_isSharedCheck_3151_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3140_);
                    lean_dec(v_inst_3137_);
                    v___x_3142_ = lean_box(0);
                    v_isShared_3143_ = v_isSharedCheck_3151_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3144_ = lean_ctor_get(v_toApplicative_3140_, 1);
                lean_inc(v_toPure_3144_);
                lean_dec_ref(v_toApplicative_3140_);
                v___x_3145_ = lean_box(0);
                v___x_3146_ = lean_apply_1(v_f_3138_, v___y_3139_);
                if v_isShared_3143_ == 0 {
                    lean_ctor_set(v___x_3142_, 1, v___x_3146_);
                    lean_ctor_set(v___x_3142_, 0, v___x_3145_);
                    v___x_3148_ = v___x_3142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3145_);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_3146_);
                    v___x_3148_ = v_reuseFailAlloc_3150_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3149_ = lean_apply_2(v_toPure_3144_, lean_box(0), v___x_3148_);
                return v___x_3149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(
    mut v_inst_3153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_3153_);
    v___f_3154_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3154_, 0, v_inst_3153_);
    v___x_3155_ = lean_alloc_closure(l_StateT_get as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_3155_, 0, lean_box(0));
    lean_closure_set(v___x_3155_, 1, lean_box(0));
    lean_closure_set(v___x_3155_, 2, v_inst_3153_);
    v___x_3156_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3156_, 0, v___x_3155_);
    lean_ctor_set(v___x_3156_, 1, v___f_3154_);
    return v___x_3156_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(
    mut v_00_u03b1_3157_: *mut LeanObject,
    mut v_00_u03b2_3158_: *mut LeanObject,
    mut v_m_3159_: *mut LeanObject,
    mut v_inst_3160_: *mut LeanObject,
    mut v_inst_3161_: *mut LeanObject,
    mut v_inst_3162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    v___x_3163_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___redArg(v_inst_3162_);
    return v___x_3163_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter___boxed(
    mut v_00_u03b1_3164_: *mut LeanObject,
    mut v_00_u03b2_3165_: *mut LeanObject,
    mut v_m_3166_: *mut LeanObject,
    mut v_inst_3167_: *mut LeanObject,
    mut v_inst_3168_: *mut LeanObject,
    mut v_inst_3169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3170_: *mut LeanObject = core::ptr::null_mut();
    v_res_3170_ = l_Lean_MonadStateCacheT_instMonadHashMapCacheAdapter(
        v_00_u03b1_3164_,
        v_00_u03b2_3165_,
        v_m_3166_,
        v_inst_3167_,
        v_inst_3168_,
        v_inst_3169_,
    );
    lean_dec_ref(v_inst_3168_);
    lean_dec_ref(v_inst_3167_);
    return v_res_3170_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___redArg___lam__0(
    mut v_x_3171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3172_: *mut LeanObject = core::ptr::null_mut();
    v_fst_3172_ = lean_ctor_get(v_x_3171_, 0);
    lean_inc(v_fst_3172_);
    return v_fst_3172_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___redArg___lam__0___boxed(
    mut v_x_3173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3174_: *mut LeanObject = core::ptr::null_mut();
    v_res_3174_ = l_Lean_MonadStateCacheT_run___redArg___lam__0(v_x_3173_);
    lean_dec_ref(v_x_3173_);
    return v_res_3174_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___redArg(
    mut v_inst_3176_: *mut LeanObject,
    mut v_x_3177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3178_ = lean_ctor_get(v_inst_3176_, 0);
    lean_inc_ref(v_toApplicative_3178_);
    lean_dec_ref(v_inst_3176_);
    v_toFunctor_3179_ = lean_ctor_get(v_toApplicative_3178_, 0);
    lean_inc_ref(v_toFunctor_3179_);
    lean_dec_ref(v_toApplicative_3178_);
    v_map_3180_ = lean_ctor_get(v_toFunctor_3179_, 0);
    lean_inc(v_map_3180_);
    lean_dec_ref(v_toFunctor_3179_);
    v___f_3181_ = l_Lean_MonadStateCacheT_run___redArg___closed__0;
    v___x_3182_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__1,
    );
    v___x_3183_ = lean_apply_1(v_x_3177_, v___x_3182_);
    v___x_3184_ = lean_apply_4(
        v_map_3180_,
        lean_box(0),
        lean_box(0),
        v___f_3181_,
        v___x_3183_,
    );
    return v___x_3184_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run(
    mut v_00_u03b1_3185_: *mut LeanObject,
    mut v_00_u03b2_3186_: *mut LeanObject,
    mut v_m_3187_: *mut LeanObject,
    mut v_inst_3188_: *mut LeanObject,
    mut v_inst_3189_: *mut LeanObject,
    mut v_inst_3190_: *mut LeanObject,
    mut v_00_u03c3_3191_: *mut LeanObject,
    mut v_x_3192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3193_ = lean_ctor_get(v_inst_3190_, 0);
    lean_inc_ref(v_toApplicative_3193_);
    lean_dec_ref(v_inst_3190_);
    v_toFunctor_3194_ = lean_ctor_get(v_toApplicative_3193_, 0);
    lean_inc_ref(v_toFunctor_3194_);
    lean_dec_ref(v_toApplicative_3193_);
    v_map_3195_ = lean_ctor_get(v_toFunctor_3194_, 0);
    lean_inc(v_map_3195_);
    lean_dec_ref(v_toFunctor_3194_);
    v___f_3196_ = l_Lean_MonadStateCacheT_run___redArg___closed__0;
    v___x_3197_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MonadCacheT_run___redArg___closed__1_once),
        _init_l_Lean_MonadCacheT_run___redArg___closed__1,
    );
    v___x_3198_ = lean_apply_1(v_x_3192_, v___x_3197_);
    v___x_3199_ = lean_apply_4(
        v_map_3195_,
        lean_box(0),
        lean_box(0),
        v___f_3196_,
        v___x_3198_,
    );
    return v___x_3199_;
}
pub unsafe fn l_Lean_MonadStateCacheT_run___boxed(
    mut v_00_u03b1_3200_: *mut LeanObject,
    mut v_00_u03b2_3201_: *mut LeanObject,
    mut v_m_3202_: *mut LeanObject,
    mut v_inst_3203_: *mut LeanObject,
    mut v_inst_3204_: *mut LeanObject,
    mut v_inst_3205_: *mut LeanObject,
    mut v_00_u03c3_3206_: *mut LeanObject,
    mut v_x_3207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3208_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3204_);
    lean_dec_ref(v_inst_3203_);
    return v_res_3208_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0(
    mut v_f_3209_: *mut LeanObject,
    mut v_toPure_3210_: *mut LeanObject,
    mut v_____x_3211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3212_ = lean_ctor_get(v_____x_3211_, 0);
                v_snd_3213_ = lean_ctor_get(v_____x_3211_, 1);
                v_isSharedCheck_3222_ = (!lean_is_exclusive(v_____x_3211_)) as u8;
                if v_isSharedCheck_3222_ == 0 {
                    v___x_3215_ = v_____x_3211_;
                    v_isShared_3216_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3213_);
                    lean_inc(v_fst_3212_);
                    lean_dec(v_____x_3211_);
                    v___x_3215_ = lean_box(0);
                    v_isShared_3216_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3217_ = lean_apply_1(v_f_3209_, v_fst_3212_);
                if v_isShared_3216_ == 0 {
                    lean_ctor_set(v___x_3215_, 0, v___x_3217_);
                    v___x_3219_ = v___x_3215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3217_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_snd_3213_);
                    v___x_3219_ = v_reuseFailAlloc_3221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3220_ = lean_apply_2(v_toPure_3210_, lean_box(0), v___x_3219_);
                return v___x_3220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1___redArg(
    mut v_inst_3223_: *mut LeanObject,
    mut v_f_3224_: *mut LeanObject,
    mut v_x_3225_: *mut LeanObject,
    mut v_a_3226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3227_ = lean_ctor_get(v_inst_3223_, 0);
    lean_inc_ref(v_toApplicative_3227_);
    v_toBind_3228_ = lean_ctor_get(v_inst_3223_, 1);
    lean_inc(v_toBind_3228_);
    lean_dec_ref(v_inst_3223_);
    v_toPure_3229_ = lean_ctor_get(v_toApplicative_3227_, 1);
    lean_inc(v_toPure_3229_);
    lean_dec_ref(v_toApplicative_3227_);
    v___x_3230_ = lean_apply_1(v_x_3225_, v_a_3226_);
    v___f_3231_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3231_, 0, v_f_3224_);
    lean_closure_set(v___f_3231_, 1, v_toPure_3229_);
    v___x_3232_ = lean_apply_4(
        v_toBind_3228_,
        lean_box(0),
        lean_box(0),
        v___x_3230_,
        v___f_3231_,
    );
    return v___x_3232_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1(
    mut v_00_u03b1_3233_: *mut LeanObject,
    mut v_00_u03b2_3234_: *mut LeanObject,
    mut v_m_3235_: *mut LeanObject,
    mut v_inst_3236_: *mut LeanObject,
    mut v_inst_3237_: *mut LeanObject,
    mut v_inst_3238_: *mut LeanObject,
    mut v_00_u03b1_3239_: *mut LeanObject,
    mut v_00_u03b2_3240_: *mut LeanObject,
    mut v_f_3241_: *mut LeanObject,
    mut v_x_3242_: *mut LeanObject,
    mut v_a_3243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3244_ = lean_ctor_get(v_inst_3238_, 0);
    lean_inc_ref(v_toApplicative_3244_);
    v_toBind_3245_ = lean_ctor_get(v_inst_3238_, 1);
    lean_inc(v_toBind_3245_);
    lean_dec_ref(v_inst_3238_);
    v_toPure_3246_ = lean_ctor_get(v_toApplicative_3244_, 1);
    lean_inc(v_toPure_3246_);
    lean_dec_ref(v_toApplicative_3244_);
    v___x_3247_ = lean_apply_1(v_x_3242_, v_a_3243_);
    v___f_3248_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3248_, 0, v_f_3241_);
    lean_closure_set(v___f_3248_, 1, v_toPure_3246_);
    v___x_3249_ = lean_apply_4(
        v_toBind_3245_,
        lean_box(0),
        lean_box(0),
        v___x_3247_,
        v___f_3248_,
    );
    return v___x_3249_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__1___boxed(
    mut v_00_u03b1_3250_: *mut LeanObject,
    mut v_00_u03b2_3251_: *mut LeanObject,
    mut v_m_3252_: *mut LeanObject,
    mut v_inst_3253_: *mut LeanObject,
    mut v_inst_3254_: *mut LeanObject,
    mut v_inst_3255_: *mut LeanObject,
    mut v_00_u03b1_3256_: *mut LeanObject,
    mut v_00_u03b2_3257_: *mut LeanObject,
    mut v_f_3258_: *mut LeanObject,
    mut v_x_3259_: *mut LeanObject,
    mut v_a_3260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3261_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3254_);
    lean_dec_ref(v_inst_3253_);
    return v_res_3261_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0(
    mut v_a_3262_: *mut LeanObject,
    mut v_toPure_3263_: *mut LeanObject,
    mut v_____x_3264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_unused_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3265_ = lean_ctor_get(v_____x_3264_, 1);
                v_isSharedCheck_3273_ = (!lean_is_exclusive(v_____x_3264_)) as u8;
                if v_isSharedCheck_3273_ == 0 {
                    v_unused_3274_ = lean_ctor_get(v_____x_3264_, 0);
                    lean_dec(v_unused_3274_);
                    v___x_3267_ = v_____x_3264_;
                    v_isShared_3268_ = v_isSharedCheck_3273_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3265_);
                    lean_dec(v_____x_3264_);
                    v___x_3267_ = lean_box(0);
                    v_isShared_3268_ = v_isSharedCheck_3273_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3268_ == 0 {
                    lean_ctor_set(v___x_3267_, 0, v_a_3262_);
                    v___x_3270_ = v___x_3267_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3262_);
                    lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_snd_3265_);
                    v___x_3270_ = v_reuseFailAlloc_3272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3271_ = lean_apply_2(v_toPure_3263_, lean_box(0), v___x_3270_);
                return v___x_3271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3___redArg(
    mut v_inst_3275_: *mut LeanObject,
    mut v_a_3276_: *mut LeanObject,
    mut v_a_3277_: *mut LeanObject,
    mut v_a_3278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3279_ = lean_ctor_get(v_inst_3275_, 0);
    lean_inc_ref(v_toApplicative_3279_);
    v_toBind_3280_ = lean_ctor_get(v_inst_3275_, 1);
    lean_inc(v_toBind_3280_);
    lean_dec_ref(v_inst_3275_);
    v_toPure_3281_ = lean_ctor_get(v_toApplicative_3279_, 1);
    lean_inc(v_toPure_3281_);
    lean_dec_ref(v_toApplicative_3279_);
    v___x_3282_ = lean_apply_1(v_a_3277_, v_a_3278_);
    v___f_3283_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3283_, 0, v_a_3276_);
    lean_closure_set(v___f_3283_, 1, v_toPure_3281_);
    v___x_3284_ = lean_apply_4(
        v_toBind_3280_,
        lean_box(0),
        lean_box(0),
        v___x_3282_,
        v___f_3283_,
    );
    return v___x_3284_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3(
    mut v_00_u03b1_3285_: *mut LeanObject,
    mut v_00_u03b2_3286_: *mut LeanObject,
    mut v_m_3287_: *mut LeanObject,
    mut v_inst_3288_: *mut LeanObject,
    mut v_inst_3289_: *mut LeanObject,
    mut v_inst_3290_: *mut LeanObject,
    mut v_00_u03b1_3291_: *mut LeanObject,
    mut v_00_u03b2_3292_: *mut LeanObject,
    mut v_a_3293_: *mut LeanObject,
    mut v_a_3294_: *mut LeanObject,
    mut v_a_3295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3296_ = lean_ctor_get(v_inst_3290_, 0);
    lean_inc_ref(v_toApplicative_3296_);
    v_toBind_3297_ = lean_ctor_get(v_inst_3290_, 1);
    lean_inc(v_toBind_3297_);
    lean_dec_ref(v_inst_3290_);
    v_toPure_3298_ = lean_ctor_get(v_toApplicative_3296_, 1);
    lean_inc(v_toPure_3298_);
    lean_dec_ref(v_toApplicative_3296_);
    v___x_3299_ = lean_apply_1(v_a_3294_, v_a_3295_);
    v___f_3300_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__3___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3300_, 0, v_a_3293_);
    lean_closure_set(v___f_3300_, 1, v_toPure_3298_);
    v___x_3301_ = lean_apply_4(
        v_toBind_3297_,
        lean_box(0),
        lean_box(0),
        v___x_3299_,
        v___f_3300_,
    );
    return v___x_3301_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__3___boxed(
    mut v_00_u03b1_3302_: *mut LeanObject,
    mut v_00_u03b2_3303_: *mut LeanObject,
    mut v_m_3304_: *mut LeanObject,
    mut v_inst_3305_: *mut LeanObject,
    mut v_inst_3306_: *mut LeanObject,
    mut v_inst_3307_: *mut LeanObject,
    mut v_00_u03b1_3308_: *mut LeanObject,
    mut v_00_u03b2_3309_: *mut LeanObject,
    mut v_a_3310_: *mut LeanObject,
    mut v_a_3311_: *mut LeanObject,
    mut v_a_3312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3313_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3306_);
    lean_dec_ref(v_inst_3305_);
    return v_res_3313_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__5___redArg(
    mut v_inst_3314_: *mut LeanObject,
    mut v_a_3315_: *mut LeanObject,
    mut v_a_3316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3320_: u8 = 0;
    let mut v_toPure_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut v_unused_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3317_ = lean_ctor_get(v_inst_3314_, 0);
                v_isSharedCheck_3326_ = (!lean_is_exclusive(v_inst_3314_)) as u8;
                if v_isSharedCheck_3326_ == 0 {
                    v_unused_3327_ = lean_ctor_get(v_inst_3314_, 1);
                    lean_dec(v_unused_3327_);
                    v___x_3319_ = v_inst_3314_;
                    v_isShared_3320_ = v_isSharedCheck_3326_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3317_);
                    lean_dec(v_inst_3314_);
                    v___x_3319_ = lean_box(0);
                    v_isShared_3320_ = v_isSharedCheck_3326_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3321_ = lean_ctor_get(v_toApplicative_3317_, 1);
                lean_inc(v_toPure_3321_);
                lean_dec_ref(v_toApplicative_3317_);
                if v_isShared_3320_ == 0 {
                    lean_ctor_set(v___x_3319_, 1, v_a_3316_);
                    lean_ctor_set(v___x_3319_, 0, v_a_3315_);
                    v___x_3323_ = v___x_3319_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3315_);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_a_3316_);
                    v___x_3323_ = v_reuseFailAlloc_3325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3324_ = lean_apply_2(v_toPure_3321_, lean_box(0), v___x_3323_);
                return v___x_3324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__5(
    mut v_00_u03b1_3328_: *mut LeanObject,
    mut v_00_u03b2_3329_: *mut LeanObject,
    mut v_m_3330_: *mut LeanObject,
    mut v_inst_3331_: *mut LeanObject,
    mut v_inst_3332_: *mut LeanObject,
    mut v_inst_3333_: *mut LeanObject,
    mut v_00_u03b1_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
    mut v_a_3336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v_toPure_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_unused_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3337_ = lean_ctor_get(v_inst_3333_, 0);
                v_isSharedCheck_3346_ = (!lean_is_exclusive(v_inst_3333_)) as u8;
                if v_isSharedCheck_3346_ == 0 {
                    v_unused_3347_ = lean_ctor_get(v_inst_3333_, 1);
                    lean_dec(v_unused_3347_);
                    v___x_3339_ = v_inst_3333_;
                    v_isShared_3340_ = v_isSharedCheck_3346_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3337_);
                    lean_dec(v_inst_3333_);
                    v___x_3339_ = lean_box(0);
                    v_isShared_3340_ = v_isSharedCheck_3346_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3341_ = lean_ctor_get(v_toApplicative_3337_, 1);
                lean_inc(v_toPure_3341_);
                lean_dec_ref(v_toApplicative_3337_);
                if v_isShared_3340_ == 0 {
                    lean_ctor_set(v___x_3339_, 1, v_a_3336_);
                    lean_ctor_set(v___x_3339_, 0, v_a_3335_);
                    v___x_3343_ = v___x_3339_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3335_);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_a_3336_);
                    v___x_3343_ = v_reuseFailAlloc_3345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3344_ = lean_apply_2(v_toPure_3341_, lean_box(0), v___x_3343_);
                return v___x_3344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__5___boxed(
    mut v_00_u03b1_3348_: *mut LeanObject,
    mut v_00_u03b2_3349_: *mut LeanObject,
    mut v_m_3350_: *mut LeanObject,
    mut v_inst_3351_: *mut LeanObject,
    mut v_inst_3352_: *mut LeanObject,
    mut v_inst_3353_: *mut LeanObject,
    mut v_00_u03b1_3354_: *mut LeanObject,
    mut v_a_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3357_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3352_);
    lean_dec_ref(v_inst_3351_);
    return v_res_3357_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0(
    mut v_fst_3358_: *mut LeanObject,
    mut v_toPure_3359_: *mut LeanObject,
    mut v_____x_3360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3365_: u8 = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3361_ = lean_ctor_get(v_____x_3360_, 0);
                v_snd_3362_ = lean_ctor_get(v_____x_3360_, 1);
                v_isSharedCheck_3371_ = (!lean_is_exclusive(v_____x_3360_)) as u8;
                if v_isSharedCheck_3371_ == 0 {
                    v___x_3364_ = v_____x_3360_;
                    v_isShared_3365_ = v_isSharedCheck_3371_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3362_);
                    lean_inc(v_fst_3361_);
                    lean_dec(v_____x_3360_);
                    v___x_3364_ = lean_box(0);
                    v_isShared_3365_ = v_isSharedCheck_3371_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3366_ = lean_apply_1(v_fst_3358_, v_fst_3361_);
                if v_isShared_3365_ == 0 {
                    lean_ctor_set(v___x_3364_, 0, v___x_3366_);
                    v___x_3368_ = v___x_3364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3366_);
                    lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_snd_3362_);
                    v___x_3368_ = v_reuseFailAlloc_3370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3369_ = lean_apply_2(v_toPure_3359_, lean_box(0), v___x_3368_);
                return v___x_3369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1(
    mut v_toApplicative_3372_: *mut LeanObject,
    mut v_x_3373_: *mut LeanObject,
    mut v_toBind_3374_: *mut LeanObject,
    mut v_____x_3375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    v_fst_3376_ = lean_ctor_get(v_____x_3375_, 0);
    lean_inc(v_fst_3376_);
    v_snd_3377_ = lean_ctor_get(v_____x_3375_, 1);
    lean_inc(v_snd_3377_);
    lean_dec_ref(v_____x_3375_);
    v_toPure_3378_ = lean_ctor_get(v_toApplicative_3372_, 1);
    lean_inc(v_toPure_3378_);
    lean_dec_ref(v_toApplicative_3372_);
    v___x_3379_ = lean_box(0);
    v___x_3380_ = lean_apply_2(v_x_3373_, v___x_3379_, v_snd_3377_);
    v___f_3381_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3381_, 0, v_fst_3376_);
    lean_closure_set(v___f_3381_, 1, v_toPure_3378_);
    v___x_3382_ = lean_apply_4(
        v_toBind_3374_,
        lean_box(0),
        lean_box(0),
        v___x_3380_,
        v___f_3381_,
    );
    return v___x_3382_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___redArg(
    mut v_inst_3383_: *mut LeanObject,
    mut v_f_3384_: *mut LeanObject,
    mut v_x_3385_: *mut LeanObject,
    mut v_a_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3387_ = lean_ctor_get(v_inst_3383_, 0);
    lean_inc_ref(v_toApplicative_3387_);
    v_toBind_3388_ = lean_ctor_get(v_inst_3383_, 1);
    lean_inc_n(v_toBind_3388_, 2);
    lean_dec_ref(v_inst_3383_);
    v___f_3389_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3389_, 0, v_toApplicative_3387_);
    lean_closure_set(v___f_3389_, 1, v_x_3385_);
    lean_closure_set(v___f_3389_, 2, v_toBind_3388_);
    v___x_3390_ = lean_apply_1(v_f_3384_, v_a_3386_);
    v___x_3391_ = lean_apply_4(
        v_toBind_3388_,
        lean_box(0),
        lean_box(0),
        v___x_3390_,
        v___f_3389_,
    );
    return v___x_3391_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7(
    mut v_00_u03b1_3392_: *mut LeanObject,
    mut v_00_u03b2_3393_: *mut LeanObject,
    mut v_m_3394_: *mut LeanObject,
    mut v_inst_3395_: *mut LeanObject,
    mut v_inst_3396_: *mut LeanObject,
    mut v_inst_3397_: *mut LeanObject,
    mut v_00_u03b1_3398_: *mut LeanObject,
    mut v_00_u03b2_3399_: *mut LeanObject,
    mut v_f_3400_: *mut LeanObject,
    mut v_x_3401_: *mut LeanObject,
    mut v_a_3402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3403_ = lean_ctor_get(v_inst_3397_, 0);
    lean_inc_ref(v_toApplicative_3403_);
    v_toBind_3404_ = lean_ctor_get(v_inst_3397_, 1);
    lean_inc_n(v_toBind_3404_, 2);
    lean_dec_ref(v_inst_3397_);
    v___f_3405_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3405_, 0, v_toApplicative_3403_);
    lean_closure_set(v___f_3405_, 1, v_x_3401_);
    lean_closure_set(v___f_3405_, 2, v_toBind_3404_);
    v___x_3406_ = lean_apply_1(v_f_3400_, v_a_3402_);
    v___x_3407_ = lean_apply_4(
        v_toBind_3404_,
        lean_box(0),
        lean_box(0),
        v___x_3406_,
        v___f_3405_,
    );
    return v___x_3407_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__7___boxed(
    mut v_00_u03b1_3408_: *mut LeanObject,
    mut v_00_u03b2_3409_: *mut LeanObject,
    mut v_m_3410_: *mut LeanObject,
    mut v_inst_3411_: *mut LeanObject,
    mut v_inst_3412_: *mut LeanObject,
    mut v_inst_3413_: *mut LeanObject,
    mut v_00_u03b1_3414_: *mut LeanObject,
    mut v_00_u03b2_3415_: *mut LeanObject,
    mut v_f_3416_: *mut LeanObject,
    mut v_x_3417_: *mut LeanObject,
    mut v_a_3418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3419_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3412_);
    lean_dec_ref(v_inst_3411_);
    return v_res_3419_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0(
    mut v_toApplicative_3420_: *mut LeanObject,
    mut v_fst_3421_: *mut LeanObject,
    mut v_____x_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3426_: u8 = 0;
    let mut v_toPure_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3432_: u8 = 0;
    let mut v_unused_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3423_ = lean_ctor_get(v_____x_3422_, 1);
                v_isSharedCheck_3432_ = (!lean_is_exclusive(v_____x_3422_)) as u8;
                if v_isSharedCheck_3432_ == 0 {
                    v_unused_3433_ = lean_ctor_get(v_____x_3422_, 0);
                    lean_dec(v_unused_3433_);
                    v___x_3425_ = v_____x_3422_;
                    v_isShared_3426_ = v_isSharedCheck_3432_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3423_);
                    lean_dec(v_____x_3422_);
                    v___x_3425_ = lean_box(0);
                    v_isShared_3426_ = v_isSharedCheck_3432_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3427_ = lean_ctor_get(v_toApplicative_3420_, 1);
                lean_inc(v_toPure_3427_);
                lean_dec_ref(v_toApplicative_3420_);
                if v_isShared_3426_ == 0 {
                    lean_ctor_set(v___x_3425_, 0, v_fst_3421_);
                    v___x_3429_ = v___x_3425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_fst_3421_);
                    lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_snd_3423_);
                    v___x_3429_ = v_reuseFailAlloc_3431_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3430_ = lean_apply_2(v_toPure_3427_, lean_box(0), v___x_3429_);
                return v___x_3430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1(
    mut v_toApplicative_3434_: *mut LeanObject,
    mut v_y_3435_: *mut LeanObject,
    mut v_toBind_3436_: *mut LeanObject,
    mut v_____x_3437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    v_fst_3438_ = lean_ctor_get(v_____x_3437_, 0);
    lean_inc(v_fst_3438_);
    v_snd_3439_ = lean_ctor_get(v_____x_3437_, 1);
    lean_inc(v_snd_3439_);
    lean_dec_ref(v_____x_3437_);
    v___f_3440_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3440_, 0, v_toApplicative_3434_);
    lean_closure_set(v___f_3440_, 1, v_fst_3438_);
    v___x_3441_ = lean_box(0);
    v___x_3442_ = lean_apply_2(v_y_3435_, v___x_3441_, v_snd_3439_);
    v___x_3443_ = lean_apply_4(
        v_toBind_3436_,
        lean_box(0),
        lean_box(0),
        v___x_3442_,
        v___f_3440_,
    );
    return v___x_3443_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___redArg(
    mut v_inst_3444_: *mut LeanObject,
    mut v_x_3445_: *mut LeanObject,
    mut v_y_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3448_ = lean_ctor_get(v_inst_3444_, 0);
    lean_inc_ref(v_toApplicative_3448_);
    v_toBind_3449_ = lean_ctor_get(v_inst_3444_, 1);
    lean_inc_n(v_toBind_3449_, 2);
    lean_dec_ref(v_inst_3444_);
    v___f_3450_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3450_, 0, v_toApplicative_3448_);
    lean_closure_set(v___f_3450_, 1, v_y_3446_);
    lean_closure_set(v___f_3450_, 2, v_toBind_3449_);
    v___x_3451_ = lean_apply_1(v_x_3445_, v_a_3447_);
    v___x_3452_ = lean_apply_4(
        v_toBind_3449_,
        lean_box(0),
        lean_box(0),
        v___x_3451_,
        v___f_3450_,
    );
    return v___x_3452_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9(
    mut v_00_u03b1_3453_: *mut LeanObject,
    mut v_00_u03b2_3454_: *mut LeanObject,
    mut v_m_3455_: *mut LeanObject,
    mut v_inst_3456_: *mut LeanObject,
    mut v_inst_3457_: *mut LeanObject,
    mut v_inst_3458_: *mut LeanObject,
    mut v_00_u03b1_3459_: *mut LeanObject,
    mut v_00_u03b2_3460_: *mut LeanObject,
    mut v_x_3461_: *mut LeanObject,
    mut v_y_3462_: *mut LeanObject,
    mut v_a_3463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3464_ = lean_ctor_get(v_inst_3458_, 0);
    lean_inc_ref(v_toApplicative_3464_);
    v_toBind_3465_ = lean_ctor_get(v_inst_3458_, 1);
    lean_inc_n(v_toBind_3465_, 2);
    lean_dec_ref(v_inst_3458_);
    v___f_3466_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3466_, 0, v_toApplicative_3464_);
    lean_closure_set(v___f_3466_, 1, v_y_3462_);
    lean_closure_set(v___f_3466_, 2, v_toBind_3465_);
    v___x_3467_ = lean_apply_1(v_x_3461_, v_a_3463_);
    v___x_3468_ = lean_apply_4(
        v_toBind_3465_,
        lean_box(0),
        lean_box(0),
        v___x_3467_,
        v___f_3466_,
    );
    return v___x_3468_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__9___boxed(
    mut v_00_u03b1_3469_: *mut LeanObject,
    mut v_00_u03b2_3470_: *mut LeanObject,
    mut v_m_3471_: *mut LeanObject,
    mut v_inst_3472_: *mut LeanObject,
    mut v_inst_3473_: *mut LeanObject,
    mut v_inst_3474_: *mut LeanObject,
    mut v_00_u03b1_3475_: *mut LeanObject,
    mut v_00_u03b2_3476_: *mut LeanObject,
    mut v_x_3477_: *mut LeanObject,
    mut v_y_3478_: *mut LeanObject,
    mut v_a_3479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3480_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3473_);
    lean_dec_ref(v_inst_3472_);
    return v_res_3480_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0(
    mut v_y_3481_: *mut LeanObject,
    mut v_____x_3482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    v_snd_3483_ = lean_ctor_get(v_____x_3482_, 1);
    lean_inc(v_snd_3483_);
    lean_dec_ref(v_____x_3482_);
    v___x_3484_ = lean_box(0);
    v___x_3485_ = lean_apply_2(v_y_3481_, v___x_3484_, v_snd_3483_);
    return v___x_3485_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11___redArg(
    mut v_inst_3486_: *mut LeanObject,
    mut v_x_3487_: *mut LeanObject,
    mut v_y_3488_: *mut LeanObject,
    mut v_a_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3490_ = lean_ctor_get(v_inst_3486_, 1);
    lean_inc(v_toBind_3490_);
    lean_dec_ref(v_inst_3486_);
    v___f_3491_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3491_, 0, v_y_3488_);
    v___x_3492_ = lean_apply_1(v_x_3487_, v_a_3489_);
    v___x_3493_ = lean_apply_4(
        v_toBind_3490_,
        lean_box(0),
        lean_box(0),
        v___x_3492_,
        v___f_3491_,
    );
    return v___x_3493_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11(
    mut v_00_u03b1_3494_: *mut LeanObject,
    mut v_00_u03b2_3495_: *mut LeanObject,
    mut v_m_3496_: *mut LeanObject,
    mut v_inst_3497_: *mut LeanObject,
    mut v_inst_3498_: *mut LeanObject,
    mut v_inst_3499_: *mut LeanObject,
    mut v_00_u03b1_3500_: *mut LeanObject,
    mut v_00_u03b2_3501_: *mut LeanObject,
    mut v_x_3502_: *mut LeanObject,
    mut v_y_3503_: *mut LeanObject,
    mut v_a_3504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3505_ = lean_ctor_get(v_inst_3499_, 1);
    lean_inc(v_toBind_3505_);
    lean_dec_ref(v_inst_3499_);
    v___f_3506_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__11___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3506_, 0, v_y_3503_);
    v___x_3507_ = lean_apply_1(v_x_3502_, v_a_3504_);
    v___x_3508_ = lean_apply_4(
        v_toBind_3505_,
        lean_box(0),
        lean_box(0),
        v___x_3507_,
        v___f_3506_,
    );
    return v___x_3508_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__11___boxed(
    mut v_00_u03b1_3509_: *mut LeanObject,
    mut v_00_u03b2_3510_: *mut LeanObject,
    mut v_m_3511_: *mut LeanObject,
    mut v_inst_3512_: *mut LeanObject,
    mut v_inst_3513_: *mut LeanObject,
    mut v_inst_3514_: *mut LeanObject,
    mut v_00_u03b1_3515_: *mut LeanObject,
    mut v_00_u03b2_3516_: *mut LeanObject,
    mut v_x_3517_: *mut LeanObject,
    mut v_y_3518_: *mut LeanObject,
    mut v_a_3519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3520_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3513_);
    lean_dec_ref(v_inst_3512_);
    return v_res_3520_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0(
    mut v_f_3521_: *mut LeanObject,
    mut v_____x_3522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    v_fst_3523_ = lean_ctor_get(v_____x_3522_, 0);
    lean_inc(v_fst_3523_);
    v_snd_3524_ = lean_ctor_get(v_____x_3522_, 1);
    lean_inc(v_snd_3524_);
    lean_dec_ref(v_____x_3522_);
    v___x_3525_ = lean_apply_2(v_f_3521_, v_fst_3523_, v_snd_3524_);
    return v___x_3525_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13___redArg(
    mut v_inst_3526_: *mut LeanObject,
    mut v_x_3527_: *mut LeanObject,
    mut v_f_3528_: *mut LeanObject,
    mut v_a_3529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3530_ = lean_ctor_get(v_inst_3526_, 1);
    lean_inc(v_toBind_3530_);
    lean_dec_ref(v_inst_3526_);
    v___f_3531_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3531_, 0, v_f_3528_);
    v___x_3532_ = lean_apply_1(v_x_3527_, v_a_3529_);
    v___x_3533_ = lean_apply_4(
        v_toBind_3530_,
        lean_box(0),
        lean_box(0),
        v___x_3532_,
        v___f_3531_,
    );
    return v___x_3533_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13(
    mut v_00_u03b1_3534_: *mut LeanObject,
    mut v_00_u03b2_3535_: *mut LeanObject,
    mut v_m_3536_: *mut LeanObject,
    mut v_inst_3537_: *mut LeanObject,
    mut v_inst_3538_: *mut LeanObject,
    mut v_inst_3539_: *mut LeanObject,
    mut v_00_u03b1_3540_: *mut LeanObject,
    mut v_00_u03b2_3541_: *mut LeanObject,
    mut v_x_3542_: *mut LeanObject,
    mut v_f_3543_: *mut LeanObject,
    mut v_a_3544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3545_ = lean_ctor_get(v_inst_3539_, 1);
    lean_inc(v_toBind_3545_);
    lean_dec_ref(v_inst_3539_);
    v___f_3546_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__13___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3546_, 0, v_f_3543_);
    v___x_3547_ = lean_apply_1(v_x_3542_, v_a_3544_);
    v___x_3548_ = lean_apply_4(
        v_toBind_3545_,
        lean_box(0),
        lean_box(0),
        v___x_3547_,
        v___f_3546_,
    );
    return v___x_3548_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___aux__13___boxed(
    mut v_00_u03b1_3549_: *mut LeanObject,
    mut v_00_u03b2_3550_: *mut LeanObject,
    mut v_m_3551_: *mut LeanObject,
    mut v_inst_3552_: *mut LeanObject,
    mut v_inst_3553_: *mut LeanObject,
    mut v_inst_3554_: *mut LeanObject,
    mut v_00_u03b1_3555_: *mut LeanObject,
    mut v_00_u03b2_3556_: *mut LeanObject,
    mut v_x_3557_: *mut LeanObject,
    mut v_f_3558_: *mut LeanObject,
    mut v_a_3559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3560_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3553_);
    lean_dec_ref(v_inst_3552_);
    return v_res_3560_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad___redArg(
    mut v_inst_3561_: *mut LeanObject,
    mut v_inst_3562_: *mut LeanObject,
    mut v_inst_3563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_3563_, 6);
    lean_inc_ref_n(v_inst_3562_, 6);
    lean_inc_ref_n(v_inst_3561_, 6);
    v___x_3564_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__1___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    lean_closure_set(v___x_3564_, 0, lean_box(0));
    lean_closure_set(v___x_3564_, 1, lean_box(0));
    lean_closure_set(v___x_3564_, 2, lean_box(0));
    lean_closure_set(v___x_3564_, 3, v_inst_3561_);
    lean_closure_set(v___x_3564_, 4, v_inst_3562_);
    lean_closure_set(v___x_3564_, 5, v_inst_3563_);
    v___x_3565_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__3___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    lean_closure_set(v___x_3565_, 0, lean_box(0));
    lean_closure_set(v___x_3565_, 1, lean_box(0));
    lean_closure_set(v___x_3565_, 2, lean_box(0));
    lean_closure_set(v___x_3565_, 3, v_inst_3561_);
    lean_closure_set(v___x_3565_, 4, v_inst_3562_);
    lean_closure_set(v___x_3565_, 5, v_inst_3563_);
    v___x_3566_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3566_, 0, v___x_3564_);
    lean_ctor_set(v___x_3566_, 1, v___x_3565_);
    v___x_3567_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__5___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___x_3567_, 0, lean_box(0));
    lean_closure_set(v___x_3567_, 1, lean_box(0));
    lean_closure_set(v___x_3567_, 2, lean_box(0));
    lean_closure_set(v___x_3567_, 3, v_inst_3561_);
    lean_closure_set(v___x_3567_, 4, v_inst_3562_);
    lean_closure_set(v___x_3567_, 5, v_inst_3563_);
    v___x_3568_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__7___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    lean_closure_set(v___x_3568_, 0, lean_box(0));
    lean_closure_set(v___x_3568_, 1, lean_box(0));
    lean_closure_set(v___x_3568_, 2, lean_box(0));
    lean_closure_set(v___x_3568_, 3, v_inst_3561_);
    lean_closure_set(v___x_3568_, 4, v_inst_3562_);
    lean_closure_set(v___x_3568_, 5, v_inst_3563_);
    v___x_3569_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__9___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    lean_closure_set(v___x_3569_, 0, lean_box(0));
    lean_closure_set(v___x_3569_, 1, lean_box(0));
    lean_closure_set(v___x_3569_, 2, lean_box(0));
    lean_closure_set(v___x_3569_, 3, v_inst_3561_);
    lean_closure_set(v___x_3569_, 4, v_inst_3562_);
    lean_closure_set(v___x_3569_, 5, v_inst_3563_);
    v___x_3570_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__11___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    lean_closure_set(v___x_3570_, 0, lean_box(0));
    lean_closure_set(v___x_3570_, 1, lean_box(0));
    lean_closure_set(v___x_3570_, 2, lean_box(0));
    lean_closure_set(v___x_3570_, 3, v_inst_3561_);
    lean_closure_set(v___x_3570_, 4, v_inst_3562_);
    lean_closure_set(v___x_3570_, 5, v_inst_3563_);
    v___x_3571_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3571_, 0, v___x_3566_);
    lean_ctor_set(v___x_3571_, 1, v___x_3567_);
    lean_ctor_set(v___x_3571_, 2, v___x_3568_);
    lean_ctor_set(v___x_3571_, 3, v___x_3569_);
    lean_ctor_set(v___x_3571_, 4, v___x_3570_);
    v___x_3572_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    lean_closure_set(v___x_3572_, 0, lean_box(0));
    lean_closure_set(v___x_3572_, 1, lean_box(0));
    lean_closure_set(v___x_3572_, 2, lean_box(0));
    lean_closure_set(v___x_3572_, 3, v_inst_3561_);
    lean_closure_set(v___x_3572_, 4, v_inst_3562_);
    lean_closure_set(v___x_3572_, 5, v_inst_3563_);
    v___x_3573_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3573_, 0, v___x_3571_);
    lean_ctor_set(v___x_3573_, 1, v___x_3572_);
    return v___x_3573_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonad(
    mut v_00_u03b1_3574_: *mut LeanObject,
    mut v_00_u03b2_3575_: *mut LeanObject,
    mut v_m_3576_: *mut LeanObject,
    mut v_inst_3577_: *mut LeanObject,
    mut v_inst_3578_: *mut LeanObject,
    mut v_inst_3579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    v___x_3580_ =
        l_Lean_MonadStateCacheT_instMonad___redArg(v_inst_3577_, v_inst_3578_, v_inst_3579_);
    return v___x_3580_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0(
    mut v_a_3581_: *mut LeanObject,
    mut v_toPure_3582_: *mut LeanObject,
    mut v_a_3583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    v___x_3584_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3584_, 0, v_a_3583_);
    lean_ctor_set(v___x_3584_, 1, v_a_3581_);
    v___x_3585_ = lean_apply_2(v_toPure_3582_, lean_box(0), v___x_3584_);
    return v___x_3585_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg(
    mut v_inst_3586_: *mut LeanObject,
    mut v_t_3587_: *mut LeanObject,
    mut v_a_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3589_ = lean_ctor_get(v_inst_3586_, 0);
    lean_inc_ref(v_toApplicative_3589_);
    v_toBind_3590_ = lean_ctor_get(v_inst_3586_, 1);
    lean_inc(v_toBind_3590_);
    lean_dec_ref(v_inst_3586_);
    v_toPure_3591_ = lean_ctor_get(v_toApplicative_3589_, 1);
    lean_inc(v_toPure_3591_);
    lean_dec_ref(v_toApplicative_3589_);
    v___f_3592_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3592_, 0, v_a_3588_);
    lean_closure_set(v___f_3592_, 1, v_toPure_3591_);
    v___x_3593_ = lean_apply_4(
        v_toBind_3590_,
        lean_box(0),
        lean_box(0),
        v_t_3587_,
        v___f_3592_,
    );
    return v___x_3593_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1(
    mut v_00_u03b1_3594_: *mut LeanObject,
    mut v_00_u03b2_3595_: *mut LeanObject,
    mut v_m_3596_: *mut LeanObject,
    mut v_inst_3597_: *mut LeanObject,
    mut v_inst_3598_: *mut LeanObject,
    mut v_inst_3599_: *mut LeanObject,
    mut v_00_u03b1_3600_: *mut LeanObject,
    mut v_t_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3603_ = lean_ctor_get(v_inst_3599_, 0);
    lean_inc_ref(v_toApplicative_3603_);
    v_toBind_3604_ = lean_ctor_get(v_inst_3599_, 1);
    lean_inc(v_toBind_3604_);
    lean_dec_ref(v_inst_3599_);
    v_toPure_3605_ = lean_ctor_get(v_toApplicative_3603_, 1);
    lean_inc(v_toPure_3605_);
    lean_dec_ref(v_toApplicative_3603_);
    v___f_3606_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3606_, 0, v_a_3602_);
    lean_closure_set(v___f_3606_, 1, v_toPure_3605_);
    v___x_3607_ = lean_apply_4(
        v_toBind_3604_,
        lean_box(0),
        lean_box(0),
        v_t_3601_,
        v___f_3606_,
    );
    return v___x_3607_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed(
    mut v_00_u03b1_3608_: *mut LeanObject,
    mut v_00_u03b2_3609_: *mut LeanObject,
    mut v_m_3610_: *mut LeanObject,
    mut v_inst_3611_: *mut LeanObject,
    mut v_inst_3612_: *mut LeanObject,
    mut v_inst_3613_: *mut LeanObject,
    mut v_00_u03b1_3614_: *mut LeanObject,
    mut v_t_3615_: *mut LeanObject,
    mut v_a_3616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3617_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3612_);
    lean_dec_ref(v_inst_3611_);
    return v_res_3617_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift___redArg(
    mut v_inst_3618_: *mut LeanObject,
    mut v_inst_3619_: *mut LeanObject,
    mut v_inst_3620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    v___x_3621_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___x_3621_, 0, lean_box(0));
    lean_closure_set(v___x_3621_, 1, lean_box(0));
    lean_closure_set(v___x_3621_, 2, lean_box(0));
    lean_closure_set(v___x_3621_, 3, v_inst_3618_);
    lean_closure_set(v___x_3621_, 4, v_inst_3619_);
    lean_closure_set(v___x_3621_, 5, v_inst_3620_);
    return v___x_3621_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadLift(
    mut v_00_u03b1_3622_: *mut LeanObject,
    mut v_00_u03b2_3623_: *mut LeanObject,
    mut v_m_3624_: *mut LeanObject,
    mut v_inst_3625_: *mut LeanObject,
    mut v_inst_3626_: *mut LeanObject,
    mut v_inst_3627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    v___x_3628_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___x_3628_, 0, lean_box(0));
    lean_closure_set(v___x_3628_, 1, lean_box(0));
    lean_closure_set(v___x_3628_, 2, lean_box(0));
    lean_closure_set(v___x_3628_, 3, v_inst_3625_);
    lean_closure_set(v___x_3628_, 4, v_inst_3626_);
    lean_closure_set(v___x_3628_, 5, v_inst_3627_);
    return v___x_3628_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___redArg(
    mut v_inst_3629_: *mut LeanObject,
    mut v_inst_3630_: *mut LeanObject,
    mut v_a_3631_: *mut LeanObject,
    mut v_a_3632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throw_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3633_ = lean_ctor_get(v_inst_3629_, 0);
    lean_inc_ref(v_toApplicative_3633_);
    v_throw_3634_ = lean_ctor_get(v_inst_3630_, 0);
    lean_inc(v_throw_3634_);
    lean_dec_ref(v_inst_3630_);
    v_toBind_3635_ = lean_ctor_get(v_inst_3629_, 1);
    lean_inc(v_toBind_3635_);
    lean_dec_ref(v_inst_3629_);
    v_toPure_3636_ = lean_ctor_get(v_toApplicative_3633_, 1);
    lean_inc(v_toPure_3636_);
    lean_dec_ref(v_toApplicative_3633_);
    v___x_3637_ = lean_apply_2(v_throw_3634_, lean_box(0), v_a_3631_);
    v___f_3638_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3638_, 0, v_a_3632_);
    lean_closure_set(v___f_3638_, 1, v_toPure_3636_);
    v___x_3639_ = lean_apply_4(
        v_toBind_3635_,
        lean_box(0),
        lean_box(0),
        v___x_3637_,
        v___f_3638_,
    );
    return v___x_3639_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1(
    mut v_00_u03b1_3640_: *mut LeanObject,
    mut v_00_u03b2_3641_: *mut LeanObject,
    mut v_m_3642_: *mut LeanObject,
    mut v_inst_3643_: *mut LeanObject,
    mut v_inst_3644_: *mut LeanObject,
    mut v_inst_3645_: *mut LeanObject,
    mut v_00_u03b5_3646_: *mut LeanObject,
    mut v_inst_3647_: *mut LeanObject,
    mut v_00_u03b1_3648_: *mut LeanObject,
    mut v_a_3649_: *mut LeanObject,
    mut v_a_3650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throw_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3651_ = lean_ctor_get(v_inst_3645_, 0);
    lean_inc_ref(v_toApplicative_3651_);
    v_throw_3652_ = lean_ctor_get(v_inst_3647_, 0);
    lean_inc(v_throw_3652_);
    lean_dec_ref(v_inst_3647_);
    v_toBind_3653_ = lean_ctor_get(v_inst_3645_, 1);
    lean_inc(v_toBind_3653_);
    lean_dec_ref(v_inst_3645_);
    v_toPure_3654_ = lean_ctor_get(v_toApplicative_3651_, 1);
    lean_inc(v_toPure_3654_);
    lean_dec_ref(v_toApplicative_3651_);
    v___x_3655_ = lean_apply_2(v_throw_3652_, lean_box(0), v_a_3649_);
    v___f_3656_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadLift___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3656_, 0, v_a_3650_);
    lean_closure_set(v___f_3656_, 1, v_toPure_3654_);
    v___x_3657_ = lean_apply_4(
        v_toBind_3653_,
        lean_box(0),
        lean_box(0),
        v___x_3655_,
        v___f_3656_,
    );
    return v___x_3657_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed(
    mut v_00_u03b1_3658_: *mut LeanObject,
    mut v_00_u03b2_3659_: *mut LeanObject,
    mut v_m_3660_: *mut LeanObject,
    mut v_inst_3661_: *mut LeanObject,
    mut v_inst_3662_: *mut LeanObject,
    mut v_inst_3663_: *mut LeanObject,
    mut v_00_u03b5_3664_: *mut LeanObject,
    mut v_inst_3665_: *mut LeanObject,
    mut v_00_u03b1_3666_: *mut LeanObject,
    mut v_a_3667_: *mut LeanObject,
    mut v_a_3668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3669_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3662_);
    lean_dec_ref(v_inst_3661_);
    return v_res_3669_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0(
    mut v_c_3670_: *mut LeanObject,
    mut v_s_3671_: *mut LeanObject,
    mut v_e_3672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    v___x_3673_ = lean_apply_2(v_c_3670_, v_e_3672_, v_s_3671_);
    return v___x_3673_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg(
    mut v_inst_3674_: *mut LeanObject,
    mut v_x_3675_: *mut LeanObject,
    mut v_c_3676_: *mut LeanObject,
    mut v_s_3677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_3678_ = lean_ctor_get(v_inst_3674_, 1);
    lean_inc(v_tryCatch_3678_);
    lean_dec_ref(v_inst_3674_);
    lean_inc_ref(v_s_3677_);
    v___f_3679_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3679_, 0, v_c_3676_);
    lean_closure_set(v___f_3679_, 1, v_s_3677_);
    v___x_3680_ = lean_apply_1(v_x_3675_, v_s_3677_);
    v___x_3681_ = lean_apply_3(v_tryCatch_3678_, lean_box(0), v___x_3680_, v___f_3679_);
    return v___x_3681_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3(
    mut v_00_u03b1_3682_: *mut LeanObject,
    mut v_00_u03b2_3683_: *mut LeanObject,
    mut v_m_3684_: *mut LeanObject,
    mut v_inst_3685_: *mut LeanObject,
    mut v_inst_3686_: *mut LeanObject,
    mut v_00_u03b5_3687_: *mut LeanObject,
    mut v_inst_3688_: *mut LeanObject,
    mut v_00_u03b1_3689_: *mut LeanObject,
    mut v_x_3690_: *mut LeanObject,
    mut v_c_3691_: *mut LeanObject,
    mut v_s_3692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_3693_ = lean_ctor_get(v_inst_3688_, 1);
    lean_inc(v_tryCatch_3693_);
    lean_dec_ref(v_inst_3688_);
    lean_inc_ref(v_s_3692_);
    v___f_3694_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3694_, 0, v_c_3691_);
    lean_closure_set(v___f_3694_, 1, v_s_3692_);
    v___x_3695_ = lean_apply_1(v_x_3690_, v_s_3692_);
    v___x_3696_ = lean_apply_3(v_tryCatch_3693_, lean_box(0), v___x_3695_, v___f_3694_);
    return v___x_3696_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed(
    mut v_00_u03b1_3697_: *mut LeanObject,
    mut v_00_u03b2_3698_: *mut LeanObject,
    mut v_m_3699_: *mut LeanObject,
    mut v_inst_3700_: *mut LeanObject,
    mut v_inst_3701_: *mut LeanObject,
    mut v_00_u03b5_3702_: *mut LeanObject,
    mut v_inst_3703_: *mut LeanObject,
    mut v_00_u03b1_3704_: *mut LeanObject,
    mut v_x_3705_: *mut LeanObject,
    mut v_c_3706_: *mut LeanObject,
    mut v_s_3707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3708_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3701_);
    lean_dec_ref(v_inst_3700_);
    return v_res_3708_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(
    mut v_inst_3709_: *mut LeanObject,
    mut v_inst_3710_: *mut LeanObject,
    mut v_inst_3711_: *mut LeanObject,
    mut v_inst_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_3712_);
    lean_inc_ref(v_inst_3710_);
    lean_inc_ref(v_inst_3709_);
    v___x_3713_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__1___boxed as *mut core::ffi::c_void,
        11,
        8,
    );
    lean_closure_set(v___x_3713_, 0, lean_box(0));
    lean_closure_set(v___x_3713_, 1, lean_box(0));
    lean_closure_set(v___x_3713_, 2, lean_box(0));
    lean_closure_set(v___x_3713_, 3, v_inst_3709_);
    lean_closure_set(v___x_3713_, 4, v_inst_3710_);
    lean_closure_set(v___x_3713_, 5, v_inst_3711_);
    lean_closure_set(v___x_3713_, 6, lean_box(0));
    lean_closure_set(v___x_3713_, 7, v_inst_3712_);
    v___x_3714_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadExceptOf___aux__3___boxed as *mut core::ffi::c_void,
        11,
        7,
    );
    lean_closure_set(v___x_3714_, 0, lean_box(0));
    lean_closure_set(v___x_3714_, 1, lean_box(0));
    lean_closure_set(v___x_3714_, 2, lean_box(0));
    lean_closure_set(v___x_3714_, 3, v_inst_3709_);
    lean_closure_set(v___x_3714_, 4, v_inst_3710_);
    lean_closure_set(v___x_3714_, 5, lean_box(0));
    lean_closure_set(v___x_3714_, 6, v_inst_3712_);
    v___x_3715_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3715_, 0, v___x_3713_);
    lean_ctor_set(v___x_3715_, 1, v___x_3714_);
    return v___x_3715_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadExceptOf(
    mut v_00_u03b1_3716_: *mut LeanObject,
    mut v_00_u03b2_3717_: *mut LeanObject,
    mut v_m_3718_: *mut LeanObject,
    mut v_inst_3719_: *mut LeanObject,
    mut v_inst_3720_: *mut LeanObject,
    mut v_inst_3721_: *mut LeanObject,
    mut v_00_u03b5_3722_: *mut LeanObject,
    mut v_inst_3723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    v___x_3724_ = l_Lean_MonadStateCacheT_instMonadExceptOf___redArg(
        v_inst_3719_,
        v_inst_3720_,
        v_inst_3721_,
        v_inst_3723_,
    );
    return v___x_3724_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0(
    mut v_fst_3725_: *mut LeanObject,
    mut v_00_u03b2_3726_: *mut LeanObject,
    mut v_x_3727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    v___x_3728_ = lean_apply_1(v_x_3727_, v_fst_3725_);
    return v___x_3728_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1(
    mut v_snd_3729_: *mut LeanObject,
    mut v_toPure_3730_: *mut LeanObject,
    mut v_a_3731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    v___x_3732_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3732_, 0, v_a_3731_);
    lean_ctor_set(v___x_3732_, 1, v_snd_3729_);
    v___x_3733_ = lean_apply_2(v_toPure_3730_, lean_box(0), v___x_3732_);
    return v___x_3733_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2(
    mut v_f_3734_: *mut LeanObject,
    mut v_toPure_3735_: *mut LeanObject,
    mut v_toBind_3736_: *mut LeanObject,
    mut v_____x_3737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    v_fst_3738_ = lean_ctor_get(v_____x_3737_, 0);
    lean_inc(v_fst_3738_);
    v_snd_3739_ = lean_ctor_get(v_____x_3737_, 1);
    lean_inc(v_snd_3739_);
    lean_dec_ref(v_____x_3737_);
    v___f_3740_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3740_, 0, v_fst_3738_);
    v___x_3741_ = lean_apply_1(v_f_3734_, v___f_3740_);
    v___f_3742_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3742_, 0, v_snd_3739_);
    lean_closure_set(v___f_3742_, 1, v_toPure_3735_);
    v___x_3743_ = lean_apply_4(
        v_toBind_3736_,
        lean_box(0),
        lean_box(0),
        v___x_3741_,
        v___f_3742_,
    );
    return v___x_3743_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg(
    mut v_inst_3744_: *mut LeanObject,
    mut v_f_3745_: *mut LeanObject,
    mut v_a_3746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3751_: u8 = 0;
    let mut v_toPure_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3747_ = lean_ctor_get(v_inst_3744_, 0);
                v_toBind_3748_ = lean_ctor_get(v_inst_3744_, 1);
                v_isSharedCheck_3759_ = (!lean_is_exclusive(v_inst_3744_)) as u8;
                if v_isSharedCheck_3759_ == 0 {
                    v___x_3750_ = v_inst_3744_;
                    v_isShared_3751_ = v_isSharedCheck_3759_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_3748_);
                    lean_inc(v_toApplicative_3747_);
                    lean_dec(v_inst_3744_);
                    v___x_3750_ = lean_box(0);
                    v_isShared_3751_ = v_isSharedCheck_3759_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3752_ = lean_ctor_get(v_toApplicative_3747_, 1);
                lean_inc_n(v_toPure_3752_, 2);
                lean_dec_ref(v_toApplicative_3747_);
                lean_inc(v_toBind_3748_);
                v___f_3753_ = lean_alloc_closure(
                    l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3753_, 0, v_f_3745_);
                lean_closure_set(v___f_3753_, 1, v_toPure_3752_);
                lean_closure_set(v___f_3753_, 2, v_toBind_3748_);
                lean_inc_ref(v_a_3746_);
                if v_isShared_3751_ == 0 {
                    lean_ctor_set(v___x_3750_, 1, v_a_3746_);
                    lean_ctor_set(v___x_3750_, 0, v_a_3746_);
                    v___x_3755_ = v___x_3750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3746_);
                    lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_a_3746_);
                    v___x_3755_ = v_reuseFailAlloc_3758_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3756_ = lean_apply_2(v_toPure_3752_, lean_box(0), v___x_3755_);
                v___x_3757_ = lean_apply_4(
                    v_toBind_3748_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_00_u03b1_3760_: *mut LeanObject,
    mut v_00_u03b2_3761_: *mut LeanObject,
    mut v_m_3762_: *mut LeanObject,
    mut v_inst_3763_: *mut LeanObject,
    mut v_inst_3764_: *mut LeanObject,
    mut v_inst_3765_: *mut LeanObject,
    mut v_00_u03b1_3766_: *mut LeanObject,
    mut v_f_3767_: *mut LeanObject,
    mut v_a_3768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3773_: u8 = 0;
    let mut v_toPure_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3769_ = lean_ctor_get(v_inst_3765_, 0);
                v_toBind_3770_ = lean_ctor_get(v_inst_3765_, 1);
                v_isSharedCheck_3781_ = (!lean_is_exclusive(v_inst_3765_)) as u8;
                if v_isSharedCheck_3781_ == 0 {
                    v___x_3772_ = v_inst_3765_;
                    v_isShared_3773_ = v_isSharedCheck_3781_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_3770_);
                    lean_inc(v_toApplicative_3769_);
                    lean_dec(v_inst_3765_);
                    v___x_3772_ = lean_box(0);
                    v_isShared_3773_ = v_isSharedCheck_3781_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_3774_ = lean_ctor_get(v_toApplicative_3769_, 1);
                lean_inc_n(v_toPure_3774_, 2);
                lean_dec_ref(v_toApplicative_3769_);
                lean_inc(v_toBind_3770_);
                v___f_3775_ = lean_alloc_closure(
                    l_Lean_MonadStateCacheT_instMonadControl___aux__1___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3775_, 0, v_f_3767_);
                lean_closure_set(v___f_3775_, 1, v_toPure_3774_);
                lean_closure_set(v___f_3775_, 2, v_toBind_3770_);
                lean_inc_ref(v_a_3768_);
                if v_isShared_3773_ == 0 {
                    lean_ctor_set(v___x_3772_, 1, v_a_3768_);
                    lean_ctor_set(v___x_3772_, 0, v_a_3768_);
                    v___x_3777_ = v___x_3772_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3768_);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_a_3768_);
                    v___x_3777_ = v_reuseFailAlloc_3780_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3778_ = lean_apply_2(v_toPure_3774_, lean_box(0), v___x_3777_);
                v___x_3779_ = lean_apply_4(
                    v_toBind_3770_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_00_u03b1_3782_: *mut LeanObject,
    mut v_00_u03b2_3783_: *mut LeanObject,
    mut v_m_3784_: *mut LeanObject,
    mut v_inst_3785_: *mut LeanObject,
    mut v_inst_3786_: *mut LeanObject,
    mut v_inst_3787_: *mut LeanObject,
    mut v_00_u03b1_3788_: *mut LeanObject,
    mut v_f_3789_: *mut LeanObject,
    mut v_a_3790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3791_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3786_);
    lean_dec_ref(v_inst_3785_);
    return v_res_3791_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0(
    mut v_fst_3792_: *mut LeanObject,
    mut v_toPure_3793_: *mut LeanObject,
    mut v_____x_3794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3798_: u8 = 0;
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_unused_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3795_ = lean_ctor_get(v_____x_3794_, 1);
                v_isSharedCheck_3803_ = (!lean_is_exclusive(v_____x_3794_)) as u8;
                if v_isSharedCheck_3803_ == 0 {
                    v_unused_3804_ = lean_ctor_get(v_____x_3794_, 0);
                    lean_dec(v_unused_3804_);
                    v___x_3797_ = v_____x_3794_;
                    v_isShared_3798_ = v_isSharedCheck_3803_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3795_);
                    lean_dec(v_____x_3794_);
                    v___x_3797_ = lean_box(0);
                    v_isShared_3798_ = v_isSharedCheck_3803_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3798_ == 0 {
                    lean_ctor_set(v___x_3797_, 0, v_fst_3792_);
                    v___x_3800_ = v___x_3797_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_fst_3792_);
                    lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_snd_3795_);
                    v___x_3800_ = v_reuseFailAlloc_3802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3801_ = lean_apply_2(v_toPure_3793_, lean_box(0), v___x_3800_);
                return v___x_3801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1(
    mut v_toPure_3805_: *mut LeanObject,
    mut v_toBind_3806_: *mut LeanObject,
    mut v_____x_3807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3813_: u8 = 0;
    let mut v___f_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3808_ = lean_ctor_get(v_____x_3807_, 0);
                lean_inc(v_fst_3808_);
                lean_dec_ref(v_____x_3807_);
                v_fst_3809_ = lean_ctor_get(v_fst_3808_, 0);
                v_snd_3810_ = lean_ctor_get(v_fst_3808_, 1);
                v_isSharedCheck_3821_ = (!lean_is_exclusive(v_fst_3808_)) as u8;
                if v_isSharedCheck_3821_ == 0 {
                    v___x_3812_ = v_fst_3808_;
                    v_isShared_3813_ = v_isSharedCheck_3821_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3810_);
                    lean_inc(v_fst_3809_);
                    lean_dec(v_fst_3808_);
                    v___x_3812_ = lean_box(0);
                    v_isShared_3813_ = v_isSharedCheck_3821_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_toPure_3805_);
                v___f_3814_ = lean_alloc_closure(
                    l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_3814_, 0, v_fst_3809_);
                lean_closure_set(v___f_3814_, 1, v_toPure_3805_);
                v___x_3815_ = lean_box(0);
                if v_isShared_3813_ == 0 {
                    lean_ctor_set(v___x_3812_, 0, v___x_3815_);
                    v___x_3817_ = v___x_3812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3815_);
                    lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_snd_3810_);
                    v___x_3817_ = v_reuseFailAlloc_3820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3818_ = lean_apply_2(v_toPure_3805_, lean_box(0), v___x_3817_);
                v___x_3819_ = lean_apply_4(
                    v_toBind_3806_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_a_3822_: *mut LeanObject,
    mut v_toPure_3823_: *mut LeanObject,
    mut v_a_3824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    v___x_3825_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3825_, 0, v_a_3824_);
    lean_ctor_set(v___x_3825_, 1, v_a_3822_);
    v___x_3826_ = lean_apply_2(v_toPure_3823_, lean_box(0), v___x_3825_);
    return v___x_3826_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg(
    mut v_inst_3827_: *mut LeanObject,
    mut v_x_3828_: *mut LeanObject,
    mut v_a_3829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3830_ = lean_ctor_get(v_inst_3827_, 0);
    lean_inc_ref(v_toApplicative_3830_);
    v_toBind_3831_ = lean_ctor_get(v_inst_3827_, 1);
    lean_inc_n(v_toBind_3831_, 3);
    lean_dec_ref(v_inst_3827_);
    v_toPure_3832_ = lean_ctor_get(v_toApplicative_3830_, 1);
    lean_inc_n(v_toPure_3832_, 2);
    lean_dec_ref(v_toApplicative_3830_);
    v___f_3833_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3833_, 0, v_toPure_3832_);
    lean_closure_set(v___f_3833_, 1, v_toBind_3831_);
    v___f_3834_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3834_, 0, v_a_3829_);
    lean_closure_set(v___f_3834_, 1, v_toPure_3832_);
    v___x_3835_ = lean_apply_4(
        v_toBind_3831_,
        lean_box(0),
        lean_box(0),
        v_x_3828_,
        v___f_3834_,
    );
    v___x_3836_ = lean_apply_4(
        v_toBind_3831_,
        lean_box(0),
        lean_box(0),
        v___x_3835_,
        v___f_3833_,
    );
    return v___x_3836_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3(
    mut v_00_u03b1_3837_: *mut LeanObject,
    mut v_00_u03b2_3838_: *mut LeanObject,
    mut v_m_3839_: *mut LeanObject,
    mut v_inst_3840_: *mut LeanObject,
    mut v_inst_3841_: *mut LeanObject,
    mut v_inst_3842_: *mut LeanObject,
    mut v_00_u03b1_3843_: *mut LeanObject,
    mut v_x_3844_: *mut LeanObject,
    mut v_a_3845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3846_ = lean_ctor_get(v_inst_3842_, 0);
    lean_inc_ref(v_toApplicative_3846_);
    v_toBind_3847_ = lean_ctor_get(v_inst_3842_, 1);
    lean_inc_n(v_toBind_3847_, 3);
    lean_dec_ref(v_inst_3842_);
    v_toPure_3848_ = lean_ctor_get(v_toApplicative_3846_, 1);
    lean_inc_n(v_toPure_3848_, 2);
    lean_dec_ref(v_toApplicative_3846_);
    v___f_3849_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3849_, 0, v_toPure_3848_);
    lean_closure_set(v___f_3849_, 1, v_toBind_3847_);
    v___f_3850_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___redArg___lam__2
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3850_, 0, v_a_3845_);
    lean_closure_set(v___f_3850_, 1, v_toPure_3848_);
    v___x_3851_ = lean_apply_4(
        v_toBind_3847_,
        lean_box(0),
        lean_box(0),
        v_x_3844_,
        v___f_3850_,
    );
    v___x_3852_ = lean_apply_4(
        v_toBind_3847_,
        lean_box(0),
        lean_box(0),
        v___x_3851_,
        v___f_3849_,
    );
    return v___x_3852_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed(
    mut v_00_u03b1_3853_: *mut LeanObject,
    mut v_00_u03b2_3854_: *mut LeanObject,
    mut v_m_3855_: *mut LeanObject,
    mut v_inst_3856_: *mut LeanObject,
    mut v_inst_3857_: *mut LeanObject,
    mut v_inst_3858_: *mut LeanObject,
    mut v_00_u03b1_3859_: *mut LeanObject,
    mut v_x_3860_: *mut LeanObject,
    mut v_a_3861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3862_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3857_);
    lean_dec_ref(v_inst_3856_);
    return v_res_3862_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl___redArg(
    mut v_inst_3863_: *mut LeanObject,
    mut v_inst_3864_: *mut LeanObject,
    mut v_inst_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_3865_);
    lean_inc_ref(v_inst_3864_);
    lean_inc_ref(v_inst_3863_);
    v___x_3866_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__1___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___x_3866_, 0, lean_box(0));
    lean_closure_set(v___x_3866_, 1, lean_box(0));
    lean_closure_set(v___x_3866_, 2, lean_box(0));
    lean_closure_set(v___x_3866_, 3, v_inst_3863_);
    lean_closure_set(v___x_3866_, 4, v_inst_3864_);
    lean_closure_set(v___x_3866_, 5, v_inst_3865_);
    v___x_3867_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadControl___aux__3___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___x_3867_, 0, lean_box(0));
    lean_closure_set(v___x_3867_, 1, lean_box(0));
    lean_closure_set(v___x_3867_, 2, lean_box(0));
    lean_closure_set(v___x_3867_, 3, v_inst_3863_);
    lean_closure_set(v___x_3867_, 4, v_inst_3864_);
    lean_closure_set(v___x_3867_, 5, v_inst_3865_);
    v___x_3868_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3868_, 0, v___x_3866_);
    lean_ctor_set(v___x_3868_, 1, v___x_3867_);
    return v___x_3868_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadControl(
    mut v_00_u03b1_3869_: *mut LeanObject,
    mut v_00_u03b2_3870_: *mut LeanObject,
    mut v_m_3871_: *mut LeanObject,
    mut v_inst_3872_: *mut LeanObject,
    mut v_inst_3873_: *mut LeanObject,
    mut v_inst_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    v___x_3875_ =
        l_Lean_MonadStateCacheT_instMonadControl___redArg(v_inst_3872_, v_inst_3873_, v_inst_3874_);
    return v___x_3875_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0(
    mut v_h_3876_: *mut LeanObject,
    mut v_s_3877_: *mut LeanObject,
    mut v_x_3878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3884_: u8 = 0;
    let mut v_fst_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3878_) == 0 {
                    v___x_3879_ = lean_box(0);
                    v___x_3880_ = lean_apply_2(v_h_3876_, v___x_3879_, v_s_3877_);
                    return v___x_3880_;
                } else {
                    lean_dec_ref(v_s_3877_);
                    v_val_3881_ = lean_ctor_get(v_x_3878_, 0);
                    v_isSharedCheck_3891_ = (!lean_is_exclusive(v_x_3878_)) as u8;
                    if v_isSharedCheck_3891_ == 0 {
                        v___x_3883_ = v_x_3878_;
                        v_isShared_3884_ = v_isSharedCheck_3891_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3881_);
                        lean_dec(v_x_3878_);
                        v___x_3883_ = lean_box(0);
                        v_isShared_3884_ = v_isSharedCheck_3891_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3885_ = lean_ctor_get(v_val_3881_, 0);
                lean_inc(v_fst_3885_);
                v_snd_3886_ = lean_ctor_get(v_val_3881_, 1);
                lean_inc(v_snd_3886_);
                lean_dec(v_val_3881_);
                if v_isShared_3884_ == 0 {
                    lean_ctor_set(v___x_3883_, 0, v_fst_3885_);
                    v___x_3888_ = v___x_3883_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_fst_3885_);
                    v___x_3888_ = v_reuseFailAlloc_3890_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3889_ = lean_apply_2(v_h_3876_, v___x_3888_, v_snd_3886_);
                return v___x_3889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1(
    mut v_toPure_3892_: *mut LeanObject,
    mut v_____x_3893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v_fst_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3904_: u8 = 0;
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3912_: u8 = 0;
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_unused_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3894_ = lean_ctor_get(v_____x_3893_, 0);
                lean_inc(v_fst_3894_);
                v_snd_3895_ = lean_ctor_get(v_____x_3893_, 1);
                lean_inc(v_snd_3895_);
                lean_dec_ref(v_____x_3893_);
                v_fst_3896_ = lean_ctor_get(v_fst_3894_, 0);
                v_isSharedCheck_3913_ = (!lean_is_exclusive(v_fst_3894_)) as u8;
                if v_isSharedCheck_3913_ == 0 {
                    v_unused_3914_ = lean_ctor_get(v_fst_3894_, 1);
                    lean_dec(v_unused_3914_);
                    v___x_3898_ = v_fst_3894_;
                    v_isShared_3899_ = v_isSharedCheck_3913_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fst_3896_);
                    lean_dec(v_fst_3894_);
                    v___x_3898_ = lean_box(0);
                    v_isShared_3899_ = v_isSharedCheck_3913_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3900_ = lean_ctor_get(v_snd_3895_, 0);
                v_snd_3901_ = lean_ctor_get(v_snd_3895_, 1);
                v_isSharedCheck_3912_ = (!lean_is_exclusive(v_snd_3895_)) as u8;
                if v_isSharedCheck_3912_ == 0 {
                    v___x_3903_ = v_snd_3895_;
                    v_isShared_3904_ = v_isSharedCheck_3912_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3901_);
                    lean_inc(v_fst_3900_);
                    lean_dec(v_snd_3895_);
                    v___x_3903_ = lean_box(0);
                    v_isShared_3904_ = v_isSharedCheck_3912_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3904_ == 0 {
                    lean_ctor_set(v___x_3903_, 1, v_fst_3900_);
                    lean_ctor_set(v___x_3903_, 0, v_fst_3896_);
                    v___x_3906_ = v___x_3903_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_fst_3896_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_fst_3900_);
                    v___x_3906_ = v_reuseFailAlloc_3911_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3899_ == 0 {
                    lean_ctor_set(v___x_3898_, 1, v_snd_3901_);
                    lean_ctor_set(v___x_3898_, 0, v___x_3906_);
                    v___x_3908_ = v___x_3898_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3906_);
                    lean_ctor_set(v_reuseFailAlloc_3910_, 1, v_snd_3901_);
                    v___x_3908_ = v_reuseFailAlloc_3910_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3909_ = lean_apply_2(v_toPure_3892_, lean_box(0), v___x_3908_);
                return v___x_3909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg(
    mut v_inst_3915_: *mut LeanObject,
    mut v_inst_3916_: *mut LeanObject,
    mut v_x_3917_: *mut LeanObject,
    mut v_h_3918_: *mut LeanObject,
    mut v_s_3919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3920_ = lean_ctor_get(v_inst_3915_, 0);
    lean_inc_ref(v_toApplicative_3920_);
    v_toBind_3921_ = lean_ctor_get(v_inst_3915_, 1);
    lean_inc(v_toBind_3921_);
    lean_dec_ref(v_inst_3915_);
    v_toPure_3922_ = lean_ctor_get(v_toApplicative_3920_, 1);
    lean_inc(v_toPure_3922_);
    lean_dec_ref(v_toApplicative_3920_);
    lean_inc_ref(v_s_3919_);
    v___f_3923_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3923_, 0, v_h_3918_);
    lean_closure_set(v___f_3923_, 1, v_s_3919_);
    v___x_3924_ = lean_apply_1(v_x_3917_, v_s_3919_);
    v___f_3925_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3925_, 0, v_toPure_3922_);
    v___x_3926_ = lean_apply_4(
        v_inst_3916_,
        lean_box(0),
        lean_box(0),
        v___x_3924_,
        v___f_3923_,
    );
    v___x_3927_ = lean_apply_4(
        v_toBind_3921_,
        lean_box(0),
        lean_box(0),
        v___x_3926_,
        v___f_3925_,
    );
    return v___x_3927_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1(
    mut v_00_u03b1_3928_: *mut LeanObject,
    mut v_00_u03b2_3929_: *mut LeanObject,
    mut v_m_3930_: *mut LeanObject,
    mut v_inst_3931_: *mut LeanObject,
    mut v_inst_3932_: *mut LeanObject,
    mut v_inst_3933_: *mut LeanObject,
    mut v_inst_3934_: *mut LeanObject,
    mut v_00_u03b1_3935_: *mut LeanObject,
    mut v_00_u03b2_3936_: *mut LeanObject,
    mut v_x_3937_: *mut LeanObject,
    mut v_h_3938_: *mut LeanObject,
    mut v_s_3939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3940_ = lean_ctor_get(v_inst_3933_, 0);
    lean_inc_ref(v_toApplicative_3940_);
    v_toBind_3941_ = lean_ctor_get(v_inst_3933_, 1);
    lean_inc(v_toBind_3941_);
    lean_dec_ref(v_inst_3933_);
    v_toPure_3942_ = lean_ctor_get(v_toApplicative_3940_, 1);
    lean_inc(v_toPure_3942_);
    lean_dec_ref(v_toApplicative_3940_);
    lean_inc_ref(v_s_3939_);
    v___f_3943_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3943_, 0, v_h_3938_);
    lean_closure_set(v___f_3943_, 1, v_s_3939_);
    v___x_3944_ = lean_apply_1(v_x_3937_, v_s_3939_);
    v___f_3945_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3945_, 0, v_toPure_3942_);
    v___x_3946_ = lean_apply_4(
        v_inst_3934_,
        lean_box(0),
        lean_box(0),
        v___x_3944_,
        v___f_3943_,
    );
    v___x_3947_ = lean_apply_4(
        v_toBind_3941_,
        lean_box(0),
        lean_box(0),
        v___x_3946_,
        v___f_3945_,
    );
    return v___x_3947_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed(
    mut v_00_u03b1_3948_: *mut LeanObject,
    mut v_00_u03b2_3949_: *mut LeanObject,
    mut v_m_3950_: *mut LeanObject,
    mut v_inst_3951_: *mut LeanObject,
    mut v_inst_3952_: *mut LeanObject,
    mut v_inst_3953_: *mut LeanObject,
    mut v_inst_3954_: *mut LeanObject,
    mut v_00_u03b1_3955_: *mut LeanObject,
    mut v_00_u03b2_3956_: *mut LeanObject,
    mut v_x_3957_: *mut LeanObject,
    mut v_h_3958_: *mut LeanObject,
    mut v_s_3959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3960_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_3952_);
    lean_dec_ref(v_inst_3951_);
    return v_res_3960_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally___redArg(
    mut v_inst_3961_: *mut LeanObject,
    mut v_inst_3962_: *mut LeanObject,
    mut v_inst_3963_: *mut LeanObject,
    mut v_inst_3964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    v___x_3965_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    lean_closure_set(v___x_3965_, 0, lean_box(0));
    lean_closure_set(v___x_3965_, 1, lean_box(0));
    lean_closure_set(v___x_3965_, 2, lean_box(0));
    lean_closure_set(v___x_3965_, 3, v_inst_3961_);
    lean_closure_set(v___x_3965_, 4, v_inst_3962_);
    lean_closure_set(v___x_3965_, 5, v_inst_3963_);
    lean_closure_set(v___x_3965_, 6, v_inst_3964_);
    return v___x_3965_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadFinally(
    mut v_00_u03b1_3966_: *mut LeanObject,
    mut v_00_u03b2_3967_: *mut LeanObject,
    mut v_m_3968_: *mut LeanObject,
    mut v_inst_3969_: *mut LeanObject,
    mut v_inst_3970_: *mut LeanObject,
    mut v_inst_3971_: *mut LeanObject,
    mut v_inst_3972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    v___x_3973_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadFinally___aux__1___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    lean_closure_set(v___x_3973_, 0, lean_box(0));
    lean_closure_set(v___x_3973_, 1, lean_box(0));
    lean_closure_set(v___x_3973_, 2, lean_box(0));
    lean_closure_set(v___x_3973_, 3, v_inst_3969_);
    lean_closure_set(v___x_3973_, 4, v_inst_3970_);
    lean_closure_set(v___x_3973_, 5, v_inst_3971_);
    lean_closure_set(v___x_3973_, 6, v_inst_3972_);
    return v___x_3973_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0(
    mut v_a_3974_: *mut LeanObject,
    mut v_toPure_3975_: *mut LeanObject,
    mut v_a_3976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    v___x_3977_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3977_, 0, v_a_3976_);
    lean_ctor_set(v___x_3977_, 1, v_a_3974_);
    v___x_3978_ = lean_apply_2(v_toPure_3975_, lean_box(0), v___x_3977_);
    return v___x_3978_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg(
    mut v_inst_3979_: *mut LeanObject,
    mut v_inst_3980_: *mut LeanObject,
    mut v_a_3981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3982_ = lean_ctor_get(v_inst_3979_, 0);
    lean_inc_ref(v_toApplicative_3982_);
    v_getRef_3983_ = lean_ctor_get(v_inst_3980_, 0);
    lean_inc(v_getRef_3983_);
    lean_dec_ref(v_inst_3980_);
    v_toBind_3984_ = lean_ctor_get(v_inst_3979_, 1);
    lean_inc(v_toBind_3984_);
    lean_dec_ref(v_inst_3979_);
    v_toPure_3985_ = lean_ctor_get(v_toApplicative_3982_, 1);
    lean_inc(v_toPure_3985_);
    lean_dec_ref(v_toApplicative_3982_);
    v___f_3986_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3986_, 0, v_a_3981_);
    lean_closure_set(v___f_3986_, 1, v_toPure_3985_);
    v___x_3987_ = lean_apply_4(
        v_toBind_3984_,
        lean_box(0),
        lean_box(0),
        v_getRef_3983_,
        v___f_3986_,
    );
    return v___x_3987_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1(
    mut v_00_u03b1_3988_: *mut LeanObject,
    mut v_00_u03b2_3989_: *mut LeanObject,
    mut v_m_3990_: *mut LeanObject,
    mut v_inst_3991_: *mut LeanObject,
    mut v_inst_3992_: *mut LeanObject,
    mut v_inst_3993_: *mut LeanObject,
    mut v_inst_3994_: *mut LeanObject,
    mut v_a_3995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3996_ = lean_ctor_get(v_inst_3993_, 0);
    lean_inc_ref(v_toApplicative_3996_);
    v_getRef_3997_ = lean_ctor_get(v_inst_3994_, 0);
    lean_inc(v_getRef_3997_);
    lean_dec_ref(v_inst_3994_);
    v_toBind_3998_ = lean_ctor_get(v_inst_3993_, 1);
    lean_inc(v_toBind_3998_);
    lean_dec_ref(v_inst_3993_);
    v_toPure_3999_ = lean_ctor_get(v_toApplicative_3996_, 1);
    lean_inc(v_toPure_3999_);
    lean_dec_ref(v_toApplicative_3996_);
    v___f_4000_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4000_, 0, v_a_3995_);
    lean_closure_set(v___f_4000_, 1, v_toPure_3999_);
    v___x_4001_ = lean_apply_4(
        v_toBind_3998_,
        lean_box(0),
        lean_box(0),
        v_getRef_3997_,
        v___f_4000_,
    );
    return v___x_4001_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed(
    mut v_00_u03b1_4002_: *mut LeanObject,
    mut v_00_u03b2_4003_: *mut LeanObject,
    mut v_m_4004_: *mut LeanObject,
    mut v_inst_4005_: *mut LeanObject,
    mut v_inst_4006_: *mut LeanObject,
    mut v_inst_4007_: *mut LeanObject,
    mut v_inst_4008_: *mut LeanObject,
    mut v_a_4009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4010_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_4006_);
    lean_dec_ref(v_inst_4005_);
    return v_res_4010_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__3___redArg(
    mut v_inst_4011_: *mut LeanObject,
    mut v_ref_4012_: *mut LeanObject,
    mut v_x_4013_: *mut LeanObject,
    mut v_a_4014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_withRef_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    v_withRef_4015_ = lean_ctor_get(v_inst_4011_, 1);
    lean_inc(v_withRef_4015_);
    lean_dec_ref(v_inst_4011_);
    v___x_4016_ = lean_apply_1(v_x_4013_, v_a_4014_);
    v___x_4017_ = lean_apply_3(v_withRef_4015_, lean_box(0), v_ref_4012_, v___x_4016_);
    return v___x_4017_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__3(
    mut v_00_u03b1_4018_: *mut LeanObject,
    mut v_00_u03b2_4019_: *mut LeanObject,
    mut v_m_4020_: *mut LeanObject,
    mut v_inst_4021_: *mut LeanObject,
    mut v_inst_4022_: *mut LeanObject,
    mut v_inst_4023_: *mut LeanObject,
    mut v_00_u03b1_4024_: *mut LeanObject,
    mut v_ref_4025_: *mut LeanObject,
    mut v_x_4026_: *mut LeanObject,
    mut v_a_4027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_withRef_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    v_withRef_4028_ = lean_ctor_get(v_inst_4023_, 1);
    lean_inc(v_withRef_4028_);
    lean_dec_ref(v_inst_4023_);
    v___x_4029_ = lean_apply_1(v_x_4026_, v_a_4027_);
    v___x_4030_ = lean_apply_3(v_withRef_4028_, lean_box(0), v_ref_4025_, v___x_4029_);
    return v___x_4030_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed(
    mut v_00_u03b1_4031_: *mut LeanObject,
    mut v_00_u03b2_4032_: *mut LeanObject,
    mut v_m_4033_: *mut LeanObject,
    mut v_inst_4034_: *mut LeanObject,
    mut v_inst_4035_: *mut LeanObject,
    mut v_inst_4036_: *mut LeanObject,
    mut v_00_u03b1_4037_: *mut LeanObject,
    mut v_ref_4038_: *mut LeanObject,
    mut v_x_4039_: *mut LeanObject,
    mut v_a_4040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4041_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_4035_);
    lean_dec_ref(v_inst_4034_);
    return v_res_4041_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef___redArg(
    mut v_inst_4042_: *mut LeanObject,
    mut v_inst_4043_: *mut LeanObject,
    mut v_inst_4044_: *mut LeanObject,
    mut v_inst_4045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_4045_);
    lean_inc_ref(v_inst_4043_);
    lean_inc_ref(v_inst_4042_);
    v___x_4046_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___x_4046_, 0, lean_box(0));
    lean_closure_set(v___x_4046_, 1, lean_box(0));
    lean_closure_set(v___x_4046_, 2, lean_box(0));
    lean_closure_set(v___x_4046_, 3, v_inst_4042_);
    lean_closure_set(v___x_4046_, 4, v_inst_4043_);
    lean_closure_set(v___x_4046_, 5, v_inst_4044_);
    lean_closure_set(v___x_4046_, 6, v_inst_4045_);
    v___x_4047_ = lean_alloc_closure(
        l_Lean_MonadStateCacheT_instMonadRef___aux__3___boxed as *mut core::ffi::c_void,
        10,
        6,
    );
    lean_closure_set(v___x_4047_, 0, lean_box(0));
    lean_closure_set(v___x_4047_, 1, lean_box(0));
    lean_closure_set(v___x_4047_, 2, lean_box(0));
    lean_closure_set(v___x_4047_, 3, v_inst_4042_);
    lean_closure_set(v___x_4047_, 4, v_inst_4043_);
    lean_closure_set(v___x_4047_, 5, v_inst_4045_);
    v___x_4048_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4048_, 0, v___x_4046_);
    lean_ctor_set(v___x_4048_, 1, v___x_4047_);
    return v___x_4048_;
}
pub unsafe fn l_Lean_MonadStateCacheT_instMonadRef(
    mut v_00_u03b1_4049_: *mut LeanObject,
    mut v_00_u03b2_4050_: *mut LeanObject,
    mut v_m_4051_: *mut LeanObject,
    mut v_inst_4052_: *mut LeanObject,
    mut v_inst_4053_: *mut LeanObject,
    mut v_inst_4054_: *mut LeanObject,
    mut v_inst_4055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    v___x_4056_ = l_Lean_MonadStateCacheT_instMonadRef___redArg(
        v_inst_4052_,
        v_inst_4053_,
        v_inst_4054_,
        v_inst_4055_,
    );
    return v___x_4056_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_MonadCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_MonadCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_MonadCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_MonadCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_MonadCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_MonadCache(builtin);
}
