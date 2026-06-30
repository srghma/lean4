// Lean compiler output
// Module: Lean.Meta.ForEachExpr
// Imports: Lean.Meta.Basic Init.Data.Range.Polymorphic.Iterators
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_array_uset, lean_expr_eqv, lean_expr_instantiate_rev, lean_infer_type, lean_mk_array,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::Basic::{
    l_instMonadControlTOfMonadControl___redArg___lam__3,
    l_instMonadControlTOfMonadControl___redArg___lam__4,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::System::ST::{
    l_ST_Prim_Ref_get___boxed, l_ST_Prim_Ref_modifyGetUnsafe___boxed, l_ST_Prim_mkRef___boxed,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_eqv___boxed,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar, l_Lean_Expr_hash,
    l_Lean_Expr_hash___boxed, l_Lean_Expr_isApp, l_Lean_Expr_isMVar, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_userName;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_MVarId_getDecl,
    l_Lean_MVarId_getDecl___boxed, l_Lean_Meta_getFVarLocalDecl___redArg,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_withLetDecl___redArg,
    l_Lean_Meta_withLocalDecl___redArg, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_setMVarUserNameTemporarily, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::MonadCache::{
    l_Lean_MonadCacheT_instMonad___redArg, l_Lean_MonadCacheT_instMonadControl___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
pub static l_Lean_Meta_visitLambda___redArg___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_visitLambda___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_visitLambda___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_eqv___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_forEachExpr_x27___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_forEachExpr_x27___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_forEachExpr_x27___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_forEachExpr_x27___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_forEachExpr_x27___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_setMVarUserNamesAt___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_setMVarUserNamesAt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_setMVarUserNamesAt___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1(
    mut v_inst_2102_: *mut leanh::LeanObject,
    mut v_inst_2103_: *mut leanh::LeanObject,
    mut v_binderName_2104_: *mut leanh::LeanObject,
    mut v_binderInfo_2105_: u8,
    mut v_d_2106_: *mut leanh::LeanObject,
    mut v___f_2107_: *mut leanh::LeanObject,
    mut v_____r_2108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2109_: u8 = 0;
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2109_ = 0;
    v___x_2110_ = l_Lean_Meta_withLocalDecl___redArg(
        v_inst_2102_,
        v_inst_2103_,
        v_binderName_2104_,
        v_binderInfo_2105_,
        v_d_2106_,
        v___f_2107_,
        v___x_2109_,
    );
    return v___x_2110_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1___boxed(
    mut v_inst_2111_: *mut leanh::LeanObject,
    mut v_inst_2112_: *mut leanh::LeanObject,
    mut v_binderName_2113_: *mut leanh::LeanObject,
    mut v_binderInfo_2114_: *mut leanh::LeanObject,
    mut v_d_2115_: *mut leanh::LeanObject,
    mut v___f_2116_: *mut leanh::LeanObject,
    mut v_____r_2117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_66__boxed_2118_: u8 = 0;
    let mut v_res_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_66__boxed_2118_ = (leanh::lean_unbox(v_binderInfo_2114_) as u8);
    v_res_2119_ =
        l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1(
            v_inst_2111_,
            v_inst_2112_,
            v_binderName_2113_,
            v_binderInfo_66__boxed_2118_,
            v_d_2115_,
            v___f_2116_,
            v_____r_2117_,
        );
    return v_res_2119_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(
    mut v_inst_2120_: *mut leanh::LeanObject,
    mut v_inst_2121_: *mut leanh::LeanObject,
    mut v_f_2122_: *mut leanh::LeanObject,
    mut v_fvars_2123_: *mut leanh::LeanObject,
    mut v_a_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_2124_) == 6 {
        let mut v_toBind_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderName_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_2129_: u8 = 0;
        let mut v___f_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_d_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2125_ = leanh::lean_ctor_get(v_inst_2120_, 1);
        leanh::lean_inc(v_toBind_2125_);
        v_binderName_2126_ = leanh::lean_ctor_get(v_a_2124_, 0);
        leanh::lean_inc(v_binderName_2126_);
        v_binderType_2127_ = leanh::lean_ctor_get(v_a_2124_, 1);
        leanh::lean_inc_ref(v_binderType_2127_);
        v_body_2128_ = leanh::lean_ctor_get(v_a_2124_, 2);
        leanh::lean_inc_ref(v_body_2128_);
        v_binderInfo_2129_ = leanh::lean_ctor_get_uint8(
            v_a_2124_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_a_2124_, 3);
        leanh::lean_inc(v_f_2122_);
        leanh::lean_inc_ref(v_inst_2121_);
        leanh::lean_inc_ref(v_inst_2120_);
        leanh::lean_inc_ref(v_fvars_2123_);
        v___f_2130_ = leanh::lean_alloc_closure(
            l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__0
                as *mut core::ffi::c_void,
            6,
            5,
        );
        leanh::lean_closure_set(v___f_2130_, 0, v_fvars_2123_);
        leanh::lean_closure_set(v___f_2130_, 1, v_inst_2120_);
        leanh::lean_closure_set(v___f_2130_, 2, v_inst_2121_);
        leanh::lean_closure_set(v___f_2130_, 3, v_f_2122_);
        leanh::lean_closure_set(v___f_2130_, 4, v_body_2128_);
        v_d_2131_ = lean_expr_instantiate_rev(v_binderType_2127_, v_fvars_2123_);
        leanh::lean_dec_ref(v_fvars_2123_);
        leanh::lean_dec_ref(v_binderType_2127_);
        v___x_2132_ = leanh::lean_box((v_binderInfo_2129_) as usize);
        leanh::lean_inc_ref(v_d_2131_);
        v___f_2133_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1___boxed as *mut core::ffi::c_void, 7, 6);
        leanh::lean_closure_set(v___f_2133_, 0, v_inst_2121_);
        leanh::lean_closure_set(v___f_2133_, 1, v_inst_2120_);
        leanh::lean_closure_set(v___f_2133_, 2, v_binderName_2126_);
        leanh::lean_closure_set(v___f_2133_, 3, v___x_2132_);
        leanh::lean_closure_set(v___f_2133_, 4, v_d_2131_);
        leanh::lean_closure_set(v___f_2133_, 5, v___f_2130_);
        v___x_2134_ = leanh::lean_apply_1(v_f_2122_, v_d_2131_);
        v___x_2135_ = leanh::lean_apply_4(
            v_toBind_2125_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2134_,
            v___f_2133_,
        );
        return v___x_2135_;
    } else {
        let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2121_);
        leanh::lean_dec_ref(v_inst_2120_);
        v___x_2136_ = lean_expr_instantiate_rev(v_a_2124_, v_fvars_2123_);
        leanh::lean_dec_ref(v_fvars_2123_);
        leanh::lean_dec_ref(v_a_2124_);
        v___x_2137_ = leanh::lean_apply_1(v_f_2122_, v___x_2136_);
        return v___x_2137_;
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__0(
    mut v_fvars_2138_: *mut leanh::LeanObject,
    mut v_inst_2139_: *mut leanh::LeanObject,
    mut v_inst_2140_: *mut leanh::LeanObject,
    mut v_f_2141_: *mut leanh::LeanObject,
    mut v_body_2142_: *mut leanh::LeanObject,
    mut v_x_2143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2144_ = lean_array_push(v_fvars_2138_, v_x_2143_);
    v___x_2145_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(
        v_inst_2139_,
        v_inst_2140_,
        v_f_2141_,
        v___x_2144_,
        v_body_2142_,
    );
    return v___x_2145_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit(
    mut v_m_2146_: *mut leanh::LeanObject,
    mut v_inst_2147_: *mut leanh::LeanObject,
    mut v_inst_2148_: *mut leanh::LeanObject,
    mut v_f_2149_: *mut leanh::LeanObject,
    mut v_fvars_2150_: *mut leanh::LeanObject,
    mut v_a_2151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2152_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(
        v_inst_2147_,
        v_inst_2148_,
        v_f_2149_,
        v_fvars_2150_,
        v_a_2151_,
    );
    return v___x_2152_;
}
pub unsafe fn l_Lean_Meta_visitLambda___redArg(
    mut v_inst_2155_: *mut leanh::LeanObject,
    mut v_inst_2156_: *mut leanh::LeanObject,
    mut v_f_2157_: *mut leanh::LeanObject,
    mut v_e_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = l_Lean_Meta_visitLambda___redArg___closed__0;
    v___x_2160_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(
        v_inst_2155_,
        v_inst_2156_,
        v_f_2157_,
        v___x_2159_,
        v_e_2158_,
    );
    return v___x_2160_;
}
pub unsafe fn l_Lean_Meta_visitLambda(
    mut v_m_2161_: *mut leanh::LeanObject,
    mut v_inst_2162_: *mut leanh::LeanObject,
    mut v_inst_2163_: *mut leanh::LeanObject,
    mut v_f_2164_: *mut leanh::LeanObject,
    mut v_e_2165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2166_ =
        l_Lean_Meta_visitLambda___redArg(v_inst_2162_, v_inst_2163_, v_f_2164_, v_e_2165_);
    return v___x_2166_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(
    mut v_inst_2167_: *mut leanh::LeanObject,
    mut v_inst_2168_: *mut leanh::LeanObject,
    mut v_f_2169_: *mut leanh::LeanObject,
    mut v_fvars_2170_: *mut leanh::LeanObject,
    mut v_a_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_2171_) == 7 {
        let mut v_toBind_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderName_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_2176_: u8 = 0;
        let mut v___f_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_d_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2172_ = leanh::lean_ctor_get(v_inst_2167_, 1);
        leanh::lean_inc(v_toBind_2172_);
        v_binderName_2173_ = leanh::lean_ctor_get(v_a_2171_, 0);
        leanh::lean_inc(v_binderName_2173_);
        v_binderType_2174_ = leanh::lean_ctor_get(v_a_2171_, 1);
        leanh::lean_inc_ref(v_binderType_2174_);
        v_body_2175_ = leanh::lean_ctor_get(v_a_2171_, 2);
        leanh::lean_inc_ref(v_body_2175_);
        v_binderInfo_2176_ = leanh::lean_ctor_get_uint8(
            v_a_2171_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_a_2171_, 3);
        leanh::lean_inc(v_f_2169_);
        leanh::lean_inc_ref(v_inst_2168_);
        leanh::lean_inc_ref(v_inst_2167_);
        leanh::lean_inc_ref(v_fvars_2170_);
        v___f_2177_ = leanh::lean_alloc_closure(
            l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg___lam__0
                as *mut core::ffi::c_void,
            6,
            5,
        );
        leanh::lean_closure_set(v___f_2177_, 0, v_fvars_2170_);
        leanh::lean_closure_set(v___f_2177_, 1, v_inst_2167_);
        leanh::lean_closure_set(v___f_2177_, 2, v_inst_2168_);
        leanh::lean_closure_set(v___f_2177_, 3, v_f_2169_);
        leanh::lean_closure_set(v___f_2177_, 4, v_body_2175_);
        v_d_2178_ = lean_expr_instantiate_rev(v_binderType_2174_, v_fvars_2170_);
        leanh::lean_dec_ref(v_fvars_2170_);
        leanh::lean_dec_ref(v_binderType_2174_);
        v___x_2179_ = leanh::lean_box((v_binderInfo_2176_) as usize);
        leanh::lean_inc_ref(v_d_2178_);
        v___f_2180_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1___boxed as *mut core::ffi::c_void, 7, 6);
        leanh::lean_closure_set(v___f_2180_, 0, v_inst_2168_);
        leanh::lean_closure_set(v___f_2180_, 1, v_inst_2167_);
        leanh::lean_closure_set(v___f_2180_, 2, v_binderName_2173_);
        leanh::lean_closure_set(v___f_2180_, 3, v___x_2179_);
        leanh::lean_closure_set(v___f_2180_, 4, v_d_2178_);
        leanh::lean_closure_set(v___f_2180_, 5, v___f_2177_);
        v___x_2181_ = leanh::lean_apply_1(v_f_2169_, v_d_2178_);
        v___x_2182_ = leanh::lean_apply_4(
            v_toBind_2172_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2181_,
            v___f_2180_,
        );
        return v___x_2182_;
    } else {
        let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2168_);
        leanh::lean_dec_ref(v_inst_2167_);
        v___x_2183_ = lean_expr_instantiate_rev(v_a_2171_, v_fvars_2170_);
        leanh::lean_dec_ref(v_fvars_2170_);
        leanh::lean_dec_ref(v_a_2171_);
        v___x_2184_ = leanh::lean_apply_1(v_f_2169_, v___x_2183_);
        return v___x_2184_;
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg___lam__0(
    mut v_fvars_2185_: *mut leanh::LeanObject,
    mut v_inst_2186_: *mut leanh::LeanObject,
    mut v_inst_2187_: *mut leanh::LeanObject,
    mut v_f_2188_: *mut leanh::LeanObject,
    mut v_body_2189_: *mut leanh::LeanObject,
    mut v_x_2190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = lean_array_push(v_fvars_2185_, v_x_2190_);
    v___x_2192_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(
        v_inst_2186_,
        v_inst_2187_,
        v_f_2188_,
        v___x_2191_,
        v_body_2189_,
    );
    return v___x_2192_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit(
    mut v_m_2193_: *mut leanh::LeanObject,
    mut v_inst_2194_: *mut leanh::LeanObject,
    mut v_inst_2195_: *mut leanh::LeanObject,
    mut v_f_2196_: *mut leanh::LeanObject,
    mut v_fvars_2197_: *mut leanh::LeanObject,
    mut v_a_2198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2199_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(
        v_inst_2194_,
        v_inst_2195_,
        v_f_2196_,
        v_fvars_2197_,
        v_a_2198_,
    );
    return v___x_2199_;
}
pub unsafe fn l_Lean_Meta_visitForall___redArg(
    mut v_inst_2200_: *mut leanh::LeanObject,
    mut v_inst_2201_: *mut leanh::LeanObject,
    mut v_f_2202_: *mut leanh::LeanObject,
    mut v_e_2203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2204_ = l_Lean_Meta_visitLambda___redArg___closed__0;
    v___x_2205_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(
        v_inst_2200_,
        v_inst_2201_,
        v_f_2202_,
        v___x_2204_,
        v_e_2203_,
    );
    return v___x_2205_;
}
pub unsafe fn l_Lean_Meta_visitForall(
    mut v_m_2206_: *mut leanh::LeanObject,
    mut v_inst_2207_: *mut leanh::LeanObject,
    mut v_inst_2208_: *mut leanh::LeanObject,
    mut v_f_2209_: *mut leanh::LeanObject,
    mut v_e_2210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2211_ =
        l_Lean_Meta_visitForall___redArg(v_inst_2207_, v_inst_2208_, v_f_2209_, v_e_2210_);
    return v___x_2211_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__1(
    mut v_inst_2212_: *mut leanh::LeanObject,
    mut v_inst_2213_: *mut leanh::LeanObject,
    mut v_declName_2214_: *mut leanh::LeanObject,
    mut v_d_2215_: *mut leanh::LeanObject,
    mut v_v_2216_: *mut leanh::LeanObject,
    mut v___f_2217_: *mut leanh::LeanObject,
    mut v_____r_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2219_: u8 = 0;
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2219_ = 0;
    v___x_2220_ = 0;
    v___x_2221_ = l_Lean_Meta_withLetDecl___redArg(
        v_inst_2212_,
        v_inst_2213_,
        v_declName_2214_,
        v_d_2215_,
        v_v_2216_,
        v___f_2217_,
        v___x_2219_,
        v___x_2220_,
    );
    return v___x_2221_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__2(
    mut v_f_2222_: *mut leanh::LeanObject,
    mut v_v_2223_: *mut leanh::LeanObject,
    mut v_toBind_2224_: *mut leanh::LeanObject,
    mut v___f_2225_: *mut leanh::LeanObject,
    mut v_____r_2226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2227_ = leanh::lean_apply_1(v_f_2222_, v_v_2223_);
    v___x_2228_ = leanh::lean_apply_4(
        v_toBind_2224_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2227_,
        v___f_2225_,
    );
    return v___x_2228_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(
    mut v_inst_2229_: *mut leanh::LeanObject,
    mut v_inst_2230_: *mut leanh::LeanObject,
    mut v_f_2231_: *mut leanh::LeanObject,
    mut v_fvars_2232_: *mut leanh::LeanObject,
    mut v_a_2233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_2233_) == 8 {
        let mut v_toBind_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_d_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2234_ = leanh::lean_ctor_get(v_inst_2229_, 1);
        leanh::lean_inc_n(v_toBind_2234_, 2);
        v_declName_2235_ = leanh::lean_ctor_get(v_a_2233_, 0);
        leanh::lean_inc(v_declName_2235_);
        v_type_2236_ = leanh::lean_ctor_get(v_a_2233_, 1);
        leanh::lean_inc_ref(v_type_2236_);
        v_value_2237_ = leanh::lean_ctor_get(v_a_2233_, 2);
        leanh::lean_inc_ref(v_value_2237_);
        v_body_2238_ = leanh::lean_ctor_get(v_a_2233_, 3);
        leanh::lean_inc_ref(v_body_2238_);
        leanh::lean_dec_ref_known(v_a_2233_, 4);
        leanh::lean_inc_n(v_f_2231_, 2);
        leanh::lean_inc_ref(v_inst_2230_);
        leanh::lean_inc_ref(v_inst_2229_);
        leanh::lean_inc_ref(v_fvars_2232_);
        v___f_2239_ = leanh::lean_alloc_closure(
            l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__0
                as *mut core::ffi::c_void,
            6,
            5,
        );
        leanh::lean_closure_set(v___f_2239_, 0, v_fvars_2232_);
        leanh::lean_closure_set(v___f_2239_, 1, v_inst_2229_);
        leanh::lean_closure_set(v___f_2239_, 2, v_inst_2230_);
        leanh::lean_closure_set(v___f_2239_, 3, v_f_2231_);
        leanh::lean_closure_set(v___f_2239_, 4, v_body_2238_);
        v_d_2240_ = lean_expr_instantiate_rev(v_type_2236_, v_fvars_2232_);
        leanh::lean_dec_ref(v_type_2236_);
        v_v_2241_ = lean_expr_instantiate_rev(v_value_2237_, v_fvars_2232_);
        leanh::lean_dec_ref(v_fvars_2232_);
        leanh::lean_dec_ref(v_value_2237_);
        leanh::lean_inc_ref(v_v_2241_);
        leanh::lean_inc_ref(v_d_2240_);
        v___f_2242_ = leanh::lean_alloc_closure(
            l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__1
                as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___f_2242_, 0, v_inst_2230_);
        leanh::lean_closure_set(v___f_2242_, 1, v_inst_2229_);
        leanh::lean_closure_set(v___f_2242_, 2, v_declName_2235_);
        leanh::lean_closure_set(v___f_2242_, 3, v_d_2240_);
        leanh::lean_closure_set(v___f_2242_, 4, v_v_2241_);
        leanh::lean_closure_set(v___f_2242_, 5, v___f_2239_);
        v___f_2243_ = leanh::lean_alloc_closure(
            l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__2
                as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_2243_, 0, v_f_2231_);
        leanh::lean_closure_set(v___f_2243_, 1, v_v_2241_);
        leanh::lean_closure_set(v___f_2243_, 2, v_toBind_2234_);
        leanh::lean_closure_set(v___f_2243_, 3, v___f_2242_);
        v___x_2244_ = leanh::lean_apply_1(v_f_2231_, v_d_2240_);
        v___x_2245_ = leanh::lean_apply_4(
            v_toBind_2234_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2244_,
            v___f_2243_,
        );
        return v___x_2245_;
    } else {
        let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2230_);
        leanh::lean_dec_ref(v_inst_2229_);
        v___x_2246_ = lean_expr_instantiate_rev(v_a_2233_, v_fvars_2232_);
        leanh::lean_dec_ref(v_fvars_2232_);
        leanh::lean_dec_ref(v_a_2233_);
        v___x_2247_ = leanh::lean_apply_1(v_f_2231_, v___x_2246_);
        return v___x_2247_;
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__0(
    mut v_fvars_2248_: *mut leanh::LeanObject,
    mut v_inst_2249_: *mut leanh::LeanObject,
    mut v_inst_2250_: *mut leanh::LeanObject,
    mut v_f_2251_: *mut leanh::LeanObject,
    mut v_body_2252_: *mut leanh::LeanObject,
    mut v_x_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2254_ = lean_array_push(v_fvars_2248_, v_x_2253_);
    v___x_2255_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(
        v_inst_2249_,
        v_inst_2250_,
        v_f_2251_,
        v___x_2254_,
        v_body_2252_,
    );
    return v___x_2255_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit(
    mut v_m_2256_: *mut leanh::LeanObject,
    mut v_inst_2257_: *mut leanh::LeanObject,
    mut v_inst_2258_: *mut leanh::LeanObject,
    mut v_f_2259_: *mut leanh::LeanObject,
    mut v_fvars_2260_: *mut leanh::LeanObject,
    mut v_a_2261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2262_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(
        v_inst_2257_,
        v_inst_2258_,
        v_f_2259_,
        v_fvars_2260_,
        v_a_2261_,
    );
    return v___x_2262_;
}
pub unsafe fn l_Lean_Meta_visitLet___redArg(
    mut v_inst_2263_: *mut leanh::LeanObject,
    mut v_inst_2264_: *mut leanh::LeanObject,
    mut v_f_2265_: *mut leanh::LeanObject,
    mut v_e_2266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = l_Lean_Meta_visitLambda___redArg___closed__0;
    v___x_2268_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(
        v_inst_2263_,
        v_inst_2264_,
        v_f_2265_,
        v___x_2267_,
        v_e_2266_,
    );
    return v___x_2268_;
}
pub unsafe fn l_Lean_Meta_visitLet(
    mut v_m_2269_: *mut leanh::LeanObject,
    mut v_inst_2270_: *mut leanh::LeanObject,
    mut v_inst_2271_: *mut leanh::LeanObject,
    mut v_f_2272_: *mut leanh::LeanObject,
    mut v_e_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2274_ = l_Lean_Meta_visitLet___redArg(v_inst_2270_, v_inst_2271_, v_f_2272_, v_e_2273_);
    return v___x_2274_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__0(
    mut v_toApplicative_2275_: *mut leanh::LeanObject,
    mut v_a_2276_: *mut leanh::LeanObject,
    mut v_a_2277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_2278_ = leanh::lean_ctor_get(v_toApplicative_2275_, 1);
    leanh::lean_inc(v_toPure_2278_);
    leanh::lean_dec_ref(v_toApplicative_2275_);
    v___x_2279_ = leanh::lean_apply_2(v_toPure_2278_, leanh::lean_box(0), v_a_2276_);
    return v___x_2279_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__1(
    mut v___x_2280_: *mut leanh::LeanObject,
    mut v___x_2281_: *mut leanh::LeanObject,
    mut v_e_2282_: *mut leanh::LeanObject,
    mut v_a_2283_: *mut leanh::LeanObject,
    mut v_s_2284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2285_ = leanh::lean_box(0);
    v___x_2286_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___x_2280_,
        v___x_2281_,
        v_s_2284_,
        v_e_2282_,
        v_a_2283_,
    );
    v___x_2287_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2287_, 0, v___x_2285_);
    leanh::lean_ctor_set(v___x_2287_, 1, v___x_2286_);
    return v___x_2287_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2(
    mut v_toApplicative_2288_: *mut leanh::LeanObject,
    mut v___x_2289_: *mut leanh::LeanObject,
    mut v___x_2290_: *mut leanh::LeanObject,
    mut v_e_2291_: *mut leanh::LeanObject,
    mut v_a_2292_: *mut leanh::LeanObject,
    mut v_x_2293_: *mut leanh::LeanObject,
    mut v_toBind_2294_: *mut leanh::LeanObject,
    mut v_a_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2296_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2296_, 0, v_toApplicative_2288_);
    leanh::lean_closure_set(v___f_2296_, 1, v_a_2295_);
    v___f_2297_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2297_, 0, v___x_2289_);
    leanh::lean_closure_set(v___f_2297_, 1, v___x_2290_);
    leanh::lean_closure_set(v___f_2297_, 2, v_e_2291_);
    leanh::lean_closure_set(v___f_2297_, 3, v_a_2295_);
    leanh::lean_inc(v_a_2292_);
    v___x_2298_ = leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___x_2298_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2298_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2298_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2298_, 3, v_a_2292_);
    leanh::lean_closure_set(v___x_2298_, 4, v___f_2297_);
    v___x_2299_ = leanh::lean_apply_2(v_x_2293_, leanh::lean_box(0), v___x_2298_);
    v___x_2300_ = leanh::lean_apply_4(
        v_toBind_2294_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2299_,
        v___f_2296_,
    );
    return v___x_2300_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2___boxed(
    mut v_toApplicative_2301_: *mut leanh::LeanObject,
    mut v___x_2302_: *mut leanh::LeanObject,
    mut v___x_2303_: *mut leanh::LeanObject,
    mut v_e_2304_: *mut leanh::LeanObject,
    mut v_a_2305_: *mut leanh::LeanObject,
    mut v_x_2306_: *mut leanh::LeanObject,
    mut v_toBind_2307_: *mut leanh::LeanObject,
    mut v_a_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2309_ =
        l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2(
            v_toApplicative_2301_,
            v___x_2302_,
            v___x_2303_,
            v_e_2304_,
            v_a_2305_,
            v_x_2306_,
            v_toBind_2307_,
            v_a_2308_,
        );
    leanh::lean_dec(v_a_2305_);
    return v_res_2309_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3(
    mut v_toApplicative_2310_: *mut leanh::LeanObject,
    mut v___x_2311_: *mut leanh::LeanObject,
    mut v___x_2312_: *mut leanh::LeanObject,
    mut v_e_2313_: *mut leanh::LeanObject,
    mut v_a_2314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_2315_ = leanh::lean_ctor_get(v_toApplicative_2310_, 1);
    leanh::lean_inc(v_toPure_2315_);
    leanh::lean_dec_ref(v_toApplicative_2310_);
    v___x_2316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___x_2311_,
        v___x_2312_,
        v_a_2314_,
        v_e_2313_,
    );
    v___x_2317_ =
        leanh::lean_apply_2(v_toPure_2315_, leanh::lean_box(0), v___x_2316_);
    return v___x_2317_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3___boxed(
    mut v_toApplicative_2318_: *mut leanh::LeanObject,
    mut v___x_2319_: *mut leanh::LeanObject,
    mut v___x_2320_: *mut leanh::LeanObject,
    mut v_e_2321_: *mut leanh::LeanObject,
    mut v_a_2322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2323_ =
        l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3(
            v_toApplicative_2318_,
            v___x_2319_,
            v___x_2320_,
            v_e_2321_,
            v_a_2322_,
        );
    leanh::lean_dec_ref(v_a_2322_);
    return v_res_2323_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__6(
    mut v_fn_2324_: *mut leanh::LeanObject,
    mut v_e_2325_: *mut leanh::LeanObject,
    mut v_toBind_2326_: *mut leanh::LeanObject,
    mut v___f_2327_: *mut leanh::LeanObject,
    mut v___f_2328_: *mut leanh::LeanObject,
    mut v_toApplicative_2329_: *mut leanh::LeanObject,
    mut v_a_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_2330_) == 0 {
        let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toApplicative_2329_);
        v___x_2331_ = leanh::lean_apply_1(v_fn_2324_, v_e_2325_);
        leanh::lean_inc(v_toBind_2326_);
        v___x_2332_ = leanh::lean_apply_4(
            v_toBind_2326_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2331_,
            v___f_2327_,
        );
        v___x_2333_ = leanh::lean_apply_4(
            v_toBind_2326_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2332_,
            v___f_2328_,
        );
        return v___x_2333_;
    } else {
        let mut v_val_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2328_);
        leanh::lean_dec(v___f_2327_);
        leanh::lean_dec(v_toBind_2326_);
        leanh::lean_dec_ref(v_e_2325_);
        leanh::lean_dec(v_fn_2324_);
        v_val_2334_ = leanh::lean_ctor_get(v_a_2330_, 0);
        leanh::lean_inc(v_val_2334_);
        leanh::lean_dec_ref_known(v_a_2330_, 1);
        v_toPure_2335_ = leanh::lean_ctor_get(v_toApplicative_2329_, 1);
        leanh::lean_inc(v_toPure_2335_);
        leanh::lean_dec_ref(v_toApplicative_2329_);
        v___x_2336_ =
            leanh::lean_apply_2(v_toPure_2335_, leanh::lean_box(0), v_val_2334_);
        return v___x_2336_;
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed(
    mut v_inst_2339_: *mut leanh::LeanObject,
    mut v_inst_2340_: *mut leanh::LeanObject,
    mut v_fn_2341_: *mut leanh::LeanObject,
    mut v_x_2342_: *mut leanh::LeanObject,
    mut v_x_2343_: *mut leanh::LeanObject,
    mut v_e_2344_: *mut leanh::LeanObject,
    mut v_a_2345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2346_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(
        v_inst_2339_,
        v_inst_2340_,
        v_fn_2341_,
        v_x_2342_,
        v_x_2343_,
        v_e_2344_,
        v_a_2345_,
    );
    leanh::lean_dec(v_a_2345_);
    return v_res_2346_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed(
    mut v_inst_2347_: *mut leanh::LeanObject,
    mut v_inst_2348_: *mut leanh::LeanObject,
    mut v_fn_2349_: *mut leanh::LeanObject,
    mut v_x_2350_: *mut leanh::LeanObject,
    mut v_x_2351_: *mut leanh::LeanObject,
    mut v_arg_2352_: *mut leanh::LeanObject,
    mut v_a_2353_: *mut leanh::LeanObject,
    mut v_a_2354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2355_ =
        l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(
            v_inst_2347_,
            v_inst_2348_,
            v_fn_2349_,
            v_x_2350_,
            v_x_2351_,
            v_arg_2352_,
            v_a_2353_,
            v_a_2354_,
        );
    leanh::lean_dec(v_a_2353_);
    return v_res_2355_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(
    mut v_toApplicative_2356_: *mut leanh::LeanObject,
    mut v_e_2357_: *mut leanh::LeanObject,
    mut v_x_2358_: *mut leanh::LeanObject,
    mut v___x_2359_: *mut leanh::LeanObject,
    mut v___x_2360_: *mut leanh::LeanObject,
    mut v_inst_2361_: *mut leanh::LeanObject,
    mut v_inst_2362_: *mut leanh::LeanObject,
    mut v_fn_2363_: *mut leanh::LeanObject,
    mut v_x_2364_: *mut leanh::LeanObject,
    mut v___x_2365_: *mut leanh::LeanObject,
    mut v_a_2366_: *mut leanh::LeanObject,
    mut v_toBind_2367_: *mut leanh::LeanObject,
    mut v_a_2368_: u8,
) -> *mut leanh::LeanObject {
    if v_a_2368_ == 0 {
        let mut v_toPure_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_2367_);
        leanh::lean_dec_ref(v___x_2365_);
        leanh::lean_dec(v_x_2364_);
        leanh::lean_dec(v_fn_2363_);
        leanh::lean_dec_ref(v_inst_2362_);
        leanh::lean_dec_ref(v_inst_2361_);
        leanh::lean_dec_ref(v___x_2360_);
        leanh::lean_dec_ref(v___x_2359_);
        leanh::lean_dec_ref(v_e_2357_);
        v_toPure_2369_ = leanh::lean_ctor_get(v_toApplicative_2356_, 1);
        leanh::lean_inc(v_toPure_2369_);
        leanh::lean_dec_ref(v_toApplicative_2356_);
        v___x_2370_ = leanh::lean_box(0);
        v___x_2371_ =
            leanh::lean_apply_2(v_toPure_2369_, leanh::lean_box(0), v___x_2370_);
        return v___x_2371_;
    } else {
        match leanh::lean_obj_tag(v_e_2357_) {
            7 => {
                let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_887__overap_2377_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_toBind_2367_);
                leanh::lean_dec_ref(v_toApplicative_2356_);
                v___x_2372_ = l_Lean_MonadCacheT_instMonadControl___redArg(
                    v_x_2358_,
                    v___x_2359_,
                    v___x_2360_,
                );
                leanh::lean_inc_ref_n(v_inst_2361_, 2);
                leanh::lean_inc_ref(v___x_2372_);
                v___f_2373_ = leanh::lean_alloc_closure(
                    l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_2373_, 0, v___x_2372_);
                leanh::lean_closure_set(v___f_2373_, 1, v_inst_2361_);
                v___f_2374_ = leanh::lean_alloc_closure(
                    l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_2374_, 0, v___x_2372_);
                leanh::lean_closure_set(v___f_2374_, 1, v_inst_2361_);
                v___x_2375_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2375_, 0, v___f_2373_);
                leanh::lean_ctor_set(v___x_2375_, 1, v___f_2374_);
                v___x_2376_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed as *mut core::ffi::c_void, 7, 5);
                leanh::lean_closure_set(v___x_2376_, 0, v_inst_2362_);
                leanh::lean_closure_set(v___x_2376_, 1, v_inst_2361_);
                leanh::lean_closure_set(v___x_2376_, 2, v_fn_2363_);
                leanh::lean_closure_set(v___x_2376_, 3, v_x_2358_);
                leanh::lean_closure_set(v___x_2376_, 4, v_x_2364_);
                v___x_887__overap_2377_ = l_Lean_Meta_visitForall___redArg(
                    v___x_2365_,
                    v___x_2375_,
                    v___x_2376_,
                    v_e_2357_,
                );
                leanh::lean_inc(v_a_2366_);
                v___x_2378_ = leanh::lean_apply_1(v___x_887__overap_2377_, v_a_2366_);
                return v___x_2378_;
            }
            6 => {
                let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_897__overap_2384_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_toBind_2367_);
                leanh::lean_dec_ref(v_toApplicative_2356_);
                v___x_2379_ = l_Lean_MonadCacheT_instMonadControl___redArg(
                    v_x_2358_,
                    v___x_2359_,
                    v___x_2360_,
                );
                leanh::lean_inc_ref_n(v_inst_2361_, 2);
                leanh::lean_inc_ref(v___x_2379_);
                v___f_2380_ = leanh::lean_alloc_closure(
                    l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_2380_, 0, v___x_2379_);
                leanh::lean_closure_set(v___f_2380_, 1, v_inst_2361_);
                v___f_2381_ = leanh::lean_alloc_closure(
                    l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_2381_, 0, v___x_2379_);
                leanh::lean_closure_set(v___f_2381_, 1, v_inst_2361_);
                v___x_2382_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2382_, 0, v___f_2380_);
                leanh::lean_ctor_set(v___x_2382_, 1, v___f_2381_);
                v___x_2383_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed as *mut core::ffi::c_void, 7, 5);
                leanh::lean_closure_set(v___x_2383_, 0, v_inst_2362_);
                leanh::lean_closure_set(v___x_2383_, 1, v_inst_2361_);
                leanh::lean_closure_set(v___x_2383_, 2, v_fn_2363_);
                leanh::lean_closure_set(v___x_2383_, 3, v_x_2358_);
                leanh::lean_closure_set(v___x_2383_, 4, v_x_2364_);
                v___x_897__overap_2384_ = l_Lean_Meta_visitLambda___redArg(
                    v___x_2365_,
                    v___x_2382_,
                    v___x_2383_,
                    v_e_2357_,
                );
                leanh::lean_inc(v_a_2366_);
                v___x_2385_ = leanh::lean_apply_1(v___x_897__overap_2384_, v_a_2366_);
                return v___x_2385_;
            }
            8 => {
                let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_908__overap_2391_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_toBind_2367_);
                leanh::lean_dec_ref(v_toApplicative_2356_);
                v___x_2386_ = l_Lean_MonadCacheT_instMonadControl___redArg(
                    v_x_2358_,
                    v___x_2359_,
                    v___x_2360_,
                );
                leanh::lean_inc_ref_n(v_inst_2361_, 2);
                leanh::lean_inc_ref(v___x_2386_);
                v___f_2387_ = leanh::lean_alloc_closure(
                    l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_2387_, 0, v___x_2386_);
                leanh::lean_closure_set(v___f_2387_, 1, v_inst_2361_);
                v___f_2388_ = leanh::lean_alloc_closure(
                    l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_2388_, 0, v___x_2386_);
                leanh::lean_closure_set(v___f_2388_, 1, v_inst_2361_);
                v___x_2389_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2389_, 0, v___f_2387_);
                leanh::lean_ctor_set(v___x_2389_, 1, v___f_2388_);
                v___x_2390_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed as *mut core::ffi::c_void, 7, 5);
                leanh::lean_closure_set(v___x_2390_, 0, v_inst_2362_);
                leanh::lean_closure_set(v___x_2390_, 1, v_inst_2361_);
                leanh::lean_closure_set(v___x_2390_, 2, v_fn_2363_);
                leanh::lean_closure_set(v___x_2390_, 3, v_x_2358_);
                leanh::lean_closure_set(v___x_2390_, 4, v_x_2364_);
                v___x_908__overap_2391_ =
                    l_Lean_Meta_visitLet___redArg(v___x_2365_, v___x_2389_, v___x_2390_, v_e_2357_);
                leanh::lean_inc(v_a_2366_);
                v___x_2392_ = leanh::lean_apply_1(v___x_908__overap_2391_, v_a_2366_);
                return v___x_2392_;
            }
            5 => {
                let mut v_fn_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_arg_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___x_2365_);
                leanh::lean_dec_ref(v___x_2360_);
                leanh::lean_dec_ref(v___x_2359_);
                leanh::lean_dec_ref(v_toApplicative_2356_);
                v_fn_2393_ = leanh::lean_ctor_get(v_e_2357_, 0);
                leanh::lean_inc_ref(v_fn_2393_);
                v_arg_2394_ = leanh::lean_ctor_get(v_e_2357_, 1);
                leanh::lean_inc_ref(v_arg_2394_);
                leanh::lean_dec_ref_known(v_e_2357_, 2);
                leanh::lean_inc(v_a_2366_);
                leanh::lean_inc(v_x_2364_);
                leanh::lean_inc(v_fn_2363_);
                leanh::lean_inc_ref(v_inst_2361_);
                leanh::lean_inc_ref(v_inst_2362_);
                v___f_2395_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed as *mut core::ffi::c_void, 8, 7);
                leanh::lean_closure_set(v___f_2395_, 0, v_inst_2362_);
                leanh::lean_closure_set(v___f_2395_, 1, v_inst_2361_);
                leanh::lean_closure_set(v___f_2395_, 2, v_fn_2363_);
                leanh::lean_closure_set(v___f_2395_, 3, v_x_2358_);
                leanh::lean_closure_set(v___f_2395_, 4, v_x_2364_);
                leanh::lean_closure_set(v___f_2395_, 5, v_arg_2394_);
                leanh::lean_closure_set(v___f_2395_, 6, v_a_2366_);
                v___x_2396_ =
                    l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(
                        v_inst_2362_,
                        v_inst_2361_,
                        v_fn_2363_,
                        v_x_2358_,
                        v_x_2364_,
                        v_fn_2393_,
                        v_a_2366_,
                    );
                v___x_2397_ = leanh::lean_apply_4(
                    v_toBind_2367_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2396_,
                    v___f_2395_,
                );
                return v___x_2397_;
            }
            10 => {
                let mut v_expr_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_toBind_2367_);
                leanh::lean_dec_ref(v___x_2365_);
                leanh::lean_dec_ref(v___x_2360_);
                leanh::lean_dec_ref(v___x_2359_);
                leanh::lean_dec_ref(v_toApplicative_2356_);
                v_expr_2398_ = leanh::lean_ctor_get(v_e_2357_, 1);
                leanh::lean_inc_ref(v_expr_2398_);
                leanh::lean_dec_ref_known(v_e_2357_, 2);
                v___x_2399_ =
                    l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(
                        v_inst_2362_,
                        v_inst_2361_,
                        v_fn_2363_,
                        v_x_2358_,
                        v_x_2364_,
                        v_expr_2398_,
                        v_a_2366_,
                    );
                return v___x_2399_;
            }
            11 => {
                let mut v_struct_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_toBind_2367_);
                leanh::lean_dec_ref(v___x_2365_);
                leanh::lean_dec_ref(v___x_2360_);
                leanh::lean_dec_ref(v___x_2359_);
                leanh::lean_dec_ref(v_toApplicative_2356_);
                v_struct_2400_ = leanh::lean_ctor_get(v_e_2357_, 2);
                leanh::lean_inc_ref(v_struct_2400_);
                leanh::lean_dec_ref_known(v_e_2357_, 3);
                v___x_2401_ =
                    l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(
                        v_inst_2362_,
                        v_inst_2361_,
                        v_fn_2363_,
                        v_x_2358_,
                        v_x_2364_,
                        v_struct_2400_,
                        v_a_2366_,
                    );
                return v___x_2401_;
            }
            _ => {
                let mut v_toPure_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_toBind_2367_);
                leanh::lean_dec_ref(v___x_2365_);
                leanh::lean_dec(v_x_2364_);
                leanh::lean_dec(v_fn_2363_);
                leanh::lean_dec_ref(v_inst_2362_);
                leanh::lean_dec_ref(v_inst_2361_);
                leanh::lean_dec_ref(v___x_2360_);
                leanh::lean_dec_ref(v___x_2359_);
                leanh::lean_dec_ref(v_e_2357_);
                v_toPure_2402_ = leanh::lean_ctor_get(v_toApplicative_2356_, 1);
                leanh::lean_inc(v_toPure_2402_);
                leanh::lean_dec_ref(v_toApplicative_2356_);
                v___x_2403_ = leanh::lean_box(0);
                v___x_2404_ = leanh::lean_apply_2(
                    v_toPure_2402_,
                    leanh::lean_box(0),
                    v___x_2403_,
                );
                return v___x_2404_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed(
    mut v_toApplicative_2405_: *mut leanh::LeanObject,
    mut v_e_2406_: *mut leanh::LeanObject,
    mut v_x_2407_: *mut leanh::LeanObject,
    mut v___x_2408_: *mut leanh::LeanObject,
    mut v___x_2409_: *mut leanh::LeanObject,
    mut v_inst_2410_: *mut leanh::LeanObject,
    mut v_inst_2411_: *mut leanh::LeanObject,
    mut v_fn_2412_: *mut leanh::LeanObject,
    mut v_x_2413_: *mut leanh::LeanObject,
    mut v___x_2414_: *mut leanh::LeanObject,
    mut v_a_2415_: *mut leanh::LeanObject,
    mut v_toBind_2416_: *mut leanh::LeanObject,
    mut v_a_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2418_: u8 = 0;
    let mut v_res_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2418_ = (leanh::lean_unbox(v_a_2417_) as u8);
    v_res_2419_ =
        l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(
            v_toApplicative_2405_,
            v_e_2406_,
            v_x_2407_,
            v___x_2408_,
            v___x_2409_,
            v_inst_2410_,
            v_inst_2411_,
            v_fn_2412_,
            v_x_2413_,
            v___x_2414_,
            v_a_2415_,
            v_toBind_2416_,
            v_a_boxed_2418_,
        );
    leanh::lean_dec(v_a_2415_);
    return v_res_2419_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(
    mut v_inst_2420_: *mut leanh::LeanObject,
    mut v_inst_2421_: *mut leanh::LeanObject,
    mut v_fn_2422_: *mut leanh::LeanObject,
    mut v_x_2423_: *mut leanh::LeanObject,
    mut v_x_2424_: *mut leanh::LeanObject,
    mut v_e_2425_: *mut leanh::LeanObject,
    mut v_a_2426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ =
        l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__0;
    v___x_2428_ =
        l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__1;
    leanh::lean_inc_ref(v_inst_2420_);
    v___x_2429_ =
        l_Lean_MonadCacheT_instMonad___redArg(v_x_2423_, v___x_2427_, v___x_2428_, v_inst_2420_);
    v_toApplicative_2430_ = leanh::lean_ctor_get(v_inst_2420_, 0);
    leanh::lean_inc_ref_n(v_toApplicative_2430_, 4);
    v_toBind_2431_ = leanh::lean_ctor_get(v_inst_2420_, 1);
    leanh::lean_inc_n(v_toBind_2431_, 5);
    leanh::lean_inc_n(v_x_2424_, 2);
    leanh::lean_inc_n(v_a_2426_, 3);
    leanh::lean_inc_ref_n(v_e_2425_, 3);
    v___f_2432_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2___boxed as *mut core::ffi::c_void, 8, 7);
    leanh::lean_closure_set(v___f_2432_, 0, v_toApplicative_2430_);
    leanh::lean_closure_set(v___f_2432_, 1, v___x_2427_);
    leanh::lean_closure_set(v___f_2432_, 2, v___x_2428_);
    leanh::lean_closure_set(v___f_2432_, 3, v_e_2425_);
    leanh::lean_closure_set(v___f_2432_, 4, v_a_2426_);
    leanh::lean_closure_set(v___f_2432_, 5, v_x_2424_);
    leanh::lean_closure_set(v___f_2432_, 6, v_toBind_2431_);
    v___f_2433_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3___boxed as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___f_2433_, 0, v_toApplicative_2430_);
    leanh::lean_closure_set(v___f_2433_, 1, v___x_2427_);
    leanh::lean_closure_set(v___f_2433_, 2, v___x_2428_);
    leanh::lean_closure_set(v___f_2433_, 3, v_e_2425_);
    leanh::lean_inc(v_fn_2422_);
    v___f_2434_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed as *mut core::ffi::c_void, 13, 12);
    leanh::lean_closure_set(v___f_2434_, 0, v_toApplicative_2430_);
    leanh::lean_closure_set(v___f_2434_, 1, v_e_2425_);
    leanh::lean_closure_set(v___f_2434_, 2, v_x_2423_);
    leanh::lean_closure_set(v___f_2434_, 3, v___x_2427_);
    leanh::lean_closure_set(v___f_2434_, 4, v___x_2428_);
    leanh::lean_closure_set(v___f_2434_, 5, v_inst_2421_);
    leanh::lean_closure_set(v___f_2434_, 6, v_inst_2420_);
    leanh::lean_closure_set(v___f_2434_, 7, v_fn_2422_);
    leanh::lean_closure_set(v___f_2434_, 8, v_x_2424_);
    leanh::lean_closure_set(v___f_2434_, 9, v___x_2429_);
    leanh::lean_closure_set(v___f_2434_, 10, v_a_2426_);
    leanh::lean_closure_set(v___f_2434_, 11, v_toBind_2431_);
    v___f_2435_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__6
            as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_2435_, 0, v_fn_2422_);
    leanh::lean_closure_set(v___f_2435_, 1, v_e_2425_);
    leanh::lean_closure_set(v___f_2435_, 2, v_toBind_2431_);
    leanh::lean_closure_set(v___f_2435_, 3, v___f_2434_);
    leanh::lean_closure_set(v___f_2435_, 4, v___f_2432_);
    leanh::lean_closure_set(v___f_2435_, 5, v_toApplicative_2430_);
    v___x_2436_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_2436_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2436_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2436_, 2, v_a_2426_);
    v___x_2437_ = leanh::lean_apply_2(v_x_2424_, leanh::lean_box(0), v___x_2436_);
    v___x_2438_ = leanh::lean_apply_4(
        v_toBind_2431_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2437_,
        v___f_2433_,
    );
    v___x_2439_ = leanh::lean_apply_4(
        v_toBind_2431_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2438_,
        v___f_2435_,
    );
    return v___x_2439_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(
    mut v_inst_2440_: *mut leanh::LeanObject,
    mut v_inst_2441_: *mut leanh::LeanObject,
    mut v_fn_2442_: *mut leanh::LeanObject,
    mut v_x_2443_: *mut leanh::LeanObject,
    mut v_x_2444_: *mut leanh::LeanObject,
    mut v_arg_2445_: *mut leanh::LeanObject,
    mut v_a_2446_: *mut leanh::LeanObject,
    mut v_a_2447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(
        v_inst_2440_,
        v_inst_2441_,
        v_fn_2442_,
        v_x_2443_,
        v_x_2444_,
        v_arg_2445_,
        v_a_2446_,
    );
    return v___x_2448_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit(
    mut v_m_2449_: *mut leanh::LeanObject,
    mut v_inst_2450_: *mut leanh::LeanObject,
    mut v_inst_2451_: *mut leanh::LeanObject,
    mut v_fn_2452_: *mut leanh::LeanObject,
    mut v_x_2453_: *mut leanh::LeanObject,
    mut v_x_2454_: *mut leanh::LeanObject,
    mut v_e_2455_: *mut leanh::LeanObject,
    mut v_a_2456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(
        v_inst_2450_,
        v_inst_2451_,
        v_fn_2452_,
        v_x_2453_,
        v_x_2454_,
        v_e_2455_,
        v_a_2456_,
    );
    return v___x_2457_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___boxed(
    mut v_m_2458_: *mut leanh::LeanObject,
    mut v_inst_2459_: *mut leanh::LeanObject,
    mut v_inst_2460_: *mut leanh::LeanObject,
    mut v_fn_2461_: *mut leanh::LeanObject,
    mut v_x_2462_: *mut leanh::LeanObject,
    mut v_x_2463_: *mut leanh::LeanObject,
    mut v_e_2464_: *mut leanh::LeanObject,
    mut v_a_2465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit(
        v_m_2458_,
        v_inst_2459_,
        v_inst_2460_,
        v_fn_2461_,
        v_x_2462_,
        v_x_2463_,
        v_e_2464_,
        v_a_2465_,
    );
    leanh::lean_dec(v_a_2465_);
    return v_res_2466_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___redArg___lam__0(
    mut v_x_2467_: *mut leanh::LeanObject,
    mut v___y_2468_: *mut leanh::LeanObject,
    mut v___y_2469_: *mut leanh::LeanObject,
    mut v___y_2470_: *mut leanh::LeanObject,
    mut v___y_2471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ = leanh::lean_apply_1(v_x_2467_, leanh::lean_box(0));
    v___x_2474_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    return v___x_2474_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed(
    mut v_x_2475_: *mut leanh::LeanObject,
    mut v___y_2476_: *mut leanh::LeanObject,
    mut v___y_2477_: *mut leanh::LeanObject,
    mut v___y_2478_: *mut leanh::LeanObject,
    mut v___y_2479_: *mut leanh::LeanObject,
    mut v___y_2480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Lean_Meta_forEachExpr_x27___redArg___lam__0(
        v_x_2475_,
        v___y_2476_,
        v___y_2477_,
        v___y_2478_,
        v___y_2479_,
    );
    leanh::lean_dec(v___y_2479_);
    leanh::lean_dec_ref(v___y_2478_);
    leanh::lean_dec(v___y_2477_);
    leanh::lean_dec_ref(v___y_2476_);
    return v_res_2481_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___redArg___lam__1(
    mut v_inst_2482_: *mut leanh::LeanObject,
    mut v_00_u03b1_2483_: *mut leanh::LeanObject,
    mut v_x_2484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2485_ = leanh::lean_alloc_closure(
        l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2485_, 0, v_x_2484_);
    v___x_2486_ = leanh::lean_apply_2(v_inst_2482_, leanh::lean_box(0), v___f_2485_);
    return v___x_2486_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___redArg___lam__2(
    mut v_toPure_2487_: *mut leanh::LeanObject,
    mut v_____x_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2489_ = leanh::lean_ctor_get(v_____x_2488_, 0);
    leanh::lean_inc(v_fst_2489_);
    leanh::lean_dec_ref(v_____x_2488_);
    v___x_2490_ =
        leanh::lean_apply_2(v_toPure_2487_, leanh::lean_box(0), v_fst_2489_);
    return v___x_2490_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___redArg___lam__3(
    mut v_a_2491_: *mut leanh::LeanObject,
    mut v_toPure_2492_: *mut leanh::LeanObject,
    mut v_s_2493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2494_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2494_, 0, v_a_2491_);
    leanh::lean_ctor_set(v___x_2494_, 1, v_s_2493_);
    v___x_2495_ =
        leanh::lean_apply_2(v_toPure_2492_, leanh::lean_box(0), v___x_2494_);
    return v___x_2495_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___redArg___lam__4(
    mut v_toPure_2496_: *mut leanh::LeanObject,
    mut v_ref_2497_: *mut leanh::LeanObject,
    mut v_x_2498_: *mut leanh::LeanObject,
    mut v_toBind_2499_: *mut leanh::LeanObject,
    mut v_a_2500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2501_ = leanh::lean_alloc_closure(
        l_Lean_Meta_forEachExpr_x27___redArg___lam__3 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2501_, 0, v_a_2500_);
    leanh::lean_closure_set(v___f_2501_, 1, v_toPure_2496_);
    v___x_2502_ =
        leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_2502_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2502_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2502_, 2, v_ref_2497_);
    v___x_2503_ = leanh::lean_apply_2(v_x_2498_, leanh::lean_box(0), v___x_2502_);
    v___x_2504_ = leanh::lean_apply_4(
        v_toBind_2499_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2503_,
        v___f_2501_,
    );
    return v___x_2504_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___redArg___lam__5(
    mut v_toPure_2505_: *mut leanh::LeanObject,
    mut v_x_2506_: *mut leanh::LeanObject,
    mut v_toBind_2507_: *mut leanh::LeanObject,
    mut v_inst_2508_: *mut leanh::LeanObject,
    mut v_inst_2509_: *mut leanh::LeanObject,
    mut v_fn_2510_: *mut leanh::LeanObject,
    mut v_x_2511_: *mut leanh::LeanObject,
    mut v_input_2512_: *mut leanh::LeanObject,
    mut v_ref_2513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_2507_);
    leanh::lean_inc(v_x_2506_);
    leanh::lean_inc(v_ref_2513_);
    v___f_2514_ = leanh::lean_alloc_closure(
        l_Lean_Meta_forEachExpr_x27___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2514_, 0, v_toPure_2505_);
    leanh::lean_closure_set(v___f_2514_, 1, v_ref_2513_);
    leanh::lean_closure_set(v___f_2514_, 2, v_x_2506_);
    leanh::lean_closure_set(v___f_2514_, 3, v_toBind_2507_);
    v___x_2515_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(
        v_inst_2508_,
        v_inst_2509_,
        v_fn_2510_,
        v_x_2511_,
        v_x_2506_,
        v_input_2512_,
        v_ref_2513_,
    );
    leanh::lean_dec(v_ref_2513_);
    v___x_2516_ = leanh::lean_apply_4(
        v_toBind_2507_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2515_,
        v___f_2514_,
    );
    return v___x_2516_;
}
pub unsafe fn _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2517_ = leanh::lean_box(0);
    v___x_2518_ = leanh::lean_unsigned_to_nat(16);
    v___x_2519_ = lean_mk_array(v___x_2518_, v___x_2517_);
    return v___x_2519_;
}
pub unsafe fn _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2520_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___redArg___closed__0_once),
        _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0,
    );
    v___x_2521_ = leanh::lean_unsigned_to_nat(0);
    v___x_2522_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2522_, 0, v___x_2521_);
    leanh::lean_ctor_set(v___x_2522_, 1, v___x_2520_);
    return v___x_2522_;
}
pub unsafe fn _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2523_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___redArg___closed__1_once),
        _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1,
    );
    v___x_2524_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_2524_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2524_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2524_, 2, v___x_2523_);
    return v___x_2524_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___redArg(
    mut v_inst_2525_: *mut leanh::LeanObject,
    mut v_inst_2526_: *mut leanh::LeanObject,
    mut v_inst_2527_: *mut leanh::LeanObject,
    mut v_input_2528_: *mut leanh::LeanObject,
    mut v_fn_2529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2530_ = leanh::lean_box(0);
    v_toApplicative_2531_ = leanh::lean_ctor_get(v_inst_2525_, 0);
    v_toBind_2532_ = leanh::lean_ctor_get(v_inst_2525_, 1);
    leanh::lean_inc_n(v_toBind_2532_, 3);
    v_toPure_2533_ = leanh::lean_ctor_get(v_toApplicative_2531_, 1);
    leanh::lean_inc_n(v_toPure_2533_, 2);
    leanh::lean_inc(v_inst_2526_);
    v_x_2534_ = leanh::lean_alloc_closure(
        l_Lean_Meta_forEachExpr_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v_x_2534_, 0, v_inst_2526_);
    v___x_2535_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once),
        _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2,
    );
    v___x_2536_ = l_Lean_Meta_forEachExpr_x27___redArg___lam__1(
        v_inst_2526_,
        leanh::lean_box(0),
        v___x_2535_,
    );
    v___f_2537_ = leanh::lean_alloc_closure(
        l_Lean_Meta_forEachExpr_x27___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2537_, 0, v_toPure_2533_);
    v___f_2538_ = leanh::lean_alloc_closure(
        l_Lean_Meta_forEachExpr_x27___redArg___lam__5 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_2538_, 0, v_toPure_2533_);
    leanh::lean_closure_set(v___f_2538_, 1, v_x_2534_);
    leanh::lean_closure_set(v___f_2538_, 2, v_toBind_2532_);
    leanh::lean_closure_set(v___f_2538_, 3, v_inst_2525_);
    leanh::lean_closure_set(v___f_2538_, 4, v_inst_2527_);
    leanh::lean_closure_set(v___f_2538_, 5, v_fn_2529_);
    leanh::lean_closure_set(v___f_2538_, 6, v_x_2530_);
    leanh::lean_closure_set(v___f_2538_, 7, v_input_2528_);
    v___x_2539_ = leanh::lean_apply_4(
        v_toBind_2532_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2536_,
        v___f_2538_,
    );
    v___x_2540_ = leanh::lean_apply_4(
        v_toBind_2532_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2539_,
        v___f_2537_,
    );
    return v___x_2540_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27(
    mut v_m_2541_: *mut leanh::LeanObject,
    mut v_inst_2542_: *mut leanh::LeanObject,
    mut v_inst_2543_: *mut leanh::LeanObject,
    mut v_inst_2544_: *mut leanh::LeanObject,
    mut v_input_2545_: *mut leanh::LeanObject,
    mut v_fn_2546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2547_ = l_Lean_Meta_forEachExpr_x27___redArg(
        v_inst_2542_,
        v_inst_2543_,
        v_inst_2544_,
        v_input_2545_,
        v_fn_2546_,
    );
    return v___x_2547_;
}
pub unsafe fn l_Lean_Meta_forEachExpr___redArg___lam__0(
    mut v_toPure_2548_: *mut leanh::LeanObject,
    mut v_____r_2549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2550_: u8 = 0;
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2550_ = 1;
    v___x_2551_ = leanh::lean_box((v___x_2550_) as usize);
    v___x_2552_ =
        leanh::lean_apply_2(v_toPure_2548_, leanh::lean_box(0), v___x_2551_);
    return v___x_2552_;
}
pub unsafe fn l_Lean_Meta_forEachExpr___redArg___lam__1(
    mut v_f_2553_: *mut leanh::LeanObject,
    mut v_toBind_2554_: *mut leanh::LeanObject,
    mut v___f_2555_: *mut leanh::LeanObject,
    mut v_e_2556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2557_ = leanh::lean_apply_1(v_f_2553_, v_e_2556_);
    v___x_2558_ = leanh::lean_apply_4(
        v_toBind_2554_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2557_,
        v___f_2555_,
    );
    return v___x_2558_;
}
pub unsafe fn l_Lean_Meta_forEachExpr___redArg(
    mut v_inst_2559_: *mut leanh::LeanObject,
    mut v_inst_2560_: *mut leanh::LeanObject,
    mut v_inst_2561_: *mut leanh::LeanObject,
    mut v_e_2562_: *mut leanh::LeanObject,
    mut v_f_2563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2564_ = leanh::lean_ctor_get(v_inst_2559_, 0);
    v_toBind_2565_ = leanh::lean_ctor_get(v_inst_2559_, 1);
    v_toPure_2566_ = leanh::lean_ctor_get(v_toApplicative_2564_, 1);
    leanh::lean_inc(v_toPure_2566_);
    v___f_2567_ = leanh::lean_alloc_closure(
        l_Lean_Meta_forEachExpr___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2567_, 0, v_toPure_2566_);
    leanh::lean_inc(v_toBind_2565_);
    v___f_2568_ = leanh::lean_alloc_closure(
        l_Lean_Meta_forEachExpr___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2568_, 0, v_f_2563_);
    leanh::lean_closure_set(v___f_2568_, 1, v_toBind_2565_);
    leanh::lean_closure_set(v___f_2568_, 2, v___f_2567_);
    v___x_2569_ = l_Lean_Meta_forEachExpr_x27___redArg(
        v_inst_2559_,
        v_inst_2560_,
        v_inst_2561_,
        v_e_2562_,
        v___f_2568_,
    );
    return v___x_2569_;
}
pub unsafe fn l_Lean_Meta_forEachExpr(
    mut v_m_2570_: *mut leanh::LeanObject,
    mut v_inst_2571_: *mut leanh::LeanObject,
    mut v_inst_2572_: *mut leanh::LeanObject,
    mut v_inst_2573_: *mut leanh::LeanObject,
    mut v_e_2574_: *mut leanh::LeanObject,
    mut v_f_2575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2576_ = l_Lean_Meta_forEachExpr___redArg(
        v_inst_2571_,
        v_inst_2572_,
        v_inst_2573_,
        v_e_2574_,
        v_f_2575_,
    );
    return v___x_2576_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(
    mut v_toPure_2577_: *mut leanh::LeanObject,
    mut v_____do__lift_2578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_userName_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: u8 = 0;
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_userName_2579_ = leanh::lean_ctor_get(v_____do__lift_2578_, 0);
    v___x_2580_ = l_Lean_Name_isAnonymous(v_userName_2579_);
    v___x_2581_ = leanh::lean_box((v___x_2580_) as usize);
    v___x_2582_ =
        leanh::lean_apply_2(v_toPure_2577_, leanh::lean_box(0), v___x_2581_);
    return v___x_2582_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed(
    mut v_toPure_2583_: *mut leanh::LeanObject,
    mut v_____do__lift_2584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2585_ =
        l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(
            v_toPure_2583_,
            v_____do__lift_2584_,
        );
    leanh::lean_dec_ref(v_____do__lift_2584_);
    return v_res_2585_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(
    mut v_inst_2586_: *mut leanh::LeanObject,
    mut v_inst_2587_: *mut leanh::LeanObject,
    mut v_x_2588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2589_ = leanh::lean_ctor_get(v_inst_2586_, 0);
    leanh::lean_inc_ref(v_toApplicative_2589_);
    if leanh::lean_obj_tag(v_x_2588_) == 2 {
        let mut v_toBind_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_mvarId_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_2590_ = leanh::lean_ctor_get(v_inst_2586_, 1);
        leanh::lean_inc(v_toBind_2590_);
        leanh::lean_dec_ref(v_inst_2586_);
        v_toPure_2591_ = leanh::lean_ctor_get(v_toApplicative_2589_, 1);
        leanh::lean_inc(v_toPure_2591_);
        leanh::lean_dec_ref(v_toApplicative_2589_);
        v_mvarId_2592_ = leanh::lean_ctor_get(v_x_2588_, 0);
        leanh::lean_inc(v_mvarId_2592_);
        leanh::lean_dec_ref_known(v_x_2588_, 1);
        v___f_2593_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
        leanh::lean_closure_set(v___f_2593_, 0, v_toPure_2591_);
        v___x_2594_ = leanh::lean_alloc_closure(
            l_Lean_MVarId_getDecl___boxed as *mut core::ffi::c_void,
            6,
            1,
        );
        leanh::lean_closure_set(v___x_2594_, 0, v_mvarId_2592_);
        v___x_2595_ =
            leanh::lean_apply_2(v_inst_2587_, leanh::lean_box(0), v___x_2594_);
        v___x_2596_ = leanh::lean_apply_4(
            v_toBind_2590_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2595_,
            v___f_2593_,
        );
        return v___x_2596_;
    } else {
        let mut v_toPure_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2598_: u8 = 0;
        let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_x_2588_);
        leanh::lean_dec(v_inst_2587_);
        leanh::lean_dec_ref(v_inst_2586_);
        v_toPure_2597_ = leanh::lean_ctor_get(v_toApplicative_2589_, 1);
        leanh::lean_inc(v_toPure_2597_);
        leanh::lean_dec_ref(v_toApplicative_2589_);
        v___x_2598_ = 0;
        v___x_2599_ = leanh::lean_box((v___x_2598_) as usize);
        v___x_2600_ =
            leanh::lean_apply_2(v_toPure_2597_, leanh::lean_box(0), v___x_2599_);
        return v___x_2600_;
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName(
    mut v_m_2601_: *mut leanh::LeanObject,
    mut v_inst_2602_: *mut leanh::LeanObject,
    mut v_inst_2603_: *mut leanh::LeanObject,
    mut v_x_2604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2605_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(
        v_inst_2602_,
        v_inst_2603_,
        v_x_2604_,
    );
    return v___x_2605_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(
    mut v_k_2606_: *mut leanh::LeanObject,
    mut v_b_2607_: *mut leanh::LeanObject,
    mut v_c_2608_: *mut leanh::LeanObject,
    mut v___y_2609_: *mut leanh::LeanObject,
    mut v___y_2610_: *mut leanh::LeanObject,
    mut v___y_2611_: *mut leanh::LeanObject,
    mut v___y_2612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2612_);
    leanh::lean_inc_ref(v___y_2611_);
    leanh::lean_inc(v___y_2610_);
    leanh::lean_inc_ref(v___y_2609_);
    v___x_2614_ = leanh::lean_apply_7(
        v_k_2606_,
        v_b_2607_,
        v_c_2608_,
        v___y_2609_,
        v___y_2610_,
        v___y_2611_,
        v___y_2612_,
        leanh::lean_box(0),
    );
    return v___x_2614_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0___boxed(
    mut v_k_2615_: *mut leanh::LeanObject,
    mut v_b_2616_: *mut leanh::LeanObject,
    mut v_c_2617_: *mut leanh::LeanObject,
    mut v___y_2618_: *mut leanh::LeanObject,
    mut v___y_2619_: *mut leanh::LeanObject,
    mut v___y_2620_: *mut leanh::LeanObject,
    mut v___y_2621_: *mut leanh::LeanObject,
    mut v___y_2622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2623_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(v_k_2615_, v_b_2616_, v_c_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
    leanh::lean_dec(v___y_2621_);
    leanh::lean_dec_ref(v___y_2620_);
    leanh::lean_dec(v___y_2619_);
    leanh::lean_dec_ref(v___y_2618_);
    return v_res_2623_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(
    mut v_type_2624_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2625_: *mut leanh::LeanObject,
    mut v_k_2626_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2627_: u8,
    mut v_whnfType_2628_: u8,
    mut v___y_2629_: *mut leanh::LeanObject,
    mut v___y_2630_: *mut leanh::LeanObject,
    mut v___y_2631_: *mut leanh::LeanObject,
    mut v___y_2632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v_a_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2647_: u8 = 0;
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2634_ = leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2634_, 0, v_k_2626_);
                v___x_2635_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    leanh::lean_box(0),
                    v_type_2624_,
                    v_maxFVars_x3f_2625_,
                    v___f_2634_,
                    v_cleanupAnnotations_2627_,
                    v_whnfType_2628_,
                    v___y_2629_,
                    v___y_2630_,
                    v___y_2631_,
                    v___y_2632_,
                );
                if leanh::lean_obj_tag(v___x_2635_) == 0 {
                    v_a_2636_ = leanh::lean_ctor_get(v___x_2635_, 0);
                    v_isSharedCheck_2643_ = (!leanh::lean_is_exclusive(v___x_2635_)) as u8;
                    if v_isSharedCheck_2643_ == 0 {
                        v___x_2638_ = v___x_2635_;
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2636_);
                        leanh::lean_dec(v___x_2635_);
                        v___x_2638_ = leanh::lean_box(0);
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2644_ = leanh::lean_ctor_get(v___x_2635_, 0);
                    v_isSharedCheck_2651_ = (!leanh::lean_is_exclusive(v___x_2635_)) as u8;
                    if v_isSharedCheck_2651_ == 0 {
                        v___x_2646_ = v___x_2635_;
                        v_isShared_2647_ = v_isSharedCheck_2651_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2644_);
                        leanh::lean_dec(v___x_2635_);
                        v___x_2646_ = leanh::lean_box(0);
                        v_isShared_2647_ = v_isSharedCheck_2651_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2639_ == 0 {
                    v___x_2641_ = v___x_2638_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2642_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
                    v___x_2641_ = v_reuseFailAlloc_2642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2641_;
            }
            3 => {
                if v_isShared_2647_ == 0 {
                    v___x_2649_ = v___x_2646_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2650_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
                    v___x_2649_ = v_reuseFailAlloc_2650_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___boxed(
    mut v_type_2652_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2653_: *mut leanh::LeanObject,
    mut v_k_2654_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2655_: *mut leanh::LeanObject,
    mut v_whnfType_2656_: *mut leanh::LeanObject,
    mut v___y_2657_: *mut leanh::LeanObject,
    mut v___y_2658_: *mut leanh::LeanObject,
    mut v___y_2659_: *mut leanh::LeanObject,
    mut v___y_2660_: *mut leanh::LeanObject,
    mut v___y_2661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2662_: u8 = 0;
    let mut v_whnfType_boxed_2663_: u8 = 0;
    let mut v_res_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2662_ = (leanh::lean_unbox(v_cleanupAnnotations_2655_) as u8);
    v_whnfType_boxed_2663_ = (leanh::lean_unbox(v_whnfType_2656_) as u8);
    v_res_2664_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(
            v_type_2652_,
            v_maxFVars_x3f_2653_,
            v_k_2654_,
            v_cleanupAnnotations_boxed_2662_,
            v_whnfType_boxed_2663_,
            v___y_2657_,
            v___y_2658_,
            v___y_2659_,
            v___y_2660_,
        );
    leanh::lean_dec(v___y_2660_);
    leanh::lean_dec_ref(v___y_2659_);
    leanh::lean_dec(v___y_2658_);
    leanh::lean_dec_ref(v___y_2657_);
    return v_res_2664_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(
    mut v_00_u03b1_2665_: *mut leanh::LeanObject,
    mut v_type_2666_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2667_: *mut leanh::LeanObject,
    mut v_k_2668_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2669_: u8,
    mut v_whnfType_2670_: u8,
    mut v___y_2671_: *mut leanh::LeanObject,
    mut v___y_2672_: *mut leanh::LeanObject,
    mut v___y_2673_: *mut leanh::LeanObject,
    mut v___y_2674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2676_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(
            v_type_2666_,
            v_maxFVars_x3f_2667_,
            v_k_2668_,
            v_cleanupAnnotations_2669_,
            v_whnfType_2670_,
            v___y_2671_,
            v___y_2672_,
            v___y_2673_,
            v___y_2674_,
        );
    return v___x_2676_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___boxed(
    mut v_00_u03b1_2677_: *mut leanh::LeanObject,
    mut v_type_2678_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2679_: *mut leanh::LeanObject,
    mut v_k_2680_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2681_: *mut leanh::LeanObject,
    mut v_whnfType_2682_: *mut leanh::LeanObject,
    mut v___y_2683_: *mut leanh::LeanObject,
    mut v___y_2684_: *mut leanh::LeanObject,
    mut v___y_2685_: *mut leanh::LeanObject,
    mut v___y_2686_: *mut leanh::LeanObject,
    mut v___y_2687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2688_: u8 = 0;
    let mut v_whnfType_boxed_2689_: u8 = 0;
    let mut v_res_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2688_ = (leanh::lean_unbox(v_cleanupAnnotations_2681_) as u8);
    v_whnfType_boxed_2689_ = (leanh::lean_unbox(v_whnfType_2682_) as u8);
    v_res_2690_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(
        v_00_u03b1_2677_,
        v_type_2678_,
        v_maxFVars_x3f_2679_,
        v_k_2680_,
        v_cleanupAnnotations_boxed_2688_,
        v_whnfType_boxed_2689_,
        v___y_2683_,
        v___y_2684_,
        v___y_2685_,
        v___y_2686_,
    );
    leanh::lean_dec(v___y_2686_);
    leanh::lean_dec_ref(v___y_2685_);
    leanh::lean_dec(v___y_2684_);
    leanh::lean_dec_ref(v___y_2683_);
    return v_res_2690_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(
    mut v_e_2691_: *mut leanh::LeanObject,
    mut v___y_2692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2694_: u8 = 0;
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2708_: u8 = 0;
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_unused_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2694_ = l_Lean_Expr_hasMVar(v_e_2691_);
                if v___x_2694_ == 0 {
                    v___x_2695_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2695_, 0, v_e_2691_);
                    return v___x_2695_;
                } else {
                    v___x_2696_ = lean_st_ref_get(v___y_2692_);
                    v_mctx_2697_ = leanh::lean_ctor_get(v___x_2696_, 0);
                    leanh::lean_inc_ref(v_mctx_2697_);
                    leanh::lean_dec(v___x_2696_);
                    v___x_2698_ = l_Lean_instantiateMVarsCore(v_mctx_2697_, v_e_2691_);
                    v_fst_2699_ = leanh::lean_ctor_get(v___x_2698_, 0);
                    leanh::lean_inc(v_fst_2699_);
                    v_snd_2700_ = leanh::lean_ctor_get(v___x_2698_, 1);
                    leanh::lean_inc(v_snd_2700_);
                    leanh::lean_dec_ref(v___x_2698_);
                    v___x_2701_ = lean_st_ref_take(v___y_2692_);
                    v_cache_2702_ = leanh::lean_ctor_get(v___x_2701_, 1);
                    v_zetaDeltaFVarIds_2703_ = leanh::lean_ctor_get(v___x_2701_, 2);
                    v_postponed_2704_ = leanh::lean_ctor_get(v___x_2701_, 3);
                    v_diag_2705_ = leanh::lean_ctor_get(v___x_2701_, 4);
                    v_isSharedCheck_2714_ = (!leanh::lean_is_exclusive(v___x_2701_)) as u8;
                    if v_isSharedCheck_2714_ == 0 {
                        v_unused_2715_ = leanh::lean_ctor_get(v___x_2701_, 0);
                        leanh::lean_dec(v_unused_2715_);
                        v___x_2707_ = v___x_2701_;
                        v_isShared_2708_ = v_isSharedCheck_2714_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_2705_);
                        leanh::lean_inc(v_postponed_2704_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_2703_);
                        leanh::lean_inc(v_cache_2702_);
                        leanh::lean_dec(v___x_2701_);
                        v___x_2707_ = leanh::lean_box(0);
                        v_isShared_2708_ = v_isSharedCheck_2714_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2708_ == 0 {
                    leanh::lean_ctor_set(v___x_2707_, 0, v_snd_2700_);
                    v___x_2710_ = v___x_2707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2713_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_snd_2700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_cache_2702_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2713_,
                        2,
                        v_zetaDeltaFVarIds_2703_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 3, v_postponed_2704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 4, v_diag_2705_);
                    v___x_2710_ = v_reuseFailAlloc_2713_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2711_ = lean_st_ref_set(v___y_2692_, v___x_2710_);
                v___x_2712_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2712_, 0, v_fst_2699_);
                return v___x_2712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg___boxed(
    mut v_e_2716_: *mut leanh::LeanObject,
    mut v___y_2717_: *mut leanh::LeanObject,
    mut v___y_2718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2719_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(
        v_e_2716_,
        v___y_2717_,
    );
    leanh::lean_dec(v___y_2717_);
    return v_res_2719_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(
    mut v_e_2720_: *mut leanh::LeanObject,
    mut v___y_2721_: *mut leanh::LeanObject,
    mut v___y_2722_: *mut leanh::LeanObject,
    mut v___y_2723_: *mut leanh::LeanObject,
    mut v___y_2724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2726_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(
        v_e_2720_,
        v___y_2722_,
    );
    return v___x_2726_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___boxed(
    mut v_e_2727_: *mut leanh::LeanObject,
    mut v___y_2728_: *mut leanh::LeanObject,
    mut v___y_2729_: *mut leanh::LeanObject,
    mut v___y_2730_: *mut leanh::LeanObject,
    mut v___y_2731_: *mut leanh::LeanObject,
    mut v___y_2732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2733_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(
        v_e_2727_,
        v___y_2728_,
        v___y_2729_,
        v___y_2730_,
        v___y_2731_,
    );
    leanh::lean_dec(v___y_2731_);
    leanh::lean_dec_ref(v___y_2730_);
    leanh::lean_dec(v___y_2729_);
    leanh::lean_dec_ref(v___y_2728_);
    return v_res_2733_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(
    mut v_a_2734_: *mut leanh::LeanObject,
    mut v___x_2735_: *mut leanh::LeanObject,
    mut v_val_2736_: *mut leanh::LeanObject,
    mut v___x_2737_: *mut leanh::LeanObject,
    mut v_xs_2738_: *mut leanh::LeanObject,
    mut v_x_2739_: *mut leanh::LeanObject,
    mut v___y_2740_: *mut leanh::LeanObject,
    mut v___y_2741_: *mut leanh::LeanObject,
    mut v___y_2742_: *mut leanh::LeanObject,
    mut v___y_2743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: u8 = 0;
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2757_: u8 = 0;
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2769_: u8 = 0;
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2778_: u8 = 0;
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut v_a_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2783_: u8 = 0;
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2787_: u8 = 0;
    let mut v_a_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2791_: u8 = 0;
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2745_ = lean_array_get_size(v_xs_2738_);
                v___x_2746_ = lean_nat_dec_lt(v_a_2734_, v___x_2745_);
                if v___x_2746_ == 0 {
                    leanh::lean_dec(v___x_2737_);
                    v___x_2747_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2747_, 0, v___x_2735_);
                    return v___x_2747_;
                } else {
                    v___x_2748_ = l_Lean_instInhabitedExpr;
                    v___x_2749_ = lean_array_get_borrowed(v___x_2748_, v_xs_2738_, v_a_2734_);
                    v___x_2750_ = l_Lean_Meta_getFVarLocalDecl___redArg(
                        v___x_2749_,
                        v___y_2740_,
                        v___y_2742_,
                        v___y_2743_,
                    );
                    if leanh::lean_obj_tag(v___x_2750_) == 0 {
                        v_a_2751_ = leanh::lean_ctor_get(v___x_2750_, 0);
                        leanh::lean_inc(v_a_2751_);
                        leanh::lean_dec_ref_known(v___x_2750_, 1);
                        v___x_2752_ = l_Lean_LocalDecl_userName(v_a_2751_);
                        leanh::lean_dec(v_a_2751_);
                        v___x_2753_ =
                            l_Lean_Core_mkFreshUserName(v___x_2752_, v___y_2742_, v___y_2743_);
                        if leanh::lean_obj_tag(v___x_2753_) == 0 {
                            v_a_2754_ = leanh::lean_ctor_get(v___x_2753_, 0);
                            v_isSharedCheck_2779_ =
                                (!leanh::lean_is_exclusive(v___x_2753_)) as u8;
                            if v_isSharedCheck_2779_ == 0 {
                                v___x_2756_ = v___x_2753_;
                                v_isShared_2757_ = v_isSharedCheck_2779_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2754_);
                                leanh::lean_dec(v___x_2753_);
                                v___x_2756_ = leanh::lean_box(0);
                                v_isShared_2757_ = v_isSharedCheck_2779_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_2737_);
                            v_a_2780_ = leanh::lean_ctor_get(v___x_2753_, 0);
                            v_isSharedCheck_2787_ =
                                (!leanh::lean_is_exclusive(v___x_2753_)) as u8;
                            if v_isSharedCheck_2787_ == 0 {
                                v___x_2782_ = v___x_2753_;
                                v_isShared_2783_ = v_isSharedCheck_2787_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2780_);
                                leanh::lean_dec(v___x_2753_);
                                v___x_2782_ = leanh::lean_box(0);
                                v_isShared_2783_ = v_isSharedCheck_2787_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2737_);
                        v_a_2788_ = leanh::lean_ctor_get(v___x_2750_, 0);
                        v_isSharedCheck_2795_ =
                            (!leanh::lean_is_exclusive(v___x_2750_)) as u8;
                        if v_isSharedCheck_2795_ == 0 {
                            v___x_2790_ = v___x_2750_;
                            v_isShared_2791_ = v_isSharedCheck_2795_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2788_);
                            leanh::lean_dec(v___x_2750_);
                            v___x_2790_ = leanh::lean_box(0);
                            v_isShared_2791_ = v_isSharedCheck_2795_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2758_ = lean_st_ref_take(v_val_2736_);
                leanh::lean_inc(v___x_2737_);
                v___x_2759_ = lean_array_push(v___x_2758_, v___x_2737_);
                v___x_2760_ = lean_st_ref_set(v_val_2736_, v___x_2759_);
                v___x_2761_ = lean_st_ref_take(v___y_2741_);
                v_mctx_2762_ = leanh::lean_ctor_get(v___x_2761_, 0);
                v_cache_2763_ = leanh::lean_ctor_get(v___x_2761_, 1);
                v_zetaDeltaFVarIds_2764_ = leanh::lean_ctor_get(v___x_2761_, 2);
                v_postponed_2765_ = leanh::lean_ctor_get(v___x_2761_, 3);
                v_diag_2766_ = leanh::lean_ctor_get(v___x_2761_, 4);
                v_isSharedCheck_2778_ = (!leanh::lean_is_exclusive(v___x_2761_)) as u8;
                if v_isSharedCheck_2778_ == 0 {
                    v___x_2768_ = v___x_2761_;
                    v_isShared_2769_ = v_isSharedCheck_2778_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2766_);
                    leanh::lean_inc(v_postponed_2765_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2764_);
                    leanh::lean_inc(v_cache_2763_);
                    leanh::lean_inc(v_mctx_2762_);
                    leanh::lean_dec(v___x_2761_);
                    v___x_2768_ = leanh::lean_box(0);
                    v_isShared_2769_ = v_isSharedCheck_2778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2770_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(
                    v_mctx_2762_,
                    v___x_2737_,
                    v_a_2754_,
                );
                if v_isShared_2769_ == 0 {
                    leanh::lean_ctor_set(v___x_2768_, 0, v___x_2770_);
                    v___x_2772_ = v___x_2768_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2777_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_cache_2763_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2777_,
                        2,
                        v_zetaDeltaFVarIds_2764_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2777_, 3, v_postponed_2765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2777_, 4, v_diag_2766_);
                    v___x_2772_ = v_reuseFailAlloc_2777_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2773_ = lean_st_ref_set(v___y_2741_, v___x_2772_);
                if v_isShared_2757_ == 0 {
                    leanh::lean_ctor_set(v___x_2756_, 0, v___x_2735_);
                    v___x_2775_ = v___x_2756_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2776_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2735_);
                    v___x_2775_ = v_reuseFailAlloc_2776_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2775_;
            }
            5 => {
                if v_isShared_2783_ == 0 {
                    v___x_2785_ = v___x_2782_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
                    v___x_2785_ = v_reuseFailAlloc_2786_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2785_;
            }
            7 => {
                if v_isShared_2791_ == 0 {
                    v___x_2793_ = v___x_2790_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2794_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
                    v___x_2793_ = v_reuseFailAlloc_2794_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed(
    mut v_a_2796_: *mut leanh::LeanObject,
    mut v___x_2797_: *mut leanh::LeanObject,
    mut v_val_2798_: *mut leanh::LeanObject,
    mut v___x_2799_: *mut leanh::LeanObject,
    mut v_xs_2800_: *mut leanh::LeanObject,
    mut v_x_2801_: *mut leanh::LeanObject,
    mut v___y_2802_: *mut leanh::LeanObject,
    mut v___y_2803_: *mut leanh::LeanObject,
    mut v___y_2804_: *mut leanh::LeanObject,
    mut v___y_2805_: *mut leanh::LeanObject,
    mut v___y_2806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2807_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(v_a_2796_, v___x_2797_, v_val_2798_, v___x_2799_, v_xs_2800_, v_x_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
    leanh::lean_dec(v___y_2805_);
    leanh::lean_dec_ref(v___y_2804_);
    leanh::lean_dec(v___y_2803_);
    leanh::lean_dec_ref(v___y_2802_);
    leanh::lean_dec_ref(v_x_2801_);
    leanh::lean_dec_ref(v_xs_2800_);
    leanh::lean_dec(v_val_2798_);
    leanh::lean_dec(v_a_2796_);
    return v_res_2807_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(
    mut v_a_2808_: *mut leanh::LeanObject,
    mut v_as_2809_: *mut leanh::LeanObject,
    mut v_i_2810_: usize,
    mut v_stop_2811_: usize,
) -> u8 {
    let mut v___x_2812_: u8 = 0;
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: u8 = 0;
    let mut v___x_2815_: usize = 0;
    let mut v___x_2816_: usize = 0;
    let mut v___x_2818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2812_ = lean_usize_dec_eq(v_i_2810_, v_stop_2811_);
                if v___x_2812_ == 0 {
                    v___x_2813_ = lean_array_uget_borrowed(v_as_2809_, v_i_2810_);
                    v___x_2814_ = lean_expr_eqv(v_a_2808_, v___x_2813_);
                    if v___x_2814_ == 0 {
                        v___x_2815_ = 1usize;
                        v___x_2816_ = lean_usize_add(v_i_2810_, v___x_2815_);
                        v_i_2810_ = v___x_2816_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2814_;
                    }
                } else {
                    v___x_2818_ = 0;
                    return v___x_2818_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1___boxed(
    mut v_a_2819_: *mut leanh::LeanObject,
    mut v_as_2820_: *mut leanh::LeanObject,
    mut v_i_2821_: *mut leanh::LeanObject,
    mut v_stop_2822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2823_: usize = 0;
    let mut v_stop_boxed_2824_: usize = 0;
    let mut v_res_2825_: u8 = 0;
    let mut v_r_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2823_ = leanh::lean_unbox_usize(v_i_2821_);
    leanh::lean_dec(v_i_2821_);
    v_stop_boxed_2824_ = leanh::lean_unbox_usize(v_stop_2822_);
    leanh::lean_dec(v_stop_2822_);
    v_res_2825_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(v_a_2819_, v_as_2820_, v_i_boxed_2823_, v_stop_boxed_2824_);
    leanh::lean_dec_ref(v_as_2820_);
    leanh::lean_dec_ref(v_a_2819_);
    v_r_2826_ = leanh::lean_box((v_res_2825_) as usize);
    return v_r_2826_;
}
pub unsafe fn l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(
    mut v_as_2827_: *mut leanh::LeanObject,
    mut v_a_2828_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    v___x_2829_ = leanh::lean_unsigned_to_nat(0);
    v___x_2830_ = lean_array_get_size(v_as_2827_);
    v___x_2831_ = lean_nat_dec_lt(v___x_2829_, v___x_2830_);
    if v___x_2831_ == 0 {
        return v___x_2831_;
    } else {
        if v___x_2831_ == 0 {
            return v___x_2831_;
        } else {
            let mut v___x_2832_: usize = 0;
            let mut v___x_2833_: usize = 0;
            let mut v___x_2834_: u8 = 0;
            v___x_2832_ = 0usize;
            v___x_2833_ = lean_usize_of_nat(v___x_2830_);
            v___x_2834_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(v_a_2828_, v_as_2827_, v___x_2832_, v___x_2833_);
            return v___x_2834_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1___boxed(
    mut v_as_2835_: *mut leanh::LeanObject,
    mut v_a_2836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2837_: u8 = 0;
    let mut v_r_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2837_ =
        l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_as_2835_, v_a_2836_);
    leanh::lean_dec_ref(v_a_2836_);
    leanh::lean_dec_ref(v_as_2835_);
    v_r_2838_ = leanh::lean_box((v_res_2837_) as usize);
    return v_r_2838_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(
    mut v_upperBound_2839_: *mut leanh::LeanObject,
    mut v___x_2840_: *mut leanh::LeanObject,
    mut v_val_2841_: *mut leanh::LeanObject,
    mut v_e_2842_: *mut leanh::LeanObject,
    mut v_isTarget_2843_: *mut leanh::LeanObject,
    mut v_a_2844_: *mut leanh::LeanObject,
    mut v_b_2845_: *mut leanh::LeanObject,
    mut v___y_2846_: *mut leanh::LeanObject,
    mut v___y_2847_: *mut leanh::LeanObject,
    mut v___y_2848_: *mut leanh::LeanObject,
    mut v___y_2849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: u8 = 0;
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2861_: u8 = 0;
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: u8 = 0;
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: u8 = 0;
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2879_: u8 = 0;
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2883_: u8 = 0;
    let mut v_a_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2891_: u8 = 0;
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2856_ = lean_nat_dec_lt(v_a_2844_, v_upperBound_2839_);
                if v___x_2856_ == 0 {
                    leanh::lean_dec(v_a_2844_);
                    leanh::lean_dec(v_val_2841_);
                    v___x_2857_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2857_, 0, v_b_2845_);
                    return v___x_2857_;
                } else {
                    v___x_2858_ = leanh::lean_box(0);
                    v___x_2859_ = lean_array_fget_borrowed(v___x_2840_, v_a_2844_);
                    v___x_2892_ = l_Lean_Expr_isMVar(v___x_2859_);
                    if v___x_2892_ == 0 {
                        v___y_2861_ = v___x_2892_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2893_ =
                            l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(
                                v_isTarget_2843_,
                                v___x_2859_,
                            );
                        v___y_2861_ = v___x_2893_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2853_ = leanh::lean_unsigned_to_nat(1);
                v___x_2854_ = lean_nat_add(v_a_2844_, v___x_2853_);
                leanh::lean_dec(v_a_2844_);
                v_a_2844_ = v___x_2854_;
                v_b_2845_ = v_a_2852_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_2861_ == 0 {
                    v_a_2852_ = v___x_2858_;
                    state = 1;
                    continue;
                } else {
                    v___x_2862_ = l_Lean_Expr_mvarId_x21(v___x_2859_);
                    leanh::lean_inc(v___x_2862_);
                    v___x_2863_ = l_Lean_MVarId_getDecl(
                        v___x_2862_,
                        v___y_2846_,
                        v___y_2847_,
                        v___y_2848_,
                        v___y_2849_,
                    );
                    if leanh::lean_obj_tag(v___x_2863_) == 0 {
                        v_a_2864_ = leanh::lean_ctor_get(v___x_2863_, 0);
                        leanh::lean_inc(v_a_2864_);
                        leanh::lean_dec_ref_known(v___x_2863_, 1);
                        v_userName_2865_ = leanh::lean_ctor_get(v_a_2864_, 0);
                        leanh::lean_inc(v_userName_2865_);
                        leanh::lean_dec(v_a_2864_);
                        v___x_2866_ = l_Lean_Name_isAnonymous(v_userName_2865_);
                        leanh::lean_dec(v_userName_2865_);
                        if v___x_2866_ == 0 {
                            leanh::lean_dec(v___x_2862_);
                            v_a_2852_ = v___x_2858_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2867_ = l_Lean_Expr_getAppFn(v_e_2842_);
                            leanh::lean_inc(v___y_2849_);
                            leanh::lean_inc_ref(v___y_2848_);
                            leanh::lean_inc(v___y_2847_);
                            leanh::lean_inc_ref(v___y_2846_);
                            v___x_2868_ = lean_infer_type(
                                v___x_2867_,
                                v___y_2846_,
                                v___y_2847_,
                                v___y_2848_,
                                v___y_2849_,
                            );
                            if leanh::lean_obj_tag(v___x_2868_) == 0 {
                                v_a_2869_ = leanh::lean_ctor_get(v___x_2868_, 0);
                                leanh::lean_inc(v_a_2869_);
                                leanh::lean_dec_ref_known(v___x_2868_, 1);
                                leanh::lean_inc(v_val_2841_);
                                leanh::lean_inc(v_a_2844_);
                                v___f_2870_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 4);
                                leanh::lean_closure_set(v___f_2870_, 0, v_a_2844_);
                                leanh::lean_closure_set(v___f_2870_, 1, v___x_2858_);
                                leanh::lean_closure_set(v___f_2870_, 2, v_val_2841_);
                                leanh::lean_closure_set(v___f_2870_, 3, v___x_2862_);
                                v___x_2871_ = leanh::lean_unsigned_to_nat(1);
                                v___x_2872_ = lean_nat_add(v_a_2844_, v___x_2871_);
                                v___x_2873_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2873_, 0, v___x_2872_);
                                v___x_2874_ = 0;
                                v___x_2875_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_a_2869_, v___x_2873_, v___f_2870_, v___x_2874_, v___x_2874_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
                                if leanh::lean_obj_tag(v___x_2875_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_2875_, 1);
                                    v_a_2852_ = v___x_2858_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_2844_);
                                    leanh::lean_dec(v_val_2841_);
                                    return v___x_2875_;
                                }
                            } else {
                                leanh::lean_dec(v___x_2862_);
                                leanh::lean_dec(v_a_2844_);
                                leanh::lean_dec(v_val_2841_);
                                v_a_2876_ = leanh::lean_ctor_get(v___x_2868_, 0);
                                v_isSharedCheck_2883_ =
                                    (!leanh::lean_is_exclusive(v___x_2868_)) as u8;
                                if v_isSharedCheck_2883_ == 0 {
                                    v___x_2878_ = v___x_2868_;
                                    v_isShared_2879_ = v_isSharedCheck_2883_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2876_);
                                    leanh::lean_dec(v___x_2868_);
                                    v___x_2878_ = leanh::lean_box(0);
                                    v_isShared_2879_ = v_isSharedCheck_2883_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2862_);
                        leanh::lean_dec(v_a_2844_);
                        leanh::lean_dec(v_val_2841_);
                        v_a_2884_ = leanh::lean_ctor_get(v___x_2863_, 0);
                        v_isSharedCheck_2891_ =
                            (!leanh::lean_is_exclusive(v___x_2863_)) as u8;
                        if v_isSharedCheck_2891_ == 0 {
                            v___x_2886_ = v___x_2863_;
                            v_isShared_2887_ = v_isSharedCheck_2891_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2884_);
                            leanh::lean_dec(v___x_2863_);
                            v___x_2886_ = leanh::lean_box(0);
                            v_isShared_2887_ = v_isSharedCheck_2891_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_2879_ == 0 {
                    v___x_2881_ = v___x_2878_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2882_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
                    v___x_2881_ = v_reuseFailAlloc_2882_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2881_;
            }
            5 => {
                if v_isShared_2887_ == 0 {
                    v___x_2889_ = v___x_2886_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2890_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
                    v___x_2889_ = v_reuseFailAlloc_2890_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___boxed(
    mut v_upperBound_2894_: *mut leanh::LeanObject,
    mut v___x_2895_: *mut leanh::LeanObject,
    mut v_val_2896_: *mut leanh::LeanObject,
    mut v_e_2897_: *mut leanh::LeanObject,
    mut v_isTarget_2898_: *mut leanh::LeanObject,
    mut v_a_2899_: *mut leanh::LeanObject,
    mut v_b_2900_: *mut leanh::LeanObject,
    mut v___y_2901_: *mut leanh::LeanObject,
    mut v___y_2902_: *mut leanh::LeanObject,
    mut v___y_2903_: *mut leanh::LeanObject,
    mut v___y_2904_: *mut leanh::LeanObject,
    mut v___y_2905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2906_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(
            v_upperBound_2894_,
            v___x_2895_,
            v_val_2896_,
            v_e_2897_,
            v_isTarget_2898_,
            v_a_2899_,
            v_b_2900_,
            v___y_2901_,
            v___y_2902_,
            v___y_2903_,
            v___y_2904_,
        );
    leanh::lean_dec(v___y_2904_);
    leanh::lean_dec_ref(v___y_2903_);
    leanh::lean_dec(v___y_2902_);
    leanh::lean_dec_ref(v___y_2901_);
    leanh::lean_dec_ref(v_isTarget_2898_);
    leanh::lean_dec_ref(v_e_2897_);
    leanh::lean_dec_ref(v___x_2895_);
    leanh::lean_dec(v_upperBound_2894_);
    return v_res_2906_;
}
pub unsafe fn _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2907_ = leanh::lean_box(0);
    v_dummy_2908_ = l_Lean_Expr_sort___override(v___x_2907_);
    return v_dummy_2908_;
}
pub unsafe fn l_Lean_Meta_setMVarUserNamesAt___lam__0(
    mut v_val_2909_: *mut leanh::LeanObject,
    mut v_isTarget_2910_: *mut leanh::LeanObject,
    mut v___x_2911_: *mut leanh::LeanObject,
    mut v_e_2912_: *mut leanh::LeanObject,
    mut v___y_2913_: *mut leanh::LeanObject,
    mut v___y_2914_: *mut leanh::LeanObject,
    mut v___y_2915_: *mut leanh::LeanObject,
    mut v___y_2916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2918_: u8 = 0;
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2932_: u8 = 0;
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2936_: u8 = 0;
    let mut v_unused_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2918_ = l_Lean_Expr_isApp(v_e_2912_);
                if v___x_2918_ == 0 {
                    leanh::lean_dec_ref(v_e_2912_);
                    leanh::lean_dec(v___x_2911_);
                    leanh::lean_dec(v_val_2909_);
                    v___x_2919_ = leanh::lean_box(0);
                    v___x_2920_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2920_, 0, v___x_2919_);
                    return v___x_2920_;
                } else {
                    v_dummy_2921_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0_once
                        ),
                        _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0,
                    );
                    v_nargs_2922_ = l_Lean_Expr_getAppNumArgs(v_e_2912_);
                    leanh::lean_inc(v_nargs_2922_);
                    v___x_2923_ = lean_mk_array(v_nargs_2922_, v_dummy_2921_);
                    v___x_2924_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2925_ = lean_nat_sub(v_nargs_2922_, v___x_2924_);
                    leanh::lean_dec(v_nargs_2922_);
                    leanh::lean_inc_ref(v_e_2912_);
                    v___x_2926_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_2912_,
                        v___x_2923_,
                        v___x_2925_,
                    );
                    v___x_2927_ = lean_array_get_size(v___x_2926_);
                    v___x_2928_ = leanh::lean_box(0);
                    v___x_2929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v___x_2927_, v___x_2926_, v_val_2909_, v_e_2912_, v_isTarget_2910_, v___x_2911_, v___x_2928_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
                    leanh::lean_dec_ref(v_e_2912_);
                    leanh::lean_dec_ref(v___x_2926_);
                    if leanh::lean_obj_tag(v___x_2929_) == 0 {
                        v_isSharedCheck_2936_ =
                            (!leanh::lean_is_exclusive(v___x_2929_)) as u8;
                        if v_isSharedCheck_2936_ == 0 {
                            v_unused_2937_ = leanh::lean_ctor_get(v___x_2929_, 0);
                            leanh::lean_dec(v_unused_2937_);
                            v___x_2931_ = v___x_2929_;
                            v_isShared_2932_ = v_isSharedCheck_2936_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2929_);
                            v___x_2931_ = leanh::lean_box(0);
                            v_isShared_2932_ = v_isSharedCheck_2936_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_2929_;
                    }
                }
            }
            1 => {
                if v_isShared_2932_ == 0 {
                    leanh::lean_ctor_set(v___x_2931_, 0, v___x_2928_);
                    v___x_2934_ = v___x_2931_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2935_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2928_);
                    v___x_2934_ = v_reuseFailAlloc_2935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed(
    mut v_val_2938_: *mut leanh::LeanObject,
    mut v_isTarget_2939_: *mut leanh::LeanObject,
    mut v___x_2940_: *mut leanh::LeanObject,
    mut v_e_2941_: *mut leanh::LeanObject,
    mut v___y_2942_: *mut leanh::LeanObject,
    mut v___y_2943_: *mut leanh::LeanObject,
    mut v___y_2944_: *mut leanh::LeanObject,
    mut v___y_2945_: *mut leanh::LeanObject,
    mut v___y_2946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2947_ = l_Lean_Meta_setMVarUserNamesAt___lam__0(
        v_val_2938_,
        v_isTarget_2939_,
        v___x_2940_,
        v_e_2941_,
        v___y_2942_,
        v___y_2943_,
        v___y_2944_,
        v___y_2945_,
    );
    leanh::lean_dec(v___y_2945_);
    leanh::lean_dec_ref(v___y_2944_);
    leanh::lean_dec(v___y_2943_);
    leanh::lean_dec_ref(v___y_2942_);
    leanh::lean_dec_ref(v_isTarget_2939_);
    return v_res_2947_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(
    mut v_k_2948_: *mut leanh::LeanObject,
    mut v___y_2949_: *mut leanh::LeanObject,
    mut v_b_2950_: *mut leanh::LeanObject,
    mut v___y_2951_: *mut leanh::LeanObject,
    mut v___y_2952_: *mut leanh::LeanObject,
    mut v___y_2953_: *mut leanh::LeanObject,
    mut v___y_2954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2954_);
    leanh::lean_inc_ref(v___y_2953_);
    leanh::lean_inc(v___y_2952_);
    leanh::lean_inc_ref(v___y_2951_);
    leanh::lean_inc(v___y_2949_);
    v___x_2956_ = leanh::lean_apply_7(
        v_k_2948_,
        v_b_2950_,
        v___y_2949_,
        v___y_2951_,
        v___y_2952_,
        v___y_2953_,
        v___y_2954_,
        leanh::lean_box(0),
    );
    return v___x_2956_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed(
    mut v_k_2957_: *mut leanh::LeanObject,
    mut v___y_2958_: *mut leanh::LeanObject,
    mut v_b_2959_: *mut leanh::LeanObject,
    mut v___y_2960_: *mut leanh::LeanObject,
    mut v___y_2961_: *mut leanh::LeanObject,
    mut v___y_2962_: *mut leanh::LeanObject,
    mut v___y_2963_: *mut leanh::LeanObject,
    mut v___y_2964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2965_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(v_k_2957_, v___y_2958_, v_b_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
    leanh::lean_dec(v___y_2963_);
    leanh::lean_dec_ref(v___y_2962_);
    leanh::lean_dec(v___y_2961_);
    leanh::lean_dec_ref(v___y_2960_);
    leanh::lean_dec(v___y_2958_);
    return v_res_2965_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(
    mut v_name_2966_: *mut leanh::LeanObject,
    mut v_bi_2967_: u8,
    mut v_type_2968_: *mut leanh::LeanObject,
    mut v_k_2969_: *mut leanh::LeanObject,
    mut v_kind_2970_: u8,
    mut v___y_2971_: *mut leanh::LeanObject,
    mut v___y_2972_: *mut leanh::LeanObject,
    mut v___y_2973_: *mut leanh::LeanObject,
    mut v___y_2974_: *mut leanh::LeanObject,
    mut v___y_2975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2982_: u8 = 0;
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_2971_);
                v___f_2977_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                leanh::lean_closure_set(v___f_2977_, 0, v_k_2969_);
                leanh::lean_closure_set(v___f_2977_, 1, v___y_2971_);
                v___x_2978_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_2966_,
                    v_bi_2967_,
                    v_type_2968_,
                    v___f_2977_,
                    v_kind_2970_,
                    v___y_2972_,
                    v___y_2973_,
                    v___y_2974_,
                    v___y_2975_,
                );
                if leanh::lean_obj_tag(v___x_2978_) == 0 {
                    return v___x_2978_;
                } else {
                    v_a_2979_ = leanh::lean_ctor_get(v___x_2978_, 0);
                    v_isSharedCheck_2986_ = (!leanh::lean_is_exclusive(v___x_2978_)) as u8;
                    if v_isSharedCheck_2986_ == 0 {
                        v___x_2981_ = v___x_2978_;
                        v_isShared_2982_ = v_isSharedCheck_2986_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2979_);
                        leanh::lean_dec(v___x_2978_);
                        v___x_2981_ = leanh::lean_box(0);
                        v_isShared_2982_ = v_isSharedCheck_2986_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2982_ == 0 {
                    v___x_2984_ = v___x_2981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2985_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
                    v___x_2984_ = v_reuseFailAlloc_2985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___boxed(
    mut v_name_2987_: *mut leanh::LeanObject,
    mut v_bi_2988_: *mut leanh::LeanObject,
    mut v_type_2989_: *mut leanh::LeanObject,
    mut v_k_2990_: *mut leanh::LeanObject,
    mut v_kind_2991_: *mut leanh::LeanObject,
    mut v___y_2992_: *mut leanh::LeanObject,
    mut v___y_2993_: *mut leanh::LeanObject,
    mut v___y_2994_: *mut leanh::LeanObject,
    mut v___y_2995_: *mut leanh::LeanObject,
    mut v___y_2996_: *mut leanh::LeanObject,
    mut v___y_2997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_2998_: u8 = 0;
    let mut v_kind_boxed_2999_: u8 = 0;
    let mut v_res_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2998_ = (leanh::lean_unbox(v_bi_2988_) as u8);
    v_kind_boxed_2999_ = (leanh::lean_unbox(v_kind_2991_) as u8);
    v_res_3000_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_2987_, v_bi_boxed_2998_, v_type_2989_, v_k_2990_, v_kind_boxed_2999_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
    leanh::lean_dec(v___y_2996_);
    leanh::lean_dec_ref(v___y_2995_);
    leanh::lean_dec(v___y_2994_);
    leanh::lean_dec_ref(v___y_2993_);
    leanh::lean_dec(v___y_2992_);
    return v_res_3000_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0___boxed(
    mut v_fvars_3001_: *mut leanh::LeanObject,
    mut v_f_3002_: *mut leanh::LeanObject,
    mut v_body_3003_: *mut leanh::LeanObject,
    mut v_x_3004_: *mut leanh::LeanObject,
    mut v___y_3005_: *mut leanh::LeanObject,
    mut v___y_3006_: *mut leanh::LeanObject,
    mut v___y_3007_: *mut leanh::LeanObject,
    mut v___y_3008_: *mut leanh::LeanObject,
    mut v___y_3009_: *mut leanh::LeanObject,
    mut v___y_3010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3011_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(v_fvars_3001_, v_f_3002_, v_body_3003_, v_x_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
    leanh::lean_dec(v___y_3009_);
    leanh::lean_dec_ref(v___y_3008_);
    leanh::lean_dec(v___y_3007_);
    leanh::lean_dec_ref(v___y_3006_);
    leanh::lean_dec(v___y_3005_);
    return v_res_3011_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(
    mut v_f_3012_: *mut leanh::LeanObject,
    mut v_fvars_3013_: *mut leanh::LeanObject,
    mut v_a_3014_: *mut leanh::LeanObject,
    mut v___y_3015_: *mut leanh::LeanObject,
    mut v___y_3016_: *mut leanh::LeanObject,
    mut v___y_3017_: *mut leanh::LeanObject,
    mut v___y_3018_: *mut leanh::LeanObject,
    mut v___y_3019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_3014_) == 6 {
        let mut v_binderName_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_3024_: u8 = 0;
        let mut v_d_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_binderName_3021_ = leanh::lean_ctor_get(v_a_3014_, 0);
        leanh::lean_inc(v_binderName_3021_);
        v_binderType_3022_ = leanh::lean_ctor_get(v_a_3014_, 1);
        leanh::lean_inc_ref(v_binderType_3022_);
        v_body_3023_ = leanh::lean_ctor_get(v_a_3014_, 2);
        leanh::lean_inc_ref(v_body_3023_);
        v_binderInfo_3024_ = leanh::lean_ctor_get_uint8(
            v_a_3014_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_a_3014_, 3);
        v_d_3025_ = lean_expr_instantiate_rev(v_binderType_3022_, v_fvars_3013_);
        leanh::lean_dec_ref(v_binderType_3022_);
        leanh::lean_inc_ref(v_f_3012_);
        leanh::lean_inc(v___y_3019_);
        leanh::lean_inc_ref(v___y_3018_);
        leanh::lean_inc(v___y_3017_);
        leanh::lean_inc_ref(v___y_3016_);
        leanh::lean_inc(v___y_3015_);
        leanh::lean_inc_ref(v_d_3025_);
        v___x_3026_ = leanh::lean_apply_7(
            v_f_3012_,
            v_d_3025_,
            v___y_3015_,
            v___y_3016_,
            v___y_3017_,
            v___y_3018_,
            v___y_3019_,
            leanh::lean_box(0),
        );
        if leanh::lean_obj_tag(v___x_3026_) == 0 {
            let mut v___f_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3028_: u8 = 0;
            let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_3026_, 1);
            v___f_3027_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
            leanh::lean_closure_set(v___f_3027_, 0, v_fvars_3013_);
            leanh::lean_closure_set(v___f_3027_, 1, v_f_3012_);
            leanh::lean_closure_set(v___f_3027_, 2, v_body_3023_);
            v___x_3028_ = 0;
            v___x_3029_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_binderName_3021_, v_binderInfo_3024_, v_d_3025_, v___f_3027_, v___x_3028_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
            return v___x_3029_;
        } else {
            leanh::lean_dec_ref(v_d_3025_);
            leanh::lean_dec_ref(v_body_3023_);
            leanh::lean_dec(v_binderName_3021_);
            leanh::lean_dec_ref(v_fvars_3013_);
            leanh::lean_dec_ref(v_f_3012_);
            return v___x_3026_;
        }
    } else {
        let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3030_ = lean_expr_instantiate_rev(v_a_3014_, v_fvars_3013_);
        leanh::lean_dec_ref(v_fvars_3013_);
        leanh::lean_dec_ref(v_a_3014_);
        leanh::lean_inc(v___y_3019_);
        leanh::lean_inc_ref(v___y_3018_);
        leanh::lean_inc(v___y_3017_);
        leanh::lean_inc_ref(v___y_3016_);
        leanh::lean_inc(v___y_3015_);
        v___x_3031_ = leanh::lean_apply_7(
            v_f_3012_,
            v___x_3030_,
            v___y_3015_,
            v___y_3016_,
            v___y_3017_,
            v___y_3018_,
            v___y_3019_,
            leanh::lean_box(0),
        );
        return v___x_3031_;
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(
    mut v_fvars_3032_: *mut leanh::LeanObject,
    mut v_f_3033_: *mut leanh::LeanObject,
    mut v_body_3034_: *mut leanh::LeanObject,
    mut v_x_3035_: *mut leanh::LeanObject,
    mut v___y_3036_: *mut leanh::LeanObject,
    mut v___y_3037_: *mut leanh::LeanObject,
    mut v___y_3038_: *mut leanh::LeanObject,
    mut v___y_3039_: *mut leanh::LeanObject,
    mut v___y_3040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3042_ = lean_array_push(v_fvars_3032_, v_x_3035_);
    v___x_3043_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_3033_, v___x_3042_, v_body_3034_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
    return v___x_3043_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___boxed(
    mut v_f_3044_: *mut leanh::LeanObject,
    mut v_fvars_3045_: *mut leanh::LeanObject,
    mut v_a_3046_: *mut leanh::LeanObject,
    mut v___y_3047_: *mut leanh::LeanObject,
    mut v___y_3048_: *mut leanh::LeanObject,
    mut v___y_3049_: *mut leanh::LeanObject,
    mut v___y_3050_: *mut leanh::LeanObject,
    mut v___y_3051_: *mut leanh::LeanObject,
    mut v___y_3052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3053_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_3044_, v_fvars_3045_, v_a_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
    leanh::lean_dec(v___y_3051_);
    leanh::lean_dec_ref(v___y_3050_);
    leanh::lean_dec(v___y_3049_);
    leanh::lean_dec_ref(v___y_3048_);
    leanh::lean_dec(v___y_3047_);
    return v_res_3053_;
}
pub unsafe fn l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(
    mut v_f_3054_: *mut leanh::LeanObject,
    mut v_e_3055_: *mut leanh::LeanObject,
    mut v___y_3056_: *mut leanh::LeanObject,
    mut v___y_3057_: *mut leanh::LeanObject,
    mut v___y_3058_: *mut leanh::LeanObject,
    mut v___y_3059_: *mut leanh::LeanObject,
    mut v___y_3060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3062_ = l_Lean_Meta_visitLambda___redArg___closed__0;
    v___x_3063_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_3054_, v___x_3062_, v_e_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
    return v___x_3063_;
}
pub unsafe fn l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10___boxed(
    mut v_f_3064_: *mut leanh::LeanObject,
    mut v_e_3065_: *mut leanh::LeanObject,
    mut v___y_3066_: *mut leanh::LeanObject,
    mut v___y_3067_: *mut leanh::LeanObject,
    mut v___y_3068_: *mut leanh::LeanObject,
    mut v___y_3069_: *mut leanh::LeanObject,
    mut v___y_3070_: *mut leanh::LeanObject,
    mut v___y_3071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3072_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v_f_3064_, v_e_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
    leanh::lean_dec(v___y_3070_);
    leanh::lean_dec_ref(v___y_3069_);
    leanh::lean_dec(v___y_3068_);
    leanh::lean_dec_ref(v___y_3067_);
    leanh::lean_dec(v___y_3066_);
    return v_res_3072_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(
    mut v_00_u03b1_3073_: *mut leanh::LeanObject,
    mut v_x_3074_: *mut leanh::LeanObject,
    mut v___y_3075_: *mut leanh::LeanObject,
    mut v___y_3076_: *mut leanh::LeanObject,
    mut v___y_3077_: *mut leanh::LeanObject,
    mut v___y_3078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3080_ = leanh::lean_apply_1(v_x_3074_, leanh::lean_box(0));
    v___x_3081_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3081_, 0, v___x_3080_);
    return v___x_3081_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0___boxed(
    mut v_00_u03b1_3082_: *mut leanh::LeanObject,
    mut v_x_3083_: *mut leanh::LeanObject,
    mut v___y_3084_: *mut leanh::LeanObject,
    mut v___y_3085_: *mut leanh::LeanObject,
    mut v___y_3086_: *mut leanh::LeanObject,
    mut v___y_3087_: *mut leanh::LeanObject,
    mut v___y_3088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3089_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(v_00_u03b1_3082_, v_x_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
    leanh::lean_dec(v___y_3087_);
    leanh::lean_dec_ref(v___y_3086_);
    leanh::lean_dec(v___y_3085_);
    leanh::lean_dec_ref(v___y_3084_);
    return v_res_3089_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0___boxed(
    mut v_fvars_3090_: *mut leanh::LeanObject,
    mut v_f_3091_: *mut leanh::LeanObject,
    mut v_body_3092_: *mut leanh::LeanObject,
    mut v_x_3093_: *mut leanh::LeanObject,
    mut v___y_3094_: *mut leanh::LeanObject,
    mut v___y_3095_: *mut leanh::LeanObject,
    mut v___y_3096_: *mut leanh::LeanObject,
    mut v___y_3097_: *mut leanh::LeanObject,
    mut v___y_3098_: *mut leanh::LeanObject,
    mut v___y_3099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3100_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(v_fvars_3090_, v_f_3091_, v_body_3092_, v_x_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
    leanh::lean_dec(v___y_3098_);
    leanh::lean_dec_ref(v___y_3097_);
    leanh::lean_dec(v___y_3096_);
    leanh::lean_dec_ref(v___y_3095_);
    leanh::lean_dec(v___y_3094_);
    return v_res_3100_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(
    mut v_f_3101_: *mut leanh::LeanObject,
    mut v_fvars_3102_: *mut leanh::LeanObject,
    mut v_a_3103_: *mut leanh::LeanObject,
    mut v___y_3104_: *mut leanh::LeanObject,
    mut v___y_3105_: *mut leanh::LeanObject,
    mut v___y_3106_: *mut leanh::LeanObject,
    mut v___y_3107_: *mut leanh::LeanObject,
    mut v___y_3108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_3103_) == 7 {
        let mut v_binderName_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_3113_: u8 = 0;
        let mut v_d_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_binderName_3110_ = leanh::lean_ctor_get(v_a_3103_, 0);
        leanh::lean_inc(v_binderName_3110_);
        v_binderType_3111_ = leanh::lean_ctor_get(v_a_3103_, 1);
        leanh::lean_inc_ref(v_binderType_3111_);
        v_body_3112_ = leanh::lean_ctor_get(v_a_3103_, 2);
        leanh::lean_inc_ref(v_body_3112_);
        v_binderInfo_3113_ = leanh::lean_ctor_get_uint8(
            v_a_3103_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_a_3103_, 3);
        v_d_3114_ = lean_expr_instantiate_rev(v_binderType_3111_, v_fvars_3102_);
        leanh::lean_dec_ref(v_binderType_3111_);
        leanh::lean_inc_ref(v_f_3101_);
        leanh::lean_inc(v___y_3108_);
        leanh::lean_inc_ref(v___y_3107_);
        leanh::lean_inc(v___y_3106_);
        leanh::lean_inc_ref(v___y_3105_);
        leanh::lean_inc(v___y_3104_);
        leanh::lean_inc_ref(v_d_3114_);
        v___x_3115_ = leanh::lean_apply_7(
            v_f_3101_,
            v_d_3114_,
            v___y_3104_,
            v___y_3105_,
            v___y_3106_,
            v___y_3107_,
            v___y_3108_,
            leanh::lean_box(0),
        );
        if leanh::lean_obj_tag(v___x_3115_) == 0 {
            let mut v___f_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3117_: u8 = 0;
            let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_3115_, 1);
            v___f_3116_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
            leanh::lean_closure_set(v___f_3116_, 0, v_fvars_3102_);
            leanh::lean_closure_set(v___f_3116_, 1, v_f_3101_);
            leanh::lean_closure_set(v___f_3116_, 2, v_body_3112_);
            v___x_3117_ = 0;
            v___x_3118_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_binderName_3110_, v_binderInfo_3113_, v_d_3114_, v___f_3116_, v___x_3117_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
            return v___x_3118_;
        } else {
            leanh::lean_dec_ref(v_d_3114_);
            leanh::lean_dec_ref(v_body_3112_);
            leanh::lean_dec(v_binderName_3110_);
            leanh::lean_dec_ref(v_fvars_3102_);
            leanh::lean_dec_ref(v_f_3101_);
            return v___x_3115_;
        }
    } else {
        let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3119_ = lean_expr_instantiate_rev(v_a_3103_, v_fvars_3102_);
        leanh::lean_dec_ref(v_fvars_3102_);
        leanh::lean_dec_ref(v_a_3103_);
        leanh::lean_inc(v___y_3108_);
        leanh::lean_inc_ref(v___y_3107_);
        leanh::lean_inc(v___y_3106_);
        leanh::lean_inc_ref(v___y_3105_);
        leanh::lean_inc(v___y_3104_);
        v___x_3120_ = leanh::lean_apply_7(
            v_f_3101_,
            v___x_3119_,
            v___y_3104_,
            v___y_3105_,
            v___y_3106_,
            v___y_3107_,
            v___y_3108_,
            leanh::lean_box(0),
        );
        return v___x_3120_;
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(
    mut v_fvars_3121_: *mut leanh::LeanObject,
    mut v_f_3122_: *mut leanh::LeanObject,
    mut v_body_3123_: *mut leanh::LeanObject,
    mut v_x_3124_: *mut leanh::LeanObject,
    mut v___y_3125_: *mut leanh::LeanObject,
    mut v___y_3126_: *mut leanh::LeanObject,
    mut v___y_3127_: *mut leanh::LeanObject,
    mut v___y_3128_: *mut leanh::LeanObject,
    mut v___y_3129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3131_ = lean_array_push(v_fvars_3121_, v_x_3124_);
    v___x_3132_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_3122_, v___x_3131_, v_body_3123_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
    return v___x_3132_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___boxed(
    mut v_f_3133_: *mut leanh::LeanObject,
    mut v_fvars_3134_: *mut leanh::LeanObject,
    mut v_a_3135_: *mut leanh::LeanObject,
    mut v___y_3136_: *mut leanh::LeanObject,
    mut v___y_3137_: *mut leanh::LeanObject,
    mut v___y_3138_: *mut leanh::LeanObject,
    mut v___y_3139_: *mut leanh::LeanObject,
    mut v___y_3140_: *mut leanh::LeanObject,
    mut v___y_3141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3142_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_3133_, v_fvars_3134_, v_a_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
    leanh::lean_dec(v___y_3140_);
    leanh::lean_dec_ref(v___y_3139_);
    leanh::lean_dec(v___y_3138_);
    leanh::lean_dec_ref(v___y_3137_);
    leanh::lean_dec(v___y_3136_);
    return v_res_3142_;
}
pub unsafe fn l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(
    mut v_f_3143_: *mut leanh::LeanObject,
    mut v_e_3144_: *mut leanh::LeanObject,
    mut v___y_3145_: *mut leanh::LeanObject,
    mut v___y_3146_: *mut leanh::LeanObject,
    mut v___y_3147_: *mut leanh::LeanObject,
    mut v___y_3148_: *mut leanh::LeanObject,
    mut v___y_3149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3151_ = l_Lean_Meta_visitLambda___redArg___closed__0;
    v___x_3152_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_3143_, v___x_3151_, v_e_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
    return v___x_3152_;
}
pub unsafe fn l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___boxed(
    mut v_f_3153_: *mut leanh::LeanObject,
    mut v_e_3154_: *mut leanh::LeanObject,
    mut v___y_3155_: *mut leanh::LeanObject,
    mut v___y_3156_: *mut leanh::LeanObject,
    mut v___y_3157_: *mut leanh::LeanObject,
    mut v___y_3158_: *mut leanh::LeanObject,
    mut v___y_3159_: *mut leanh::LeanObject,
    mut v___y_3160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3161_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v_f_3153_, v_e_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
    leanh::lean_dec(v___y_3159_);
    leanh::lean_dec_ref(v___y_3158_);
    leanh::lean_dec(v___y_3157_);
    leanh::lean_dec_ref(v___y_3156_);
    leanh::lean_dec(v___y_3155_);
    return v_res_3161_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(
    mut v_a_3162_: *mut leanh::LeanObject,
    mut v_x_3163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3163_) == 0 {
                    v___x_3164_ = leanh::lean_box(0);
                    return v___x_3164_;
                } else {
                    v_key_3165_ = leanh::lean_ctor_get(v_x_3163_, 0);
                    v_value_3166_ = leanh::lean_ctor_get(v_x_3163_, 1);
                    v_tail_3167_ = leanh::lean_ctor_get(v_x_3163_, 2);
                    v___x_3168_ = lean_expr_eqv(v_key_3165_, v_a_3162_);
                    if v___x_3168_ == 0 {
                        v_x_3163_ = v_tail_3167_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_3166_);
                        v___x_3170_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3170_, 0, v_value_3166_);
                        return v___x_3170_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg___boxed(
    mut v_a_3171_: *mut leanh::LeanObject,
    mut v_x_3172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3173_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_3171_, v_x_3172_);
    leanh::lean_dec(v_x_3172_);
    leanh::lean_dec_ref(v_a_3171_);
    return v_res_3173_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(
    mut v_m_3174_: *mut leanh::LeanObject,
    mut v_a_3175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: u64 = 0;
    let mut v___x_3179_: u64 = 0;
    let mut v___x_3180_: u64 = 0;
    let mut v_fold_3181_: u64 = 0;
    let mut v___x_3182_: u64 = 0;
    let mut v___x_3183_: u64 = 0;
    let mut v___x_3184_: u64 = 0;
    let mut v___x_3185_: usize = 0;
    let mut v___x_3186_: usize = 0;
    let mut v___x_3187_: usize = 0;
    let mut v___x_3188_: usize = 0;
    let mut v___x_3189_: usize = 0;
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3176_ = leanh::lean_ctor_get(v_m_3174_, 1);
    v___x_3177_ = lean_array_get_size(v_buckets_3176_);
    v___x_3178_ = l_Lean_Expr_hash(v_a_3175_);
    v___x_3179_ = 32u64;
    v___x_3180_ = lean_uint64_shift_right(v___x_3178_, v___x_3179_);
    v_fold_3181_ = lean_uint64_xor(v___x_3178_, v___x_3180_);
    v___x_3182_ = 16u64;
    v___x_3183_ = lean_uint64_shift_right(v_fold_3181_, v___x_3182_);
    v___x_3184_ = lean_uint64_xor(v_fold_3181_, v___x_3183_);
    v___x_3185_ = lean_uint64_to_usize(v___x_3184_);
    v___x_3186_ = lean_usize_of_nat(v___x_3177_);
    v___x_3187_ = 1usize;
    v___x_3188_ = lean_usize_sub(v___x_3186_, v___x_3187_);
    v___x_3189_ = lean_usize_land(v___x_3185_, v___x_3188_);
    v___x_3190_ = lean_array_uget_borrowed(v_buckets_3176_, v___x_3189_);
    v___x_3191_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_3175_, v___x_3190_);
    return v___x_3191_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg___boxed(
    mut v_m_3192_: *mut leanh::LeanObject,
    mut v_a_3193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3194_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_3192_, v_a_3193_);
    leanh::lean_dec_ref(v_a_3193_);
    leanh::lean_dec_ref(v_m_3192_);
    return v_res_3194_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(
    mut v_a_3195_: *mut leanh::LeanObject,
    mut v_b_3196_: *mut leanh::LeanObject,
    mut v_x_3197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3203_: u8 = 0;
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3197_) == 0 {
                    leanh::lean_dec(v_b_3196_);
                    leanh::lean_dec_ref(v_a_3195_);
                    return v_x_3197_;
                } else {
                    v_key_3198_ = leanh::lean_ctor_get(v_x_3197_, 0);
                    v_value_3199_ = leanh::lean_ctor_get(v_x_3197_, 1);
                    v_tail_3200_ = leanh::lean_ctor_get(v_x_3197_, 2);
                    v_isSharedCheck_3212_ = (!leanh::lean_is_exclusive(v_x_3197_)) as u8;
                    if v_isSharedCheck_3212_ == 0 {
                        v___x_3202_ = v_x_3197_;
                        v_isShared_3203_ = v_isSharedCheck_3212_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3200_);
                        leanh::lean_inc(v_value_3199_);
                        leanh::lean_inc(v_key_3198_);
                        leanh::lean_dec(v_x_3197_);
                        v___x_3202_ = leanh::lean_box(0);
                        v_isShared_3203_ = v_isSharedCheck_3212_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3204_ = lean_expr_eqv(v_key_3198_, v_a_3195_);
                if v___x_3204_ == 0 {
                    v___x_3205_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_3195_, v_b_3196_, v_tail_3200_);
                    if v_isShared_3203_ == 0 {
                        leanh::lean_ctor_set(v___x_3202_, 2, v___x_3205_);
                        v___x_3207_ = v___x_3202_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3208_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_key_3198_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_value_3199_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 2, v___x_3205_);
                        v___x_3207_ = v_reuseFailAlloc_3208_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_3199_);
                    leanh::lean_dec(v_key_3198_);
                    if v_isShared_3203_ == 0 {
                        leanh::lean_ctor_set(v___x_3202_, 1, v_b_3196_);
                        leanh::lean_ctor_set(v___x_3202_, 0, v_a_3195_);
                        v___x_3210_ = v___x_3202_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3211_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3195_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_b_3196_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3211_, 2, v_tail_3200_);
                        v___x_3210_ = v_reuseFailAlloc_3211_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3207_;
            }
            3 => {
                return v___x_3210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(
    mut v_x_3213_: *mut leanh::LeanObject,
    mut v_x_3214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3220_: u8 = 0;
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: u64 = 0;
    let mut v___x_3223_: u64 = 0;
    let mut v___x_3224_: u64 = 0;
    let mut v_fold_3225_: u64 = 0;
    let mut v___x_3226_: u64 = 0;
    let mut v___x_3227_: u64 = 0;
    let mut v___x_3228_: u64 = 0;
    let mut v___x_3229_: usize = 0;
    let mut v___x_3230_: usize = 0;
    let mut v___x_3231_: usize = 0;
    let mut v___x_3232_: usize = 0;
    let mut v___x_3233_: usize = 0;
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3214_) == 0 {
                    return v_x_3213_;
                } else {
                    v_key_3215_ = leanh::lean_ctor_get(v_x_3214_, 0);
                    v_value_3216_ = leanh::lean_ctor_get(v_x_3214_, 1);
                    v_tail_3217_ = leanh::lean_ctor_get(v_x_3214_, 2);
                    v_isSharedCheck_3240_ = (!leanh::lean_is_exclusive(v_x_3214_)) as u8;
                    if v_isSharedCheck_3240_ == 0 {
                        v___x_3219_ = v_x_3214_;
                        v_isShared_3220_ = v_isSharedCheck_3240_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3217_);
                        leanh::lean_inc(v_value_3216_);
                        leanh::lean_inc(v_key_3215_);
                        leanh::lean_dec(v_x_3214_);
                        v___x_3219_ = leanh::lean_box(0);
                        v_isShared_3220_ = v_isSharedCheck_3240_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3221_ = lean_array_get_size(v_x_3213_);
                v___x_3222_ = l_Lean_Expr_hash(v_key_3215_);
                v___x_3223_ = 32u64;
                v___x_3224_ = lean_uint64_shift_right(v___x_3222_, v___x_3223_);
                v_fold_3225_ = lean_uint64_xor(v___x_3222_, v___x_3224_);
                v___x_3226_ = 16u64;
                v___x_3227_ = lean_uint64_shift_right(v_fold_3225_, v___x_3226_);
                v___x_3228_ = lean_uint64_xor(v_fold_3225_, v___x_3227_);
                v___x_3229_ = lean_uint64_to_usize(v___x_3228_);
                v___x_3230_ = lean_usize_of_nat(v___x_3221_);
                v___x_3231_ = 1usize;
                v___x_3232_ = lean_usize_sub(v___x_3230_, v___x_3231_);
                v___x_3233_ = lean_usize_land(v___x_3229_, v___x_3232_);
                v___x_3234_ = lean_array_uget_borrowed(v_x_3213_, v___x_3233_);
                leanh::lean_inc(v___x_3234_);
                if v_isShared_3220_ == 0 {
                    leanh::lean_ctor_set(v___x_3219_, 2, v___x_3234_);
                    v___x_3236_ = v___x_3219_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_key_3215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_value_3216_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 2, v___x_3234_);
                    v___x_3236_ = v_reuseFailAlloc_3239_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3237_ = lean_array_uset(v_x_3213_, v___x_3233_, v___x_3236_);
                v_x_3213_ = v___x_3237_;
                v_x_3214_ = v_tail_3217_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(
    mut v_i_3241_: *mut leanh::LeanObject,
    mut v_source_3242_: *mut leanh::LeanObject,
    mut v_target_3243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v_es_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3244_ = lean_array_get_size(v_source_3242_);
                v___x_3245_ = lean_nat_dec_lt(v_i_3241_, v___x_3244_);
                if v___x_3245_ == 0 {
                    leanh::lean_dec_ref(v_source_3242_);
                    leanh::lean_dec(v_i_3241_);
                    return v_target_3243_;
                } else {
                    v_es_3246_ = lean_array_fget(v_source_3242_, v_i_3241_);
                    v___x_3247_ = leanh::lean_box(0);
                    v_source_3248_ = lean_array_fset(v_source_3242_, v_i_3241_, v___x_3247_);
                    v_target_3249_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(v_target_3243_, v_es_3246_);
                    v___x_3250_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3251_ = lean_nat_add(v_i_3241_, v___x_3250_);
                    leanh::lean_dec(v_i_3241_);
                    v_i_3241_ = v___x_3251_;
                    v_source_3242_ = v_source_3248_;
                    v_target_3243_ = v_target_3249_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(
    mut v_data_3253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3254_ = lean_array_get_size(v_data_3253_);
    v___x_3255_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3256_ = lean_nat_mul(v___x_3254_, v___x_3255_);
    v___x_3257_ = leanh::lean_unsigned_to_nat(0);
    v___x_3258_ = leanh::lean_box(0);
    v___x_3259_ = lean_mk_array(v_nbuckets_3256_, v___x_3258_);
    v___x_3260_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v___x_3257_, v_data_3253_, v___x_3259_);
    return v___x_3260_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(
    mut v_a_3261_: *mut leanh::LeanObject,
    mut v_x_3262_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3263_: u8 = 0;
    let mut v_key_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3262_) == 0 {
                    v___x_3263_ = 0;
                    return v___x_3263_;
                } else {
                    v_key_3264_ = leanh::lean_ctor_get(v_x_3262_, 0);
                    v_tail_3265_ = leanh::lean_ctor_get(v_x_3262_, 2);
                    v___x_3266_ = lean_expr_eqv(v_key_3264_, v_a_3261_);
                    if v___x_3266_ == 0 {
                        v_x_3262_ = v_tail_3265_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3266_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg___boxed(
    mut v_a_3268_: *mut leanh::LeanObject,
    mut v_x_3269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3270_: u8 = 0;
    let mut v_r_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_3268_, v_x_3269_);
    leanh::lean_dec(v_x_3269_);
    leanh::lean_dec_ref(v_a_3268_);
    v_r_3271_ = leanh::lean_box((v_res_3270_) as usize);
    return v_r_3271_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(
    mut v_m_3272_: *mut leanh::LeanObject,
    mut v_a_3273_: *mut leanh::LeanObject,
    mut v_b_3274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3279_: u8 = 0;
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: u64 = 0;
    let mut v___x_3282_: u64 = 0;
    let mut v___x_3283_: u64 = 0;
    let mut v_fold_3284_: u64 = 0;
    let mut v___x_3285_: u64 = 0;
    let mut v___x_3286_: u64 = 0;
    let mut v___x_3287_: u64 = 0;
    let mut v___x_3288_: usize = 0;
    let mut v___x_3289_: usize = 0;
    let mut v___x_3290_: usize = 0;
    let mut v___x_3291_: usize = 0;
    let mut v___x_3292_: usize = 0;
    let mut v_bkt_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: u8 = 0;
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: u8 = 0;
    let mut v_val_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3275_ = leanh::lean_ctor_get(v_m_3272_, 0);
                v_buckets_3276_ = leanh::lean_ctor_get(v_m_3272_, 1);
                v_isSharedCheck_3319_ = (!leanh::lean_is_exclusive(v_m_3272_)) as u8;
                if v_isSharedCheck_3319_ == 0 {
                    v___x_3278_ = v_m_3272_;
                    v_isShared_3279_ = v_isSharedCheck_3319_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3276_);
                    leanh::lean_inc(v_size_3275_);
                    leanh::lean_dec(v_m_3272_);
                    v___x_3278_ = leanh::lean_box(0);
                    v_isShared_3279_ = v_isSharedCheck_3319_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3280_ = lean_array_get_size(v_buckets_3276_);
                v___x_3281_ = l_Lean_Expr_hash(v_a_3273_);
                v___x_3282_ = 32u64;
                v___x_3283_ = lean_uint64_shift_right(v___x_3281_, v___x_3282_);
                v_fold_3284_ = lean_uint64_xor(v___x_3281_, v___x_3283_);
                v___x_3285_ = 16u64;
                v___x_3286_ = lean_uint64_shift_right(v_fold_3284_, v___x_3285_);
                v___x_3287_ = lean_uint64_xor(v_fold_3284_, v___x_3286_);
                v___x_3288_ = lean_uint64_to_usize(v___x_3287_);
                v___x_3289_ = lean_usize_of_nat(v___x_3280_);
                v___x_3290_ = 1usize;
                v___x_3291_ = lean_usize_sub(v___x_3289_, v___x_3290_);
                v___x_3292_ = lean_usize_land(v___x_3288_, v___x_3291_);
                v_bkt_3293_ = lean_array_uget_borrowed(v_buckets_3276_, v___x_3292_);
                v___x_3294_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_3273_, v_bkt_3293_);
                if v___x_3294_ == 0 {
                    v___x_3295_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3296_ = lean_nat_add(v_size_3275_, v___x_3295_);
                    leanh::lean_dec(v_size_3275_);
                    leanh::lean_inc(v_bkt_3293_);
                    v___x_3297_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3297_, 0, v_a_3273_);
                    leanh::lean_ctor_set(v___x_3297_, 1, v_b_3274_);
                    leanh::lean_ctor_set(v___x_3297_, 2, v_bkt_3293_);
                    v_buckets_x27_3298_ =
                        lean_array_uset(v_buckets_3276_, v___x_3292_, v___x_3297_);
                    v___x_3299_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3300_ = lean_nat_mul(v_size_x27_3296_, v___x_3299_);
                    v___x_3301_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3302_ = lean_nat_div(v___x_3300_, v___x_3301_);
                    leanh::lean_dec(v___x_3300_);
                    v___x_3303_ = lean_array_get_size(v_buckets_x27_3298_);
                    v___x_3304_ = lean_nat_dec_le(v___x_3302_, v___x_3303_);
                    leanh::lean_dec(v___x_3302_);
                    if v___x_3304_ == 0 {
                        v_val_3305_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_buckets_x27_3298_);
                        if v_isShared_3279_ == 0 {
                            leanh::lean_ctor_set(v___x_3278_, 1, v_val_3305_);
                            leanh::lean_ctor_set(v___x_3278_, 0, v_size_x27_3296_);
                            v___x_3307_ = v___x_3278_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3308_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3308_,
                                0,
                                v_size_x27_3296_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3308_, 1, v_val_3305_);
                            v___x_3307_ = v_reuseFailAlloc_3308_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3279_ == 0 {
                            leanh::lean_ctor_set(v___x_3278_, 1, v_buckets_x27_3298_);
                            leanh::lean_ctor_set(v___x_3278_, 0, v_size_x27_3296_);
                            v___x_3310_ = v___x_3278_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3311_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3311_,
                                0,
                                v_size_x27_3296_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3311_,
                                1,
                                v_buckets_x27_3298_,
                            );
                            v___x_3310_ = v_reuseFailAlloc_3311_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_3293_);
                    v___x_3312_ = leanh::lean_box(0);
                    v_buckets_x27_3313_ =
                        lean_array_uset(v_buckets_3276_, v___x_3292_, v___x_3312_);
                    v___x_3314_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_3273_, v_b_3274_, v_bkt_3293_);
                    v___x_3315_ = lean_array_uset(v_buckets_x27_3313_, v___x_3292_, v___x_3314_);
                    if v_isShared_3279_ == 0 {
                        leanh::lean_ctor_set(v___x_3278_, 1, v___x_3315_);
                        v___x_3317_ = v___x_3278_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3318_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_size_3275_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3318_, 1, v___x_3315_);
                        v___x_3317_ = v_reuseFailAlloc_3318_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3307_;
            }
            3 => {
                return v___x_3310_;
            }
            4 => {
                return v___x_3317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(
    mut v_a_3320_: *mut leanh::LeanObject,
    mut v_e_3321_: *mut leanh::LeanObject,
    mut v_a_3322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = lean_st_ref_take(v_a_3320_);
    v___x_3325_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v___x_3324_, v_e_3321_, v_a_3322_);
    v___x_3326_ = lean_st_ref_set(v_a_3320_, v___x_3325_);
    v___x_3327_ = leanh::lean_box(0);
    return v___x_3327_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed(
    mut v_a_3328_: *mut leanh::LeanObject,
    mut v_e_3329_: *mut leanh::LeanObject,
    mut v_a_3330_: *mut leanh::LeanObject,
    mut v___y_3331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3332_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(v_a_3328_, v_e_3329_, v_a_3330_);
    leanh::lean_dec(v_a_3328_);
    return v_res_3332_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(
    mut v_name_3333_: *mut leanh::LeanObject,
    mut v_type_3334_: *mut leanh::LeanObject,
    mut v_val_3335_: *mut leanh::LeanObject,
    mut v_k_3336_: *mut leanh::LeanObject,
    mut v_nondep_3337_: u8,
    mut v_kind_3338_: u8,
    mut v___y_3339_: *mut leanh::LeanObject,
    mut v___y_3340_: *mut leanh::LeanObject,
    mut v___y_3341_: *mut leanh::LeanObject,
    mut v___y_3342_: *mut leanh::LeanObject,
    mut v___y_3343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3350_: u8 = 0;
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3339_);
                v___f_3345_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                leanh::lean_closure_set(v___f_3345_, 0, v_k_3336_);
                leanh::lean_closure_set(v___f_3345_, 1, v___y_3339_);
                v___x_3346_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    leanh::lean_box(0),
                    v_name_3333_,
                    v_type_3334_,
                    v_val_3335_,
                    v___f_3345_,
                    v_nondep_3337_,
                    v_kind_3338_,
                    v___y_3340_,
                    v___y_3341_,
                    v___y_3342_,
                    v___y_3343_,
                );
                if leanh::lean_obj_tag(v___x_3346_) == 0 {
                    return v___x_3346_;
                } else {
                    v_a_3347_ = leanh::lean_ctor_get(v___x_3346_, 0);
                    v_isSharedCheck_3354_ = (!leanh::lean_is_exclusive(v___x_3346_)) as u8;
                    if v_isSharedCheck_3354_ == 0 {
                        v___x_3349_ = v___x_3346_;
                        v_isShared_3350_ = v_isSharedCheck_3354_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3347_);
                        leanh::lean_dec(v___x_3346_);
                        v___x_3349_ = leanh::lean_box(0);
                        v_isShared_3350_ = v_isSharedCheck_3354_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3350_ == 0 {
                    v___x_3352_ = v___x_3349_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3353_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
                    v___x_3352_ = v_reuseFailAlloc_3353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg___boxed(
    mut v_name_3355_: *mut leanh::LeanObject,
    mut v_type_3356_: *mut leanh::LeanObject,
    mut v_val_3357_: *mut leanh::LeanObject,
    mut v_k_3358_: *mut leanh::LeanObject,
    mut v_nondep_3359_: *mut leanh::LeanObject,
    mut v_kind_3360_: *mut leanh::LeanObject,
    mut v___y_3361_: *mut leanh::LeanObject,
    mut v___y_3362_: *mut leanh::LeanObject,
    mut v___y_3363_: *mut leanh::LeanObject,
    mut v___y_3364_: *mut leanh::LeanObject,
    mut v___y_3365_: *mut leanh::LeanObject,
    mut v___y_3366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_3367_: u8 = 0;
    let mut v_kind_boxed_3368_: u8 = 0;
    let mut v_res_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3367_ = (leanh::lean_unbox(v_nondep_3359_) as u8);
    v_kind_boxed_3368_ = (leanh::lean_unbox(v_kind_3360_) as u8);
    v_res_3369_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_3355_, v_type_3356_, v_val_3357_, v_k_3358_, v_nondep_boxed_3367_, v_kind_boxed_3368_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
    leanh::lean_dec(v___y_3365_);
    leanh::lean_dec_ref(v___y_3364_);
    leanh::lean_dec(v___y_3363_);
    leanh::lean_dec_ref(v___y_3362_);
    leanh::lean_dec(v___y_3361_);
    return v_res_3369_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed(
    mut v_fvars_3370_: *mut leanh::LeanObject,
    mut v_f_3371_: *mut leanh::LeanObject,
    mut v_body_3372_: *mut leanh::LeanObject,
    mut v_x_3373_: *mut leanh::LeanObject,
    mut v___y_3374_: *mut leanh::LeanObject,
    mut v___y_3375_: *mut leanh::LeanObject,
    mut v___y_3376_: *mut leanh::LeanObject,
    mut v___y_3377_: *mut leanh::LeanObject,
    mut v___y_3378_: *mut leanh::LeanObject,
    mut v___y_3379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3380_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(v_fvars_3370_, v_f_3371_, v_body_3372_, v_x_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
    leanh::lean_dec(v___y_3378_);
    leanh::lean_dec_ref(v___y_3377_);
    leanh::lean_dec(v___y_3376_);
    leanh::lean_dec_ref(v___y_3375_);
    leanh::lean_dec(v___y_3374_);
    return v_res_3380_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(
    mut v_f_3381_: *mut leanh::LeanObject,
    mut v_fvars_3382_: *mut leanh::LeanObject,
    mut v_a_3383_: *mut leanh::LeanObject,
    mut v___y_3384_: *mut leanh::LeanObject,
    mut v___y_3385_: *mut leanh::LeanObject,
    mut v___y_3386_: *mut leanh::LeanObject,
    mut v___y_3387_: *mut leanh::LeanObject,
    mut v___y_3388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_3383_) == 8 {
        let mut v_declName_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_d_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_declName_3390_ = leanh::lean_ctor_get(v_a_3383_, 0);
        leanh::lean_inc(v_declName_3390_);
        v_type_3391_ = leanh::lean_ctor_get(v_a_3383_, 1);
        leanh::lean_inc_ref(v_type_3391_);
        v_value_3392_ = leanh::lean_ctor_get(v_a_3383_, 2);
        leanh::lean_inc_ref(v_value_3392_);
        v_body_3393_ = leanh::lean_ctor_get(v_a_3383_, 3);
        leanh::lean_inc_ref(v_body_3393_);
        leanh::lean_dec_ref_known(v_a_3383_, 4);
        v_d_3394_ = lean_expr_instantiate_rev(v_type_3391_, v_fvars_3382_);
        leanh::lean_dec_ref(v_type_3391_);
        leanh::lean_inc_ref(v_f_3381_);
        leanh::lean_inc(v___y_3388_);
        leanh::lean_inc_ref(v___y_3387_);
        leanh::lean_inc(v___y_3386_);
        leanh::lean_inc_ref(v___y_3385_);
        leanh::lean_inc(v___y_3384_);
        leanh::lean_inc_ref(v_d_3394_);
        v___x_3395_ = leanh::lean_apply_7(
            v_f_3381_,
            v_d_3394_,
            v___y_3384_,
            v___y_3385_,
            v___y_3386_,
            v___y_3387_,
            v___y_3388_,
            leanh::lean_box(0),
        );
        if leanh::lean_obj_tag(v___x_3395_) == 0 {
            let mut v_v_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_3395_, 1);
            v_v_3396_ = lean_expr_instantiate_rev(v_value_3392_, v_fvars_3382_);
            leanh::lean_dec_ref(v_value_3392_);
            leanh::lean_inc_ref(v_f_3381_);
            leanh::lean_inc(v___y_3388_);
            leanh::lean_inc_ref(v___y_3387_);
            leanh::lean_inc(v___y_3386_);
            leanh::lean_inc_ref(v___y_3385_);
            leanh::lean_inc(v___y_3384_);
            leanh::lean_inc_ref(v_v_3396_);
            v___x_3397_ = leanh::lean_apply_7(
                v_f_3381_,
                v_v_3396_,
                v___y_3384_,
                v___y_3385_,
                v___y_3386_,
                v___y_3387_,
                v___y_3388_,
                leanh::lean_box(0),
            );
            if leanh::lean_obj_tag(v___x_3397_) == 0 {
                let mut v___f_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3399_: u8 = 0;
                let mut v___x_3400_: u8 = 0;
                let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_3397_, 1);
                v___f_3398_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                leanh::lean_closure_set(v___f_3398_, 0, v_fvars_3382_);
                leanh::lean_closure_set(v___f_3398_, 1, v_f_3381_);
                leanh::lean_closure_set(v___f_3398_, 2, v_body_3393_);
                v___x_3399_ = 0;
                v___x_3400_ = 0;
                v___x_3401_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_declName_3390_, v_d_3394_, v_v_3396_, v___f_3398_, v___x_3399_, v___x_3400_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
                return v___x_3401_;
            } else {
                leanh::lean_dec_ref(v_v_3396_);
                leanh::lean_dec_ref(v_d_3394_);
                leanh::lean_dec_ref(v_body_3393_);
                leanh::lean_dec(v_declName_3390_);
                leanh::lean_dec_ref(v_fvars_3382_);
                leanh::lean_dec_ref(v_f_3381_);
                return v___x_3397_;
            }
        } else {
            leanh::lean_dec_ref(v_d_3394_);
            leanh::lean_dec_ref(v_body_3393_);
            leanh::lean_dec_ref(v_value_3392_);
            leanh::lean_dec(v_declName_3390_);
            leanh::lean_dec_ref(v_fvars_3382_);
            leanh::lean_dec_ref(v_f_3381_);
            return v___x_3395_;
        }
    } else {
        let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3402_ = lean_expr_instantiate_rev(v_a_3383_, v_fvars_3382_);
        leanh::lean_dec_ref(v_fvars_3382_);
        leanh::lean_dec_ref(v_a_3383_);
        leanh::lean_inc(v___y_3388_);
        leanh::lean_inc_ref(v___y_3387_);
        leanh::lean_inc(v___y_3386_);
        leanh::lean_inc_ref(v___y_3385_);
        leanh::lean_inc(v___y_3384_);
        v___x_3403_ = leanh::lean_apply_7(
            v_f_3381_,
            v___x_3402_,
            v___y_3384_,
            v___y_3385_,
            v___y_3386_,
            v___y_3387_,
            v___y_3388_,
            leanh::lean_box(0),
        );
        return v___x_3403_;
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(
    mut v_fvars_3404_: *mut leanh::LeanObject,
    mut v_f_3405_: *mut leanh::LeanObject,
    mut v_body_3406_: *mut leanh::LeanObject,
    mut v_x_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
    mut v___y_3412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = lean_array_push(v_fvars_3404_, v_x_3407_);
    v___x_3415_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_3405_, v___x_3414_, v_body_3406_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
    return v___x_3415_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___boxed(
    mut v_f_3416_: *mut leanh::LeanObject,
    mut v_fvars_3417_: *mut leanh::LeanObject,
    mut v_a_3418_: *mut leanh::LeanObject,
    mut v___y_3419_: *mut leanh::LeanObject,
    mut v___y_3420_: *mut leanh::LeanObject,
    mut v___y_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3425_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_3416_, v_fvars_3417_, v_a_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
    leanh::lean_dec(v___y_3423_);
    leanh::lean_dec_ref(v___y_3422_);
    leanh::lean_dec(v___y_3421_);
    leanh::lean_dec_ref(v___y_3420_);
    leanh::lean_dec(v___y_3419_);
    return v_res_3425_;
}
pub unsafe fn l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(
    mut v_f_3426_: *mut leanh::LeanObject,
    mut v_e_3427_: *mut leanh::LeanObject,
    mut v___y_3428_: *mut leanh::LeanObject,
    mut v___y_3429_: *mut leanh::LeanObject,
    mut v___y_3430_: *mut leanh::LeanObject,
    mut v___y_3431_: *mut leanh::LeanObject,
    mut v___y_3432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ = l_Lean_Meta_visitLambda___redArg___closed__0;
    v___x_3435_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_3426_, v___x_3434_, v_e_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
    return v___x_3435_;
}
pub unsafe fn l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11___boxed(
    mut v_f_3436_: *mut leanh::LeanObject,
    mut v_e_3437_: *mut leanh::LeanObject,
    mut v___y_3438_: *mut leanh::LeanObject,
    mut v___y_3439_: *mut leanh::LeanObject,
    mut v___y_3440_: *mut leanh::LeanObject,
    mut v___y_3441_: *mut leanh::LeanObject,
    mut v___y_3442_: *mut leanh::LeanObject,
    mut v___y_3443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3444_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v_f_3436_, v_e_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
    leanh::lean_dec(v___y_3442_);
    leanh::lean_dec_ref(v___y_3441_);
    leanh::lean_dec(v___y_3440_);
    leanh::lean_dec_ref(v___y_3439_);
    leanh::lean_dec(v___y_3438_);
    return v_res_3444_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed(
    mut v_fn_3445_: *mut leanh::LeanObject,
    mut v___y_3446_: *mut leanh::LeanObject,
    mut v___y_3447_: *mut leanh::LeanObject,
    mut v___y_3448_: *mut leanh::LeanObject,
    mut v___y_3449_: *mut leanh::LeanObject,
    mut v___y_3450_: *mut leanh::LeanObject,
    mut v___y_3451_: *mut leanh::LeanObject,
    mut v___y_3452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3453_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(v_fn_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
    leanh::lean_dec(v___y_3451_);
    leanh::lean_dec_ref(v___y_3450_);
    leanh::lean_dec(v___y_3449_);
    leanh::lean_dec_ref(v___y_3448_);
    leanh::lean_dec(v___y_3447_);
    return v_res_3453_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(
    mut v_fn_3454_: *mut leanh::LeanObject,
    mut v_e_3455_: *mut leanh::LeanObject,
    mut v_a_3456_: *mut leanh::LeanObject,
    mut v___y_3457_: *mut leanh::LeanObject,
    mut v___y_3458_: *mut leanh::LeanObject,
    mut v___y_3459_: *mut leanh::LeanObject,
    mut v___y_3460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3468_: u8 = 0;
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3472_: u8 = 0;
    let mut v_unused_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3482_: u8 = 0;
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: u8 = 0;
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3506_: u8 = 0;
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3510_: u8 = 0;
    let mut v_val_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3515_: u8 = 0;
    let mut v_a_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3519_: u8 = 0;
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_3456_);
                v___x_3477_ = leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_3477_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3477_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_3477_, 2, v_a_3456_);
                v___x_3478_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(leanh::lean_box(0), v___x_3477_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
                if leanh::lean_obj_tag(v___x_3478_) == 0 {
                    v_a_3479_ = leanh::lean_ctor_get(v___x_3478_, 0);
                    v_isSharedCheck_3515_ = (!leanh::lean_is_exclusive(v___x_3478_)) as u8;
                    if v_isSharedCheck_3515_ == 0 {
                        v___x_3481_ = v___x_3478_;
                        v_isShared_3482_ = v_isSharedCheck_3515_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3479_);
                        leanh::lean_dec(v___x_3478_);
                        v___x_3481_ = leanh::lean_box(0);
                        v_isShared_3482_ = v_isSharedCheck_3515_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3455_);
                    leanh::lean_dec_ref(v_fn_3454_);
                    v_a_3516_ = leanh::lean_ctor_get(v___x_3478_, 0);
                    v_isSharedCheck_3523_ = (!leanh::lean_is_exclusive(v___x_3478_)) as u8;
                    if v_isSharedCheck_3523_ == 0 {
                        v___x_3518_ = v___x_3478_;
                        v_isShared_3519_ = v_isSharedCheck_3523_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3516_);
                        leanh::lean_dec(v___x_3478_);
                        v___x_3518_ = leanh::lean_box(0);
                        v_isShared_3519_ = v_isSharedCheck_3523_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_3456_);
                v___f_3464_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                leanh::lean_closure_set(v___f_3464_, 0, v_a_3456_);
                leanh::lean_closure_set(v___f_3464_, 1, v_e_3455_);
                leanh::lean_closure_set(v___f_3464_, 2, v_a_3463_);
                v___x_3465_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(leanh::lean_box(0), v___f_3464_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
                if leanh::lean_obj_tag(v___x_3465_) == 0 {
                    v_isSharedCheck_3472_ = (!leanh::lean_is_exclusive(v___x_3465_)) as u8;
                    if v_isSharedCheck_3472_ == 0 {
                        v_unused_3473_ = leanh::lean_ctor_get(v___x_3465_, 0);
                        leanh::lean_dec(v_unused_3473_);
                        v___x_3467_ = v___x_3465_;
                        v_isShared_3468_ = v_isSharedCheck_3472_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3465_);
                        v___x_3467_ = leanh::lean_box(0);
                        v_isShared_3468_ = v_isSharedCheck_3472_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_3465_;
                }
            }
            2 => {
                if v_isShared_3468_ == 0 {
                    leanh::lean_ctor_set(v___x_3467_, 0, v_a_3463_);
                    v___x_3470_ = v___x_3467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3471_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3463_);
                    v___x_3470_ = v_reuseFailAlloc_3471_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3470_;
            }
            4 => {
                if leanh::lean_obj_tag(v___y_3475_) == 0 {
                    v_a_3476_ = leanh::lean_ctor_get(v___y_3475_, 0);
                    leanh::lean_inc(v_a_3476_);
                    leanh::lean_dec_ref_known(v___y_3475_, 1);
                    v_a_3463_ = v_a_3476_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_3455_);
                    return v___y_3475_;
                }
            }
            5 => {
                v___x_3483_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_a_3479_, v_e_3455_);
                leanh::lean_dec(v_a_3479_);
                if leanh::lean_obj_tag(v___x_3483_) == 0 {
                    leanh::lean_del_object(v___x_3481_);
                    leanh::lean_inc_ref(v_fn_3454_);
                    leanh::lean_inc(v___y_3460_);
                    leanh::lean_inc_ref(v___y_3459_);
                    leanh::lean_inc(v___y_3458_);
                    leanh::lean_inc_ref(v___y_3457_);
                    leanh::lean_inc_ref(v_e_3455_);
                    v___x_3484_ = leanh::lean_apply_6(
                        v_fn_3454_,
                        v_e_3455_,
                        v___y_3457_,
                        v___y_3458_,
                        v___y_3459_,
                        v___y_3460_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3484_) == 0 {
                        v_a_3485_ = leanh::lean_ctor_get(v___x_3484_, 0);
                        leanh::lean_inc(v_a_3485_);
                        leanh::lean_dec_ref_known(v___x_3484_, 1);
                        v___x_3486_ = (leanh::lean_unbox(v_a_3485_) as u8);
                        leanh::lean_dec(v_a_3485_);
                        if v___x_3486_ == 0 {
                            leanh::lean_dec_ref(v_fn_3454_);
                            v___x_3487_ = leanh::lean_box(0);
                            v_a_3463_ = v___x_3487_;
                            state = 1;
                            continue;
                        } else {
                            match leanh::lean_obj_tag(v_e_3455_) {
                                7 => {
                                    v___f_3488_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed as *mut core::ffi::c_void, 8, 1);
                                    leanh::lean_closure_set(v___f_3488_, 0, v_fn_3454_);
                                    leanh::lean_inc_ref(v_e_3455_);
                                    v___x_3489_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v___f_3488_, v_e_3455_, v_a_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
                                    v___y_3475_ = v___x_3489_;
                                    state = 4;
                                    continue;
                                }
                                6 => {
                                    v___f_3490_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed as *mut core::ffi::c_void, 8, 1);
                                    leanh::lean_closure_set(v___f_3490_, 0, v_fn_3454_);
                                    leanh::lean_inc_ref(v_e_3455_);
                                    v___x_3491_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v___f_3490_, v_e_3455_, v_a_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
                                    v___y_3475_ = v___x_3491_;
                                    state = 4;
                                    continue;
                                }
                                8 => {
                                    v___f_3492_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed as *mut core::ffi::c_void, 8, 1);
                                    leanh::lean_closure_set(v___f_3492_, 0, v_fn_3454_);
                                    leanh::lean_inc_ref(v_e_3455_);
                                    v___x_3493_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v___f_3492_, v_e_3455_, v_a_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
                                    v___y_3475_ = v___x_3493_;
                                    state = 4;
                                    continue;
                                }
                                5 => {
                                    v_fn_3494_ = leanh::lean_ctor_get(v_e_3455_, 0);
                                    v_arg_3495_ = leanh::lean_ctor_get(v_e_3455_, 1);
                                    leanh::lean_inc_ref(v_fn_3494_);
                                    leanh::lean_inc_ref(v_fn_3454_);
                                    v___x_3496_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_3454_, v_fn_3494_, v_a_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
                                    if leanh::lean_obj_tag(v___x_3496_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_3496_, 1);
                                        leanh::lean_inc_ref(v_arg_3495_);
                                        v___x_3497_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_3454_, v_arg_3495_, v_a_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
                                        v___y_3475_ = v___x_3497_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref(v_fn_3454_);
                                        v___y_3475_ = v___x_3496_;
                                        state = 4;
                                        continue;
                                    }
                                }
                                10 => {
                                    v_expr_3498_ = leanh::lean_ctor_get(v_e_3455_, 1);
                                    leanh::lean_inc_ref(v_expr_3498_);
                                    v___x_3499_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_3454_, v_expr_3498_, v_a_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
                                    v___y_3475_ = v___x_3499_;
                                    state = 4;
                                    continue;
                                }
                                11 => {
                                    v_struct_3500_ = leanh::lean_ctor_get(v_e_3455_, 2);
                                    leanh::lean_inc_ref(v_struct_3500_);
                                    v___x_3501_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_3454_, v_struct_3500_, v_a_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
                                    v___y_3475_ = v___x_3501_;
                                    state = 4;
                                    continue;
                                }
                                _ => {
                                    leanh::lean_dec_ref(v_fn_3454_);
                                    v___x_3502_ = leanh::lean_box(0);
                                    v_a_3463_ = v___x_3502_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_3455_);
                        leanh::lean_dec_ref(v_fn_3454_);
                        v_a_3503_ = leanh::lean_ctor_get(v___x_3484_, 0);
                        v_isSharedCheck_3510_ =
                            (!leanh::lean_is_exclusive(v___x_3484_)) as u8;
                        if v_isSharedCheck_3510_ == 0 {
                            v___x_3505_ = v___x_3484_;
                            v_isShared_3506_ = v_isSharedCheck_3510_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3503_);
                            leanh::lean_dec(v___x_3484_);
                            v___x_3505_ = leanh::lean_box(0);
                            v_isShared_3506_ = v_isSharedCheck_3510_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3455_);
                    leanh::lean_dec_ref(v_fn_3454_);
                    v_val_3511_ = leanh::lean_ctor_get(v___x_3483_, 0);
                    leanh::lean_inc(v_val_3511_);
                    leanh::lean_dec_ref_known(v___x_3483_, 1);
                    if v_isShared_3482_ == 0 {
                        leanh::lean_ctor_set(v___x_3481_, 0, v_val_3511_);
                        v___x_3513_ = v___x_3481_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3514_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_val_3511_);
                        v___x_3513_ = v_reuseFailAlloc_3514_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3506_ == 0 {
                    v___x_3508_ = v___x_3505_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3509_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
                    v___x_3508_ = v_reuseFailAlloc_3509_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3508_;
            }
            8 => {
                return v___x_3513_;
            }
            9 => {
                if v_isShared_3519_ == 0 {
                    v___x_3521_ = v___x_3518_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3522_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
                    v___x_3521_ = v_reuseFailAlloc_3522_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(
    mut v_fn_3524_: *mut leanh::LeanObject,
    mut v___y_3525_: *mut leanh::LeanObject,
    mut v___y_3526_: *mut leanh::LeanObject,
    mut v___y_3527_: *mut leanh::LeanObject,
    mut v___y_3528_: *mut leanh::LeanObject,
    mut v___y_3529_: *mut leanh::LeanObject,
    mut v___y_3530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3532_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
    return v___x_3532_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___boxed(
    mut v_fn_3533_: *mut leanh::LeanObject,
    mut v_e_3534_: *mut leanh::LeanObject,
    mut v_a_3535_: *mut leanh::LeanObject,
    mut v___y_3536_: *mut leanh::LeanObject,
    mut v___y_3537_: *mut leanh::LeanObject,
    mut v___y_3538_: *mut leanh::LeanObject,
    mut v___y_3539_: *mut leanh::LeanObject,
    mut v___y_3540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3541_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_3533_, v_e_3534_, v_a_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
    leanh::lean_dec(v___y_3539_);
    leanh::lean_dec_ref(v___y_3538_);
    leanh::lean_dec(v___y_3537_);
    leanh::lean_dec_ref(v___y_3536_);
    leanh::lean_dec(v_a_3535_);
    return v_res_3541_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(
    mut v_00_u03b1_3542_: *mut leanh::LeanObject,
    mut v_x_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
    mut v___y_3545_: *mut leanh::LeanObject,
    mut v___y_3546_: *mut leanh::LeanObject,
    mut v___y_3547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3549_ = leanh::lean_apply_1(v_x_3543_, leanh::lean_box(0));
    v___x_3550_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3550_, 0, v___x_3549_);
    return v___x_3550_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0___boxed(
    mut v_00_u03b1_3551_: *mut leanh::LeanObject,
    mut v_x_3552_: *mut leanh::LeanObject,
    mut v___y_3553_: *mut leanh::LeanObject,
    mut v___y_3554_: *mut leanh::LeanObject,
    mut v___y_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3558_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(v_00_u03b1_3551_, v_x_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
    leanh::lean_dec(v___y_3556_);
    leanh::lean_dec_ref(v___y_3555_);
    leanh::lean_dec(v___y_3554_);
    leanh::lean_dec_ref(v___y_3553_);
    return v_res_3558_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(
    mut v_input_3559_: *mut leanh::LeanObject,
    mut v_fn_3560_: *mut leanh::LeanObject,
    mut v___y_3561_: *mut leanh::LeanObject,
    mut v___y_3562_: *mut leanh::LeanObject,
    mut v___y_3563_: *mut leanh::LeanObject,
    mut v___y_3564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3575_: u8 = 0;
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3579_: u8 = 0;
    let mut v_unused_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3566_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once),
                    _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2,
                );
                v___x_3567_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(leanh::lean_box(0), v___x_3566_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
                v_a_3568_ = leanh::lean_ctor_get(v___x_3567_, 0);
                leanh::lean_inc(v_a_3568_);
                leanh::lean_dec_ref(v___x_3567_);
                v___x_3569_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_3560_, v_input_3559_, v_a_3568_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
                if leanh::lean_obj_tag(v___x_3569_) == 0 {
                    v_a_3570_ = leanh::lean_ctor_get(v___x_3569_, 0);
                    leanh::lean_inc(v_a_3570_);
                    leanh::lean_dec_ref_known(v___x_3569_, 1);
                    v___x_3571_ = leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___x_3571_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_3571_, 1, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_3571_, 2, v_a_3568_);
                    v___x_3572_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(leanh::lean_box(0), v___x_3571_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
                    v_isSharedCheck_3579_ = (!leanh::lean_is_exclusive(v___x_3572_)) as u8;
                    if v_isSharedCheck_3579_ == 0 {
                        v_unused_3580_ = leanh::lean_ctor_get(v___x_3572_, 0);
                        leanh::lean_dec(v_unused_3580_);
                        v___x_3574_ = v___x_3572_;
                        v_isShared_3575_ = v_isSharedCheck_3579_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3572_);
                        v___x_3574_ = leanh::lean_box(0);
                        v_isShared_3575_ = v_isSharedCheck_3579_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3568_);
                    return v___x_3569_;
                }
            }
            1 => {
                if v_isShared_3575_ == 0 {
                    leanh::lean_ctor_set(v___x_3574_, 0, v_a_3570_);
                    v___x_3577_ = v___x_3574_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3578_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3570_);
                    v___x_3577_ = v_reuseFailAlloc_3578_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3577_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___boxed(
    mut v_input_3581_: *mut leanh::LeanObject,
    mut v_fn_3582_: *mut leanh::LeanObject,
    mut v___y_3583_: *mut leanh::LeanObject,
    mut v___y_3584_: *mut leanh::LeanObject,
    mut v___y_3585_: *mut leanh::LeanObject,
    mut v___y_3586_: *mut leanh::LeanObject,
    mut v___y_3587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3588_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_input_3581_, v_fn_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
    leanh::lean_dec(v___y_3586_);
    leanh::lean_dec_ref(v___y_3585_);
    leanh::lean_dec(v___y_3584_);
    leanh::lean_dec_ref(v___y_3583_);
    return v_res_3588_;
}
pub unsafe fn l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(
    mut v_f_3589_: *mut leanh::LeanObject,
    mut v_e_3590_: *mut leanh::LeanObject,
    mut v___y_3591_: *mut leanh::LeanObject,
    mut v___y_3592_: *mut leanh::LeanObject,
    mut v___y_3593_: *mut leanh::LeanObject,
    mut v___y_3594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3599_: u8 = 0;
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3605_: u8 = 0;
    let mut v_unused_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3594_);
                leanh::lean_inc_ref(v___y_3593_);
                leanh::lean_inc(v___y_3592_);
                leanh::lean_inc_ref(v___y_3591_);
                v___x_3596_ = leanh::lean_apply_6(
                    v_f_3589_,
                    v_e_3590_,
                    v___y_3591_,
                    v___y_3592_,
                    v___y_3593_,
                    v___y_3594_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3596_) == 0 {
                    v_isSharedCheck_3605_ = (!leanh::lean_is_exclusive(v___x_3596_)) as u8;
                    if v_isSharedCheck_3605_ == 0 {
                        v_unused_3606_ = leanh::lean_ctor_get(v___x_3596_, 0);
                        leanh::lean_dec(v_unused_3606_);
                        v___x_3598_ = v___x_3596_;
                        v_isShared_3599_ = v_isSharedCheck_3605_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3596_);
                        v___x_3598_ = leanh::lean_box(0);
                        v_isShared_3599_ = v_isSharedCheck_3605_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3607_ = leanh::lean_ctor_get(v___x_3596_, 0);
                    v_isSharedCheck_3614_ = (!leanh::lean_is_exclusive(v___x_3596_)) as u8;
                    if v_isSharedCheck_3614_ == 0 {
                        v___x_3609_ = v___x_3596_;
                        v_isShared_3610_ = v_isSharedCheck_3614_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3607_);
                        leanh::lean_dec(v___x_3596_);
                        v___x_3609_ = leanh::lean_box(0);
                        v_isShared_3610_ = v_isSharedCheck_3614_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3600_ = 1;
                v___x_3601_ = leanh::lean_box((v___x_3600_) as usize);
                if v_isShared_3599_ == 0 {
                    leanh::lean_ctor_set(v___x_3598_, 0, v___x_3601_);
                    v___x_3603_ = v___x_3598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3604_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
                    v___x_3603_ = v_reuseFailAlloc_3604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3603_;
            }
            3 => {
                if v_isShared_3610_ == 0 {
                    v___x_3612_ = v___x_3609_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3613_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
                    v___x_3612_ = v_reuseFailAlloc_3613_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed(
    mut v_f_3615_: *mut leanh::LeanObject,
    mut v_e_3616_: *mut leanh::LeanObject,
    mut v___y_3617_: *mut leanh::LeanObject,
    mut v___y_3618_: *mut leanh::LeanObject,
    mut v___y_3619_: *mut leanh::LeanObject,
    mut v___y_3620_: *mut leanh::LeanObject,
    mut v___y_3621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3622_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(
        v_f_3615_,
        v_e_3616_,
        v___y_3617_,
        v___y_3618_,
        v___y_3619_,
        v___y_3620_,
    );
    leanh::lean_dec(v___y_3620_);
    leanh::lean_dec_ref(v___y_3619_);
    leanh::lean_dec(v___y_3618_);
    leanh::lean_dec_ref(v___y_3617_);
    return v_res_3622_;
}
pub unsafe fn l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(
    mut v_e_3623_: *mut leanh::LeanObject,
    mut v_f_3624_: *mut leanh::LeanObject,
    mut v___y_3625_: *mut leanh::LeanObject,
    mut v___y_3626_: *mut leanh::LeanObject,
    mut v___y_3627_: *mut leanh::LeanObject,
    mut v___y_3628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3630_ = leanh::lean_alloc_closure(
        l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v___f_3630_, 0, v_f_3624_);
    v___x_3631_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_e_3623_, v___f_3630_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
    return v___x_3631_;
}
pub unsafe fn l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___boxed(
    mut v_e_3632_: *mut leanh::LeanObject,
    mut v_f_3633_: *mut leanh::LeanObject,
    mut v___y_3634_: *mut leanh::LeanObject,
    mut v___y_3635_: *mut leanh::LeanObject,
    mut v___y_3636_: *mut leanh::LeanObject,
    mut v___y_3637_: *mut leanh::LeanObject,
    mut v___y_3638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3639_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(
        v_e_3632_,
        v_f_3633_,
        v___y_3634_,
        v___y_3635_,
        v___y_3636_,
        v___y_3637_,
    );
    leanh::lean_dec(v___y_3637_);
    leanh::lean_dec_ref(v___y_3636_);
    leanh::lean_dec(v___y_3635_);
    leanh::lean_dec_ref(v___y_3634_);
    return v_res_3639_;
}
pub unsafe fn l_Lean_Meta_setMVarUserNamesAt(
    mut v_e_3642_: *mut leanh::LeanObject,
    mut v_isTarget_3643_: *mut leanh::LeanObject,
    mut v_a_3644_: *mut leanh::LeanObject,
    mut v_a_3645_: *mut leanh::LeanObject,
    mut v_a_3646_: *mut leanh::LeanObject,
    mut v_a_3647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3658_: u8 = 0;
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v_unused_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3668_: u8 = 0;
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3649_ = leanh::lean_unsigned_to_nat(0);
                v___x_3650_ = l_Lean_Meta_setMVarUserNamesAt___closed__0;
                v___x_3651_ = lean_st_mk_ref(v___x_3650_);
                v___x_3652_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(
                        v_e_3642_, v_a_3645_,
                    );
                v_a_3653_ = leanh::lean_ctor_get(v___x_3652_, 0);
                leanh::lean_inc(v_a_3653_);
                leanh::lean_dec_ref(v___x_3652_);
                leanh::lean_inc(v___x_3651_);
                v___f_3654_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    3,
                );
                leanh::lean_closure_set(v___f_3654_, 0, v___x_3651_);
                leanh::lean_closure_set(v___f_3654_, 1, v_isTarget_3643_);
                leanh::lean_closure_set(v___f_3654_, 2, v___x_3649_);
                v___x_3655_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(
                    v_a_3653_,
                    v___f_3654_,
                    v_a_3644_,
                    v_a_3645_,
                    v_a_3646_,
                    v_a_3647_,
                );
                if leanh::lean_obj_tag(v___x_3655_) == 0 {
                    v_isSharedCheck_3663_ = (!leanh::lean_is_exclusive(v___x_3655_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v_unused_3664_ = leanh::lean_ctor_get(v___x_3655_, 0);
                        leanh::lean_dec(v_unused_3664_);
                        v___x_3657_ = v___x_3655_;
                        v_isShared_3658_ = v_isSharedCheck_3663_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3655_);
                        v___x_3657_ = leanh::lean_box(0);
                        v_isShared_3658_ = v_isSharedCheck_3663_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3651_);
                    v_a_3665_ = leanh::lean_ctor_get(v___x_3655_, 0);
                    v_isSharedCheck_3672_ = (!leanh::lean_is_exclusive(v___x_3655_)) as u8;
                    if v_isSharedCheck_3672_ == 0 {
                        v___x_3667_ = v___x_3655_;
                        v_isShared_3668_ = v_isSharedCheck_3672_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3665_);
                        leanh::lean_dec(v___x_3655_);
                        v___x_3667_ = leanh::lean_box(0);
                        v_isShared_3668_ = v_isSharedCheck_3672_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3659_ = lean_st_ref_get(v___x_3651_);
                leanh::lean_dec(v___x_3651_);
                if v_isShared_3658_ == 0 {
                    leanh::lean_ctor_set(v___x_3657_, 0, v___x_3659_);
                    v___x_3661_ = v___x_3657_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3662_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
                    v___x_3661_ = v_reuseFailAlloc_3662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3661_;
            }
            3 => {
                if v_isShared_3668_ == 0 {
                    v___x_3670_ = v___x_3667_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3671_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
                    v___x_3670_ = v_reuseFailAlloc_3671_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_setMVarUserNamesAt___boxed(
    mut v_e_3673_: *mut leanh::LeanObject,
    mut v_isTarget_3674_: *mut leanh::LeanObject,
    mut v_a_3675_: *mut leanh::LeanObject,
    mut v_a_3676_: *mut leanh::LeanObject,
    mut v_a_3677_: *mut leanh::LeanObject,
    mut v_a_3678_: *mut leanh::LeanObject,
    mut v_a_3679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3680_ = l_Lean_Meta_setMVarUserNamesAt(
        v_e_3673_,
        v_isTarget_3674_,
        v_a_3675_,
        v_a_3676_,
        v_a_3677_,
        v_a_3678_,
    );
    leanh::lean_dec(v_a_3678_);
    leanh::lean_dec_ref(v_a_3677_);
    leanh::lean_dec(v_a_3676_);
    leanh::lean_dec_ref(v_a_3675_);
    return v_res_3680_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(
    mut v_upperBound_3681_: *mut leanh::LeanObject,
    mut v___x_3682_: *mut leanh::LeanObject,
    mut v_val_3683_: *mut leanh::LeanObject,
    mut v_e_3684_: *mut leanh::LeanObject,
    mut v_isTarget_3685_: *mut leanh::LeanObject,
    mut v_inst_3686_: *mut leanh::LeanObject,
    mut v_R_3687_: *mut leanh::LeanObject,
    mut v_a_3688_: *mut leanh::LeanObject,
    mut v_b_3689_: *mut leanh::LeanObject,
    mut v_c_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
    mut v___y_3693_: *mut leanh::LeanObject,
    mut v___y_3694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3696_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(
            v_upperBound_3681_,
            v___x_3682_,
            v_val_3683_,
            v_e_3684_,
            v_isTarget_3685_,
            v_a_3688_,
            v_b_3689_,
            v___y_3691_,
            v___y_3692_,
            v___y_3693_,
            v___y_3694_,
        );
    return v___x_3696_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___boxed(
    mut v_upperBound_3697_: *mut leanh::LeanObject,
    mut v___x_3698_: *mut leanh::LeanObject,
    mut v_val_3699_: *mut leanh::LeanObject,
    mut v_e_3700_: *mut leanh::LeanObject,
    mut v_isTarget_3701_: *mut leanh::LeanObject,
    mut v_inst_3702_: *mut leanh::LeanObject,
    mut v_R_3703_: *mut leanh::LeanObject,
    mut v_a_3704_: *mut leanh::LeanObject,
    mut v_b_3705_: *mut leanh::LeanObject,
    mut v_c_3706_: *mut leanh::LeanObject,
    mut v___y_3707_: *mut leanh::LeanObject,
    mut v___y_3708_: *mut leanh::LeanObject,
    mut v___y_3709_: *mut leanh::LeanObject,
    mut v___y_3710_: *mut leanh::LeanObject,
    mut v___y_3711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3712_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(
        v_upperBound_3697_,
        v___x_3698_,
        v_val_3699_,
        v_e_3700_,
        v_isTarget_3701_,
        v_inst_3702_,
        v_R_3703_,
        v_a_3704_,
        v_b_3705_,
        v_c_3706_,
        v___y_3707_,
        v___y_3708_,
        v___y_3709_,
        v___y_3710_,
    );
    leanh::lean_dec(v___y_3710_);
    leanh::lean_dec_ref(v___y_3709_);
    leanh::lean_dec(v___y_3708_);
    leanh::lean_dec_ref(v___y_3707_);
    leanh::lean_dec_ref(v_isTarget_3701_);
    leanh::lean_dec_ref(v_e_3700_);
    leanh::lean_dec_ref(v___x_3698_);
    leanh::lean_dec(v_upperBound_3697_);
    return v_res_3712_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(
    mut v_00_u03b2_3713_: *mut leanh::LeanObject,
    mut v_m_3714_: *mut leanh::LeanObject,
    mut v_a_3715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_3714_, v_a_3715_);
    return v___x_3716_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___boxed(
    mut v_00_u03b2_3717_: *mut leanh::LeanObject,
    mut v_m_3718_: *mut leanh::LeanObject,
    mut v_a_3719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(v_00_u03b2_3717_, v_m_3718_, v_a_3719_);
    leanh::lean_dec_ref(v_a_3719_);
    leanh::lean_dec_ref(v_m_3718_);
    return v_res_3720_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8(
    mut v_00_u03b2_3721_: *mut leanh::LeanObject,
    mut v_m_3722_: *mut leanh::LeanObject,
    mut v_a_3723_: *mut leanh::LeanObject,
    mut v_b_3724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3725_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v_m_3722_, v_a_3723_, v_b_3724_);
    return v___x_3725_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(
    mut v_00_u03b2_3726_: *mut leanh::LeanObject,
    mut v_a_3727_: *mut leanh::LeanObject,
    mut v_x_3728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3729_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_3727_, v_x_3728_);
    return v___x_3729_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___boxed(
    mut v_00_u03b2_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
    mut v_x_3732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3733_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(v_00_u03b2_3730_, v_a_3731_, v_x_3732_);
    leanh::lean_dec(v_x_3732_);
    leanh::lean_dec_ref(v_a_3731_);
    return v_res_3733_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(
    mut v_00_u03b2_3734_: *mut leanh::LeanObject,
    mut v_a_3735_: *mut leanh::LeanObject,
    mut v_x_3736_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3737_: u8 = 0;
    v___x_3737_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_3735_, v_x_3736_);
    return v___x_3737_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___boxed(
    mut v_00_u03b2_3738_: *mut leanh::LeanObject,
    mut v_a_3739_: *mut leanh::LeanObject,
    mut v_x_3740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3741_: u8 = 0;
    let mut v_r_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(v_00_u03b2_3738_, v_a_3739_, v_x_3740_);
    leanh::lean_dec(v_x_3740_);
    leanh::lean_dec_ref(v_a_3739_);
    v_r_3742_ = leanh::lean_box((v_res_3741_) as usize);
    return v_r_3742_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11(
    mut v_00_u03b2_3743_: *mut leanh::LeanObject,
    mut v_data_3744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_data_3744_);
    return v___x_3745_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12(
    mut v_00_u03b2_3746_: *mut leanh::LeanObject,
    mut v_a_3747_: *mut leanh::LeanObject,
    mut v_b_3748_: *mut leanh::LeanObject,
    mut v_x_3749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3750_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_3747_, v_b_3748_, v_x_3749_);
    return v___x_3750_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(
    mut v_00_u03b1_3751_: *mut leanh::LeanObject,
    mut v_name_3752_: *mut leanh::LeanObject,
    mut v_bi_3753_: u8,
    mut v_type_3754_: *mut leanh::LeanObject,
    mut v_k_3755_: *mut leanh::LeanObject,
    mut v_kind_3756_: u8,
    mut v___y_3757_: *mut leanh::LeanObject,
    mut v___y_3758_: *mut leanh::LeanObject,
    mut v___y_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
    mut v___y_3761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3763_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_3752_, v_bi_3753_, v_type_3754_, v_k_3755_, v_kind_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
    return v___x_3763_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___boxed(
    mut v_00_u03b1_3764_: *mut leanh::LeanObject,
    mut v_name_3765_: *mut leanh::LeanObject,
    mut v_bi_3766_: *mut leanh::LeanObject,
    mut v_type_3767_: *mut leanh::LeanObject,
    mut v_k_3768_: *mut leanh::LeanObject,
    mut v_kind_3769_: *mut leanh::LeanObject,
    mut v___y_3770_: *mut leanh::LeanObject,
    mut v___y_3771_: *mut leanh::LeanObject,
    mut v___y_3772_: *mut leanh::LeanObject,
    mut v___y_3773_: *mut leanh::LeanObject,
    mut v___y_3774_: *mut leanh::LeanObject,
    mut v___y_3775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3776_: u8 = 0;
    let mut v_kind_boxed_3777_: u8 = 0;
    let mut v_res_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3776_ = (leanh::lean_unbox(v_bi_3766_) as u8);
    v_kind_boxed_3777_ = (leanh::lean_unbox(v_kind_3769_) as u8);
    v_res_3778_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(v_00_u03b1_3764_, v_name_3765_, v_bi_boxed_3776_, v_type_3767_, v_k_3768_, v_kind_boxed_3777_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
    leanh::lean_dec(v___y_3774_);
    leanh::lean_dec_ref(v___y_3773_);
    leanh::lean_dec(v___y_3772_);
    leanh::lean_dec_ref(v___y_3771_);
    leanh::lean_dec(v___y_3770_);
    return v_res_3778_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(
    mut v_00_u03b1_3779_: *mut leanh::LeanObject,
    mut v_name_3780_: *mut leanh::LeanObject,
    mut v_type_3781_: *mut leanh::LeanObject,
    mut v_val_3782_: *mut leanh::LeanObject,
    mut v_k_3783_: *mut leanh::LeanObject,
    mut v_nondep_3784_: u8,
    mut v_kind_3785_: u8,
    mut v___y_3786_: *mut leanh::LeanObject,
    mut v___y_3787_: *mut leanh::LeanObject,
    mut v___y_3788_: *mut leanh::LeanObject,
    mut v___y_3789_: *mut leanh::LeanObject,
    mut v___y_3790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3792_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_3780_, v_type_3781_, v_val_3782_, v_k_3783_, v_nondep_3784_, v_kind_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
    return v___x_3792_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___boxed(
    mut v_00_u03b1_3793_: *mut leanh::LeanObject,
    mut v_name_3794_: *mut leanh::LeanObject,
    mut v_type_3795_: *mut leanh::LeanObject,
    mut v_val_3796_: *mut leanh::LeanObject,
    mut v_k_3797_: *mut leanh::LeanObject,
    mut v_nondep_3798_: *mut leanh::LeanObject,
    mut v_kind_3799_: *mut leanh::LeanObject,
    mut v___y_3800_: *mut leanh::LeanObject,
    mut v___y_3801_: *mut leanh::LeanObject,
    mut v___y_3802_: *mut leanh::LeanObject,
    mut v___y_3803_: *mut leanh::LeanObject,
    mut v___y_3804_: *mut leanh::LeanObject,
    mut v___y_3805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_3806_: u8 = 0;
    let mut v_kind_boxed_3807_: u8 = 0;
    let mut v_res_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3806_ = (leanh::lean_unbox(v_nondep_3798_) as u8);
    v_kind_boxed_3807_ = (leanh::lean_unbox(v_kind_3799_) as u8);
    v_res_3808_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(v_00_u03b1_3793_, v_name_3794_, v_type_3795_, v_val_3796_, v_k_3797_, v_nondep_boxed_3806_, v_kind_boxed_3807_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
    leanh::lean_dec(v___y_3804_);
    leanh::lean_dec_ref(v___y_3803_);
    leanh::lean_dec(v___y_3802_);
    leanh::lean_dec_ref(v___y_3801_);
    leanh::lean_dec(v___y_3800_);
    return v_res_3808_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12(
    mut v_00_u03b2_3809_: *mut leanh::LeanObject,
    mut v_i_3810_: *mut leanh::LeanObject,
    mut v_source_3811_: *mut leanh::LeanObject,
    mut v_target_3812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3813_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v_i_3810_, v_source_3811_, v_target_3812_);
    return v___x_3813_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16(
    mut v_00_u03b2_3814_: *mut leanh::LeanObject,
    mut v_x_3815_: *mut leanh::LeanObject,
    mut v_x_3816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3817_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(v_x_3815_, v_x_3816_);
    return v___x_3817_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(
    mut v_as_3818_: *mut leanh::LeanObject,
    mut v_sz_3819_: usize,
    mut v_i_3820_: usize,
    mut v_b_3821_: *mut leanh::LeanObject,
    mut v___y_3822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3834_: u8 = 0;
    let mut v_a_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: usize = 0;
    let mut v___x_3843_: usize = 0;
    let mut v_reuseFailAlloc_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3824_ = lean_usize_dec_lt(v_i_3820_, v_sz_3819_);
                if v___x_3824_ == 0 {
                    v___x_3825_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3825_, 0, v_b_3821_);
                    return v___x_3825_;
                } else {
                    v___x_3826_ = lean_st_ref_take(v___y_3822_);
                    v_mctx_3827_ = leanh::lean_ctor_get(v___x_3826_, 0);
                    v_cache_3828_ = leanh::lean_ctor_get(v___x_3826_, 1);
                    v_zetaDeltaFVarIds_3829_ = leanh::lean_ctor_get(v___x_3826_, 2);
                    v_postponed_3830_ = leanh::lean_ctor_get(v___x_3826_, 3);
                    v_diag_3831_ = leanh::lean_ctor_get(v___x_3826_, 4);
                    v_isSharedCheck_3846_ = (!leanh::lean_is_exclusive(v___x_3826_)) as u8;
                    if v_isSharedCheck_3846_ == 0 {
                        v___x_3833_ = v___x_3826_;
                        v_isShared_3834_ = v_isSharedCheck_3846_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_3831_);
                        leanh::lean_inc(v_postponed_3830_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_3829_);
                        leanh::lean_inc(v_cache_3828_);
                        leanh::lean_inc(v_mctx_3827_);
                        leanh::lean_dec(v___x_3826_);
                        v___x_3833_ = leanh::lean_box(0);
                        v_isShared_3834_ = v_isSharedCheck_3846_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3835_ = lean_array_uget_borrowed(v_as_3818_, v_i_3820_);
                v___x_3836_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_3835_);
                v___x_3837_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(
                    v_mctx_3827_,
                    v_a_3835_,
                    v___x_3836_,
                );
                if v_isShared_3834_ == 0 {
                    leanh::lean_ctor_set(v___x_3833_, 0, v___x_3837_);
                    v___x_3839_ = v___x_3833_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3845_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3845_, 1, v_cache_3828_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3845_,
                        2,
                        v_zetaDeltaFVarIds_3829_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3845_, 3, v_postponed_3830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3845_, 4, v_diag_3831_);
                    v___x_3839_ = v_reuseFailAlloc_3845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3840_ = lean_st_ref_set(v___y_3822_, v___x_3839_);
                v___x_3841_ = leanh::lean_box(0);
                v___x_3842_ = 1usize;
                v___x_3843_ = lean_usize_add(v_i_3820_, v___x_3842_);
                v_i_3820_ = v___x_3843_;
                v_b_3821_ = v___x_3841_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg___boxed(
    mut v_as_3847_: *mut leanh::LeanObject,
    mut v_sz_3848_: *mut leanh::LeanObject,
    mut v_i_3849_: *mut leanh::LeanObject,
    mut v_b_3850_: *mut leanh::LeanObject,
    mut v___y_3851_: *mut leanh::LeanObject,
    mut v___y_3852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3853_: usize = 0;
    let mut v_i_boxed_3854_: usize = 0;
    let mut v_res_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3853_ = leanh::lean_unbox_usize(v_sz_3848_);
    leanh::lean_dec(v_sz_3848_);
    v_i_boxed_3854_ = leanh::lean_unbox_usize(v_i_3849_);
    leanh::lean_dec(v_i_3849_);
    v_res_3855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_3847_, v_sz_boxed_3853_, v_i_boxed_3854_, v_b_3850_, v___y_3851_);
    leanh::lean_dec(v___y_3851_);
    leanh::lean_dec_ref(v_as_3847_);
    return v_res_3855_;
}
pub unsafe fn l_Lean_Meta_resetMVarUserNames(
    mut v_toReset_3856_: *mut leanh::LeanObject,
    mut v_a_3857_: *mut leanh::LeanObject,
    mut v_a_3858_: *mut leanh::LeanObject,
    mut v_a_3859_: *mut leanh::LeanObject,
    mut v_a_3860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3863_: usize = 0;
    let mut v___x_3864_: usize = 0;
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3868_: u8 = 0;
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3872_: u8 = 0;
    let mut v_unused_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3862_ = leanh::lean_box(0);
                v_sz_3863_ = lean_array_size(v_toReset_3856_);
                v___x_3864_ = 0usize;
                v___x_3865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_toReset_3856_, v_sz_3863_, v___x_3864_, v___x_3862_, v_a_3858_);
                if leanh::lean_obj_tag(v___x_3865_) == 0 {
                    v_isSharedCheck_3872_ = (!leanh::lean_is_exclusive(v___x_3865_)) as u8;
                    if v_isSharedCheck_3872_ == 0 {
                        v_unused_3873_ = leanh::lean_ctor_get(v___x_3865_, 0);
                        leanh::lean_dec(v_unused_3873_);
                        v___x_3867_ = v___x_3865_;
                        v_isShared_3868_ = v_isSharedCheck_3872_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3865_);
                        v___x_3867_ = leanh::lean_box(0);
                        v_isShared_3868_ = v_isSharedCheck_3872_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3865_;
                }
            }
            1 => {
                if v_isShared_3868_ == 0 {
                    leanh::lean_ctor_set(v___x_3867_, 0, v___x_3862_);
                    v___x_3870_ = v___x_3867_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3871_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3862_);
                    v___x_3870_ = v_reuseFailAlloc_3871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3870_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_resetMVarUserNames___boxed(
    mut v_toReset_3874_: *mut leanh::LeanObject,
    mut v_a_3875_: *mut leanh::LeanObject,
    mut v_a_3876_: *mut leanh::LeanObject,
    mut v_a_3877_: *mut leanh::LeanObject,
    mut v_a_3878_: *mut leanh::LeanObject,
    mut v_a_3879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3880_ =
        l_Lean_Meta_resetMVarUserNames(v_toReset_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_);
    leanh::lean_dec(v_a_3878_);
    leanh::lean_dec_ref(v_a_3877_);
    leanh::lean_dec(v_a_3876_);
    leanh::lean_dec_ref(v_a_3875_);
    leanh::lean_dec_ref(v_toReset_3874_);
    return v_res_3880_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(
    mut v_as_3881_: *mut leanh::LeanObject,
    mut v_sz_3882_: usize,
    mut v_i_3883_: usize,
    mut v_b_3884_: *mut leanh::LeanObject,
    mut v___y_3885_: *mut leanh::LeanObject,
    mut v___y_3886_: *mut leanh::LeanObject,
    mut v___y_3887_: *mut leanh::LeanObject,
    mut v___y_3888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_3881_, v_sz_3882_, v_i_3883_, v_b_3884_, v___y_3886_);
    return v___x_3890_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___boxed(
    mut v_as_3891_: *mut leanh::LeanObject,
    mut v_sz_3892_: *mut leanh::LeanObject,
    mut v_i_3893_: *mut leanh::LeanObject,
    mut v_b_3894_: *mut leanh::LeanObject,
    mut v___y_3895_: *mut leanh::LeanObject,
    mut v___y_3896_: *mut leanh::LeanObject,
    mut v___y_3897_: *mut leanh::LeanObject,
    mut v___y_3898_: *mut leanh::LeanObject,
    mut v___y_3899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3900_: usize = 0;
    let mut v_i_boxed_3901_: usize = 0;
    let mut v_res_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3900_ = leanh::lean_unbox_usize(v_sz_3892_);
    leanh::lean_dec(v_sz_3892_);
    v_i_boxed_3901_ = leanh::lean_unbox_usize(v_i_3893_);
    leanh::lean_dec(v_i_3893_);
    v_res_3902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(v_as_3891_, v_sz_boxed_3900_, v_i_boxed_3901_, v_b_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
    leanh::lean_dec(v___y_3898_);
    leanh::lean_dec_ref(v___y_3897_);
    leanh::lean_dec(v___y_3896_);
    leanh::lean_dec_ref(v___y_3895_);
    leanh::lean_dec_ref(v_as_3891_);
    return v_res_3902_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(
    mut v_x_3903_: *mut leanh::LeanObject,
    mut v___y_3904_: *mut leanh::LeanObject,
    mut v___y_3905_: *mut leanh::LeanObject,
    mut v___y_3906_: *mut leanh::LeanObject,
    mut v___y_3907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mvarId_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v_userName_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: u8 = 0;
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3921_: u8 = 0;
    let mut v_a_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3925_: u8 = 0;
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3929_: u8 = 0;
    let mut v___x_3930_: u8 = 0;
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3903_) == 2 {
                    v_mvarId_3909_ = leanh::lean_ctor_get(v_x_3903_, 0);
                    leanh::lean_inc(v_mvarId_3909_);
                    leanh::lean_dec_ref_known(v_x_3903_, 1);
                    v___x_3910_ = l_Lean_MVarId_getDecl(
                        v_mvarId_3909_,
                        v___y_3904_,
                        v___y_3905_,
                        v___y_3906_,
                        v___y_3907_,
                    );
                    if leanh::lean_obj_tag(v___x_3910_) == 0 {
                        v_a_3911_ = leanh::lean_ctor_get(v___x_3910_, 0);
                        v_isSharedCheck_3921_ =
                            (!leanh::lean_is_exclusive(v___x_3910_)) as u8;
                        if v_isSharedCheck_3921_ == 0 {
                            v___x_3913_ = v___x_3910_;
                            v_isShared_3914_ = v_isSharedCheck_3921_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3911_);
                            leanh::lean_dec(v___x_3910_);
                            v___x_3913_ = leanh::lean_box(0);
                            v_isShared_3914_ = v_isSharedCheck_3921_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3922_ = leanh::lean_ctor_get(v___x_3910_, 0);
                        v_isSharedCheck_3929_ =
                            (!leanh::lean_is_exclusive(v___x_3910_)) as u8;
                        if v_isSharedCheck_3929_ == 0 {
                            v___x_3924_ = v___x_3910_;
                            v_isShared_3925_ = v_isSharedCheck_3929_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3922_);
                            leanh::lean_dec(v___x_3910_);
                            v___x_3924_ = leanh::lean_box(0);
                            v_isShared_3925_ = v_isSharedCheck_3929_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_3903_);
                    v___x_3930_ = 0;
                    v___x_3931_ = leanh::lean_box((v___x_3930_) as usize);
                    v___x_3932_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3932_, 0, v___x_3931_);
                    return v___x_3932_;
                }
            }
            1 => {
                v_userName_3915_ = leanh::lean_ctor_get(v_a_3911_, 0);
                leanh::lean_inc(v_userName_3915_);
                leanh::lean_dec(v_a_3911_);
                v___x_3916_ = l_Lean_Name_isAnonymous(v_userName_3915_);
                leanh::lean_dec(v_userName_3915_);
                v___x_3917_ = leanh::lean_box((v___x_3916_) as usize);
                if v_isShared_3914_ == 0 {
                    leanh::lean_ctor_set(v___x_3913_, 0, v___x_3917_);
                    v___x_3919_ = v___x_3913_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3920_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
                    v___x_3919_ = v_reuseFailAlloc_3920_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3919_;
            }
            3 => {
                if v_isShared_3925_ == 0 {
                    v___x_3927_ = v___x_3924_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3928_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
                    v___x_3927_ = v_reuseFailAlloc_3928_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0___boxed(
    mut v_x_3933_: *mut leanh::LeanObject,
    mut v___y_3934_: *mut leanh::LeanObject,
    mut v___y_3935_: *mut leanh::LeanObject,
    mut v___y_3936_: *mut leanh::LeanObject,
    mut v___y_3937_: *mut leanh::LeanObject,
    mut v___y_3938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3939_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v_x_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
    leanh::lean_dec(v___y_3937_);
    leanh::lean_dec_ref(v___y_3936_);
    leanh::lean_dec(v___y_3935_);
    leanh::lean_dec_ref(v___y_3934_);
    return v_res_3939_;
}
pub unsafe fn l_Lean_Meta_mkForallFVars_x27___lam__0(
    mut v_val_3940_: *mut leanh::LeanObject,
    mut v_a_3941_: *mut leanh::LeanObject,
    mut v_a_3942_: *mut leanh::LeanObject,
    mut v_a_3943_: *mut leanh::LeanObject,
    mut v_a_3944_: *mut leanh::LeanObject,
    mut v_a_x3f_3945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3947_ = lean_st_ref_get(v_val_3940_);
    v___x_3948_ =
        l_Lean_Meta_resetMVarUserNames(v___x_3947_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_);
    leanh::lean_dec(v___x_3947_);
    return v___x_3948_;
}
pub unsafe fn l_Lean_Meta_mkForallFVars_x27___lam__0___boxed(
    mut v_val_3949_: *mut leanh::LeanObject,
    mut v_a_3950_: *mut leanh::LeanObject,
    mut v_a_3951_: *mut leanh::LeanObject,
    mut v_a_3952_: *mut leanh::LeanObject,
    mut v_a_3953_: *mut leanh::LeanObject,
    mut v_a_x3f_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3956_ = l_Lean_Meta_mkForallFVars_x27___lam__0(
        v_val_3949_,
        v_a_3950_,
        v_a_3951_,
        v_a_3952_,
        v_a_3953_,
        v_a_x3f_3954_,
    );
    leanh::lean_dec(v_a_x3f_3954_);
    leanh::lean_dec(v_a_3953_);
    leanh::lean_dec_ref(v_a_3952_);
    leanh::lean_dec(v_a_3951_);
    leanh::lean_dec_ref(v_a_3950_);
    leanh::lean_dec(v_val_3949_);
    return v_res_3956_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(
    mut v_xs_3957_: *mut leanh::LeanObject,
    mut v_as_3958_: *mut leanh::LeanObject,
    mut v_sz_3959_: usize,
    mut v_i_3960_: usize,
    mut v_b_3961_: *mut leanh::LeanObject,
    mut v___y_3962_: *mut leanh::LeanObject,
    mut v___y_3963_: *mut leanh::LeanObject,
    mut v___y_3964_: *mut leanh::LeanObject,
    mut v___y_3965_: *mut leanh::LeanObject,
    mut v___y_3966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: usize = 0;
    let mut v___x_3980_: usize = 0;
    let mut v_a_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3985_: u8 = 0;
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3989_: u8 = 0;
    let mut v_a_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3993_: u8 = 0;
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3997_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3968_ = lean_usize_dec_lt(v_i_3960_, v_sz_3959_);
                if v___x_3968_ == 0 {
                    leanh::lean_dec_ref(v_xs_3957_);
                    v___x_3969_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3969_, 0, v_b_3961_);
                    return v___x_3969_;
                } else {
                    v_a_3970_ = lean_array_uget_borrowed(v_as_3958_, v_i_3960_);
                    leanh::lean_inc(v___y_3966_);
                    leanh::lean_inc_ref(v___y_3965_);
                    leanh::lean_inc(v___y_3964_);
                    leanh::lean_inc_ref(v___y_3963_);
                    leanh::lean_inc(v_a_3970_);
                    v___x_3971_ = lean_infer_type(
                        v_a_3970_,
                        v___y_3963_,
                        v___y_3964_,
                        v___y_3965_,
                        v___y_3966_,
                    );
                    if leanh::lean_obj_tag(v___x_3971_) == 0 {
                        v_a_3972_ = leanh::lean_ctor_get(v___x_3971_, 0);
                        leanh::lean_inc(v_a_3972_);
                        leanh::lean_dec_ref_known(v___x_3971_, 1);
                        leanh::lean_inc_ref(v_xs_3957_);
                        v___x_3973_ = l_Lean_Meta_setMVarUserNamesAt(
                            v_a_3972_,
                            v_xs_3957_,
                            v___y_3963_,
                            v___y_3964_,
                            v___y_3965_,
                            v___y_3966_,
                        );
                        if leanh::lean_obj_tag(v___x_3973_) == 0 {
                            v_a_3974_ = leanh::lean_ctor_get(v___x_3973_, 0);
                            leanh::lean_inc(v_a_3974_);
                            leanh::lean_dec_ref_known(v___x_3973_, 1);
                            v___x_3975_ = lean_st_ref_take(v___y_3962_);
                            v___x_3976_ = l_Array_append___redArg(v___x_3975_, v_a_3974_);
                            leanh::lean_dec(v_a_3974_);
                            v___x_3977_ = lean_st_ref_set(v___y_3962_, v___x_3976_);
                            v___x_3978_ = leanh::lean_box(0);
                            v___x_3979_ = 1usize;
                            v___x_3980_ = lean_usize_add(v_i_3960_, v___x_3979_);
                            v_i_3960_ = v___x_3980_;
                            v_b_3961_ = v___x_3978_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_xs_3957_);
                            v_a_3982_ = leanh::lean_ctor_get(v___x_3973_, 0);
                            v_isSharedCheck_3989_ =
                                (!leanh::lean_is_exclusive(v___x_3973_)) as u8;
                            if v_isSharedCheck_3989_ == 0 {
                                v___x_3984_ = v___x_3973_;
                                v_isShared_3985_ = v_isSharedCheck_3989_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3982_);
                                leanh::lean_dec(v___x_3973_);
                                v___x_3984_ = leanh::lean_box(0);
                                v_isShared_3985_ = v_isSharedCheck_3989_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_xs_3957_);
                        v_a_3990_ = leanh::lean_ctor_get(v___x_3971_, 0);
                        v_isSharedCheck_3997_ =
                            (!leanh::lean_is_exclusive(v___x_3971_)) as u8;
                        if v_isSharedCheck_3997_ == 0 {
                            v___x_3992_ = v___x_3971_;
                            v_isShared_3993_ = v_isSharedCheck_3997_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3990_);
                            leanh::lean_dec(v___x_3971_);
                            v___x_3992_ = leanh::lean_box(0);
                            v_isShared_3993_ = v_isSharedCheck_3997_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3985_ == 0 {
                    v___x_3987_ = v___x_3984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3988_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
                    v___x_3987_ = v_reuseFailAlloc_3988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3987_;
            }
            3 => {
                if v_isShared_3993_ == 0 {
                    v___x_3995_ = v___x_3992_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3996_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
                    v___x_3995_ = v_reuseFailAlloc_3996_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2___boxed(
    mut v_xs_3998_: *mut leanh::LeanObject,
    mut v_as_3999_: *mut leanh::LeanObject,
    mut v_sz_4000_: *mut leanh::LeanObject,
    mut v_i_4001_: *mut leanh::LeanObject,
    mut v_b_4002_: *mut leanh::LeanObject,
    mut v___y_4003_: *mut leanh::LeanObject,
    mut v___y_4004_: *mut leanh::LeanObject,
    mut v___y_4005_: *mut leanh::LeanObject,
    mut v___y_4006_: *mut leanh::LeanObject,
    mut v___y_4007_: *mut leanh::LeanObject,
    mut v___y_4008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4009_: usize = 0;
    let mut v_i_boxed_4010_: usize = 0;
    let mut v_res_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4009_ = leanh::lean_unbox_usize(v_sz_4000_);
    leanh::lean_dec(v_sz_4000_);
    v_i_boxed_4010_ = leanh::lean_unbox_usize(v_i_4001_);
    leanh::lean_dec(v_i_4001_);
    v_res_4011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_3998_, v_as_3999_, v_sz_boxed_4009_, v_i_boxed_4010_, v_b_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
    leanh::lean_dec(v___y_4007_);
    leanh::lean_dec_ref(v___y_4006_);
    leanh::lean_dec(v___y_4005_);
    leanh::lean_dec_ref(v___y_4004_);
    leanh::lean_dec(v___y_4003_);
    leanh::lean_dec_ref(v_as_3999_);
    return v_res_4011_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(
    mut v_xs_4012_: *mut leanh::LeanObject,
    mut v_as_4013_: *mut leanh::LeanObject,
    mut v_sz_4014_: usize,
    mut v_i_4015_: usize,
    mut v_b_4016_: *mut leanh::LeanObject,
    mut v___y_4017_: *mut leanh::LeanObject,
    mut v___y_4018_: *mut leanh::LeanObject,
    mut v___y_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
    mut v___y_4021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4023_: u8 = 0;
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: usize = 0;
    let mut v___x_4035_: usize = 0;
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4040_: u8 = 0;
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4044_: u8 = 0;
    let mut v_a_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4048_: u8 = 0;
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4023_ = lean_usize_dec_lt(v_i_4015_, v_sz_4014_);
                if v___x_4023_ == 0 {
                    leanh::lean_dec_ref(v_xs_4012_);
                    v___x_4024_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4024_, 0, v_b_4016_);
                    return v___x_4024_;
                } else {
                    v_a_4025_ = lean_array_uget_borrowed(v_as_4013_, v_i_4015_);
                    leanh::lean_inc(v___y_4021_);
                    leanh::lean_inc_ref(v___y_4020_);
                    leanh::lean_inc(v___y_4019_);
                    leanh::lean_inc_ref(v___y_4018_);
                    leanh::lean_inc(v_a_4025_);
                    v___x_4026_ = lean_infer_type(
                        v_a_4025_,
                        v___y_4018_,
                        v___y_4019_,
                        v___y_4020_,
                        v___y_4021_,
                    );
                    if leanh::lean_obj_tag(v___x_4026_) == 0 {
                        v_a_4027_ = leanh::lean_ctor_get(v___x_4026_, 0);
                        leanh::lean_inc(v_a_4027_);
                        leanh::lean_dec_ref_known(v___x_4026_, 1);
                        leanh::lean_inc_ref(v_xs_4012_);
                        v___x_4028_ = l_Lean_Meta_setMVarUserNamesAt(
                            v_a_4027_,
                            v_xs_4012_,
                            v___y_4018_,
                            v___y_4019_,
                            v___y_4020_,
                            v___y_4021_,
                        );
                        if leanh::lean_obj_tag(v___x_4028_) == 0 {
                            v_a_4029_ = leanh::lean_ctor_get(v___x_4028_, 0);
                            leanh::lean_inc(v_a_4029_);
                            leanh::lean_dec_ref_known(v___x_4028_, 1);
                            v___x_4030_ = lean_st_ref_take(v___y_4017_);
                            v___x_4031_ = l_Array_append___redArg(v___x_4030_, v_a_4029_);
                            leanh::lean_dec(v_a_4029_);
                            v___x_4032_ = lean_st_ref_set(v___y_4017_, v___x_4031_);
                            v___x_4033_ = leanh::lean_box(0);
                            v___x_4034_ = 1usize;
                            v___x_4035_ = lean_usize_add(v_i_4015_, v___x_4034_);
                            v___x_4036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_4012_, v_as_4013_, v_sz_4014_, v___x_4035_, v___x_4033_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
                            return v___x_4036_;
                        } else {
                            leanh::lean_dec_ref(v_xs_4012_);
                            v_a_4037_ = leanh::lean_ctor_get(v___x_4028_, 0);
                            v_isSharedCheck_4044_ =
                                (!leanh::lean_is_exclusive(v___x_4028_)) as u8;
                            if v_isSharedCheck_4044_ == 0 {
                                v___x_4039_ = v___x_4028_;
                                v_isShared_4040_ = v_isSharedCheck_4044_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4037_);
                                leanh::lean_dec(v___x_4028_);
                                v___x_4039_ = leanh::lean_box(0);
                                v_isShared_4040_ = v_isSharedCheck_4044_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_xs_4012_);
                        v_a_4045_ = leanh::lean_ctor_get(v___x_4026_, 0);
                        v_isSharedCheck_4052_ =
                            (!leanh::lean_is_exclusive(v___x_4026_)) as u8;
                        if v_isSharedCheck_4052_ == 0 {
                            v___x_4047_ = v___x_4026_;
                            v_isShared_4048_ = v_isSharedCheck_4052_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4045_);
                            leanh::lean_dec(v___x_4026_);
                            v___x_4047_ = leanh::lean_box(0);
                            v_isShared_4048_ = v_isSharedCheck_4052_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4040_ == 0 {
                    v___x_4042_ = v___x_4039_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4043_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
                    v___x_4042_ = v_reuseFailAlloc_4043_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4042_;
            }
            3 => {
                if v_isShared_4048_ == 0 {
                    v___x_4050_ = v___x_4047_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4051_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
                    v___x_4050_ = v_reuseFailAlloc_4051_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2___boxed(
    mut v_xs_4053_: *mut leanh::LeanObject,
    mut v_as_4054_: *mut leanh::LeanObject,
    mut v_sz_4055_: *mut leanh::LeanObject,
    mut v_i_4056_: *mut leanh::LeanObject,
    mut v_b_4057_: *mut leanh::LeanObject,
    mut v___y_4058_: *mut leanh::LeanObject,
    mut v___y_4059_: *mut leanh::LeanObject,
    mut v___y_4060_: *mut leanh::LeanObject,
    mut v___y_4061_: *mut leanh::LeanObject,
    mut v___y_4062_: *mut leanh::LeanObject,
    mut v___y_4063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4064_: usize = 0;
    let mut v_i_boxed_4065_: usize = 0;
    let mut v_res_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4064_ = leanh::lean_unbox_usize(v_sz_4055_);
    leanh::lean_dec(v_sz_4055_);
    v_i_boxed_4065_ = leanh::lean_unbox_usize(v_i_4056_);
    leanh::lean_dec(v_i_4056_);
    v_res_4066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_4053_, v_as_4054_, v_sz_boxed_4064_, v_i_boxed_4065_, v_b_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
    leanh::lean_dec(v___y_4062_);
    leanh::lean_dec_ref(v___y_4061_);
    leanh::lean_dec(v___y_4060_);
    leanh::lean_dec_ref(v___y_4059_);
    leanh::lean_dec(v___y_4058_);
    leanh::lean_dec_ref(v_as_4054_);
    return v_res_4066_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(
    mut v_as_4067_: *mut leanh::LeanObject,
    mut v_i_4068_: usize,
    mut v_stop_4069_: usize,
    mut v___y_4070_: *mut leanh::LeanObject,
    mut v___y_4071_: *mut leanh::LeanObject,
    mut v___y_4072_: *mut leanh::LeanObject,
    mut v___y_4073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4075_: u8 = 0;
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4082_: u8 = 0;
    let mut v___x_4083_: usize = 0;
    let mut v___x_4084_: usize = 0;
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4089_: u8 = 0;
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4075_ = lean_usize_dec_eq(v_i_4068_, v_stop_4069_);
                if v___x_4075_ == 0 {
                    v___x_4076_ = lean_array_uget_borrowed(v_as_4067_, v_i_4068_);
                    leanh::lean_inc(v___x_4076_);
                    v___x_4077_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v___x_4076_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
                    if leanh::lean_obj_tag(v___x_4077_) == 0 {
                        v_a_4078_ = leanh::lean_ctor_get(v___x_4077_, 0);
                        v_isSharedCheck_4089_ =
                            (!leanh::lean_is_exclusive(v___x_4077_)) as u8;
                        if v_isSharedCheck_4089_ == 0 {
                            v___x_4080_ = v___x_4077_;
                            v_isShared_4081_ = v_isSharedCheck_4089_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4078_);
                            leanh::lean_dec(v___x_4077_);
                            v___x_4080_ = leanh::lean_box(0);
                            v_isShared_4081_ = v_isSharedCheck_4089_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_4077_;
                    }
                } else {
                    v___x_4090_ = 0;
                    v___x_4091_ = leanh::lean_box((v___x_4090_) as usize);
                    v___x_4092_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4092_, 0, v___x_4091_);
                    return v___x_4092_;
                }
            }
            1 => {
                v___x_4082_ = (leanh::lean_unbox(v_a_4078_) as u8);
                if v___x_4082_ == 0 {
                    leanh::lean_del_object(v___x_4080_);
                    leanh::lean_dec(v_a_4078_);
                    v___x_4083_ = 1usize;
                    v___x_4084_ = lean_usize_add(v_i_4068_, v___x_4083_);
                    v_i_4068_ = v___x_4084_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_4081_ == 0 {
                        v___x_4087_ = v___x_4080_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4088_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4078_);
                        v___x_4087_ = v_reuseFailAlloc_4088_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4087_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1___boxed(
    mut v_as_4093_: *mut leanh::LeanObject,
    mut v_i_4094_: *mut leanh::LeanObject,
    mut v_stop_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
    mut v___y_4098_: *mut leanh::LeanObject,
    mut v___y_4099_: *mut leanh::LeanObject,
    mut v___y_4100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4101_: usize = 0;
    let mut v_stop_boxed_4102_: usize = 0;
    let mut v_res_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4101_ = leanh::lean_unbox_usize(v_i_4094_);
    leanh::lean_dec(v_i_4094_);
    v_stop_boxed_4102_ = leanh::lean_unbox_usize(v_stop_4095_);
    leanh::lean_dec(v_stop_4095_);
    v_res_4103_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_as_4093_, v_i_boxed_4101_, v_stop_boxed_4102_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
    leanh::lean_dec(v___y_4099_);
    leanh::lean_dec_ref(v___y_4098_);
    leanh::lean_dec(v___y_4097_);
    leanh::lean_dec_ref(v___y_4096_);
    leanh::lean_dec_ref(v_as_4093_);
    return v_res_4103_;
}
pub unsafe fn l_Lean_Meta_mkForallFVars_x27(
    mut v_xs_4104_: *mut leanh::LeanObject,
    mut v_type_4105_: *mut leanh::LeanObject,
    mut v_a_4106_: *mut leanh::LeanObject,
    mut v_a_4107_: *mut leanh::LeanObject,
    mut v_a_4108_: *mut leanh::LeanObject,
    mut v_a_4109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4112_: u8 = 0;
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: u8 = 0;
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: u8 = 0;
    let mut v___x_4119_: usize = 0;
    let mut v___x_4120_: usize = 0;
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: u8 = 0;
    let mut v___x_4124_: u8 = 0;
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_unused_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4142_: u8 = 0;
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4146_: u8 = 0;
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4148_: usize = 0;
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: u8 = 0;
    let mut v___x_4156_: u8 = 0;
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4161_: u8 = 0;
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4167_: u8 = 0;
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4172_: u8 = 0;
    let mut v_unused_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4177_: u8 = 0;
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut v_reuseFailAlloc_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4183_: u8 = 0;
    let mut v_a_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4190_: u8 = 0;
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4116_ = leanh::lean_unsigned_to_nat(0);
                v___x_4117_ = lean_array_get_size(v_xs_4104_);
                v___x_4118_ = lean_nat_dec_lt(v___x_4116_, v___x_4117_);
                if v___x_4118_ == 0 {
                    v_a_4112_ = v___x_4118_;
                    state = 1;
                    continue;
                } else {
                    if v___x_4118_ == 0 {
                        v_a_4112_ = v___x_4118_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4119_ = 0usize;
                        v___x_4120_ = lean_usize_of_nat(v___x_4117_);
                        v___x_4121_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_xs_4104_, v___x_4119_, v___x_4120_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_);
                        if leanh::lean_obj_tag(v___x_4121_) == 0 {
                            v_a_4122_ = leanh::lean_ctor_get(v___x_4121_, 0);
                            leanh::lean_inc(v_a_4122_);
                            leanh::lean_dec_ref_known(v___x_4121_, 1);
                            v___x_4123_ = (leanh::lean_unbox(v_a_4122_) as u8);
                            if v___x_4123_ == 0 {
                                v___x_4124_ = (leanh::lean_unbox(v_a_4122_) as u8);
                                leanh::lean_dec(v_a_4122_);
                                v_a_4112_ = v___x_4124_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_4122_);
                                v___x_4125_ = l_Lean_Meta_setMVarUserNamesAt___closed__0;
                                v___x_4126_ = lean_st_mk_ref(v___x_4125_);
                                v___x_4147_ = leanh::lean_box(0);
                                v_sz_4148_ = lean_array_size(v_xs_4104_);
                                leanh::lean_inc_ref(v_xs_4104_);
                                v___x_4149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_4104_, v_xs_4104_, v_sz_4148_, v___x_4119_, v___x_4147_, v___x_4126_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_);
                                if leanh::lean_obj_tag(v___x_4149_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4149_, 1);
                                    leanh::lean_inc_ref(v_xs_4104_);
                                    leanh::lean_inc_ref(v_type_4105_);
                                    v___x_4150_ = l_Lean_Meta_setMVarUserNamesAt(
                                        v_type_4105_,
                                        v_xs_4104_,
                                        v_a_4106_,
                                        v_a_4107_,
                                        v_a_4108_,
                                        v_a_4109_,
                                    );
                                    if leanh::lean_obj_tag(v___x_4150_) == 0 {
                                        v_a_4151_ = leanh::lean_ctor_get(v___x_4150_, 0);
                                        leanh::lean_inc(v_a_4151_);
                                        leanh::lean_dec_ref_known(v___x_4150_, 1);
                                        v___x_4152_ = lean_st_ref_take(v___x_4126_);
                                        v___x_4153_ =
                                            l_Array_append___redArg(v___x_4152_, v_a_4151_);
                                        leanh::lean_dec(v_a_4151_);
                                        v___x_4154_ = lean_st_ref_set(v___x_4126_, v___x_4153_);
                                        v___x_4155_ = 0;
                                        v___x_4156_ = 1;
                                        v___x_4157_ = l_Lean_Meta_mkForallFVars(
                                            v_xs_4104_,
                                            v_type_4105_,
                                            v___x_4155_,
                                            v___x_4118_,
                                            v___x_4118_,
                                            v___x_4156_,
                                            v_a_4106_,
                                            v_a_4107_,
                                            v_a_4108_,
                                            v_a_4109_,
                                        );
                                        leanh::lean_dec_ref(v_xs_4104_);
                                        if leanh::lean_obj_tag(v___x_4157_) == 0 {
                                            v_a_4158_ = leanh::lean_ctor_get(v___x_4157_, 0);
                                            v_isSharedCheck_4183_ =
                                                (!leanh::lean_is_exclusive(v___x_4157_))
                                                    as u8;
                                            if v_isSharedCheck_4183_ == 0 {
                                                v___x_4160_ = v___x_4157_;
                                                v_isShared_4161_ = v_isSharedCheck_4183_;
                                                state = 7;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4158_);
                                                leanh::lean_dec(v___x_4157_);
                                                v___x_4160_ = leanh::lean_box(0);
                                                v_isShared_4161_ = v_isSharedCheck_4183_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            v_a_4184_ = leanh::lean_ctor_get(v___x_4157_, 0);
                                            leanh::lean_inc(v_a_4184_);
                                            leanh::lean_dec_ref_known(v___x_4157_, 1);
                                            v_a_4128_ = v_a_4184_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_type_4105_);
                                        leanh::lean_dec_ref(v_xs_4104_);
                                        v_a_4185_ = leanh::lean_ctor_get(v___x_4150_, 0);
                                        leanh::lean_inc(v_a_4185_);
                                        leanh::lean_dec_ref_known(v___x_4150_, 1);
                                        v_a_4128_ = v_a_4185_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_type_4105_);
                                    leanh::lean_dec_ref(v_xs_4104_);
                                    v_a_4186_ = leanh::lean_ctor_get(v___x_4149_, 0);
                                    leanh::lean_inc(v_a_4186_);
                                    leanh::lean_dec_ref_known(v___x_4149_, 1);
                                    v_a_4128_ = v_a_4186_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_type_4105_);
                            leanh::lean_dec_ref(v_xs_4104_);
                            v_a_4187_ = leanh::lean_ctor_get(v___x_4121_, 0);
                            v_isSharedCheck_4194_ =
                                (!leanh::lean_is_exclusive(v___x_4121_)) as u8;
                            if v_isSharedCheck_4194_ == 0 {
                                v___x_4189_ = v___x_4121_;
                                v_isShared_4190_ = v_isSharedCheck_4194_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4187_);
                                leanh::lean_dec(v___x_4121_);
                                v___x_4189_ = leanh::lean_box(0);
                                v_isShared_4190_ = v_isSharedCheck_4194_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4113_ = 1;
                v___x_4114_ = 1;
                v___x_4115_ = l_Lean_Meta_mkForallFVars(
                    v_xs_4104_,
                    v_type_4105_,
                    v_a_4112_,
                    v___x_4113_,
                    v___x_4113_,
                    v___x_4114_,
                    v_a_4106_,
                    v_a_4107_,
                    v_a_4108_,
                    v_a_4109_,
                );
                leanh::lean_dec_ref(v_xs_4104_);
                return v___x_4115_;
            }
            2 => {
                v___x_4129_ = leanh::lean_box(0);
                v___x_4130_ = l_Lean_Meta_mkForallFVars_x27___lam__0(
                    v___x_4126_,
                    v_a_4106_,
                    v_a_4107_,
                    v_a_4108_,
                    v_a_4109_,
                    v___x_4129_,
                );
                leanh::lean_dec(v___x_4126_);
                if leanh::lean_obj_tag(v___x_4130_) == 0 {
                    v_isSharedCheck_4137_ = (!leanh::lean_is_exclusive(v___x_4130_)) as u8;
                    if v_isSharedCheck_4137_ == 0 {
                        v_unused_4138_ = leanh::lean_ctor_get(v___x_4130_, 0);
                        leanh::lean_dec(v_unused_4138_);
                        v___x_4132_ = v___x_4130_;
                        v_isShared_4133_ = v_isSharedCheck_4137_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4130_);
                        v___x_4132_ = leanh::lean_box(0);
                        v_isShared_4133_ = v_isSharedCheck_4137_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_4128_);
                    v_a_4139_ = leanh::lean_ctor_get(v___x_4130_, 0);
                    v_isSharedCheck_4146_ = (!leanh::lean_is_exclusive(v___x_4130_)) as u8;
                    if v_isSharedCheck_4146_ == 0 {
                        v___x_4141_ = v___x_4130_;
                        v_isShared_4142_ = v_isSharedCheck_4146_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4139_);
                        leanh::lean_dec(v___x_4130_);
                        v___x_4141_ = leanh::lean_box(0);
                        v_isShared_4142_ = v_isSharedCheck_4146_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4133_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4132_, 1);
                    leanh::lean_ctor_set(v___x_4132_, 0, v_a_4128_);
                    v___x_4135_ = v___x_4132_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4128_);
                    v___x_4135_ = v_reuseFailAlloc_4136_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4135_;
            }
            5 => {
                if v_isShared_4142_ == 0 {
                    v___x_4144_ = v___x_4141_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4145_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
                    v___x_4144_ = v_reuseFailAlloc_4145_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4144_;
            }
            7 => {
                leanh::lean_inc(v_a_4158_);
                if v_isShared_4161_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4160_, 1);
                    v___x_4163_ = v___x_4160_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4182_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4158_);
                    v___x_4163_ = v_reuseFailAlloc_4182_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4164_ = l_Lean_Meta_mkForallFVars_x27___lam__0(
                    v___x_4126_,
                    v_a_4106_,
                    v_a_4107_,
                    v_a_4108_,
                    v_a_4109_,
                    v___x_4163_,
                );
                leanh::lean_dec_ref(v___x_4163_);
                if leanh::lean_obj_tag(v___x_4164_) == 0 {
                    v_isSharedCheck_4172_ = (!leanh::lean_is_exclusive(v___x_4164_)) as u8;
                    if v_isSharedCheck_4172_ == 0 {
                        v_unused_4173_ = leanh::lean_ctor_get(v___x_4164_, 0);
                        leanh::lean_dec(v_unused_4173_);
                        v___x_4166_ = v___x_4164_;
                        v_isShared_4167_ = v_isSharedCheck_4172_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4164_);
                        v___x_4166_ = leanh::lean_box(0);
                        v_isShared_4167_ = v_isSharedCheck_4172_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4158_);
                    leanh::lean_dec(v___x_4126_);
                    v_a_4174_ = leanh::lean_ctor_get(v___x_4164_, 0);
                    v_isSharedCheck_4181_ = (!leanh::lean_is_exclusive(v___x_4164_)) as u8;
                    if v_isSharedCheck_4181_ == 0 {
                        v___x_4176_ = v___x_4164_;
                        v_isShared_4177_ = v_isSharedCheck_4181_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4174_);
                        leanh::lean_dec(v___x_4164_);
                        v___x_4176_ = leanh::lean_box(0);
                        v_isShared_4177_ = v_isSharedCheck_4181_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                v___x_4168_ = lean_st_ref_get(v___x_4126_);
                leanh::lean_dec(v___x_4126_);
                leanh::lean_dec(v___x_4168_);
                if v_isShared_4167_ == 0 {
                    leanh::lean_ctor_set(v___x_4166_, 0, v_a_4158_);
                    v___x_4170_ = v___x_4166_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4171_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4158_);
                    v___x_4170_ = v_reuseFailAlloc_4171_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4170_;
            }
            11 => {
                if v_isShared_4177_ == 0 {
                    v___x_4179_ = v___x_4176_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
                    v___x_4179_ = v_reuseFailAlloc_4180_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4179_;
            }
            13 => {
                if v_isShared_4190_ == 0 {
                    v___x_4192_ = v___x_4189_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4193_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
                    v___x_4192_ = v_reuseFailAlloc_4193_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkForallFVars_x27___boxed(
    mut v_xs_4195_: *mut leanh::LeanObject,
    mut v_type_4196_: *mut leanh::LeanObject,
    mut v_a_4197_: *mut leanh::LeanObject,
    mut v_a_4198_: *mut leanh::LeanObject,
    mut v_a_4199_: *mut leanh::LeanObject,
    mut v_a_4200_: *mut leanh::LeanObject,
    mut v_a_4201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Lean_Meta_mkForallFVars_x27(
        v_xs_4195_,
        v_type_4196_,
        v_a_4197_,
        v_a_4198_,
        v_a_4199_,
        v_a_4200_,
    );
    leanh::lean_dec(v_a_4200_);
    leanh::lean_dec_ref(v_a_4199_);
    leanh::lean_dec(v_a_4198_);
    leanh::lean_dec_ref(v_a_4197_);
    return v_res_4202_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_ForEachExpr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ForEachExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ForEachExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ForEachExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ForEachExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_ForEachExpr(builtin);
}