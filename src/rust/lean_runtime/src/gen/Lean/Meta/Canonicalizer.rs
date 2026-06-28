// Lean compiler output
// Module: Lean.Meta.Canonicalizer
// Imports: Lean.Util.ShareCommon Lean.Meta.FunInfo Std.Data.HashMap.Raw Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_getRevArg_x21, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar, l_Lean_Expr_hash,
    l_Lean_Expr_isMVar,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey, l_Lean_Meta_ParamInfo_isExplicit,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::FunInfo::{
    initialize_Lean_Meta_FunInfo, l_Lean_Meta_getFunInfo, runtime_initialize_Lean_Meta_FunInfo,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::ShareCommon::{
    initialize_Lean_Util_ShareCommon, runtime_initialize_Lean_Util_ShareCommon,
};
use crate::r#gen::Std::Data::HashMap::Raw::{
    initialize_Std_Data_HashMap_Raw, runtime_initialize_Std_Data_HashMap_Raw,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land, lean_usize_to_uint64,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_nat_sub, lean_uint64_dec_eq, lean_uint64_mix_hash,
    lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
pub static l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value:
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
    m_fun: l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Canonicalizer_instBEqExprVisited: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value:
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
    m_fun: l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Canonicalizer_instHashableExprVisited: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Canonicalizer_instInhabitedState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0: u64 =
    0;
pub static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1239_ = crate::leanh::lean_box(0);
    v___x_1240_ = l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1;
    v___x_1241_ = l_Lean_Expr_const___override(v___x_1240_, v___x_1239_);
    return v___x_1241_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1242_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2_once
        ),
        _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2,
    );
    return v___x_1242_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1243_ = l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default;
    return v___x_1243_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(
    mut v_a_1244_: *mut crate::leanh::LeanObject,
    mut v_b_1245_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1246_: usize = 0;
    let mut v___x_1247_: usize = 0;
    let mut v___x_1248_: u8 = 0;
    v___x_1246_ = lean_ptr_addr(v_a_1244_);
    v___x_1247_ = lean_ptr_addr(v_b_1245_);
    v___x_1248_ = lean_usize_dec_eq(v___x_1246_, v___x_1247_);
    return v___x_1248_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed(
    mut v_a_1249_: *mut crate::leanh::LeanObject,
    mut v_b_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1251_: u8 = 0;
    let mut v_r_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(v_a_1249_, v_b_1250_);
    crate::leanh::lean_dec_ref(v_b_1250_);
    crate::leanh::lean_dec_ref(v_a_1249_);
    v_r_1252_ = crate::leanh::lean_box((v_res_1251_) as usize);
    return v_r_1252_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(
    mut v_a_1255_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: u64 = 0;
    v___x_1256_ = lean_ptr_addr(v_a_1255_);
    v___x_1257_ = lean_usize_to_uint64(v___x_1256_);
    return v___x_1257_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed(
    mut v_a_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1259_: u64 = 0;
    let mut v_r_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1259_ = l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(v_a_1258_);
    crate::leanh::lean_dec_ref(v_a_1258_);
    v_r_1260_ = crate::leanh::lean_box_uint64(v_res_1259_);
    return v_r_1260_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1263_ = crate::leanh::lean_box(0);
    v___x_1264_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1265_ = lean_mk_array(v___x_1264_, v___x_1263_);
    return v___x_1265_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0_once),
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0,
    );
    v___x_1267_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1268_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1268_, 0, v___x_1267_);
    crate::leanh::lean_ctor_set(v___x_1268_, 1, v___x_1266_);
    return v___x_1268_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1_once),
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1,
    );
    v___x_1270_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1270_, 0, v___x_1269_);
    crate::leanh::lean_ctor_set(v___x_1270_, 1, v___x_1269_);
    return v___x_1270_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1271_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2_once),
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2,
    );
    return v___x_1271_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(
    mut v_x_1272_: *mut crate::leanh::LeanObject,
    mut v_transparency_1273_: u8,
    mut v_s_1274_: *mut crate::leanh::LeanObject,
    mut v_a_1275_: *mut crate::leanh::LeanObject,
    mut v_a_1276_: *mut crate::leanh::LeanObject,
    mut v_a_1277_: *mut crate::leanh::LeanObject,
    mut v_a_1278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1280_ = lean_st_mk_ref(v_s_1274_);
                v___x_1281_ = crate::leanh::lean_box((v_transparency_1273_) as usize);
                crate::leanh::lean_inc(v_a_1278_);
                crate::leanh::lean_inc_ref(v_a_1277_);
                crate::leanh::lean_inc(v_a_1276_);
                crate::leanh::lean_inc_ref(v_a_1275_);
                crate::leanh::lean_inc(v___x_1280_);
                v___x_1282_ = crate::leanh::lean_apply_7(
                    v_x_1272_,
                    v___x_1281_,
                    v___x_1280_,
                    v_a_1275_,
                    v_a_1276_,
                    v_a_1277_,
                    v_a_1278_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1282_) == 0 {
                    v_a_1283_ = crate::leanh::lean_ctor_get(v___x_1282_, 0);
                    v_isSharedCheck_1291_ = (!crate::leanh::lean_is_exclusive(v___x_1282_)) as u8;
                    if v_isSharedCheck_1291_ == 0 {
                        v___x_1285_ = v___x_1282_;
                        v_isShared_1286_ = v_isSharedCheck_1291_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1283_);
                        crate::leanh::lean_dec(v___x_1282_);
                        v___x_1285_ = crate::leanh::lean_box(0);
                        v_isShared_1286_ = v_isSharedCheck_1291_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1280_);
                    return v___x_1282_;
                }
            }
            1 => {
                v___x_1287_ = lean_st_ref_get(v___x_1280_);
                crate::leanh::lean_dec(v___x_1280_);
                crate::leanh::lean_dec(v___x_1287_);
                if v_isShared_1286_ == 0 {
                    v___x_1289_ = v___x_1285_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1283_);
                    v___x_1289_ = v_reuseFailAlloc_1290_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg___boxed(
    mut v_x_1292_: *mut crate::leanh::LeanObject,
    mut v_transparency_1293_: *mut crate::leanh::LeanObject,
    mut v_s_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
    mut v_a_1296_: *mut crate::leanh::LeanObject,
    mut v_a_1297_: *mut crate::leanh::LeanObject,
    mut v_a_1298_: *mut crate::leanh::LeanObject,
    mut v_a_1299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_1300_: u8 = 0;
    let mut v_res_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1300_ = (crate::leanh::lean_unbox(v_transparency_1293_) as u8);
    v_res_1301_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(
        v_x_1292_,
        v_transparency_boxed_1300_,
        v_s_1294_,
        v_a_1295_,
        v_a_1296_,
        v_a_1297_,
        v_a_1298_,
    );
    crate::leanh::lean_dec(v_a_1298_);
    crate::leanh::lean_dec_ref(v_a_1297_);
    crate::leanh::lean_dec(v_a_1296_);
    crate::leanh::lean_dec_ref(v_a_1295_);
    return v_res_1301_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run_x27(
    mut v_00_u03b1_1302_: *mut crate::leanh::LeanObject,
    mut v_x_1303_: *mut crate::leanh::LeanObject,
    mut v_transparency_1304_: u8,
    mut v_s_1305_: *mut crate::leanh::LeanObject,
    mut v_a_1306_: *mut crate::leanh::LeanObject,
    mut v_a_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1311_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(
        v_x_1303_,
        v_transparency_1304_,
        v_s_1305_,
        v_a_1306_,
        v_a_1307_,
        v_a_1308_,
        v_a_1309_,
    );
    return v___x_1311_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run_x27___boxed(
    mut v_00_u03b1_1312_: *mut crate::leanh::LeanObject,
    mut v_x_1313_: *mut crate::leanh::LeanObject,
    mut v_transparency_1314_: *mut crate::leanh::LeanObject,
    mut v_s_1315_: *mut crate::leanh::LeanObject,
    mut v_a_1316_: *mut crate::leanh::LeanObject,
    mut v_a_1317_: *mut crate::leanh::LeanObject,
    mut v_a_1318_: *mut crate::leanh::LeanObject,
    mut v_a_1319_: *mut crate::leanh::LeanObject,
    mut v_a_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_1321_: u8 = 0;
    let mut v_res_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1321_ = (crate::leanh::lean_unbox(v_transparency_1314_) as u8);
    v_res_1322_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27(
        v_00_u03b1_1312_,
        v_x_1313_,
        v_transparency_boxed_1321_,
        v_s_1315_,
        v_a_1316_,
        v_a_1317_,
        v_a_1318_,
        v_a_1319_,
    );
    crate::leanh::lean_dec(v_a_1319_);
    crate::leanh::lean_dec_ref(v_a_1318_);
    crate::leanh::lean_dec(v_a_1317_);
    crate::leanh::lean_dec_ref(v_a_1316_);
    return v_res_1322_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run___redArg(
    mut v_x_1323_: *mut crate::leanh::LeanObject,
    mut v_transparency_1324_: u8,
    mut v_s_1325_: *mut crate::leanh::LeanObject,
    mut v_a_1326_: *mut crate::leanh::LeanObject,
    mut v_a_1327_: *mut crate::leanh::LeanObject,
    mut v_a_1328_: *mut crate::leanh::LeanObject,
    mut v_a_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1337_: u8 = 0;
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v_a_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1351_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1331_ = lean_st_mk_ref(v_s_1325_);
                v___x_1332_ = crate::leanh::lean_box((v_transparency_1324_) as usize);
                crate::leanh::lean_inc(v_a_1329_);
                crate::leanh::lean_inc_ref(v_a_1328_);
                crate::leanh::lean_inc(v_a_1327_);
                crate::leanh::lean_inc_ref(v_a_1326_);
                crate::leanh::lean_inc(v___x_1331_);
                v___x_1333_ = crate::leanh::lean_apply_7(
                    v_x_1323_,
                    v___x_1332_,
                    v___x_1331_,
                    v_a_1326_,
                    v_a_1327_,
                    v_a_1328_,
                    v_a_1329_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1333_) == 0 {
                    v_a_1334_ = crate::leanh::lean_ctor_get(v___x_1333_, 0);
                    v_isSharedCheck_1343_ = (!crate::leanh::lean_is_exclusive(v___x_1333_)) as u8;
                    if v_isSharedCheck_1343_ == 0 {
                        v___x_1336_ = v___x_1333_;
                        v_isShared_1337_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1334_);
                        crate::leanh::lean_dec(v___x_1333_);
                        v___x_1336_ = crate::leanh::lean_box(0);
                        v_isShared_1337_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1331_);
                    v_a_1344_ = crate::leanh::lean_ctor_get(v___x_1333_, 0);
                    v_isSharedCheck_1351_ = (!crate::leanh::lean_is_exclusive(v___x_1333_)) as u8;
                    if v_isSharedCheck_1351_ == 0 {
                        v___x_1346_ = v___x_1333_;
                        v_isShared_1347_ = v_isSharedCheck_1351_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1344_);
                        crate::leanh::lean_dec(v___x_1333_);
                        v___x_1346_ = crate::leanh::lean_box(0);
                        v_isShared_1347_ = v_isSharedCheck_1351_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1338_ = lean_st_ref_get(v___x_1331_);
                crate::leanh::lean_dec(v___x_1331_);
                v___x_1339_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1339_, 0, v_a_1334_);
                crate::leanh::lean_ctor_set(v___x_1339_, 1, v___x_1338_);
                if v_isShared_1337_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1336_, 0, v___x_1339_);
                    v___x_1341_ = v___x_1336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1341_;
            }
            3 => {
                if v_isShared_1347_ == 0 {
                    v___x_1349_ = v___x_1346_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1350_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
                    v___x_1349_ = v_reuseFailAlloc_1350_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run___redArg___boxed(
    mut v_x_1352_: *mut crate::leanh::LeanObject,
    mut v_transparency_1353_: *mut crate::leanh::LeanObject,
    mut v_s_1354_: *mut crate::leanh::LeanObject,
    mut v_a_1355_: *mut crate::leanh::LeanObject,
    mut v_a_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_a_1358_: *mut crate::leanh::LeanObject,
    mut v_a_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_1360_: u8 = 0;
    let mut v_res_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1360_ = (crate::leanh::lean_unbox(v_transparency_1353_) as u8);
    v_res_1361_ = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(
        v_x_1352_,
        v_transparency_boxed_1360_,
        v_s_1354_,
        v_a_1355_,
        v_a_1356_,
        v_a_1357_,
        v_a_1358_,
    );
    crate::leanh::lean_dec(v_a_1358_);
    crate::leanh::lean_dec_ref(v_a_1357_);
    crate::leanh::lean_dec(v_a_1356_);
    crate::leanh::lean_dec_ref(v_a_1355_);
    return v_res_1361_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run(
    mut v_00_u03b1_1362_: *mut crate::leanh::LeanObject,
    mut v_x_1363_: *mut crate::leanh::LeanObject,
    mut v_transparency_1364_: u8,
    mut v_s_1365_: *mut crate::leanh::LeanObject,
    mut v_a_1366_: *mut crate::leanh::LeanObject,
    mut v_a_1367_: *mut crate::leanh::LeanObject,
    mut v_a_1368_: *mut crate::leanh::LeanObject,
    mut v_a_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(
        v_x_1363_,
        v_transparency_1364_,
        v_s_1365_,
        v_a_1366_,
        v_a_1367_,
        v_a_1368_,
        v_a_1369_,
    );
    return v___x_1371_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run___boxed(
    mut v_00_u03b1_1372_: *mut crate::leanh::LeanObject,
    mut v_x_1373_: *mut crate::leanh::LeanObject,
    mut v_transparency_1374_: *mut crate::leanh::LeanObject,
    mut v_s_1375_: *mut crate::leanh::LeanObject,
    mut v_a_1376_: *mut crate::leanh::LeanObject,
    mut v_a_1377_: *mut crate::leanh::LeanObject,
    mut v_a_1378_: *mut crate::leanh::LeanObject,
    mut v_a_1379_: *mut crate::leanh::LeanObject,
    mut v_a_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transparency_boxed_1381_: u8 = 0;
    let mut v_res_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1381_ = (crate::leanh::lean_unbox(v_transparency_1374_) as u8);
    v_res_1382_ = l_Lean_Meta_Canonicalizer_CanonM_run(
        v_00_u03b1_1372_,
        v_x_1373_,
        v_transparency_boxed_1381_,
        v_s_1375_,
        v_a_1376_,
        v_a_1377_,
        v_a_1378_,
        v_a_1379_,
    );
    crate::leanh::lean_dec(v_a_1379_);
    crate::leanh::lean_dec_ref(v_a_1378_);
    crate::leanh::lean_dec(v_a_1377_);
    crate::leanh::lean_dec_ref(v_a_1376_);
    return v_res_1382_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(
    mut v_a_1383_: *mut crate::leanh::LeanObject,
    mut v_x_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: usize = 0;
    let mut v___x_1390_: usize = 0;
    let mut v___x_1391_: u8 = 0;
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1384_) == 0 {
                    v___x_1385_ = crate::leanh::lean_box(0);
                    return v___x_1385_;
                } else {
                    v_key_1386_ = crate::leanh::lean_ctor_get(v_x_1384_, 0);
                    v_value_1387_ = crate::leanh::lean_ctor_get(v_x_1384_, 1);
                    v_tail_1388_ = crate::leanh::lean_ctor_get(v_x_1384_, 2);
                    v___x_1389_ = lean_ptr_addr(v_key_1386_);
                    v___x_1390_ = lean_ptr_addr(v_a_1383_);
                    v___x_1391_ = lean_usize_dec_eq(v___x_1389_, v___x_1390_);
                    if v___x_1391_ == 0 {
                        v_x_1384_ = v_tail_1388_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1387_);
                        v___x_1393_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1393_, 0, v_value_1387_);
                        return v___x_1393_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg___boxed(
    mut v_a_1394_: *mut crate::leanh::LeanObject,
    mut v_x_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(v_a_1394_, v_x_1395_);
    crate::leanh::lean_dec(v_x_1395_);
    crate::leanh::lean_dec_ref(v_a_1394_);
    return v_res_1396_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(
    mut v_m_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: usize = 0;
    let mut v___x_1402_: u64 = 0;
    let mut v___x_1403_: u64 = 0;
    let mut v___x_1404_: u64 = 0;
    let mut v_fold_1405_: u64 = 0;
    let mut v___x_1406_: u64 = 0;
    let mut v___x_1407_: u64 = 0;
    let mut v___x_1408_: u64 = 0;
    let mut v___x_1409_: usize = 0;
    let mut v___x_1410_: usize = 0;
    let mut v___x_1411_: usize = 0;
    let mut v___x_1412_: usize = 0;
    let mut v___x_1413_: usize = 0;
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1399_ = crate::leanh::lean_ctor_get(v_m_1397_, 1);
    v___x_1400_ = lean_array_get_size(v_buckets_1399_);
    v___x_1401_ = lean_ptr_addr(v_a_1398_);
    v___x_1402_ = lean_usize_to_uint64(v___x_1401_);
    v___x_1403_ = 32u64;
    v___x_1404_ = lean_uint64_shift_right(v___x_1402_, v___x_1403_);
    v_fold_1405_ = lean_uint64_xor(v___x_1402_, v___x_1404_);
    v___x_1406_ = 16u64;
    v___x_1407_ = lean_uint64_shift_right(v_fold_1405_, v___x_1406_);
    v___x_1408_ = lean_uint64_xor(v_fold_1405_, v___x_1407_);
    v___x_1409_ = lean_uint64_to_usize(v___x_1408_);
    v___x_1410_ = lean_usize_of_nat(v___x_1400_);
    v___x_1411_ = 1usize;
    v___x_1412_ = lean_usize_sub(v___x_1410_, v___x_1411_);
    v___x_1413_ = lean_usize_land(v___x_1409_, v___x_1412_);
    v___x_1414_ = lean_array_uget_borrowed(v_buckets_1399_, v___x_1413_);
    v___x_1415_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(v_a_1398_, v___x_1414_);
    return v___x_1415_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg___boxed(
    mut v_m_1416_: *mut crate::leanh::LeanObject,
    mut v_a_1417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_m_1416_, v_a_1417_);
    crate::leanh::lean_dec_ref(v_a_1417_);
    crate::leanh::lean_dec_ref(v_m_1416_);
    return v_res_1418_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(
    mut v_e_1419_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cache_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: u8 = 0;
    v_cache_1421_ = crate::leanh::lean_ctor_get(v_____do__lift_1420_, 0);
    v_buckets_1422_ = crate::leanh::lean_ctor_get(v_cache_1421_, 1);
    v___x_1423_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1424_ = lean_array_get_size(v_buckets_1422_);
    v___x_1425_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
    if v___x_1425_ == 0 {
        let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1426_ = crate::leanh::lean_box(0);
        return v___x_1426_;
    } else {
        let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1427_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_cache_1421_, v_e_1419_);
        return v___x_1427_;
    }
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(
    mut v_e_1428_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1430_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(
        v_e_1428_,
        v_____do__lift_1429_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_1429_);
    crate::leanh::lean_dec_ref(v_e_1428_);
    return v_res_1430_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(
    mut v_00_u03b2_1431_: *mut crate::leanh::LeanObject,
    mut v_m_1432_: *mut crate::leanh::LeanObject,
    mut v_a_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_m_1432_, v_a_1433_);
    return v___x_1434_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___boxed(
    mut v_00_u03b2_1435_: *mut crate::leanh::LeanObject,
    mut v_m_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(v_00_u03b2_1435_, v_m_1436_, v_a_1437_);
    crate::leanh::lean_dec_ref(v_a_1437_);
    crate::leanh::lean_dec_ref(v_m_1436_);
    return v_res_1438_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0(
    mut v_00_u03b2_1439_: *mut crate::leanh::LeanObject,
    mut v_a_1440_: *mut crate::leanh::LeanObject,
    mut v_x_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(v_a_1440_, v_x_1441_);
    return v___x_1442_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___boxed(
    mut v_00_u03b2_1443_: *mut crate::leanh::LeanObject,
    mut v_a_1444_: *mut crate::leanh::LeanObject,
    mut v_x_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1446_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0(v_00_u03b2_1443_, v_a_1444_, v_x_1445_);
    crate::leanh::lean_dec(v_x_1445_);
    crate::leanh::lean_dec_ref(v_a_1444_);
    return v_res_1446_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(
    mut v_a_1447_: *mut crate::leanh::LeanObject,
    mut v_x_1448_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1449_: u8 = 0;
    let mut v_key_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: usize = 0;
    let mut v___x_1453_: usize = 0;
    let mut v___x_1454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1448_) == 0 {
                    v___x_1449_ = 0;
                    return v___x_1449_;
                } else {
                    v_key_1450_ = crate::leanh::lean_ctor_get(v_x_1448_, 0);
                    v_tail_1451_ = crate::leanh::lean_ctor_get(v_x_1448_, 2);
                    v___x_1452_ = lean_ptr_addr(v_key_1450_);
                    v___x_1453_ = lean_ptr_addr(v_a_1447_);
                    v___x_1454_ = lean_usize_dec_eq(v___x_1452_, v___x_1453_);
                    if v___x_1454_ == 0 {
                        v_x_1448_ = v_tail_1451_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1454_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg___boxed(
    mut v_a_1456_: *mut crate::leanh::LeanObject,
    mut v_x_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1458_: u8 = 0;
    let mut v_r_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(v_a_1456_, v_x_1457_);
    crate::leanh::lean_dec(v_x_1457_);
    crate::leanh::lean_dec_ref(v_a_1456_);
    v_r_1459_ = crate::leanh::lean_box((v_res_1458_) as usize);
    return v_r_1459_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1460_: *mut crate::leanh::LeanObject,
    mut v_x_1461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1467_: u8 = 0;
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: usize = 0;
    let mut v___x_1470_: u64 = 0;
    let mut v___x_1471_: u64 = 0;
    let mut v___x_1472_: u64 = 0;
    let mut v_fold_1473_: u64 = 0;
    let mut v___x_1474_: u64 = 0;
    let mut v___x_1475_: u64 = 0;
    let mut v___x_1476_: u64 = 0;
    let mut v___x_1477_: usize = 0;
    let mut v___x_1478_: usize = 0;
    let mut v___x_1479_: usize = 0;
    let mut v___x_1480_: usize = 0;
    let mut v___x_1481_: usize = 0;
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1461_) == 0 {
                    return v_x_1460_;
                } else {
                    v_key_1462_ = crate::leanh::lean_ctor_get(v_x_1461_, 0);
                    v_value_1463_ = crate::leanh::lean_ctor_get(v_x_1461_, 1);
                    v_tail_1464_ = crate::leanh::lean_ctor_get(v_x_1461_, 2);
                    v_isSharedCheck_1488_ = (!crate::leanh::lean_is_exclusive(v_x_1461_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v___x_1466_ = v_x_1461_;
                        v_isShared_1467_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1464_);
                        crate::leanh::lean_inc(v_value_1463_);
                        crate::leanh::lean_inc(v_key_1462_);
                        crate::leanh::lean_dec(v_x_1461_);
                        v___x_1466_ = crate::leanh::lean_box(0);
                        v_isShared_1467_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1468_ = lean_array_get_size(v_x_1460_);
                v___x_1469_ = lean_ptr_addr(v_key_1462_);
                v___x_1470_ = lean_usize_to_uint64(v___x_1469_);
                v___x_1471_ = 32u64;
                v___x_1472_ = lean_uint64_shift_right(v___x_1470_, v___x_1471_);
                v_fold_1473_ = lean_uint64_xor(v___x_1470_, v___x_1472_);
                v___x_1474_ = 16u64;
                v___x_1475_ = lean_uint64_shift_right(v_fold_1473_, v___x_1474_);
                v___x_1476_ = lean_uint64_xor(v_fold_1473_, v___x_1475_);
                v___x_1477_ = lean_uint64_to_usize(v___x_1476_);
                v___x_1478_ = lean_usize_of_nat(v___x_1468_);
                v___x_1479_ = 1usize;
                v___x_1480_ = lean_usize_sub(v___x_1478_, v___x_1479_);
                v___x_1481_ = lean_usize_land(v___x_1477_, v___x_1480_);
                v___x_1482_ = lean_array_uget_borrowed(v_x_1460_, v___x_1481_);
                crate::leanh::lean_inc(v___x_1482_);
                if v_isShared_1467_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1466_, 2, v___x_1482_);
                    v___x_1484_ = v___x_1466_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_key_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_value_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 2, v___x_1482_);
                    v___x_1484_ = v_reuseFailAlloc_1487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1485_ = lean_array_uset(v_x_1460_, v___x_1481_, v___x_1484_);
                v_x_1460_ = v___x_1485_;
                v_x_1461_ = v_tail_1464_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2___redArg(
    mut v_i_1489_: *mut crate::leanh::LeanObject,
    mut v_source_1490_: *mut crate::leanh::LeanObject,
    mut v_target_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v_es_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1492_ = lean_array_get_size(v_source_1490_);
                v___x_1493_ = lean_nat_dec_lt(v_i_1489_, v___x_1492_);
                if v___x_1493_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1490_);
                    crate::leanh::lean_dec(v_i_1489_);
                    return v_target_1491_;
                } else {
                    v_es_1494_ = lean_array_fget(v_source_1490_, v_i_1489_);
                    v___x_1495_ = crate::leanh::lean_box(0);
                    v_source_1496_ = lean_array_fset(v_source_1490_, v_i_1489_, v___x_1495_);
                    v_target_1497_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1491_, v_es_1494_);
                    v___x_1498_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1499_ = lean_nat_add(v_i_1489_, v___x_1498_);
                    crate::leanh::lean_dec(v_i_1489_);
                    v_i_1489_ = v___x_1499_;
                    v_source_1490_ = v_source_1496_;
                    v_target_1491_ = v_target_1497_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1___redArg(
    mut v_data_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = lean_array_get_size(v_data_1501_);
    v___x_1503_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1504_ = lean_nat_mul(v___x_1502_, v___x_1503_);
    v___x_1505_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1506_ = crate::leanh::lean_box(0);
    v___x_1507_ = lean_mk_array(v_nbuckets_1504_, v___x_1506_);
    v___x_1508_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2___redArg(v___x_1505_, v_data_1501_, v___x_1507_);
    return v___x_1508_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(
    mut v_a_1509_: *mut crate::leanh::LeanObject,
    mut v_b_1510_: *mut crate::leanh::LeanObject,
    mut v_x_1511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1517_: u8 = 0;
    let mut v___x_1518_: usize = 0;
    let mut v___x_1519_: usize = 0;
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1511_) == 0 {
                    crate::leanh::lean_dec(v_b_1510_);
                    crate::leanh::lean_dec_ref(v_a_1509_);
                    return v_x_1511_;
                } else {
                    v_key_1512_ = crate::leanh::lean_ctor_get(v_x_1511_, 0);
                    v_value_1513_ = crate::leanh::lean_ctor_get(v_x_1511_, 1);
                    v_tail_1514_ = crate::leanh::lean_ctor_get(v_x_1511_, 2);
                    v_isSharedCheck_1528_ = (!crate::leanh::lean_is_exclusive(v_x_1511_)) as u8;
                    if v_isSharedCheck_1528_ == 0 {
                        v___x_1516_ = v_x_1511_;
                        v_isShared_1517_ = v_isSharedCheck_1528_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1514_);
                        crate::leanh::lean_inc(v_value_1513_);
                        crate::leanh::lean_inc(v_key_1512_);
                        crate::leanh::lean_dec(v_x_1511_);
                        v___x_1516_ = crate::leanh::lean_box(0);
                        v_isShared_1517_ = v_isSharedCheck_1528_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1518_ = lean_ptr_addr(v_key_1512_);
                v___x_1519_ = lean_ptr_addr(v_a_1509_);
                v___x_1520_ = lean_usize_dec_eq(v___x_1518_, v___x_1519_);
                if v___x_1520_ == 0 {
                    v___x_1521_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(v_a_1509_, v_b_1510_, v_tail_1514_);
                    if v_isShared_1517_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1516_, 2, v___x_1521_);
                        v___x_1523_ = v___x_1516_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1524_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_key_1512_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_value_1513_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 2, v___x_1521_);
                        v___x_1523_ = v_reuseFailAlloc_1524_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1513_);
                    crate::leanh::lean_dec(v_key_1512_);
                    if v_isShared_1517_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1516_, 1, v_b_1510_);
                        crate::leanh::lean_ctor_set(v___x_1516_, 0, v_a_1509_);
                        v___x_1526_ = v___x_1516_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1527_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1509_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_b_1510_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_tail_1514_);
                        v___x_1526_ = v_reuseFailAlloc_1527_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1523_;
            }
            3 => {
                return v___x_1526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(
    mut v_m_1529_: *mut crate::leanh::LeanObject,
    mut v_a_1530_: *mut crate::leanh::LeanObject,
    mut v_b_1531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: usize = 0;
    let mut v___x_1539_: u64 = 0;
    let mut v___x_1540_: u64 = 0;
    let mut v___x_1541_: u64 = 0;
    let mut v_fold_1542_: u64 = 0;
    let mut v___x_1543_: u64 = 0;
    let mut v___x_1544_: u64 = 0;
    let mut v___x_1545_: u64 = 0;
    let mut v___x_1546_: usize = 0;
    let mut v___x_1547_: usize = 0;
    let mut v___x_1548_: usize = 0;
    let mut v___x_1549_: usize = 0;
    let mut v___x_1550_: usize = 0;
    let mut v_bkt_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v_val_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1532_ = crate::leanh::lean_ctor_get(v_m_1529_, 0);
                v_buckets_1533_ = crate::leanh::lean_ctor_get(v_m_1529_, 1);
                v_isSharedCheck_1577_ = (!crate::leanh::lean_is_exclusive(v_m_1529_)) as u8;
                if v_isSharedCheck_1577_ == 0 {
                    v___x_1535_ = v_m_1529_;
                    v_isShared_1536_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1533_);
                    crate::leanh::lean_inc(v_size_1532_);
                    crate::leanh::lean_dec(v_m_1529_);
                    v___x_1535_ = crate::leanh::lean_box(0);
                    v_isShared_1536_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1537_ = lean_array_get_size(v_buckets_1533_);
                v___x_1538_ = lean_ptr_addr(v_a_1530_);
                v___x_1539_ = lean_usize_to_uint64(v___x_1538_);
                v___x_1540_ = 32u64;
                v___x_1541_ = lean_uint64_shift_right(v___x_1539_, v___x_1540_);
                v_fold_1542_ = lean_uint64_xor(v___x_1539_, v___x_1541_);
                v___x_1543_ = 16u64;
                v___x_1544_ = lean_uint64_shift_right(v_fold_1542_, v___x_1543_);
                v___x_1545_ = lean_uint64_xor(v_fold_1542_, v___x_1544_);
                v___x_1546_ = lean_uint64_to_usize(v___x_1545_);
                v___x_1547_ = lean_usize_of_nat(v___x_1537_);
                v___x_1548_ = 1usize;
                v___x_1549_ = lean_usize_sub(v___x_1547_, v___x_1548_);
                v___x_1550_ = lean_usize_land(v___x_1546_, v___x_1549_);
                v_bkt_1551_ = lean_array_uget_borrowed(v_buckets_1533_, v___x_1550_);
                v___x_1552_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(v_a_1530_, v_bkt_1551_);
                if v___x_1552_ == 0 {
                    v___x_1553_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1554_ = lean_nat_add(v_size_1532_, v___x_1553_);
                    crate::leanh::lean_dec(v_size_1532_);
                    crate::leanh::lean_inc(v_bkt_1551_);
                    v___x_1555_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1555_, 0, v_a_1530_);
                    crate::leanh::lean_ctor_set(v___x_1555_, 1, v_b_1531_);
                    crate::leanh::lean_ctor_set(v___x_1555_, 2, v_bkt_1551_);
                    v_buckets_x27_1556_ =
                        lean_array_uset(v_buckets_1533_, v___x_1550_, v___x_1555_);
                    v___x_1557_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1558_ = lean_nat_mul(v_size_x27_1554_, v___x_1557_);
                    v___x_1559_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1560_ = lean_nat_div(v___x_1558_, v___x_1559_);
                    crate::leanh::lean_dec(v___x_1558_);
                    v___x_1561_ = lean_array_get_size(v_buckets_x27_1556_);
                    v___x_1562_ = lean_nat_dec_le(v___x_1560_, v___x_1561_);
                    crate::leanh::lean_dec(v___x_1560_);
                    if v___x_1562_ == 0 {
                        v_val_1563_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1___redArg(v_buckets_x27_1556_);
                        if v_isShared_1536_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1535_, 1, v_val_1563_);
                            crate::leanh::lean_ctor_set(v___x_1535_, 0, v_size_x27_1554_);
                            v___x_1565_ = v___x_1535_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1566_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1566_,
                                0,
                                v_size_x27_1554_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_val_1563_);
                            v___x_1565_ = v_reuseFailAlloc_1566_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1536_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1535_, 1, v_buckets_x27_1556_);
                            crate::leanh::lean_ctor_set(v___x_1535_, 0, v_size_x27_1554_);
                            v___x_1568_ = v___x_1535_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1569_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1569_,
                                0,
                                v_size_x27_1554_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1569_,
                                1,
                                v_buckets_x27_1556_,
                            );
                            v___x_1568_ = v_reuseFailAlloc_1569_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1551_);
                    v___x_1570_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1571_ =
                        lean_array_uset(v_buckets_1533_, v___x_1550_, v___x_1570_);
                    v___x_1572_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(v_a_1530_, v_b_1531_, v_bkt_1551_);
                    v___x_1573_ = lean_array_uset(v_buckets_x27_1571_, v___x_1550_, v___x_1572_);
                    if v_isShared_1536_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1535_, 1, v___x_1573_);
                        v___x_1575_ = v___x_1535_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1576_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_size_1532_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1573_);
                        v___x_1575_ = v_reuseFailAlloc_1576_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1565_;
            }
            3 => {
                return v___x_1568_;
            }
            4 => {
                return v___x_1575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(
    mut v_e_1578_: *mut crate::leanh::LeanObject,
    mut v_key_1579_: u64,
    mut v_a_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyToExprs_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1597_: u8 = 0;
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_unused_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1582_ = lean_st_ref_take(v_a_1580_);
                v_cache_1588_ = crate::leanh::lean_ctor_get(v___x_1582_, 0);
                crate::leanh::lean_inc_ref(v_cache_1588_);
                v_keyToExprs_1589_ = crate::leanh::lean_ctor_get(v___x_1582_, 1);
                crate::leanh::lean_inc_ref(v_keyToExprs_1589_);
                v_buckets_1590_ = crate::leanh::lean_ctor_get(v_cache_1588_, 1);
                v___x_1591_ = crate::leanh::lean_box(0);
                v___x_1592_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1593_ = lean_array_get_size(v_buckets_1590_);
                v___x_1594_ = lean_nat_dec_lt(v___x_1592_, v___x_1593_);
                if v___x_1594_ == 0 {
                    crate::leanh::lean_dec_ref(v_keyToExprs_1589_);
                    crate::leanh::lean_dec_ref(v_cache_1588_);
                    crate::leanh::lean_dec_ref(v_e_1578_);
                    v_fst_1584_ = v___x_1591_;
                    v_snd_1585_ = v___x_1582_;
                    state = 1;
                    continue;
                } else {
                    v_isSharedCheck_1603_ = (!crate::leanh::lean_is_exclusive(v___x_1582_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v_unused_1604_ = crate::leanh::lean_ctor_get(v___x_1582_, 1);
                        crate::leanh::lean_dec(v_unused_1604_);
                        v_unused_1605_ = crate::leanh::lean_ctor_get(v___x_1582_, 0);
                        crate::leanh::lean_dec(v_unused_1605_);
                        v___x_1596_ = v___x_1582_;
                        v_isShared_1597_ = v_isSharedCheck_1603_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1582_);
                        v___x_1596_ = crate::leanh::lean_box(0);
                        v_isShared_1597_ = v_isSharedCheck_1603_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1586_ = lean_st_ref_set(v_a_1580_, v_snd_1585_);
                v___x_1587_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1587_, 0, v_fst_1584_);
                return v___x_1587_;
            }
            2 => {
                v___x_1598_ = crate::leanh::lean_box_uint64(v_key_1579_);
                v___x_1599_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(v_cache_1588_, v_e_1578_, v___x_1598_);
                if v_isShared_1597_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1596_, 0, v___x_1599_);
                    v___x_1601_ = v___x_1596_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_keyToExprs_1589_);
                    v___x_1601_ = v_reuseFailAlloc_1602_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_1584_ = v___x_1591_;
                v_snd_1585_ = v___x_1601_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg___boxed(
    mut v_e_1606_: *mut crate::leanh::LeanObject,
    mut v_key_1607_: *mut crate::leanh::LeanObject,
    mut v_a_1608_: *mut crate::leanh::LeanObject,
    mut v_a_1609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_boxed_1610_: u64 = 0;
    let mut v_res_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_key_boxed_1610_ = crate::leanh::lean_unbox_uint64(v_key_1607_);
    crate::leanh::lean_dec_ref(v_key_1607_);
    v_res_1611_ =
        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(
            v_e_1606_,
            v_key_boxed_1610_,
            v_a_1608_,
        );
    crate::leanh::lean_dec(v_a_1608_);
    return v_res_1611_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(
    mut v_e_1612_: *mut crate::leanh::LeanObject,
    mut v_key_1613_: u64,
    mut v_a_1614_: u8,
    mut v_a_1615_: *mut crate::leanh::LeanObject,
    mut v_a_1616_: *mut crate::leanh::LeanObject,
    mut v_a_1617_: *mut crate::leanh::LeanObject,
    mut v_a_1618_: *mut crate::leanh::LeanObject,
    mut v_a_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ =
        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(
            v_e_1612_,
            v_key_1613_,
            v_a_1615_,
        );
    return v___x_1621_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___boxed(
    mut v_e_1622_: *mut crate::leanh::LeanObject,
    mut v_key_1623_: *mut crate::leanh::LeanObject,
    mut v_a_1624_: *mut crate::leanh::LeanObject,
    mut v_a_1625_: *mut crate::leanh::LeanObject,
    mut v_a_1626_: *mut crate::leanh::LeanObject,
    mut v_a_1627_: *mut crate::leanh::LeanObject,
    mut v_a_1628_: *mut crate::leanh::LeanObject,
    mut v_a_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_boxed_1631_: u64 = 0;
    let mut v_a_boxed_1632_: u8 = 0;
    let mut v_res_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_key_boxed_1631_ = crate::leanh::lean_unbox_uint64(v_key_1623_);
    crate::leanh::lean_dec_ref(v_key_1623_);
    v_a_boxed_1632_ = (crate::leanh::lean_unbox(v_a_1624_) as u8);
    v_res_1633_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(
        v_e_1622_,
        v_key_boxed_1631_,
        v_a_boxed_1632_,
        v_a_1625_,
        v_a_1626_,
        v_a_1627_,
        v_a_1628_,
        v_a_1629_,
    );
    crate::leanh::lean_dec(v_a_1629_);
    crate::leanh::lean_dec_ref(v_a_1628_);
    crate::leanh::lean_dec(v_a_1627_);
    crate::leanh::lean_dec_ref(v_a_1626_);
    crate::leanh::lean_dec(v_a_1625_);
    return v_res_1633_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0(
    mut v_00_u03b2_1634_: *mut crate::leanh::LeanObject,
    mut v_m_1635_: *mut crate::leanh::LeanObject,
    mut v_a_1636_: *mut crate::leanh::LeanObject,
    mut v_b_1637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(v_m_1635_, v_a_1636_, v_b_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0(
    mut v_00_u03b2_1639_: *mut crate::leanh::LeanObject,
    mut v_a_1640_: *mut crate::leanh::LeanObject,
    mut v_x_1641_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1642_: u8 = 0;
    v___x_1642_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(v_a_1640_, v_x_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___boxed(
    mut v_00_u03b2_1643_: *mut crate::leanh::LeanObject,
    mut v_a_1644_: *mut crate::leanh::LeanObject,
    mut v_x_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1646_: u8 = 0;
    let mut v_r_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0(v_00_u03b2_1643_, v_a_1644_, v_x_1645_);
    crate::leanh::lean_dec(v_x_1645_);
    crate::leanh::lean_dec_ref(v_a_1644_);
    v_r_1647_ = crate::leanh::lean_box((v_res_1646_) as usize);
    return v_r_1647_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1(
    mut v_00_u03b2_1648_: *mut crate::leanh::LeanObject,
    mut v_data_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1650_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1___redArg(v_data_1649_);
    return v___x_1650_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2(
    mut v_00_u03b2_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_b_1653_: *mut crate::leanh::LeanObject,
    mut v_x_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(v_a_1652_, v_b_1653_, v_x_1654_);
    return v___x_1655_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1656_: *mut crate::leanh::LeanObject,
    mut v_i_1657_: *mut crate::leanh::LeanObject,
    mut v_source_1658_: *mut crate::leanh::LeanObject,
    mut v_target_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2___redArg(v_i_1657_, v_source_1658_, v_target_1659_);
    return v___x_1660_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1661_: *mut crate::leanh::LeanObject,
    mut v_x_1662_: *mut crate::leanh::LeanObject,
    mut v_x_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1664_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1662_, v_x_1663_);
    return v___x_1664_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(
    mut v_e_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut v_unused_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1668_ = l_Lean_Expr_hasMVar(v_e_1665_);
                if v___x_1668_ == 0 {
                    v___x_1669_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1669_, 0, v_e_1665_);
                    return v___x_1669_;
                } else {
                    v___x_1670_ = lean_st_ref_get(v___y_1666_);
                    v_mctx_1671_ = crate::leanh::lean_ctor_get(v___x_1670_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1671_);
                    crate::leanh::lean_dec(v___x_1670_);
                    v___x_1672_ = l_Lean_instantiateMVarsCore(v_mctx_1671_, v_e_1665_);
                    v_fst_1673_ = crate::leanh::lean_ctor_get(v___x_1672_, 0);
                    crate::leanh::lean_inc(v_fst_1673_);
                    v_snd_1674_ = crate::leanh::lean_ctor_get(v___x_1672_, 1);
                    crate::leanh::lean_inc(v_snd_1674_);
                    crate::leanh::lean_dec_ref(v___x_1672_);
                    v___x_1675_ = lean_st_ref_take(v___y_1666_);
                    v_cache_1676_ = crate::leanh::lean_ctor_get(v___x_1675_, 1);
                    v_zetaDeltaFVarIds_1677_ = crate::leanh::lean_ctor_get(v___x_1675_, 2);
                    v_postponed_1678_ = crate::leanh::lean_ctor_get(v___x_1675_, 3);
                    v_diag_1679_ = crate::leanh::lean_ctor_get(v___x_1675_, 4);
                    v_isSharedCheck_1688_ = (!crate::leanh::lean_is_exclusive(v___x_1675_)) as u8;
                    if v_isSharedCheck_1688_ == 0 {
                        v_unused_1689_ = crate::leanh::lean_ctor_get(v___x_1675_, 0);
                        crate::leanh::lean_dec(v_unused_1689_);
                        v___x_1681_ = v___x_1675_;
                        v_isShared_1682_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1679_);
                        crate::leanh::lean_inc(v_postponed_1678_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1677_);
                        crate::leanh::lean_inc(v_cache_1676_);
                        crate::leanh::lean_dec(v___x_1675_);
                        v___x_1681_ = crate::leanh::lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1681_, 0, v_snd_1674_);
                    v___x_1684_ = v___x_1681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1687_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_snd_1674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_cache_1676_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1687_,
                        2,
                        v_zetaDeltaFVarIds_1677_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_postponed_1678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_diag_1679_);
                    v___x_1684_ = v_reuseFailAlloc_1687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1685_ = lean_st_ref_set(v___y_1666_, v___x_1684_);
                v___x_1686_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1686_, 0, v_fst_1673_);
                return v___x_1686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(
    mut v_e_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1690_, v___y_1691_);
    crate::leanh::lean_dec(v___y_1691_);
    return v_res_1693_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(
    mut v_e_1694_: *mut crate::leanh::LeanObject,
    mut v___y_1695_: u8,
    mut v___y_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1694_, v___y_1698_);
    return v___x_1702_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(
    mut v_e_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
    mut v___y_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_13173__boxed_1711_: u8 = 0;
    let mut v_res_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_13173__boxed_1711_ = (crate::leanh::lean_unbox(v___y_1704_) as u8);
    v_res_1712_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(v_e_1703_, v___y_13173__boxed_1711_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
    crate::leanh::lean_dec(v___y_1709_);
    crate::leanh::lean_dec_ref(v___y_1708_);
    crate::leanh::lean_dec(v___y_1707_);
    crate::leanh::lean_dec_ref(v___y_1706_);
    crate::leanh::lean_dec(v___y_1705_);
    return v_res_1712_;
}
pub unsafe fn _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0()
-> u64 {
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: u64 = 0;
    v___x_1713_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1714_ = lean_uint64_of_nat(v___x_1713_);
    return v___x_1714_;
}
pub unsafe fn _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1715_: u64 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_once
        ),
        _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0,
    );
    v___x_1716_ = crate::leanh::lean_box_uint64(v___x_1715_);
    return v___x_1716_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
    mut v_e_1721_: *mut crate::leanh::LeanObject,
    mut v_a_1722_: u8,
    mut v_a_1723_: *mut crate::leanh::LeanObject,
    mut v_a_1724_: *mut crate::leanh::LeanObject,
    mut v_a_1725_: *mut crate::leanh::LeanObject,
    mut v_a_1726_: *mut crate::leanh::LeanObject,
    mut v_a_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1732_: u8 = 0;
    let mut v___y_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: u64 = 0;
    let mut v___x_1746_: u64 = 0;
    let mut v___x_1747_: u64 = 0;
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut v_key_1754_: u64 = 0;
    let mut v___y_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut v_unused_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u64 = 0;
    let mut v___x_1793_: u64 = 0;
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut v_a_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_declName_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_1810_: u64 = 0;
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1816_: u8 = 0;
    let mut v___y_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u64 = 0;
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1829_: u8 = 0;
    let mut v___y_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut v_a_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1856_: u8 = 0;
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1860_: u8 = 0;
    let mut v_binderType_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1874_: u64 = 0;
    let mut v___x_1875_: u64 = 0;
    let mut v___x_1876_: u64 = 0;
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut v_expr_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u64 = 0;
    let mut v_idx_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v___x_1893_: u64 = 0;
    let mut v___x_1894_: u64 = 0;
    let mut v___x_1895_: u64 = 0;
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut v___x_1901_: u64 = 0;
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1774_ = lean_st_ref_get(v_a_1723_);
                v___x_1775_ =
                    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(
                        v_e_1721_,
                        v___x_1774_,
                    );
                crate::leanh::lean_dec(v___x_1774_);
                if crate::leanh::lean_obj_tag(v___x_1775_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_1721_);
                    v_val_1776_ = crate::leanh::lean_ctor_get(v___x_1775_, 0);
                    v_isSharedCheck_1783_ = (!crate::leanh::lean_is_exclusive(v___x_1775_)) as u8;
                    if v_isSharedCheck_1783_ == 0 {
                        v___x_1778_ = v___x_1775_;
                        v_isShared_1779_ = v_isSharedCheck_1783_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1776_);
                        crate::leanh::lean_dec(v___x_1775_);
                        v___x_1778_ = crate::leanh::lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_1783_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1775_);
                    match crate::leanh::lean_obj_tag(v_e_1721_) {
                        2 => {
                            crate::leanh::lean_inc_ref(v_e_1721_);
                            v___x_1784_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1721_, v_a_1725_);
                            if crate::leanh::lean_obj_tag(v___x_1784_) == 0 {
                                v_a_1785_ = crate::leanh::lean_ctor_get(v___x_1784_, 0);
                                v_isSharedCheck_1798_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1784_)) as u8;
                                if v_isSharedCheck_1798_ == 0 {
                                    v___x_1787_ = v___x_1784_;
                                    v_isShared_1788_ = v_isSharedCheck_1798_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1785_);
                                    crate::leanh::lean_dec(v___x_1784_);
                                    v___x_1787_ = crate::leanh::lean_box(0);
                                    v_isShared_1788_ = v_isSharedCheck_1798_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_1721_, 1);
                                v_a_1799_ = crate::leanh::lean_ctor_get(v___x_1784_, 0);
                                v_isSharedCheck_1806_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1784_)) as u8;
                                if v_isSharedCheck_1806_ == 0 {
                                    v___x_1801_ = v___x_1784_;
                                    v_isShared_1802_ = v_isSharedCheck_1806_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1799_);
                                    crate::leanh::lean_dec(v___x_1784_);
                                    v___x_1801_ = crate::leanh::lean_box(0);
                                    v_isShared_1802_ = v_isSharedCheck_1806_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                        4 => {
                            v_declName_1807_ = crate::leanh::lean_ctor_get(v_e_1721_, 0);
                            crate::leanh::lean_inc(v_declName_1807_);
                            crate::leanh::lean_dec_ref_known(v_e_1721_, 2);
                            if crate::leanh::lean_obj_tag(v_declName_1807_) == 0 {
                                v___x_1808_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1;
                                v___x_1809_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1809_, 0, v___x_1808_);
                                return v___x_1809_;
                            } else {
                                v_hash_1810_ = crate::leanh::lean_ctor_get_uint64(
                                    v_declName_1807_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                                        as u32,
                                );
                                crate::leanh::lean_dec(v_declName_1807_);
                                v___x_1811_ = crate::leanh::lean_box_uint64(v_hash_1810_);
                                v___x_1812_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1812_, 0, v___x_1811_);
                                return v___x_1812_;
                            }
                        }
                        5 => {
                            v___x_1813_ = l_Lean_Expr_getAppFn(v_e_1721_);
                            v___x_1848_ = l_Lean_Expr_isMVar(v___x_1813_);
                            if v___x_1848_ == 0 {
                                v___y_1829_ = v_a_1722_;
                                v___y_1830_ = v_a_1723_;
                                v___y_1831_ = v_a_1724_;
                                v___y_1832_ = v_a_1725_;
                                v___y_1833_ = v_a_1726_;
                                v___y_1834_ = v_a_1727_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_e_1721_);
                                v___x_1849_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1721_, v_a_1725_);
                                if crate::leanh::lean_obj_tag(v___x_1849_) == 0 {
                                    v_a_1850_ = crate::leanh::lean_ctor_get(v___x_1849_, 0);
                                    crate::leanh::lean_inc(v_a_1850_);
                                    crate::leanh::lean_dec_ref_known(v___x_1849_, 1);
                                    v___x_1851_ = lean_expr_eqv(v_a_1850_, v_e_1721_);
                                    if v___x_1851_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_1813_);
                                        crate::leanh::lean_dec_ref_known(v_e_1721_, 2);
                                        v_e_1721_ = v_a_1850_;
                                        state = 0;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_1850_);
                                        v___y_1829_ = v_a_1722_;
                                        v___y_1830_ = v_a_1723_;
                                        v___y_1831_ = v_a_1724_;
                                        v___y_1832_ = v_a_1725_;
                                        v___y_1833_ = v_a_1726_;
                                        v___y_1834_ = v_a_1727_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_1813_);
                                    crate::leanh::lean_dec_ref_known(v_e_1721_, 2);
                                    v_a_1853_ = crate::leanh::lean_ctor_get(v___x_1849_, 0);
                                    v_isSharedCheck_1860_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1849_)) as u8;
                                    if v_isSharedCheck_1860_ == 0 {
                                        v___x_1855_ = v___x_1849_;
                                        v_isShared_1856_ = v_isSharedCheck_1860_;
                                        state = 19;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1853_);
                                        crate::leanh::lean_dec(v___x_1849_);
                                        v___x_1855_ = crate::leanh::lean_box(0);
                                        v_isShared_1856_ = v_isSharedCheck_1860_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            }
                        }
                        6 => {
                            v_binderType_1861_ = crate::leanh::lean_ctor_get(v_e_1721_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_1861_);
                            v_body_1862_ = crate::leanh::lean_ctor_get(v_e_1721_, 2);
                            crate::leanh::lean_inc_ref(v_body_1862_);
                            crate::leanh::lean_dec_ref_known(v_e_1721_, 3);
                            v_t_1730_ = v_binderType_1861_;
                            v_b_1731_ = v_body_1862_;
                            v___y_1732_ = v_a_1722_;
                            v___y_1733_ = v_a_1723_;
                            v___y_1734_ = v_a_1724_;
                            v___y_1735_ = v_a_1725_;
                            v___y_1736_ = v_a_1726_;
                            v___y_1737_ = v_a_1727_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_binderType_1863_ = crate::leanh::lean_ctor_get(v_e_1721_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_1863_);
                            v_body_1864_ = crate::leanh::lean_ctor_get(v_e_1721_, 2);
                            crate::leanh::lean_inc_ref(v_body_1864_);
                            crate::leanh::lean_dec_ref_known(v_e_1721_, 3);
                            v_t_1730_ = v_binderType_1863_;
                            v_b_1731_ = v_body_1864_;
                            v___y_1732_ = v_a_1722_;
                            v___y_1733_ = v_a_1723_;
                            v___y_1734_ = v_a_1724_;
                            v___y_1735_ = v_a_1725_;
                            v___y_1736_ = v_a_1726_;
                            v___y_1737_ = v_a_1727_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            v_value_1865_ = crate::leanh::lean_ctor_get(v_e_1721_, 2);
                            crate::leanh::lean_inc_ref(v_value_1865_);
                            v_body_1866_ = crate::leanh::lean_ctor_get(v_e_1721_, 3);
                            crate::leanh::lean_inc_ref(v_body_1866_);
                            crate::leanh::lean_dec_ref_known(v_e_1721_, 4);
                            v___x_1867_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_value_1865_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                            if crate::leanh::lean_obj_tag(v___x_1867_) == 0 {
                                v_a_1868_ = crate::leanh::lean_ctor_get(v___x_1867_, 0);
                                crate::leanh::lean_inc(v_a_1868_);
                                crate::leanh::lean_dec_ref_known(v___x_1867_, 1);
                                v___x_1869_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_body_1866_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                                if crate::leanh::lean_obj_tag(v___x_1869_) == 0 {
                                    v_a_1870_ = crate::leanh::lean_ctor_get(v___x_1869_, 0);
                                    v_isSharedCheck_1881_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1869_)) as u8;
                                    if v_isSharedCheck_1881_ == 0 {
                                        v___x_1872_ = v___x_1869_;
                                        v_isShared_1873_ = v_isSharedCheck_1881_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1870_);
                                        crate::leanh::lean_dec(v___x_1869_);
                                        v___x_1872_ = crate::leanh::lean_box(0);
                                        v_isShared_1873_ = v_isSharedCheck_1881_;
                                        state = 21;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1868_);
                                    return v___x_1869_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_body_1866_);
                                return v___x_1867_;
                            }
                        }
                        10 => {
                            v_expr_1882_ = crate::leanh::lean_ctor_get(v_e_1721_, 1);
                            crate::leanh::lean_inc_ref(v_expr_1882_);
                            v___x_1883_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_expr_1882_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                            if crate::leanh::lean_obj_tag(v___x_1883_) == 0 {
                                v_a_1884_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                                crate::leanh::lean_inc(v_a_1884_);
                                crate::leanh::lean_dec_ref_known(v___x_1883_, 1);
                                v___x_1885_ = crate::leanh::lean_unbox_uint64(v_a_1884_);
                                crate::leanh::lean_dec(v_a_1884_);
                                v_key_1754_ = v___x_1885_;
                                v___y_1755_ = v_a_1723_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_1721_, 2);
                                return v___x_1883_;
                            }
                        }
                        11 => {
                            v_idx_1886_ = crate::leanh::lean_ctor_get(v_e_1721_, 1);
                            crate::leanh::lean_inc(v_idx_1886_);
                            v_struct_1887_ = crate::leanh::lean_ctor_get(v_e_1721_, 2);
                            crate::leanh::lean_inc_ref(v_struct_1887_);
                            crate::leanh::lean_dec_ref_known(v_e_1721_, 3);
                            v___x_1888_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_struct_1887_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                            if crate::leanh::lean_obj_tag(v___x_1888_) == 0 {
                                v_a_1889_ = crate::leanh::lean_ctor_get(v___x_1888_, 0);
                                v_isSharedCheck_1900_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1888_)) as u8;
                                if v_isSharedCheck_1900_ == 0 {
                                    v___x_1891_ = v___x_1888_;
                                    v_isShared_1892_ = v_isSharedCheck_1900_;
                                    state = 23;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1889_);
                                    crate::leanh::lean_dec(v___x_1888_);
                                    v___x_1891_ = crate::leanh::lean_box(0);
                                    v_isShared_1892_ = v_isSharedCheck_1900_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_idx_1886_);
                                return v___x_1888_;
                            }
                        }
                        _ => {
                            v___x_1901_ = l_Lean_Expr_hash(v_e_1721_);
                            crate::leanh::lean_dec_ref(v_e_1721_);
                            v___x_1902_ = crate::leanh::lean_box_uint64(v___x_1901_);
                            v___x_1903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1903_, 0, v___x_1902_);
                            return v___x_1903_;
                        }
                    }
                }
            }
            1 => {
                v___x_1738_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
                    v_t_1730_,
                    v___y_1732_,
                    v___y_1733_,
                    v___y_1734_,
                    v___y_1735_,
                    v___y_1736_,
                    v___y_1737_,
                );
                if crate::leanh::lean_obj_tag(v___x_1738_) == 0 {
                    v_a_1739_ = crate::leanh::lean_ctor_get(v___x_1738_, 0);
                    crate::leanh::lean_inc(v_a_1739_);
                    crate::leanh::lean_dec_ref_known(v___x_1738_, 1);
                    v___x_1740_ =
                        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
                            v_b_1731_,
                            v___y_1732_,
                            v___y_1733_,
                            v___y_1734_,
                            v___y_1735_,
                            v___y_1736_,
                            v___y_1737_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1740_) == 0 {
                        v_a_1741_ = crate::leanh::lean_ctor_get(v___x_1740_, 0);
                        v_isSharedCheck_1752_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1740_)) as u8;
                        if v_isSharedCheck_1752_ == 0 {
                            v___x_1743_ = v___x_1740_;
                            v_isShared_1744_ = v_isSharedCheck_1752_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1741_);
                            crate::leanh::lean_dec(v___x_1740_);
                            v___x_1743_ = crate::leanh::lean_box(0);
                            v_isShared_1744_ = v_isSharedCheck_1752_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1739_);
                        return v___x_1740_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_1731_);
                    return v___x_1738_;
                }
            }
            2 => {
                v___x_1745_ = crate::leanh::lean_unbox_uint64(v_a_1739_);
                crate::leanh::lean_dec(v_a_1739_);
                v___x_1746_ = crate::leanh::lean_unbox_uint64(v_a_1741_);
                crate::leanh::lean_dec(v_a_1741_);
                v___x_1747_ = lean_uint64_mix_hash(v___x_1745_, v___x_1746_);
                v___x_1748_ = crate::leanh::lean_box_uint64(v___x_1747_);
                if v_isShared_1744_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1743_, 0, v___x_1748_);
                    v___x_1750_ = v___x_1743_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1751_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
                    v___x_1750_ = v_reuseFailAlloc_1751_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1750_;
            }
            4 => {
                v___x_1756_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(v_e_1721_, v_key_1754_, v___y_1755_);
                if crate::leanh::lean_obj_tag(v___x_1756_) == 0 {
                    v_isSharedCheck_1764_ = (!crate::leanh::lean_is_exclusive(v___x_1756_)) as u8;
                    if v_isSharedCheck_1764_ == 0 {
                        v_unused_1765_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                        crate::leanh::lean_dec(v_unused_1765_);
                        v___x_1758_ = v___x_1756_;
                        v_isShared_1759_ = v_isSharedCheck_1764_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1756_);
                        v___x_1758_ = crate::leanh::lean_box(0);
                        v_isShared_1759_ = v_isSharedCheck_1764_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_1766_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                    v_isSharedCheck_1773_ = (!crate::leanh::lean_is_exclusive(v___x_1756_)) as u8;
                    if v_isSharedCheck_1773_ == 0 {
                        v___x_1768_ = v___x_1756_;
                        v_isShared_1769_ = v_isSharedCheck_1773_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1766_);
                        crate::leanh::lean_dec(v___x_1756_);
                        v___x_1768_ = crate::leanh::lean_box(0);
                        v_isShared_1769_ = v_isSharedCheck_1773_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1760_ = crate::leanh::lean_box_uint64(v_key_1754_);
                if v_isShared_1759_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1758_, 0, v___x_1760_);
                    v___x_1762_ = v___x_1758_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
                    v___x_1762_ = v_reuseFailAlloc_1763_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1762_;
            }
            7 => {
                if v_isShared_1769_ == 0 {
                    v___x_1771_ = v___x_1768_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
                    v___x_1771_ = v_reuseFailAlloc_1772_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1771_;
            }
            9 => {
                if v_isShared_1779_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1778_, 0);
                    v___x_1781_ = v___x_1778_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_val_1776_);
                    v___x_1781_ = v_reuseFailAlloc_1782_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1781_;
            }
            11 => {
                v___x_1789_ = lean_expr_eqv(v_a_1785_, v_e_1721_);
                if v___x_1789_ == 0 {
                    crate::leanh::lean_del_object(v___x_1787_);
                    v___x_1790_ =
                        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
                            v_a_1785_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_,
                            v_a_1727_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1790_) == 0 {
                        v_a_1791_ = crate::leanh::lean_ctor_get(v___x_1790_, 0);
                        crate::leanh::lean_inc(v_a_1791_);
                        crate::leanh::lean_dec_ref_known(v___x_1790_, 1);
                        v___x_1792_ = crate::leanh::lean_unbox_uint64(v_a_1791_);
                        crate::leanh::lean_dec(v_a_1791_);
                        v_key_1754_ = v___x_1792_;
                        v___y_1755_ = v_a_1723_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_1721_, 1);
                        return v___x_1790_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1785_);
                    v___x_1793_ = l_Lean_Expr_hash(v_e_1721_);
                    crate::leanh::lean_dec_ref_known(v_e_1721_, 1);
                    v___x_1794_ = crate::leanh::lean_box_uint64(v___x_1793_);
                    if v_isShared_1788_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1787_, 0, v___x_1794_);
                        v___x_1796_ = v___x_1787_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1797_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
                        v___x_1796_ = v_reuseFailAlloc_1797_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_1796_;
            }
            13 => {
                if v_isShared_1802_ == 0 {
                    v___x_1804_ = v___x_1801_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1805_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
                    v___x_1804_ = v_reuseFailAlloc_1805_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1804_;
            }
            15 => {
                v___x_1822_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
                    v___x_1813_,
                    v___y_1816_,
                    v___y_1817_,
                    v___y_1818_,
                    v___y_1819_,
                    v___y_1820_,
                    v___y_1821_,
                );
                if crate::leanh::lean_obj_tag(v___x_1822_) == 0 {
                    v_a_1823_ = crate::leanh::lean_ctor_get(v___x_1822_, 0);
                    crate::leanh::lean_inc(v_a_1823_);
                    crate::leanh::lean_dec_ref_known(v___x_1822_, 1);
                    v___x_1824_ = l_Lean_Expr_getAppNumArgs(v_e_1721_);
                    v___x_1825_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1826_ = crate::leanh::lean_unbox_uint64(v_a_1823_);
                    crate::leanh::lean_dec(v_a_1823_);
                    v___x_1827_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_1824_, v_e_1721_, v___x_1824_, v_info_1815_, v___x_1825_, v___x_1826_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
                    crate::leanh::lean_dec_ref(v_info_1815_);
                    crate::leanh::lean_dec_ref_known(v_e_1721_, 2);
                    crate::leanh::lean_dec(v___x_1824_);
                    return v___x_1827_;
                } else {
                    crate::leanh::lean_dec_ref(v_info_1815_);
                    crate::leanh::lean_dec_ref_known(v_e_1721_, 2);
                    return v___x_1822_;
                }
            }
            16 => {
                v___x_1835_ = l_Lean_Expr_hasLooseBVars(v___x_1813_);
                if v___x_1835_ == 0 {
                    v___x_1836_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v___x_1813_);
                    v___x_1837_ = l_Lean_Meta_getFunInfo(
                        v___x_1813_,
                        v___x_1836_,
                        v___y_1831_,
                        v___y_1832_,
                        v___y_1833_,
                        v___y_1834_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1837_) == 0 {
                        v_a_1838_ = crate::leanh::lean_ctor_get(v___x_1837_, 0);
                        crate::leanh::lean_inc(v_a_1838_);
                        crate::leanh::lean_dec_ref_known(v___x_1837_, 1);
                        v_info_1815_ = v_a_1838_;
                        v___y_1816_ = v___y_1829_;
                        v___y_1817_ = v___y_1830_;
                        v___y_1818_ = v___y_1831_;
                        v___y_1819_ = v___y_1832_;
                        v___y_1820_ = v___y_1833_;
                        v___y_1821_ = v___y_1834_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1813_);
                        crate::leanh::lean_dec_ref_known(v_e_1721_, 2);
                        v_a_1839_ = crate::leanh::lean_ctor_get(v___x_1837_, 0);
                        v_isSharedCheck_1846_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1837_)) as u8;
                        if v_isSharedCheck_1846_ == 0 {
                            v___x_1841_ = v___x_1837_;
                            v_isShared_1842_ = v_isSharedCheck_1846_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1839_);
                            crate::leanh::lean_dec(v___x_1837_);
                            v___x_1841_ = crate::leanh::lean_box(0);
                            v_isShared_1842_ = v_isSharedCheck_1846_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    v___x_1847_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2;
                    v_info_1815_ = v___x_1847_;
                    v___y_1816_ = v___y_1829_;
                    v___y_1817_ = v___y_1830_;
                    v___y_1818_ = v___y_1831_;
                    v___y_1819_ = v___y_1832_;
                    v___y_1820_ = v___y_1833_;
                    v___y_1821_ = v___y_1834_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                if v_isShared_1842_ == 0 {
                    v___x_1844_ = v___x_1841_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
                    v___x_1844_ = v_reuseFailAlloc_1845_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1844_;
            }
            19 => {
                if v_isShared_1856_ == 0 {
                    v___x_1858_ = v___x_1855_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1859_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
                    v___x_1858_ = v_reuseFailAlloc_1859_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1858_;
            }
            21 => {
                v___x_1874_ = crate::leanh::lean_unbox_uint64(v_a_1868_);
                crate::leanh::lean_dec(v_a_1868_);
                v___x_1875_ = crate::leanh::lean_unbox_uint64(v_a_1870_);
                crate::leanh::lean_dec(v_a_1870_);
                v___x_1876_ = lean_uint64_mix_hash(v___x_1874_, v___x_1875_);
                v___x_1877_ = crate::leanh::lean_box_uint64(v___x_1876_);
                if v_isShared_1873_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1872_, 0, v___x_1877_);
                    v___x_1879_ = v___x_1872_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1880_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
                    v___x_1879_ = v_reuseFailAlloc_1880_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1879_;
            }
            23 => {
                v___x_1893_ = lean_uint64_of_nat(v_idx_1886_);
                crate::leanh::lean_dec(v_idx_1886_);
                v___x_1894_ = crate::leanh::lean_unbox_uint64(v_a_1889_);
                crate::leanh::lean_dec(v_a_1889_);
                v___x_1895_ = lean_uint64_mix_hash(v___x_1893_, v___x_1894_);
                v___x_1896_ = crate::leanh::lean_box_uint64(v___x_1895_);
                if v_isShared_1892_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1891_, 0, v___x_1896_);
                    v___x_1898_ = v___x_1891_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1899_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
                    v___x_1898_ = v_reuseFailAlloc_1899_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(
    mut v___x_1904_: *mut crate::leanh::LeanObject,
    mut v_e_1905_: *mut crate::leanh::LeanObject,
    mut v_upperBound_1906_: *mut crate::leanh::LeanObject,
    mut v_info_1907_: *mut crate::leanh::LeanObject,
    mut v_a_1908_: *mut crate::leanh::LeanObject,
    mut v_b_1909_: u64,
    mut v___y_1910_: u8,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
    mut v___y_1915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1918_: u64 = 0;
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u64 = 0;
    let mut v___x_1931_: u64 = 0;
    let mut v___x_1932_: u8 = 0;
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: u8 = 0;
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u64 = 0;
    let mut v___x_1945_: u64 = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: u8 = 0;
    let mut v_isProp_1948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1932_ = lean_nat_dec_lt(v_a_1908_, v_upperBound_1906_);
                if v___x_1932_ == 0 {
                    crate::leanh::lean_dec(v_a_1908_);
                    v___x_1933_ = crate::leanh::lean_box_uint64(v_b_1909_);
                    v___x_1934_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1934_, 0, v___x_1933_);
                    return v___x_1934_;
                } else {
                    v_paramInfo_1935_ = crate::leanh::lean_ctor_get(v_info_1907_, 0);
                    v___x_1936_ = lean_array_get_size(v_paramInfo_1935_);
                    v___x_1937_ = lean_nat_dec_lt(v_a_1908_, v___x_1936_);
                    if v___x_1937_ == 0 {
                        v___x_1938_ = lean_nat_sub(v___x_1904_, v_a_1908_);
                        v___x_1939_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1940_ = lean_nat_sub(v___x_1938_, v___x_1939_);
                        crate::leanh::lean_dec(v___x_1938_);
                        v___x_1941_ = l_Lean_Expr_getRevArg_x21(v_e_1905_, v___x_1940_);
                        v___x_1942_ =
                            l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
                                v___x_1941_,
                                v___y_1910_,
                                v___y_1911_,
                                v___y_1912_,
                                v___y_1913_,
                                v___y_1914_,
                                v___y_1915_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_1942_) == 0 {
                            v_a_1943_ = crate::leanh::lean_ctor_get(v___x_1942_, 0);
                            crate::leanh::lean_inc(v_a_1943_);
                            crate::leanh::lean_dec_ref_known(v___x_1942_, 1);
                            v___x_1944_ = crate::leanh::lean_unbox_uint64(v_a_1943_);
                            crate::leanh::lean_dec(v_a_1943_);
                            v___x_1945_ = lean_uint64_mix_hash(v_b_1909_, v___x_1944_);
                            v_a_1918_ = v___x_1945_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1908_);
                            return v___x_1942_;
                        }
                    } else {
                        v___x_1946_ = lean_array_fget_borrowed(v_paramInfo_1935_, v_a_1908_);
                        v___x_1947_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_1946_);
                        if v___x_1947_ == 0 {
                            v___y_1923_ = v___x_1947_;
                            state = 2;
                            continue;
                        } else {
                            v_isProp_1948_ = crate::leanh::lean_ctor_get_uint8(
                                v___x_1946_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2)
                                    as u32,
                            );
                            if v_isProp_1948_ == 0 {
                                v___y_1923_ = v___x_1947_;
                                state = 2;
                                continue;
                            } else {
                                v_a_1918_ = v_b_1909_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1919_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1920_ = lean_nat_add(v_a_1908_, v___x_1919_);
                crate::leanh::lean_dec(v_a_1908_);
                v_a_1908_ = v___x_1920_;
                v_b_1909_ = v_a_1918_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_1923_ == 0 {
                    v_a_1918_ = v_b_1909_;
                    state = 1;
                    continue;
                } else {
                    v___x_1924_ = lean_nat_sub(v___x_1904_, v_a_1908_);
                    v___x_1925_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1926_ = lean_nat_sub(v___x_1924_, v___x_1925_);
                    crate::leanh::lean_dec(v___x_1924_);
                    v___x_1927_ = l_Lean_Expr_getRevArg_x21(v_e_1905_, v___x_1926_);
                    v___x_1928_ =
                        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
                            v___x_1927_,
                            v___y_1910_,
                            v___y_1911_,
                            v___y_1912_,
                            v___y_1913_,
                            v___y_1914_,
                            v___y_1915_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1928_) == 0 {
                        v_a_1929_ = crate::leanh::lean_ctor_get(v___x_1928_, 0);
                        crate::leanh::lean_inc(v_a_1929_);
                        crate::leanh::lean_dec_ref_known(v___x_1928_, 1);
                        v___x_1930_ = crate::leanh::lean_unbox_uint64(v_a_1929_);
                        crate::leanh::lean_dec(v_a_1929_);
                        v___x_1931_ = lean_uint64_mix_hash(v_b_1909_, v___x_1930_);
                        v_a_1918_ = v___x_1931_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_1908_);
                        return v___x_1928_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(
    mut v___x_1949_: *mut crate::leanh::LeanObject,
    mut v_e_1950_: *mut crate::leanh::LeanObject,
    mut v_upperBound_1951_: *mut crate::leanh::LeanObject,
    mut v_info_1952_: *mut crate::leanh::LeanObject,
    mut v_a_1953_: *mut crate::leanh::LeanObject,
    mut v_b_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
    mut v___y_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1962_: u64 = 0;
    let mut v___y_13205__boxed_1963_: u8 = 0;
    let mut v_res_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1962_ = crate::leanh::lean_unbox_uint64(v_b_1954_);
    crate::leanh::lean_dec_ref(v_b_1954_);
    v___y_13205__boxed_1963_ = (crate::leanh::lean_unbox(v___y_1955_) as u8);
    v_res_1964_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_1949_, v_e_1950_, v_upperBound_1951_, v_info_1952_, v_a_1953_, v_b_boxed_1962_, v___y_13205__boxed_1963_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
    crate::leanh::lean_dec(v___y_1960_);
    crate::leanh::lean_dec_ref(v___y_1959_);
    crate::leanh::lean_dec(v___y_1958_);
    crate::leanh::lean_dec_ref(v___y_1957_);
    crate::leanh::lean_dec(v___y_1956_);
    crate::leanh::lean_dec_ref(v_info_1952_);
    crate::leanh::lean_dec(v_upperBound_1951_);
    crate::leanh::lean_dec_ref(v_e_1950_);
    crate::leanh::lean_dec(v___x_1949_);
    return v_res_1964_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(
    mut v_e_1965_: *mut crate::leanh::LeanObject,
    mut v_a_1966_: *mut crate::leanh::LeanObject,
    mut v_a_1967_: *mut crate::leanh::LeanObject,
    mut v_a_1968_: *mut crate::leanh::LeanObject,
    mut v_a_1969_: *mut crate::leanh::LeanObject,
    mut v_a_1970_: *mut crate::leanh::LeanObject,
    mut v_a_1971_: *mut crate::leanh::LeanObject,
    mut v_a_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1973_: u8 = 0;
    let mut v_res_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1973_ = (crate::leanh::lean_unbox(v_a_1966_) as u8);
    v_res_1974_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
        v_e_1965_,
        v_a_boxed_1973_,
        v_a_1967_,
        v_a_1968_,
        v_a_1969_,
        v_a_1970_,
        v_a_1971_,
    );
    crate::leanh::lean_dec(v_a_1971_);
    crate::leanh::lean_dec_ref(v_a_1970_);
    crate::leanh::lean_dec(v_a_1969_);
    crate::leanh::lean_dec_ref(v_a_1968_);
    crate::leanh::lean_dec(v_a_1967_);
    return v_res_1974_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(
    mut v___x_1975_: *mut crate::leanh::LeanObject,
    mut v_e_1976_: *mut crate::leanh::LeanObject,
    mut v_upperBound_1977_: *mut crate::leanh::LeanObject,
    mut v_info_1978_: *mut crate::leanh::LeanObject,
    mut v_inst_1979_: *mut crate::leanh::LeanObject,
    mut v_R_1980_: *mut crate::leanh::LeanObject,
    mut v_a_1981_: *mut crate::leanh::LeanObject,
    mut v_b_1982_: u64,
    mut v_c_1983_: *mut crate::leanh::LeanObject,
    mut v___y_1984_: u8,
    mut v___y_1985_: *mut crate::leanh::LeanObject,
    mut v___y_1986_: *mut crate::leanh::LeanObject,
    mut v___y_1987_: *mut crate::leanh::LeanObject,
    mut v___y_1988_: *mut crate::leanh::LeanObject,
    mut v___y_1989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_1975_, v_e_1976_, v_upperBound_1977_, v_info_1978_, v_a_1981_, v_b_1982_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
    return v___x_1991_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(
    mut v___x_1992_: *mut crate::leanh::LeanObject,
    mut v_e_1993_: *mut crate::leanh::LeanObject,
    mut v_upperBound_1994_: *mut crate::leanh::LeanObject,
    mut v_info_1995_: *mut crate::leanh::LeanObject,
    mut v_inst_1996_: *mut crate::leanh::LeanObject,
    mut v_R_1997_: *mut crate::leanh::LeanObject,
    mut v_a_1998_: *mut crate::leanh::LeanObject,
    mut v_b_1999_: *mut crate::leanh::LeanObject,
    mut v_c_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
    mut v___y_2002_: *mut crate::leanh::LeanObject,
    mut v___y_2003_: *mut crate::leanh::LeanObject,
    mut v___y_2004_: *mut crate::leanh::LeanObject,
    mut v___y_2005_: *mut crate::leanh::LeanObject,
    mut v___y_2006_: *mut crate::leanh::LeanObject,
    mut v___y_2007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_2008_: u64 = 0;
    let mut v___y_13678__boxed_2009_: u8 = 0;
    let mut v_res_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2008_ = crate::leanh::lean_unbox_uint64(v_b_1999_);
    crate::leanh::lean_dec_ref(v_b_1999_);
    v___y_13678__boxed_2009_ = (crate::leanh::lean_unbox(v___y_2001_) as u8);
    v_res_2010_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(v___x_1992_, v_e_1993_, v_upperBound_1994_, v_info_1995_, v_inst_1996_, v_R_1997_, v_a_1998_, v_b_boxed_2008_, v_c_2000_, v___y_13678__boxed_2009_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
    crate::leanh::lean_dec(v___y_2006_);
    crate::leanh::lean_dec_ref(v___y_2005_);
    crate::leanh::lean_dec(v___y_2004_);
    crate::leanh::lean_dec_ref(v___y_2003_);
    crate::leanh::lean_dec(v___y_2002_);
    crate::leanh::lean_dec_ref(v_info_1995_);
    crate::leanh::lean_dec(v_upperBound_1994_);
    crate::leanh::lean_dec_ref(v_e_1993_);
    crate::leanh::lean_dec(v___x_1992_);
    return v_res_2010_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(
    mut v_a_2011_: u64,
    mut v_x_2012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: u64 = 0;
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2012_) == 0 {
                    v___x_2013_ = crate::leanh::lean_box(0);
                    return v___x_2013_;
                } else {
                    v_key_2014_ = crate::leanh::lean_ctor_get(v_x_2012_, 0);
                    v_value_2015_ = crate::leanh::lean_ctor_get(v_x_2012_, 1);
                    v_tail_2016_ = crate::leanh::lean_ctor_get(v_x_2012_, 2);
                    v___x_2017_ = crate::leanh::lean_unbox_uint64(v_key_2014_);
                    v___x_2018_ = lean_uint64_dec_eq(v___x_2017_, v_a_2011_);
                    if v___x_2018_ == 0 {
                        v_x_2012_ = v_tail_2016_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2015_);
                        v___x_2020_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2020_, 0, v_value_2015_);
                        return v___x_2020_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg___boxed(
    mut v_a_2021_: *mut crate::leanh::LeanObject,
    mut v_x_2022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2023_: u64 = 0;
    let mut v_res_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2023_ = crate::leanh::lean_unbox_uint64(v_a_2021_);
    crate::leanh::lean_dec_ref(v_a_2021_);
    v_res_2024_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_boxed_2023_, v_x_2022_);
    crate::leanh::lean_dec(v_x_2022_);
    return v_res_2024_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(
    mut v_m_2025_: *mut crate::leanh::LeanObject,
    mut v_a_2026_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: u64 = 0;
    let mut v___x_2030_: u64 = 0;
    let mut v_fold_2031_: u64 = 0;
    let mut v___x_2032_: u64 = 0;
    let mut v___x_2033_: u64 = 0;
    let mut v___x_2034_: u64 = 0;
    let mut v___x_2035_: usize = 0;
    let mut v___x_2036_: usize = 0;
    let mut v___x_2037_: usize = 0;
    let mut v___x_2038_: usize = 0;
    let mut v___x_2039_: usize = 0;
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2027_ = crate::leanh::lean_ctor_get(v_m_2025_, 1);
    v___x_2028_ = lean_array_get_size(v_buckets_2027_);
    v___x_2029_ = 32u64;
    v___x_2030_ = lean_uint64_shift_right(v_a_2026_, v___x_2029_);
    v_fold_2031_ = lean_uint64_xor(v_a_2026_, v___x_2030_);
    v___x_2032_ = 16u64;
    v___x_2033_ = lean_uint64_shift_right(v_fold_2031_, v___x_2032_);
    v___x_2034_ = lean_uint64_xor(v_fold_2031_, v___x_2033_);
    v___x_2035_ = lean_uint64_to_usize(v___x_2034_);
    v___x_2036_ = lean_usize_of_nat(v___x_2028_);
    v___x_2037_ = 1usize;
    v___x_2038_ = lean_usize_sub(v___x_2036_, v___x_2037_);
    v___x_2039_ = lean_usize_land(v___x_2035_, v___x_2038_);
    v___x_2040_ = lean_array_uget_borrowed(v_buckets_2027_, v___x_2039_);
    v___x_2041_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_2026_, v___x_2040_);
    return v___x_2041_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg___boxed(
    mut v_m_2042_: *mut crate::leanh::LeanObject,
    mut v_a_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2044_: u64 = 0;
    let mut v_res_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2044_ = crate::leanh::lean_unbox_uint64(v_a_2043_);
    crate::leanh::lean_dec_ref(v_a_2043_);
    v_res_2045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_m_2042_, v_a_boxed_2044_);
    crate::leanh::lean_dec_ref(v_m_2042_);
    return v_res_2045_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(
    mut v_k_2046_: u64,
    mut v_____do__lift_2047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyToExprs_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyToExprs_2048_ = crate::leanh::lean_ctor_get(v_____do__lift_2047_, 1);
    v___x_2049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_keyToExprs_2048_, v_k_2046_);
    return v___x_2049_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(
    mut v_k_2050_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_2052_: u64 = 0;
    let mut v_res_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_2052_ = crate::leanh::lean_unbox_uint64(v_k_2050_);
    crate::leanh::lean_dec_ref(v_k_2050_);
    v_res_2053_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(
        v_k_boxed_2052_,
        v_____do__lift_2051_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_2051_);
    return v_res_2053_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(
    mut v_00_u03b2_2054_: *mut crate::leanh::LeanObject,
    mut v_m_2055_: *mut crate::leanh::LeanObject,
    mut v_a_2056_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_m_2055_, v_a_2056_);
    return v___x_2057_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___boxed(
    mut v_00_u03b2_2058_: *mut crate::leanh::LeanObject,
    mut v_m_2059_: *mut crate::leanh::LeanObject,
    mut v_a_2060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2061_: u64 = 0;
    let mut v_res_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2061_ = crate::leanh::lean_unbox_uint64(v_a_2060_);
    crate::leanh::lean_dec_ref(v_a_2060_);
    v_res_2062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(v_00_u03b2_2058_, v_m_2059_, v_a_boxed_2061_);
    crate::leanh::lean_dec_ref(v_m_2059_);
    return v_res_2062_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0(
    mut v_00_u03b2_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: u64,
    mut v_x_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_2064_, v_x_2065_);
    return v___x_2066_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___boxed(
    mut v_00_u03b2_2067_: *mut crate::leanh::LeanObject,
    mut v_a_2068_: *mut crate::leanh::LeanObject,
    mut v_x_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2070_: u64 = 0;
    let mut v_res_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2070_ = crate::leanh::lean_unbox_uint64(v_a_2068_);
    crate::leanh::lean_dec_ref(v_a_2068_);
    v_res_2071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0(v_00_u03b2_2067_, v_a_boxed_2070_, v_x_2069_);
    crate::leanh::lean_dec(v_x_2069_);
    return v_res_2071_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(
    mut v_a_2072_: u64,
    mut v_b_2073_: *mut crate::leanh::LeanObject,
    mut v_x_2074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2081_: u64 = 0;
    let mut v___x_2082_: u8 = 0;
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2074_) == 0 {
                    crate::leanh::lean_dec(v_b_2073_);
                    return v_x_2074_;
                } else {
                    v_key_2075_ = crate::leanh::lean_ctor_get(v_x_2074_, 0);
                    v_value_2076_ = crate::leanh::lean_ctor_get(v_x_2074_, 1);
                    v_tail_2077_ = crate::leanh::lean_ctor_get(v_x_2074_, 2);
                    v_isSharedCheck_2091_ = (!crate::leanh::lean_is_exclusive(v_x_2074_)) as u8;
                    if v_isSharedCheck_2091_ == 0 {
                        v___x_2079_ = v_x_2074_;
                        v_isShared_2080_ = v_isSharedCheck_2091_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2077_);
                        crate::leanh::lean_inc(v_value_2076_);
                        crate::leanh::lean_inc(v_key_2075_);
                        crate::leanh::lean_dec(v_x_2074_);
                        v___x_2079_ = crate::leanh::lean_box(0);
                        v_isShared_2080_ = v_isSharedCheck_2091_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2081_ = crate::leanh::lean_unbox_uint64(v_key_2075_);
                v___x_2082_ = lean_uint64_dec_eq(v___x_2081_, v_a_2072_);
                if v___x_2082_ == 0 {
                    v___x_2083_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_2072_, v_b_2073_, v_tail_2077_);
                    if v_isShared_2080_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2079_, 2, v___x_2083_);
                        v___x_2085_ = v___x_2079_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2086_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_key_2075_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_value_2076_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 2, v___x_2083_);
                        v___x_2085_ = v_reuseFailAlloc_2086_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_2076_);
                    crate::leanh::lean_dec(v_key_2075_);
                    v___x_2087_ = crate::leanh::lean_box_uint64(v_a_2072_);
                    if v_isShared_2080_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2079_, 1, v_b_2073_);
                        crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2087_);
                        v___x_2089_ = v___x_2079_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2090_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_b_2073_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_tail_2077_);
                        v___x_2089_ = v_reuseFailAlloc_2090_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2085_;
            }
            3 => {
                return v___x_2089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg___boxed(
    mut v_a_2092_: *mut crate::leanh::LeanObject,
    mut v_b_2093_: *mut crate::leanh::LeanObject,
    mut v_x_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2095_: u64 = 0;
    let mut v_res_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2095_ = crate::leanh::lean_unbox_uint64(v_a_2092_);
    crate::leanh::lean_dec_ref(v_a_2092_);
    v_res_2096_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_boxed_2095_, v_b_2093_, v_x_2094_);
    return v_res_2096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_2097_: *mut crate::leanh::LeanObject,
    mut v_x_2098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: u64 = 0;
    let mut v___x_2107_: u64 = 0;
    let mut v___x_2108_: u64 = 0;
    let mut v___x_2109_: u64 = 0;
    let mut v_fold_2110_: u64 = 0;
    let mut v___x_2111_: u64 = 0;
    let mut v___x_2112_: u64 = 0;
    let mut v___x_2113_: u64 = 0;
    let mut v___x_2114_: usize = 0;
    let mut v___x_2115_: usize = 0;
    let mut v___x_2116_: usize = 0;
    let mut v___x_2117_: usize = 0;
    let mut v___x_2118_: usize = 0;
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2098_) == 0 {
                    return v_x_2097_;
                } else {
                    v_key_2099_ = crate::leanh::lean_ctor_get(v_x_2098_, 0);
                    v_value_2100_ = crate::leanh::lean_ctor_get(v_x_2098_, 1);
                    v_tail_2101_ = crate::leanh::lean_ctor_get(v_x_2098_, 2);
                    v_isSharedCheck_2125_ = (!crate::leanh::lean_is_exclusive(v_x_2098_)) as u8;
                    if v_isSharedCheck_2125_ == 0 {
                        v___x_2103_ = v_x_2098_;
                        v_isShared_2104_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2101_);
                        crate::leanh::lean_inc(v_value_2100_);
                        crate::leanh::lean_inc(v_key_2099_);
                        crate::leanh::lean_dec(v_x_2098_);
                        v___x_2103_ = crate::leanh::lean_box(0);
                        v_isShared_2104_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2105_ = lean_array_get_size(v_x_2097_);
                v___x_2106_ = 32u64;
                v___x_2107_ = crate::leanh::lean_unbox_uint64(v_key_2099_);
                v___x_2108_ = lean_uint64_shift_right(v___x_2107_, v___x_2106_);
                v___x_2109_ = crate::leanh::lean_unbox_uint64(v_key_2099_);
                v_fold_2110_ = lean_uint64_xor(v___x_2109_, v___x_2108_);
                v___x_2111_ = 16u64;
                v___x_2112_ = lean_uint64_shift_right(v_fold_2110_, v___x_2111_);
                v___x_2113_ = lean_uint64_xor(v_fold_2110_, v___x_2112_);
                v___x_2114_ = lean_uint64_to_usize(v___x_2113_);
                v___x_2115_ = lean_usize_of_nat(v___x_2105_);
                v___x_2116_ = 1usize;
                v___x_2117_ = lean_usize_sub(v___x_2115_, v___x_2116_);
                v___x_2118_ = lean_usize_land(v___x_2114_, v___x_2117_);
                v___x_2119_ = lean_array_uget_borrowed(v_x_2097_, v___x_2118_);
                crate::leanh::lean_inc(v___x_2119_);
                if v_isShared_2104_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2103_, 2, v___x_2119_);
                    v___x_2121_ = v___x_2103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2124_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_key_2099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_value_2100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 2, v___x_2119_);
                    v___x_2121_ = v_reuseFailAlloc_2124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2122_ = lean_array_uset(v_x_2097_, v___x_2118_, v___x_2121_);
                v_x_2097_ = v___x_2122_;
                v_x_2098_ = v_tail_2101_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(
    mut v_i_2126_: *mut crate::leanh::LeanObject,
    mut v_source_2127_: *mut crate::leanh::LeanObject,
    mut v_target_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u8 = 0;
    let mut v_es_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2129_ = lean_array_get_size(v_source_2127_);
                v___x_2130_ = lean_nat_dec_lt(v_i_2126_, v___x_2129_);
                if v___x_2130_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2127_);
                    crate::leanh::lean_dec(v_i_2126_);
                    return v_target_2128_;
                } else {
                    v_es_2131_ = lean_array_fget(v_source_2127_, v_i_2126_);
                    v___x_2132_ = crate::leanh::lean_box(0);
                    v_source_2133_ = lean_array_fset(v_source_2127_, v_i_2126_, v___x_2132_);
                    v_target_2134_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(v_target_2128_, v_es_2131_);
                    v___x_2135_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2136_ = lean_nat_add(v_i_2126_, v___x_2135_);
                    crate::leanh::lean_dec(v_i_2126_);
                    v_i_2126_ = v___x_2136_;
                    v_source_2127_ = v_source_2133_;
                    v_target_2128_ = v_target_2134_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(
    mut v_data_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2139_ = lean_array_get_size(v_data_2138_);
    v___x_2140_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2141_ = lean_nat_mul(v___x_2139_, v___x_2140_);
    v___x_2142_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2143_ = crate::leanh::lean_box(0);
    v___x_2144_ = lean_mk_array(v_nbuckets_2141_, v___x_2143_);
    v___x_2145_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(v___x_2142_, v_data_2138_, v___x_2144_);
    return v___x_2145_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(
    mut v_a_2146_: u64,
    mut v_x_2147_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2148_: u8 = 0;
    let mut v_key_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u64 = 0;
    let mut v___x_2152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2147_) == 0 {
                    v___x_2148_ = 0;
                    return v___x_2148_;
                } else {
                    v_key_2149_ = crate::leanh::lean_ctor_get(v_x_2147_, 0);
                    v_tail_2150_ = crate::leanh::lean_ctor_get(v_x_2147_, 2);
                    v___x_2151_ = crate::leanh::lean_unbox_uint64(v_key_2149_);
                    v___x_2152_ = lean_uint64_dec_eq(v___x_2151_, v_a_2146_);
                    if v___x_2152_ == 0 {
                        v_x_2147_ = v_tail_2150_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2152_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg___boxed(
    mut v_a_2154_: *mut crate::leanh::LeanObject,
    mut v_x_2155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2156_: u64 = 0;
    let mut v_res_2157_: u8 = 0;
    let mut v_r_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2156_ = crate::leanh::lean_unbox_uint64(v_a_2154_);
    crate::leanh::lean_dec_ref(v_a_2154_);
    v_res_2157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_boxed_2156_, v_x_2155_);
    crate::leanh::lean_dec(v_x_2155_);
    v_r_2158_ = crate::leanh::lean_box((v_res_2157_) as usize);
    return v_r_2158_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(
    mut v_m_2159_: *mut crate::leanh::LeanObject,
    mut v_a_2160_: u64,
    mut v_b_2161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2166_: u8 = 0;
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: u64 = 0;
    let mut v___x_2169_: u64 = 0;
    let mut v_fold_2170_: u64 = 0;
    let mut v___x_2171_: u64 = 0;
    let mut v___x_2172_: u64 = 0;
    let mut v___x_2173_: u64 = 0;
    let mut v___x_2174_: usize = 0;
    let mut v___x_2175_: usize = 0;
    let mut v___x_2176_: usize = 0;
    let mut v___x_2177_: usize = 0;
    let mut v___x_2178_: usize = 0;
    let mut v_bkt_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: u8 = 0;
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u8 = 0;
    let mut v_val_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2162_ = crate::leanh::lean_ctor_get(v_m_2159_, 0);
                v_buckets_2163_ = crate::leanh::lean_ctor_get(v_m_2159_, 1);
                v_isSharedCheck_2206_ = (!crate::leanh::lean_is_exclusive(v_m_2159_)) as u8;
                if v_isSharedCheck_2206_ == 0 {
                    v___x_2165_ = v_m_2159_;
                    v_isShared_2166_ = v_isSharedCheck_2206_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2163_);
                    crate::leanh::lean_inc(v_size_2162_);
                    crate::leanh::lean_dec(v_m_2159_);
                    v___x_2165_ = crate::leanh::lean_box(0);
                    v_isShared_2166_ = v_isSharedCheck_2206_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2167_ = lean_array_get_size(v_buckets_2163_);
                v___x_2168_ = 32u64;
                v___x_2169_ = lean_uint64_shift_right(v_a_2160_, v___x_2168_);
                v_fold_2170_ = lean_uint64_xor(v_a_2160_, v___x_2169_);
                v___x_2171_ = 16u64;
                v___x_2172_ = lean_uint64_shift_right(v_fold_2170_, v___x_2171_);
                v___x_2173_ = lean_uint64_xor(v_fold_2170_, v___x_2172_);
                v___x_2174_ = lean_uint64_to_usize(v___x_2173_);
                v___x_2175_ = lean_usize_of_nat(v___x_2167_);
                v___x_2176_ = 1usize;
                v___x_2177_ = lean_usize_sub(v___x_2175_, v___x_2176_);
                v___x_2178_ = lean_usize_land(v___x_2174_, v___x_2177_);
                v_bkt_2179_ = lean_array_uget_borrowed(v_buckets_2163_, v___x_2178_);
                v___x_2180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_2160_, v_bkt_2179_);
                if v___x_2180_ == 0 {
                    v___x_2181_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2182_ = lean_nat_add(v_size_2162_, v___x_2181_);
                    crate::leanh::lean_dec(v_size_2162_);
                    v___x_2183_ = crate::leanh::lean_box_uint64(v_a_2160_);
                    crate::leanh::lean_inc(v_bkt_2179_);
                    v___x_2184_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2184_, 0, v___x_2183_);
                    crate::leanh::lean_ctor_set(v___x_2184_, 1, v_b_2161_);
                    crate::leanh::lean_ctor_set(v___x_2184_, 2, v_bkt_2179_);
                    v_buckets_x27_2185_ =
                        lean_array_uset(v_buckets_2163_, v___x_2178_, v___x_2184_);
                    v___x_2186_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2187_ = lean_nat_mul(v_size_x27_2182_, v___x_2186_);
                    v___x_2188_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2189_ = lean_nat_div(v___x_2187_, v___x_2188_);
                    crate::leanh::lean_dec(v___x_2187_);
                    v___x_2190_ = lean_array_get_size(v_buckets_x27_2185_);
                    v___x_2191_ = lean_nat_dec_le(v___x_2189_, v___x_2190_);
                    crate::leanh::lean_dec(v___x_2189_);
                    if v___x_2191_ == 0 {
                        v_val_2192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(v_buckets_x27_2185_);
                        if v_isShared_2166_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2165_, 1, v_val_2192_);
                            crate::leanh::lean_ctor_set(v___x_2165_, 0, v_size_x27_2182_);
                            v___x_2194_ = v___x_2165_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2195_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2195_,
                                0,
                                v_size_x27_2182_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_val_2192_);
                            v___x_2194_ = v_reuseFailAlloc_2195_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2166_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2165_, 1, v_buckets_x27_2185_);
                            crate::leanh::lean_ctor_set(v___x_2165_, 0, v_size_x27_2182_);
                            v___x_2197_ = v___x_2165_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2198_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2198_,
                                0,
                                v_size_x27_2182_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2198_,
                                1,
                                v_buckets_x27_2185_,
                            );
                            v___x_2197_ = v_reuseFailAlloc_2198_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2179_);
                    v___x_2199_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2200_ =
                        lean_array_uset(v_buckets_2163_, v___x_2178_, v___x_2199_);
                    v___x_2201_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_2160_, v_b_2161_, v_bkt_2179_);
                    v___x_2202_ = lean_array_uset(v_buckets_x27_2200_, v___x_2178_, v___x_2201_);
                    if v_isShared_2166_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2165_, 1, v___x_2202_);
                        v___x_2204_ = v___x_2165_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2205_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_size_2162_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2202_);
                        v___x_2204_ = v_reuseFailAlloc_2205_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2194_;
            }
            3 => {
                return v___x_2197_;
            }
            4 => {
                return v___x_2204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___boxed(
    mut v_m_2207_: *mut crate::leanh::LeanObject,
    mut v_a_2208_: *mut crate::leanh::LeanObject,
    mut v_b_2209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2210_: u64 = 0;
    let mut v_res_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2210_ = crate::leanh::lean_unbox_uint64(v_a_2208_);
    crate::leanh::lean_dec_ref(v_a_2208_);
    v_res_2211_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_m_2207_, v_a_boxed_2210_, v_b_2209_);
    return v_res_2211_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(
    mut v_e_2215_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2216_: *mut crate::leanh::LeanObject,
    mut v_b_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
    mut v___y_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
    mut v___y_2221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_a_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2244_: u8 = 0;
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_2216_) == 0 {
                    crate::leanh::lean_dec_ref(v_e_2215_);
                    v___x_2223_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2223_, 0, v_b_2217_);
                    return v___x_2223_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_2217_);
                    v_head_2224_ = crate::leanh::lean_ctor_get(v_as_x27_2216_, 0);
                    v_tail_2225_ = crate::leanh::lean_ctor_get(v_as_x27_2216_, 1);
                    crate::leanh::lean_inc(v_head_2224_);
                    crate::leanh::lean_inc_ref(v_e_2215_);
                    v___x_2226_ = l_Lean_Meta_isExprDefEq(
                        v_e_2215_,
                        v_head_2224_,
                        v___y_2218_,
                        v___y_2219_,
                        v___y_2220_,
                        v___y_2221_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2226_) == 0 {
                        v_a_2227_ = crate::leanh::lean_ctor_get(v___x_2226_, 0);
                        v_isSharedCheck_2240_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2226_)) as u8;
                        if v_isSharedCheck_2240_ == 0 {
                            v___x_2229_ = v___x_2226_;
                            v_isShared_2230_ = v_isSharedCheck_2240_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2227_);
                            crate::leanh::lean_dec(v___x_2226_);
                            v___x_2229_ = crate::leanh::lean_box(0);
                            v_isShared_2230_ = v_isSharedCheck_2240_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_2215_);
                        v_a_2241_ = crate::leanh::lean_ctor_get(v___x_2226_, 0);
                        v_isSharedCheck_2248_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2226_)) as u8;
                        if v_isSharedCheck_2248_ == 0 {
                            v___x_2243_ = v___x_2226_;
                            v_isShared_2244_ = v_isSharedCheck_2248_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2241_);
                            crate::leanh::lean_dec(v___x_2226_);
                            v___x_2243_ = crate::leanh::lean_box(0);
                            v_isShared_2244_ = v_isSharedCheck_2248_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2231_ = crate::leanh::lean_box(0);
                v___x_2232_ = (crate::leanh::lean_unbox(v_a_2227_) as u8);
                crate::leanh::lean_dec(v_a_2227_);
                if v___x_2232_ == 0 {
                    crate::leanh::lean_del_object(v___x_2229_);
                    v___x_2233_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0;
                    v_as_x27_2216_ = v_tail_2225_;
                    v_b_2217_ = v___x_2233_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_2215_);
                    crate::leanh::lean_inc(v_head_2224_);
                    v___x_2235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2235_, 0, v_head_2224_);
                    v___x_2236_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2236_, 0, v___x_2235_);
                    crate::leanh::lean_ctor_set(v___x_2236_, 1, v___x_2231_);
                    if v_isShared_2230_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2229_, 0, v___x_2236_);
                        v___x_2238_ = v___x_2229_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
                        v___x_2238_ = v_reuseFailAlloc_2239_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2238_;
            }
            3 => {
                if v_isShared_2244_ == 0 {
                    v___x_2246_ = v___x_2243_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2247_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
                    v___x_2246_ = v_reuseFailAlloc_2247_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(
    mut v_e_2249_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2250_: *mut crate::leanh::LeanObject,
    mut v_b_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
    mut v___y_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2257_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(
        v_e_2249_,
        v_as_x27_2250_,
        v_b_2251_,
        v___y_2252_,
        v___y_2253_,
        v___y_2254_,
        v___y_2255_,
    );
    crate::leanh::lean_dec(v___y_2255_);
    crate::leanh::lean_dec_ref(v___y_2254_);
    crate::leanh::lean_dec(v___y_2253_);
    crate::leanh::lean_dec_ref(v___y_2252_);
    crate::leanh::lean_dec(v_as_x27_2250_);
    return v_res_2257_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_canon(
    mut v_e_2258_: *mut crate::leanh::LeanObject,
    mut v_a_2259_: u8,
    mut v_a_2260_: *mut crate::leanh::LeanObject,
    mut v_a_2261_: *mut crate::leanh::LeanObject,
    mut v_a_2262_: *mut crate::leanh::LeanObject,
    mut v_a_2263_: *mut crate::leanh::LeanObject,
    mut v_a_2264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2270_: u8 = 0;
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: u64 = 0;
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2276_: u8 = 0;
    let mut v_ctxApprox_2277_: u8 = 0;
    let mut v_quasiPatternApprox_2278_: u8 = 0;
    let mut v_constApprox_2279_: u8 = 0;
    let mut v_isDefEqStuckEx_2280_: u8 = 0;
    let mut v_unificationHints_2281_: u8 = 0;
    let mut v_proofIrrelevance_2282_: u8 = 0;
    let mut v_assignSyntheticOpaque_2283_: u8 = 0;
    let mut v_offsetCnstrs_2284_: u8 = 0;
    let mut v_etaStruct_2285_: u8 = 0;
    let mut v_univApprox_2286_: u8 = 0;
    let mut v_iota_2287_: u8 = 0;
    let mut v_beta_2288_: u8 = 0;
    let mut v_proj_2289_: u8 = 0;
    let mut v_zeta_2290_: u8 = 0;
    let mut v_zetaDelta_2291_: u8 = 0;
    let mut v_zetaUnused_2292_: u8 = 0;
    let mut v_zetaHave_2293_: u8 = 0;
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2296_: u8 = 0;
    let mut v_trackZetaDelta_2297_: u8 = 0;
    let mut v_zetaDeltaSet_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2304_: u8 = 0;
    let mut v_inTypeClassResolution_2305_: u8 = 0;
    let mut v_cacheInferType_2306_: u8 = 0;
    let mut v_config_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: u64 = 0;
    let mut v___x_2310_: u64 = 0;
    let mut v___x_2311_: u64 = 0;
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u64 = 0;
    let mut v___x_2314_: u64 = 0;
    let mut v_key_2315_: u64 = 0;
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v_fst_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2326_: u8 = 0;
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyToExprs_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2332_: u8 = 0;
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u64 = 0;
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2345_: u8 = 0;
    let mut v_val_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2350_: u8 = 0;
    let mut v_unused_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2352_: u8 = 0;
    let mut v_a_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_reuseFailAlloc_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2362_: u8 = 0;
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyToExprs_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2368_: u8 = 0;
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u64 = 0;
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut v_a_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2385_: u8 = 0;
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2258_);
                v___x_2266_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
                    v_e_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_,
                );
                if crate::leanh::lean_obj_tag(v___x_2266_) == 0 {
                    v_a_2267_ = crate::leanh::lean_ctor_get(v___x_2266_, 0);
                    v_isSharedCheck_2381_ = (!crate::leanh::lean_is_exclusive(v___x_2266_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v___x_2269_ = v___x_2266_;
                        v_isShared_2270_ = v_isSharedCheck_2381_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2267_);
                        crate::leanh::lean_dec(v___x_2266_);
                        v___x_2269_ = crate::leanh::lean_box(0);
                        v_isShared_2270_ = v_isSharedCheck_2381_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2258_);
                    v_a_2382_ = crate::leanh::lean_ctor_get(v___x_2266_, 0);
                    v_isSharedCheck_2389_ = (!crate::leanh::lean_is_exclusive(v___x_2266_)) as u8;
                    if v_isSharedCheck_2389_ == 0 {
                        v___x_2384_ = v___x_2266_;
                        v_isShared_2385_ = v_isSharedCheck_2389_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2382_);
                        crate::leanh::lean_dec(v___x_2266_);
                        v___x_2384_ = crate::leanh::lean_box(0);
                        v_isShared_2385_ = v_isSharedCheck_2389_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2271_ = lean_st_ref_get(v_a_2260_);
                v___x_2272_ = crate::leanh::lean_unbox_uint64(v_a_2267_);
                v___x_2273_ =
                    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(
                        v___x_2272_,
                        v___x_2271_,
                    );
                crate::leanh::lean_dec(v___x_2271_);
                if crate::leanh::lean_obj_tag(v___x_2273_) == 1 {
                    crate::leanh::lean_del_object(v___x_2269_);
                    v_val_2274_ = crate::leanh::lean_ctor_get(v___x_2273_, 0);
                    crate::leanh::lean_inc(v_val_2274_);
                    crate::leanh::lean_dec_ref_known(v___x_2273_, 1);
                    v___x_2275_ = l_Lean_Meta_Context_config(v_a_2261_);
                    v_foApprox_2276_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 0 as u32);
                    v_ctxApprox_2277_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 1 as u32);
                    v_quasiPatternApprox_2278_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2275_, 2 as u32);
                    v_constApprox_2279_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 3 as u32);
                    v_isDefEqStuckEx_2280_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2275_, 4 as u32);
                    v_unificationHints_2281_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2275_, 5 as u32);
                    v_proofIrrelevance_2282_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2275_, 6 as u32);
                    v_assignSyntheticOpaque_2283_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2275_, 7 as u32);
                    v_offsetCnstrs_2284_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 8 as u32);
                    v_etaStruct_2285_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 10 as u32);
                    v_univApprox_2286_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 11 as u32);
                    v_iota_2287_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 12 as u32);
                    v_beta_2288_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 13 as u32);
                    v_proj_2289_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 14 as u32);
                    v_zeta_2290_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 15 as u32);
                    v_zetaDelta_2291_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 16 as u32);
                    v_zetaUnused_2292_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 17 as u32);
                    v_zetaHave_2293_ = crate::leanh::lean_ctor_get_uint8(v___x_2275_, 18 as u32);
                    v_isSharedCheck_2362_ = (!crate::leanh::lean_is_exclusive(v___x_2275_)) as u8;
                    if v_isSharedCheck_2362_ == 0 {
                        v___x_2295_ = v___x_2275_;
                        v_isShared_2296_ = v_isSharedCheck_2362_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2275_);
                        v___x_2295_ = crate::leanh::lean_box(0);
                        v_isShared_2296_ = v_isSharedCheck_2362_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2273_);
                    v___x_2363_ = lean_st_ref_take(v_a_2260_);
                    v_cache_2364_ = crate::leanh::lean_ctor_get(v___x_2363_, 0);
                    v_keyToExprs_2365_ = crate::leanh::lean_ctor_get(v___x_2363_, 1);
                    v_isSharedCheck_2380_ = (!crate::leanh::lean_is_exclusive(v___x_2363_)) as u8;
                    if v_isSharedCheck_2380_ == 0 {
                        v___x_2367_ = v___x_2363_;
                        v_isShared_2368_ = v_isSharedCheck_2380_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_keyToExprs_2365_);
                        crate::leanh::lean_inc(v_cache_2364_);
                        crate::leanh::lean_dec(v___x_2363_);
                        v___x_2367_ = crate::leanh::lean_box(0);
                        v_isShared_2368_ = v_isSharedCheck_2380_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v_trackZetaDelta_2297_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2298_ = crate::leanh::lean_ctor_get(v_a_2261_, 1);
                v_lctx_2299_ = crate::leanh::lean_ctor_get(v_a_2261_, 2);
                v_localInstances_2300_ = crate::leanh::lean_ctor_get(v_a_2261_, 3);
                v_defEqCtx_x3f_2301_ = crate::leanh::lean_ctor_get(v_a_2261_, 4);
                v_synthPendingDepth_2302_ = crate::leanh::lean_ctor_get(v_a_2261_, 5);
                v_canUnfold_x3f_2303_ = crate::leanh::lean_ctor_get(v_a_2261_, 6);
                v_univApprox_2304_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2305_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2306_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2296_ == 0 {
                    v_config_2308_ = v___x_2295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2361_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        0 as u32,
                        v_foApprox_2276_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        1 as u32,
                        v_ctxApprox_2277_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        2 as u32,
                        v_quasiPatternApprox_2278_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        3 as u32,
                        v_constApprox_2279_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        4 as u32,
                        v_isDefEqStuckEx_2280_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        5 as u32,
                        v_unificationHints_2281_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        6 as u32,
                        v_proofIrrelevance_2282_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        7 as u32,
                        v_assignSyntheticOpaque_2283_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        8 as u32,
                        v_offsetCnstrs_2284_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        10 as u32,
                        v_etaStruct_2285_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        11 as u32,
                        v_univApprox_2286_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        12 as u32,
                        v_iota_2287_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        13 as u32,
                        v_beta_2288_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        14 as u32,
                        v_proj_2289_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        15 as u32,
                        v_zeta_2290_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        16 as u32,
                        v_zetaDelta_2291_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        17 as u32,
                        v_zetaUnused_2292_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        18 as u32,
                        v_zetaHave_2293_,
                    );
                    v_config_2308_ = v_reuseFailAlloc_2361_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(v_config_2308_, 9 as u32, v_a_2259_);
                v___x_2309_ = l_Lean_Meta_Context_configKey(v_a_2261_);
                v___x_2310_ = 3u64;
                v___x_2311_ = lean_uint64_shift_right(v___x_2309_, v___x_2310_);
                v___x_2312_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0;
                v___x_2313_ = lean_uint64_shift_left(v___x_2311_, v___x_2310_);
                v___x_2314_ = l_Lean_Meta_TransparencyMode_toUInt64(v_a_2259_);
                v_key_2315_ = lean_uint64_lor(v___x_2313_, v___x_2314_);
                v___x_2316_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2316_, 0, v_config_2308_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2316_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2315_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2303_);
                crate::leanh::lean_inc(v_synthPendingDepth_2302_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2301_);
                crate::leanh::lean_inc_ref(v_localInstances_2300_);
                crate::leanh::lean_inc_ref(v_lctx_2299_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2298_);
                v___x_2317_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2317_, 0, v___x_2316_);
                crate::leanh::lean_ctor_set(v___x_2317_, 1, v_zetaDeltaSet_2298_);
                crate::leanh::lean_ctor_set(v___x_2317_, 2, v_lctx_2299_);
                crate::leanh::lean_ctor_set(v___x_2317_, 3, v_localInstances_2300_);
                crate::leanh::lean_ctor_set(v___x_2317_, 4, v_defEqCtx_x3f_2301_);
                crate::leanh::lean_ctor_set(v___x_2317_, 5, v_synthPendingDepth_2302_);
                crate::leanh::lean_ctor_set(v___x_2317_, 6, v_canUnfold_x3f_2303_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2297_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2304_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2305_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2306_,
                );
                crate::leanh::lean_inc_ref(v_e_2258_);
                v___x_2318_ =
                    l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(
                        v_e_2258_,
                        v_val_2274_,
                        v___x_2312_,
                        v___x_2317_,
                        v_a_2262_,
                        v_a_2263_,
                        v_a_2264_,
                    );
                crate::leanh::lean_dec_ref_known(v___x_2317_, 7);
                if crate::leanh::lean_obj_tag(v___x_2318_) == 0 {
                    v_a_2319_ = crate::leanh::lean_ctor_get(v___x_2318_, 0);
                    v_isSharedCheck_2352_ = (!crate::leanh::lean_is_exclusive(v___x_2318_)) as u8;
                    if v_isSharedCheck_2352_ == 0 {
                        v___x_2321_ = v___x_2318_;
                        v_isShared_2322_ = v_isSharedCheck_2352_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2319_);
                        crate::leanh::lean_dec(v___x_2318_);
                        v___x_2321_ = crate::leanh::lean_box(0);
                        v_isShared_2322_ = v_isSharedCheck_2352_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_2274_);
                    crate::leanh::lean_dec(v_a_2267_);
                    crate::leanh::lean_dec_ref(v_e_2258_);
                    v_a_2353_ = crate::leanh::lean_ctor_get(v___x_2318_, 0);
                    v_isSharedCheck_2360_ = (!crate::leanh::lean_is_exclusive(v___x_2318_)) as u8;
                    if v_isSharedCheck_2360_ == 0 {
                        v___x_2355_ = v___x_2318_;
                        v_isShared_2356_ = v_isSharedCheck_2360_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2353_);
                        crate::leanh::lean_dec(v___x_2318_);
                        v___x_2355_ = crate::leanh::lean_box(0);
                        v_isShared_2356_ = v_isSharedCheck_2360_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_2323_ = crate::leanh::lean_ctor_get(v_a_2319_, 0);
                v_isSharedCheck_2350_ = (!crate::leanh::lean_is_exclusive(v_a_2319_)) as u8;
                if v_isSharedCheck_2350_ == 0 {
                    v_unused_2351_ = crate::leanh::lean_ctor_get(v_a_2319_, 1);
                    crate::leanh::lean_dec(v_unused_2351_);
                    v___x_2325_ = v_a_2319_;
                    v_isShared_2326_ = v_isSharedCheck_2350_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2323_);
                    crate::leanh::lean_dec(v_a_2319_);
                    v___x_2325_ = crate::leanh::lean_box(0);
                    v_isShared_2326_ = v_isSharedCheck_2350_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_fst_2323_) == 0 {
                    v___x_2327_ = lean_st_ref_take(v_a_2260_);
                    v_cache_2328_ = crate::leanh::lean_ctor_get(v___x_2327_, 0);
                    v_keyToExprs_2329_ = crate::leanh::lean_ctor_get(v___x_2327_, 1);
                    v_isSharedCheck_2345_ = (!crate::leanh::lean_is_exclusive(v___x_2327_)) as u8;
                    if v_isSharedCheck_2345_ == 0 {
                        v___x_2331_ = v___x_2327_;
                        v_isShared_2332_ = v_isSharedCheck_2345_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_keyToExprs_2329_);
                        crate::leanh::lean_inc(v_cache_2328_);
                        crate::leanh::lean_dec(v___x_2327_);
                        v___x_2331_ = crate::leanh::lean_box(0);
                        v_isShared_2332_ = v_isSharedCheck_2345_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2325_);
                    crate::leanh::lean_dec(v_val_2274_);
                    crate::leanh::lean_dec(v_a_2267_);
                    crate::leanh::lean_dec_ref(v_e_2258_);
                    v_val_2346_ = crate::leanh::lean_ctor_get(v_fst_2323_, 0);
                    crate::leanh::lean_inc(v_val_2346_);
                    crate::leanh::lean_dec_ref_known(v_fst_2323_, 1);
                    if v_isShared_2322_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2321_, 0, v_val_2346_);
                        v___x_2348_ = v___x_2321_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2349_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_val_2346_);
                        v___x_2348_ = v_reuseFailAlloc_2349_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v_e_2258_);
                if v_isShared_2326_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2325_, 1);
                    crate::leanh::lean_ctor_set(v___x_2325_, 1, v_val_2274_);
                    crate::leanh::lean_ctor_set(v___x_2325_, 0, v_e_2258_);
                    v___x_2334_ = v___x_2325_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2344_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_e_2258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_val_2274_);
                    v___x_2334_ = v_reuseFailAlloc_2344_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2335_ = crate::leanh::lean_unbox_uint64(v_a_2267_);
                crate::leanh::lean_dec(v_a_2267_);
                v___x_2336_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_keyToExprs_2329_, v___x_2335_, v___x_2334_);
                if v_isShared_2332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2331_, 1, v___x_2336_);
                    v___x_2338_ = v___x_2331_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2343_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_cache_2328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2336_);
                    v___x_2338_ = v_reuseFailAlloc_2343_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2339_ = lean_st_ref_set(v_a_2260_, v___x_2338_);
                if v_isShared_2322_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2321_, 0, v_e_2258_);
                    v___x_2341_ = v___x_2321_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_e_2258_);
                    v___x_2341_ = v_reuseFailAlloc_2342_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2341_;
            }
            10 => {
                return v___x_2348_;
            }
            11 => {
                if v_isShared_2356_ == 0 {
                    v___x_2358_ = v___x_2355_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2359_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
                    v___x_2358_ = v_reuseFailAlloc_2359_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2358_;
            }
            13 => {
                v___x_2369_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_2258_);
                v___x_2370_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2370_, 0, v_e_2258_);
                crate::leanh::lean_ctor_set(v___x_2370_, 1, v___x_2369_);
                v___x_2371_ = crate::leanh::lean_unbox_uint64(v_a_2267_);
                crate::leanh::lean_dec(v_a_2267_);
                v___x_2372_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_keyToExprs_2365_, v___x_2371_, v___x_2370_);
                if v_isShared_2368_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2367_, 1, v___x_2372_);
                    v___x_2374_ = v___x_2367_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_cache_2364_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2372_);
                    v___x_2374_ = v_reuseFailAlloc_2379_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2375_ = lean_st_ref_set(v_a_2260_, v___x_2374_);
                if v_isShared_2270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2269_, 0, v_e_2258_);
                    v___x_2377_ = v___x_2269_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2378_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_e_2258_);
                    v___x_2377_ = v_reuseFailAlloc_2378_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2377_;
            }
            16 => {
                if v_isShared_2385_ == 0 {
                    v___x_2387_ = v___x_2384_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
                    v___x_2387_ = v_reuseFailAlloc_2388_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Canonicalizer_canon___boxed(
    mut v_e_2390_: *mut crate::leanh::LeanObject,
    mut v_a_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
    mut v_a_2393_: *mut crate::leanh::LeanObject,
    mut v_a_2394_: *mut crate::leanh::LeanObject,
    mut v_a_2395_: *mut crate::leanh::LeanObject,
    mut v_a_2396_: *mut crate::leanh::LeanObject,
    mut v_a_2397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2398_: u8 = 0;
    let mut v_res_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2398_ = (crate::leanh::lean_unbox(v_a_2391_) as u8);
    v_res_2399_ = l_Lean_Meta_Canonicalizer_canon(
        v_e_2390_,
        v_a_boxed_2398_,
        v_a_2392_,
        v_a_2393_,
        v_a_2394_,
        v_a_2395_,
        v_a_2396_,
    );
    crate::leanh::lean_dec(v_a_2396_);
    crate::leanh::lean_dec_ref(v_a_2395_);
    crate::leanh::lean_dec(v_a_2394_);
    crate::leanh::lean_dec_ref(v_a_2393_);
    crate::leanh::lean_dec(v_a_2392_);
    return v_res_2399_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0(
    mut v_e_2400_: *mut crate::leanh::LeanObject,
    mut v_as_2401_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2402_: *mut crate::leanh::LeanObject,
    mut v_b_2403_: *mut crate::leanh::LeanObject,
    mut v_a_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: u8,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
    mut v___y_2409_: *mut crate::leanh::LeanObject,
    mut v___y_2410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2412_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(
        v_e_2400_,
        v_as_x27_2402_,
        v_b_2403_,
        v___y_2407_,
        v___y_2408_,
        v___y_2409_,
        v___y_2410_,
    );
    return v___x_2412_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___boxed(
    mut v_e_2413_: *mut crate::leanh::LeanObject,
    mut v_as_2414_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2415_: *mut crate::leanh::LeanObject,
    mut v_b_2416_: *mut crate::leanh::LeanObject,
    mut v_a_2417_: *mut crate::leanh::LeanObject,
    mut v___y_2418_: *mut crate::leanh::LeanObject,
    mut v___y_2419_: *mut crate::leanh::LeanObject,
    mut v___y_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
    mut v___y_2422_: *mut crate::leanh::LeanObject,
    mut v___y_2423_: *mut crate::leanh::LeanObject,
    mut v___y_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_10919__boxed_2425_: u8 = 0;
    let mut v_res_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_10919__boxed_2425_ = (crate::leanh::lean_unbox(v___y_2418_) as u8);
    v_res_2426_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0(
        v_e_2413_,
        v_as_2414_,
        v_as_x27_2415_,
        v_b_2416_,
        v_a_2417_,
        v___y_10919__boxed_2425_,
        v___y_2419_,
        v___y_2420_,
        v___y_2421_,
        v___y_2422_,
        v___y_2423_,
    );
    crate::leanh::lean_dec(v___y_2423_);
    crate::leanh::lean_dec_ref(v___y_2422_);
    crate::leanh::lean_dec(v___y_2421_);
    crate::leanh::lean_dec_ref(v___y_2420_);
    crate::leanh::lean_dec(v___y_2419_);
    crate::leanh::lean_dec(v_as_x27_2415_);
    crate::leanh::lean_dec(v_as_2414_);
    return v_res_2426_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1(
    mut v_00_u03b2_2427_: *mut crate::leanh::LeanObject,
    mut v_m_2428_: *mut crate::leanh::LeanObject,
    mut v_a_2429_: u64,
    mut v_b_2430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2431_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_m_2428_, v_a_2429_, v_b_2430_);
    return v___x_2431_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___boxed(
    mut v_00_u03b2_2432_: *mut crate::leanh::LeanObject,
    mut v_m_2433_: *mut crate::leanh::LeanObject,
    mut v_a_2434_: *mut crate::leanh::LeanObject,
    mut v_b_2435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2436_: u64 = 0;
    let mut v_res_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2436_ = crate::leanh::lean_unbox_uint64(v_a_2434_);
    crate::leanh::lean_dec_ref(v_a_2434_);
    v_res_2437_ =
        l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1(
            v_00_u03b2_2432_,
            v_m_2433_,
            v_a_boxed_2436_,
            v_b_2435_,
        );
    return v_res_2437_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1(
    mut v_00_u03b2_2438_: *mut crate::leanh::LeanObject,
    mut v_a_2439_: u64,
    mut v_x_2440_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2441_: u8 = 0;
    v___x_2441_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_2439_, v_x_2440_);
    return v___x_2441_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___boxed(
    mut v_00_u03b2_2442_: *mut crate::leanh::LeanObject,
    mut v_a_2443_: *mut crate::leanh::LeanObject,
    mut v_x_2444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2445_: u64 = 0;
    let mut v_res_2446_: u8 = 0;
    let mut v_r_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2445_ = crate::leanh::lean_unbox_uint64(v_a_2443_);
    crate::leanh::lean_dec_ref(v_a_2443_);
    v_res_2446_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1(v_00_u03b2_2442_, v_a_boxed_2445_, v_x_2444_);
    crate::leanh::lean_dec(v_x_2444_);
    v_r_2447_ = crate::leanh::lean_box((v_res_2446_) as usize);
    return v_r_2447_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2(
    mut v_00_u03b2_2448_: *mut crate::leanh::LeanObject,
    mut v_data_2449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(v_data_2449_);
    return v___x_2450_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3(
    mut v_00_u03b2_2451_: *mut crate::leanh::LeanObject,
    mut v_a_2452_: u64,
    mut v_b_2453_: *mut crate::leanh::LeanObject,
    mut v_x_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_2452_, v_b_2453_, v_x_2454_);
    return v___x_2455_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___boxed(
    mut v_00_u03b2_2456_: *mut crate::leanh::LeanObject,
    mut v_a_2457_: *mut crate::leanh::LeanObject,
    mut v_b_2458_: *mut crate::leanh::LeanObject,
    mut v_x_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2460_: u64 = 0;
    let mut v_res_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2460_ = crate::leanh::lean_unbox_uint64(v_a_2457_);
    crate::leanh::lean_dec_ref(v_a_2457_);
    v_res_2461_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3(v_00_u03b2_2456_, v_a_boxed_2460_, v_b_2458_, v_x_2459_);
    return v_res_2461_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2462_: *mut crate::leanh::LeanObject,
    mut v_i_2463_: *mut crate::leanh::LeanObject,
    mut v_source_2464_: *mut crate::leanh::LeanObject,
    mut v_target_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(v_i_2463_, v_source_2464_, v_target_2465_);
    return v___x_2466_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2467_: *mut crate::leanh::LeanObject,
    mut v_x_2468_: *mut crate::leanh::LeanObject,
    mut v_x_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2470_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2468_, v_x_2469_);
    return v___x_2470_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Canonicalizer(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_ShareCommon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default =
        _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default);
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited =
        _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited);
    l_Lean_Meta_Canonicalizer_instInhabitedState =
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState);
    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1 = _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Canonicalizer(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Canonicalizer(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_ShareCommon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_FunInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Canonicalizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Canonicalizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Canonicalizer(builtin);
}
