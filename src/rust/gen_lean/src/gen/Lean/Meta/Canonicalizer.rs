// Lean compiler output
// Module: Lean.Meta.Canonicalizer
// Imports: Lean.Util.ShareCommon Lean.Meta.FunInfo Std.Data.HashMap.Raw Init.Data.Range.Polymorphic.Iterators
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_mk_array, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_ptr_addr,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_dec_eq,
    lean_uint64_lor, lean_uint64_mix_hash, lean_uint64_of_nat, lean_uint64_shift_left,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_dec_eq,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub, lean_usize_to_uint64,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
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
pub static l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value
        ) as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value:
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
    m_fun: l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Canonicalizer_instBEqExprVisited: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value:
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
    m_fun: l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Canonicalizer_instHashableExprVisited: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Canonicalizer_instInhabitedState: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0: u64 =
    0;
pub static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2_value
) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1239_ = leanh::lean_box(0);
    v___x_1240_ = l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1;
    v___x_1241_ = l_Lean_Expr_const___override(v___x_1240_, v___x_1239_);
    return v___x_1241_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default()
-> *mut leanh::LeanObject {
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1242_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1243_ = l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default;
    return v___x_1243_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(
    mut v_a_1244_: *mut leanh::LeanObject,
    mut v_b_1245_: *mut leanh::LeanObject,
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
    mut v_a_1249_: *mut leanh::LeanObject,
    mut v_b_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1251_: u8 = 0;
    let mut v_r_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(v_a_1249_, v_b_1250_);
    leanh::lean_dec_ref(v_b_1250_);
    leanh::lean_dec_ref(v_a_1249_);
    v_r_1252_ = leanh::lean_box((v_res_1251_) as usize);
    return v_r_1252_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(
    mut v_a_1255_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: u64 = 0;
    v___x_1256_ = lean_ptr_addr(v_a_1255_);
    v___x_1257_ = lean_usize_to_uint64(v___x_1256_);
    return v___x_1257_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed(
    mut v_a_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1259_: u64 = 0;
    let mut v_r_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1259_ = l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(v_a_1258_);
    leanh::lean_dec_ref(v_a_1258_);
    v_r_1260_ = leanh::lean_box_uint64(v_res_1259_);
    return v_r_1260_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1263_ = leanh::lean_box(0);
    v___x_1264_ = leanh::lean_unsigned_to_nat(16);
    v___x_1265_ = lean_mk_array(v___x_1264_, v___x_1263_);
    return v___x_1265_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0_once),
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0,
    );
    v___x_1267_ = leanh::lean_unsigned_to_nat(0);
    v___x_1268_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1268_, 0, v___x_1267_);
    leanh::lean_ctor_set(v___x_1268_, 1, v___x_1266_);
    return v___x_1268_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1_once),
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1,
    );
    v___x_1270_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1270_, 0, v___x_1269_);
    leanh::lean_ctor_set(v___x_1270_, 1, v___x_1269_);
    return v___x_1270_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState() -> *mut leanh::LeanObject
{
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1271_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2_once),
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2,
    );
    return v___x_1271_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(
    mut v_x_1272_: *mut leanh::LeanObject,
    mut v_transparency_1273_: u8,
    mut v_s_1274_: *mut leanh::LeanObject,
    mut v_a_1275_: *mut leanh::LeanObject,
    mut v_a_1276_: *mut leanh::LeanObject,
    mut v_a_1277_: *mut leanh::LeanObject,
    mut v_a_1278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1280_ = lean_st_mk_ref(v_s_1274_);
                v___x_1281_ = leanh::lean_box((v_transparency_1273_) as usize);
                leanh::lean_inc(v_a_1278_);
                leanh::lean_inc_ref(v_a_1277_);
                leanh::lean_inc(v_a_1276_);
                leanh::lean_inc_ref(v_a_1275_);
                leanh::lean_inc(v___x_1280_);
                v___x_1282_ = leanh::lean_apply_7(
                    v_x_1272_,
                    v___x_1281_,
                    v___x_1280_,
                    v_a_1275_,
                    v_a_1276_,
                    v_a_1277_,
                    v_a_1278_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1282_) == 0 {
                    v_a_1283_ = leanh::lean_ctor_get(v___x_1282_, 0);
                    v_isSharedCheck_1291_ = (!leanh::lean_is_exclusive(v___x_1282_)) as u8;
                    if v_isSharedCheck_1291_ == 0 {
                        v___x_1285_ = v___x_1282_;
                        v_isShared_1286_ = v_isSharedCheck_1291_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1283_);
                        leanh::lean_dec(v___x_1282_);
                        v___x_1285_ = leanh::lean_box(0);
                        v_isShared_1286_ = v_isSharedCheck_1291_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1280_);
                    return v___x_1282_;
                }
            }
            1 => {
                v___x_1287_ = lean_st_ref_get(v___x_1280_);
                leanh::lean_dec(v___x_1280_);
                leanh::lean_dec(v___x_1287_);
                if v_isShared_1286_ == 0 {
                    v___x_1289_ = v___x_1285_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1290_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1283_);
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
    mut v_x_1292_: *mut leanh::LeanObject,
    mut v_transparency_1293_: *mut leanh::LeanObject,
    mut v_s_1294_: *mut leanh::LeanObject,
    mut v_a_1295_: *mut leanh::LeanObject,
    mut v_a_1296_: *mut leanh::LeanObject,
    mut v_a_1297_: *mut leanh::LeanObject,
    mut v_a_1298_: *mut leanh::LeanObject,
    mut v_a_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_transparency_boxed_1300_: u8 = 0;
    let mut v_res_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1300_ = (leanh::lean_unbox(v_transparency_1293_) as u8);
    v_res_1301_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(
        v_x_1292_,
        v_transparency_boxed_1300_,
        v_s_1294_,
        v_a_1295_,
        v_a_1296_,
        v_a_1297_,
        v_a_1298_,
    );
    leanh::lean_dec(v_a_1298_);
    leanh::lean_dec_ref(v_a_1297_);
    leanh::lean_dec(v_a_1296_);
    leanh::lean_dec_ref(v_a_1295_);
    return v_res_1301_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run_x27(
    mut v_00_u03b1_1302_: *mut leanh::LeanObject,
    mut v_x_1303_: *mut leanh::LeanObject,
    mut v_transparency_1304_: u8,
    mut v_s_1305_: *mut leanh::LeanObject,
    mut v_a_1306_: *mut leanh::LeanObject,
    mut v_a_1307_: *mut leanh::LeanObject,
    mut v_a_1308_: *mut leanh::LeanObject,
    mut v_a_1309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1312_: *mut leanh::LeanObject,
    mut v_x_1313_: *mut leanh::LeanObject,
    mut v_transparency_1314_: *mut leanh::LeanObject,
    mut v_s_1315_: *mut leanh::LeanObject,
    mut v_a_1316_: *mut leanh::LeanObject,
    mut v_a_1317_: *mut leanh::LeanObject,
    mut v_a_1318_: *mut leanh::LeanObject,
    mut v_a_1319_: *mut leanh::LeanObject,
    mut v_a_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_transparency_boxed_1321_: u8 = 0;
    let mut v_res_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1321_ = (leanh::lean_unbox(v_transparency_1314_) as u8);
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
    leanh::lean_dec(v_a_1319_);
    leanh::lean_dec_ref(v_a_1318_);
    leanh::lean_dec(v_a_1317_);
    leanh::lean_dec_ref(v_a_1316_);
    return v_res_1322_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run___redArg(
    mut v_x_1323_: *mut leanh::LeanObject,
    mut v_transparency_1324_: u8,
    mut v_s_1325_: *mut leanh::LeanObject,
    mut v_a_1326_: *mut leanh::LeanObject,
    mut v_a_1327_: *mut leanh::LeanObject,
    mut v_a_1328_: *mut leanh::LeanObject,
    mut v_a_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1337_: u8 = 0;
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v_a_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1351_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1331_ = lean_st_mk_ref(v_s_1325_);
                v___x_1332_ = leanh::lean_box((v_transparency_1324_) as usize);
                leanh::lean_inc(v_a_1329_);
                leanh::lean_inc_ref(v_a_1328_);
                leanh::lean_inc(v_a_1327_);
                leanh::lean_inc_ref(v_a_1326_);
                leanh::lean_inc(v___x_1331_);
                v___x_1333_ = leanh::lean_apply_7(
                    v_x_1323_,
                    v___x_1332_,
                    v___x_1331_,
                    v_a_1326_,
                    v_a_1327_,
                    v_a_1328_,
                    v_a_1329_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1333_) == 0 {
                    v_a_1334_ = leanh::lean_ctor_get(v___x_1333_, 0);
                    v_isSharedCheck_1343_ = (!leanh::lean_is_exclusive(v___x_1333_)) as u8;
                    if v_isSharedCheck_1343_ == 0 {
                        v___x_1336_ = v___x_1333_;
                        v_isShared_1337_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1334_);
                        leanh::lean_dec(v___x_1333_);
                        v___x_1336_ = leanh::lean_box(0);
                        v_isShared_1337_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1331_);
                    v_a_1344_ = leanh::lean_ctor_get(v___x_1333_, 0);
                    v_isSharedCheck_1351_ = (!leanh::lean_is_exclusive(v___x_1333_)) as u8;
                    if v_isSharedCheck_1351_ == 0 {
                        v___x_1346_ = v___x_1333_;
                        v_isShared_1347_ = v_isSharedCheck_1351_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1344_);
                        leanh::lean_dec(v___x_1333_);
                        v___x_1346_ = leanh::lean_box(0);
                        v_isShared_1347_ = v_isSharedCheck_1351_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1338_ = lean_st_ref_get(v___x_1331_);
                leanh::lean_dec(v___x_1331_);
                v___x_1339_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1339_, 0, v_a_1334_);
                leanh::lean_ctor_set(v___x_1339_, 1, v___x_1338_);
                if v_isShared_1337_ == 0 {
                    leanh::lean_ctor_set(v___x_1336_, 0, v___x_1339_);
                    v___x_1341_ = v___x_1336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
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
                    v_reuseFailAlloc_1350_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
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
    mut v_x_1352_: *mut leanh::LeanObject,
    mut v_transparency_1353_: *mut leanh::LeanObject,
    mut v_s_1354_: *mut leanh::LeanObject,
    mut v_a_1355_: *mut leanh::LeanObject,
    mut v_a_1356_: *mut leanh::LeanObject,
    mut v_a_1357_: *mut leanh::LeanObject,
    mut v_a_1358_: *mut leanh::LeanObject,
    mut v_a_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_transparency_boxed_1360_: u8 = 0;
    let mut v_res_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1360_ = (leanh::lean_unbox(v_transparency_1353_) as u8);
    v_res_1361_ = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(
        v_x_1352_,
        v_transparency_boxed_1360_,
        v_s_1354_,
        v_a_1355_,
        v_a_1356_,
        v_a_1357_,
        v_a_1358_,
    );
    leanh::lean_dec(v_a_1358_);
    leanh::lean_dec_ref(v_a_1357_);
    leanh::lean_dec(v_a_1356_);
    leanh::lean_dec_ref(v_a_1355_);
    return v_res_1361_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run(
    mut v_00_u03b1_1362_: *mut leanh::LeanObject,
    mut v_x_1363_: *mut leanh::LeanObject,
    mut v_transparency_1364_: u8,
    mut v_s_1365_: *mut leanh::LeanObject,
    mut v_a_1366_: *mut leanh::LeanObject,
    mut v_a_1367_: *mut leanh::LeanObject,
    mut v_a_1368_: *mut leanh::LeanObject,
    mut v_a_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1372_: *mut leanh::LeanObject,
    mut v_x_1373_: *mut leanh::LeanObject,
    mut v_transparency_1374_: *mut leanh::LeanObject,
    mut v_s_1375_: *mut leanh::LeanObject,
    mut v_a_1376_: *mut leanh::LeanObject,
    mut v_a_1377_: *mut leanh::LeanObject,
    mut v_a_1378_: *mut leanh::LeanObject,
    mut v_a_1379_: *mut leanh::LeanObject,
    mut v_a_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_transparency_boxed_1381_: u8 = 0;
    let mut v_res_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1381_ = (leanh::lean_unbox(v_transparency_1374_) as u8);
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
    leanh::lean_dec(v_a_1379_);
    leanh::lean_dec_ref(v_a_1378_);
    leanh::lean_dec(v_a_1377_);
    leanh::lean_dec_ref(v_a_1376_);
    return v_res_1382_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(
    mut v_a_1383_: *mut leanh::LeanObject,
    mut v_x_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: usize = 0;
    let mut v___x_1390_: usize = 0;
    let mut v___x_1391_: u8 = 0;
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1384_) == 0 {
                    v___x_1385_ = leanh::lean_box(0);
                    return v___x_1385_;
                } else {
                    v_key_1386_ = leanh::lean_ctor_get(v_x_1384_, 0);
                    v_value_1387_ = leanh::lean_ctor_get(v_x_1384_, 1);
                    v_tail_1388_ = leanh::lean_ctor_get(v_x_1384_, 2);
                    v___x_1389_ = lean_ptr_addr(v_key_1386_);
                    v___x_1390_ = lean_ptr_addr(v_a_1383_);
                    v___x_1391_ = lean_usize_dec_eq(v___x_1389_, v___x_1390_);
                    if v___x_1391_ == 0 {
                        v_x_1384_ = v_tail_1388_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1387_);
                        v___x_1393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1393_, 0, v_value_1387_);
                        return v___x_1393_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg___boxed(
    mut v_a_1394_: *mut leanh::LeanObject,
    mut v_x_1395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(v_a_1394_, v_x_1395_);
    leanh::lean_dec(v_x_1395_);
    leanh::lean_dec_ref(v_a_1394_);
    return v_res_1396_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(
    mut v_m_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1399_ = leanh::lean_ctor_get(v_m_1397_, 1);
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
    mut v_m_1416_: *mut leanh::LeanObject,
    mut v_a_1417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_m_1416_, v_a_1417_);
    leanh::lean_dec_ref(v_a_1417_);
    leanh::lean_dec_ref(v_m_1416_);
    return v_res_1418_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(
    mut v_e_1419_: *mut leanh::LeanObject,
    mut v_____do__lift_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cache_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: u8 = 0;
    v_cache_1421_ = leanh::lean_ctor_get(v_____do__lift_1420_, 0);
    v_buckets_1422_ = leanh::lean_ctor_get(v_cache_1421_, 1);
    v___x_1423_ = leanh::lean_unsigned_to_nat(0);
    v___x_1424_ = lean_array_get_size(v_buckets_1422_);
    v___x_1425_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
    if v___x_1425_ == 0 {
        let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1426_ = leanh::lean_box(0);
        return v___x_1426_;
    } else {
        let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1427_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_cache_1421_, v_e_1419_);
        return v___x_1427_;
    }
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(
    mut v_e_1428_: *mut leanh::LeanObject,
    mut v_____do__lift_1429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1430_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(
        v_e_1428_,
        v_____do__lift_1429_,
    );
    leanh::lean_dec_ref(v_____do__lift_1429_);
    leanh::lean_dec_ref(v_e_1428_);
    return v_res_1430_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(
    mut v_00_u03b2_1431_: *mut leanh::LeanObject,
    mut v_m_1432_: *mut leanh::LeanObject,
    mut v_a_1433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_m_1432_, v_a_1433_);
    return v___x_1434_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___boxed(
    mut v_00_u03b2_1435_: *mut leanh::LeanObject,
    mut v_m_1436_: *mut leanh::LeanObject,
    mut v_a_1437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(v_00_u03b2_1435_, v_m_1436_, v_a_1437_);
    leanh::lean_dec_ref(v_a_1437_);
    leanh::lean_dec_ref(v_m_1436_);
    return v_res_1438_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0(
    mut v_00_u03b2_1439_: *mut leanh::LeanObject,
    mut v_a_1440_: *mut leanh::LeanObject,
    mut v_x_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(v_a_1440_, v_x_1441_);
    return v___x_1442_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___boxed(
    mut v_00_u03b2_1443_: *mut leanh::LeanObject,
    mut v_a_1444_: *mut leanh::LeanObject,
    mut v_x_1445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1446_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0(v_00_u03b2_1443_, v_a_1444_, v_x_1445_);
    leanh::lean_dec(v_x_1445_);
    leanh::lean_dec_ref(v_a_1444_);
    return v_res_1446_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(
    mut v_a_1447_: *mut leanh::LeanObject,
    mut v_x_1448_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1449_: u8 = 0;
    let mut v_key_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: usize = 0;
    let mut v___x_1453_: usize = 0;
    let mut v___x_1454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1448_) == 0 {
                    v___x_1449_ = 0;
                    return v___x_1449_;
                } else {
                    v_key_1450_ = leanh::lean_ctor_get(v_x_1448_, 0);
                    v_tail_1451_ = leanh::lean_ctor_get(v_x_1448_, 2);
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
    mut v_a_1456_: *mut leanh::LeanObject,
    mut v_x_1457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1458_: u8 = 0;
    let mut v_r_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(v_a_1456_, v_x_1457_);
    leanh::lean_dec(v_x_1457_);
    leanh::lean_dec_ref(v_a_1456_);
    v_r_1459_ = leanh::lean_box((v_res_1458_) as usize);
    return v_r_1459_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1460_: *mut leanh::LeanObject,
    mut v_x_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1467_: u8 = 0;
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1461_) == 0 {
                    return v_x_1460_;
                } else {
                    v_key_1462_ = leanh::lean_ctor_get(v_x_1461_, 0);
                    v_value_1463_ = leanh::lean_ctor_get(v_x_1461_, 1);
                    v_tail_1464_ = leanh::lean_ctor_get(v_x_1461_, 2);
                    v_isSharedCheck_1488_ = (!leanh::lean_is_exclusive(v_x_1461_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v___x_1466_ = v_x_1461_;
                        v_isShared_1467_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1464_);
                        leanh::lean_inc(v_value_1463_);
                        leanh::lean_inc(v_key_1462_);
                        leanh::lean_dec(v_x_1461_);
                        v___x_1466_ = leanh::lean_box(0);
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
                leanh::lean_inc(v___x_1482_);
                if v_isShared_1467_ == 0 {
                    leanh::lean_ctor_set(v___x_1466_, 2, v___x_1482_);
                    v___x_1484_ = v___x_1466_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_key_1462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_value_1463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 2, v___x_1482_);
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
    mut v_i_1489_: *mut leanh::LeanObject,
    mut v_source_1490_: *mut leanh::LeanObject,
    mut v_target_1491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v_es_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1492_ = lean_array_get_size(v_source_1490_);
                v___x_1493_ = lean_nat_dec_lt(v_i_1489_, v___x_1492_);
                if v___x_1493_ == 0 {
                    leanh::lean_dec_ref(v_source_1490_);
                    leanh::lean_dec(v_i_1489_);
                    return v_target_1491_;
                } else {
                    v_es_1494_ = lean_array_fget(v_source_1490_, v_i_1489_);
                    v___x_1495_ = leanh::lean_box(0);
                    v_source_1496_ = lean_array_fset(v_source_1490_, v_i_1489_, v___x_1495_);
                    v_target_1497_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1491_, v_es_1494_);
                    v___x_1498_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1499_ = lean_nat_add(v_i_1489_, v___x_1498_);
                    leanh::lean_dec(v_i_1489_);
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
    mut v_data_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = lean_array_get_size(v_data_1501_);
    v___x_1503_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1504_ = lean_nat_mul(v___x_1502_, v___x_1503_);
    v___x_1505_ = leanh::lean_unsigned_to_nat(0);
    v___x_1506_ = leanh::lean_box(0);
    v___x_1507_ = lean_mk_array(v_nbuckets_1504_, v___x_1506_);
    v___x_1508_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2___redArg(v___x_1505_, v_data_1501_, v___x_1507_);
    return v___x_1508_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(
    mut v_a_1509_: *mut leanh::LeanObject,
    mut v_b_1510_: *mut leanh::LeanObject,
    mut v_x_1511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1517_: u8 = 0;
    let mut v___x_1518_: usize = 0;
    let mut v___x_1519_: usize = 0;
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1511_) == 0 {
                    leanh::lean_dec(v_b_1510_);
                    leanh::lean_dec_ref(v_a_1509_);
                    return v_x_1511_;
                } else {
                    v_key_1512_ = leanh::lean_ctor_get(v_x_1511_, 0);
                    v_value_1513_ = leanh::lean_ctor_get(v_x_1511_, 1);
                    v_tail_1514_ = leanh::lean_ctor_get(v_x_1511_, 2);
                    v_isSharedCheck_1528_ = (!leanh::lean_is_exclusive(v_x_1511_)) as u8;
                    if v_isSharedCheck_1528_ == 0 {
                        v___x_1516_ = v_x_1511_;
                        v_isShared_1517_ = v_isSharedCheck_1528_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1514_);
                        leanh::lean_inc(v_value_1513_);
                        leanh::lean_inc(v_key_1512_);
                        leanh::lean_dec(v_x_1511_);
                        v___x_1516_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_1516_, 2, v___x_1521_);
                        v___x_1523_ = v___x_1516_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1524_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_key_1512_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_value_1513_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 2, v___x_1521_);
                        v___x_1523_ = v_reuseFailAlloc_1524_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1513_);
                    leanh::lean_dec(v_key_1512_);
                    if v_isShared_1517_ == 0 {
                        leanh::lean_ctor_set(v___x_1516_, 1, v_b_1510_);
                        leanh::lean_ctor_set(v___x_1516_, 0, v_a_1509_);
                        v___x_1526_ = v___x_1516_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1527_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1509_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_b_1510_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_tail_1514_);
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
    mut v_m_1529_: *mut leanh::LeanObject,
    mut v_a_1530_: *mut leanh::LeanObject,
    mut v_b_1531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v_val_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1532_ = leanh::lean_ctor_get(v_m_1529_, 0);
                v_buckets_1533_ = leanh::lean_ctor_get(v_m_1529_, 1);
                v_isSharedCheck_1577_ = (!leanh::lean_is_exclusive(v_m_1529_)) as u8;
                if v_isSharedCheck_1577_ == 0 {
                    v___x_1535_ = v_m_1529_;
                    v_isShared_1536_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1533_);
                    leanh::lean_inc(v_size_1532_);
                    leanh::lean_dec(v_m_1529_);
                    v___x_1535_ = leanh::lean_box(0);
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
                    v___x_1553_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1554_ = lean_nat_add(v_size_1532_, v___x_1553_);
                    leanh::lean_dec(v_size_1532_);
                    leanh::lean_inc(v_bkt_1551_);
                    v___x_1555_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1555_, 0, v_a_1530_);
                    leanh::lean_ctor_set(v___x_1555_, 1, v_b_1531_);
                    leanh::lean_ctor_set(v___x_1555_, 2, v_bkt_1551_);
                    v_buckets_x27_1556_ =
                        lean_array_uset(v_buckets_1533_, v___x_1550_, v___x_1555_);
                    v___x_1557_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1558_ = lean_nat_mul(v_size_x27_1554_, v___x_1557_);
                    v___x_1559_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1560_ = lean_nat_div(v___x_1558_, v___x_1559_);
                    leanh::lean_dec(v___x_1558_);
                    v___x_1561_ = lean_array_get_size(v_buckets_x27_1556_);
                    v___x_1562_ = lean_nat_dec_le(v___x_1560_, v___x_1561_);
                    leanh::lean_dec(v___x_1560_);
                    if v___x_1562_ == 0 {
                        v_val_1563_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1___redArg(v_buckets_x27_1556_);
                        if v_isShared_1536_ == 0 {
                            leanh::lean_ctor_set(v___x_1535_, 1, v_val_1563_);
                            leanh::lean_ctor_set(v___x_1535_, 0, v_size_x27_1554_);
                            v___x_1565_ = v___x_1535_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1566_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1566_,
                                0,
                                v_size_x27_1554_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_val_1563_);
                            v___x_1565_ = v_reuseFailAlloc_1566_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1536_ == 0 {
                            leanh::lean_ctor_set(v___x_1535_, 1, v_buckets_x27_1556_);
                            leanh::lean_ctor_set(v___x_1535_, 0, v_size_x27_1554_);
                            v___x_1568_ = v___x_1535_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1569_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1569_,
                                0,
                                v_size_x27_1554_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_1551_);
                    v___x_1570_ = leanh::lean_box(0);
                    v_buckets_x27_1571_ =
                        lean_array_uset(v_buckets_1533_, v___x_1550_, v___x_1570_);
                    v___x_1572_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(v_a_1530_, v_b_1531_, v_bkt_1551_);
                    v___x_1573_ = lean_array_uset(v_buckets_x27_1571_, v___x_1550_, v___x_1572_);
                    if v_isShared_1536_ == 0 {
                        leanh::lean_ctor_set(v___x_1535_, 1, v___x_1573_);
                        v___x_1575_ = v___x_1535_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1576_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_size_1532_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1573_);
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
    mut v_e_1578_: *mut leanh::LeanObject,
    mut v_key_1579_: u64,
    mut v_a_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyToExprs_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1597_: u8 = 0;
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_unused_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1582_ = lean_st_ref_take(v_a_1580_);
                v_cache_1588_ = leanh::lean_ctor_get(v___x_1582_, 0);
                leanh::lean_inc_ref(v_cache_1588_);
                v_keyToExprs_1589_ = leanh::lean_ctor_get(v___x_1582_, 1);
                leanh::lean_inc_ref(v_keyToExprs_1589_);
                v_buckets_1590_ = leanh::lean_ctor_get(v_cache_1588_, 1);
                v___x_1591_ = leanh::lean_box(0);
                v___x_1592_ = leanh::lean_unsigned_to_nat(0);
                v___x_1593_ = lean_array_get_size(v_buckets_1590_);
                v___x_1594_ = lean_nat_dec_lt(v___x_1592_, v___x_1593_);
                if v___x_1594_ == 0 {
                    leanh::lean_dec_ref(v_keyToExprs_1589_);
                    leanh::lean_dec_ref(v_cache_1588_);
                    leanh::lean_dec_ref(v_e_1578_);
                    v_fst_1584_ = v___x_1591_;
                    v_snd_1585_ = v___x_1582_;
                    state = 1;
                    continue;
                } else {
                    v_isSharedCheck_1603_ = (!leanh::lean_is_exclusive(v___x_1582_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v_unused_1604_ = leanh::lean_ctor_get(v___x_1582_, 1);
                        leanh::lean_dec(v_unused_1604_);
                        v_unused_1605_ = leanh::lean_ctor_get(v___x_1582_, 0);
                        leanh::lean_dec(v_unused_1605_);
                        v___x_1596_ = v___x_1582_;
                        v_isShared_1597_ = v_isSharedCheck_1603_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1582_);
                        v___x_1596_ = leanh::lean_box(0);
                        v_isShared_1597_ = v_isSharedCheck_1603_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1586_ = lean_st_ref_set(v_a_1580_, v_snd_1585_);
                v___x_1587_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1587_, 0, v_fst_1584_);
                return v___x_1587_;
            }
            2 => {
                v___x_1598_ = leanh::lean_box_uint64(v_key_1579_);
                v___x_1599_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(v_cache_1588_, v_e_1578_, v___x_1598_);
                if v_isShared_1597_ == 0 {
                    leanh::lean_ctor_set(v___x_1596_, 0, v___x_1599_);
                    v___x_1601_ = v___x_1596_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_keyToExprs_1589_);
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
    mut v_e_1606_: *mut leanh::LeanObject,
    mut v_key_1607_: *mut leanh::LeanObject,
    mut v_a_1608_: *mut leanh::LeanObject,
    mut v_a_1609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_boxed_1610_: u64 = 0;
    let mut v_res_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_key_boxed_1610_ = leanh::lean_unbox_uint64(v_key_1607_);
    leanh::lean_dec_ref(v_key_1607_);
    v_res_1611_ =
        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(
            v_e_1606_,
            v_key_boxed_1610_,
            v_a_1608_,
        );
    leanh::lean_dec(v_a_1608_);
    return v_res_1611_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(
    mut v_e_1612_: *mut leanh::LeanObject,
    mut v_key_1613_: u64,
    mut v_a_1614_: u8,
    mut v_a_1615_: *mut leanh::LeanObject,
    mut v_a_1616_: *mut leanh::LeanObject,
    mut v_a_1617_: *mut leanh::LeanObject,
    mut v_a_1618_: *mut leanh::LeanObject,
    mut v_a_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ =
        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(
            v_e_1612_,
            v_key_1613_,
            v_a_1615_,
        );
    return v___x_1621_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___boxed(
    mut v_e_1622_: *mut leanh::LeanObject,
    mut v_key_1623_: *mut leanh::LeanObject,
    mut v_a_1624_: *mut leanh::LeanObject,
    mut v_a_1625_: *mut leanh::LeanObject,
    mut v_a_1626_: *mut leanh::LeanObject,
    mut v_a_1627_: *mut leanh::LeanObject,
    mut v_a_1628_: *mut leanh::LeanObject,
    mut v_a_1629_: *mut leanh::LeanObject,
    mut v_a_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_boxed_1631_: u64 = 0;
    let mut v_a_boxed_1632_: u8 = 0;
    let mut v_res_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_key_boxed_1631_ = leanh::lean_unbox_uint64(v_key_1623_);
    leanh::lean_dec_ref(v_key_1623_);
    v_a_boxed_1632_ = (leanh::lean_unbox(v_a_1624_) as u8);
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
    leanh::lean_dec(v_a_1629_);
    leanh::lean_dec_ref(v_a_1628_);
    leanh::lean_dec(v_a_1627_);
    leanh::lean_dec_ref(v_a_1626_);
    leanh::lean_dec(v_a_1625_);
    return v_res_1633_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0(
    mut v_00_u03b2_1634_: *mut leanh::LeanObject,
    mut v_m_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
    mut v_b_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(v_m_1635_, v_a_1636_, v_b_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0(
    mut v_00_u03b2_1639_: *mut leanh::LeanObject,
    mut v_a_1640_: *mut leanh::LeanObject,
    mut v_x_1641_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1642_: u8 = 0;
    v___x_1642_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(v_a_1640_, v_x_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___boxed(
    mut v_00_u03b2_1643_: *mut leanh::LeanObject,
    mut v_a_1644_: *mut leanh::LeanObject,
    mut v_x_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1646_: u8 = 0;
    let mut v_r_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0(v_00_u03b2_1643_, v_a_1644_, v_x_1645_);
    leanh::lean_dec(v_x_1645_);
    leanh::lean_dec_ref(v_a_1644_);
    v_r_1647_ = leanh::lean_box((v_res_1646_) as usize);
    return v_r_1647_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1(
    mut v_00_u03b2_1648_: *mut leanh::LeanObject,
    mut v_data_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1650_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1___redArg(v_data_1649_);
    return v___x_1650_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2(
    mut v_00_u03b2_1651_: *mut leanh::LeanObject,
    mut v_a_1652_: *mut leanh::LeanObject,
    mut v_b_1653_: *mut leanh::LeanObject,
    mut v_x_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(v_a_1652_, v_b_1653_, v_x_1654_);
    return v___x_1655_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1656_: *mut leanh::LeanObject,
    mut v_i_1657_: *mut leanh::LeanObject,
    mut v_source_1658_: *mut leanh::LeanObject,
    mut v_target_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2___redArg(v_i_1657_, v_source_1658_, v_target_1659_);
    return v___x_1660_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1661_: *mut leanh::LeanObject,
    mut v_x_1662_: *mut leanh::LeanObject,
    mut v_x_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1664_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1662_, v_x_1663_);
    return v___x_1664_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(
    mut v_e_1665_: *mut leanh::LeanObject,
    mut v___y_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut v_unused_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1668_ = l_Lean_Expr_hasMVar(v_e_1665_);
                if v___x_1668_ == 0 {
                    v___x_1669_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1669_, 0, v_e_1665_);
                    return v___x_1669_;
                } else {
                    v___x_1670_ = lean_st_ref_get(v___y_1666_);
                    v_mctx_1671_ = leanh::lean_ctor_get(v___x_1670_, 0);
                    leanh::lean_inc_ref(v_mctx_1671_);
                    leanh::lean_dec(v___x_1670_);
                    v___x_1672_ = l_Lean_instantiateMVarsCore(v_mctx_1671_, v_e_1665_);
                    v_fst_1673_ = leanh::lean_ctor_get(v___x_1672_, 0);
                    leanh::lean_inc(v_fst_1673_);
                    v_snd_1674_ = leanh::lean_ctor_get(v___x_1672_, 1);
                    leanh::lean_inc(v_snd_1674_);
                    leanh::lean_dec_ref(v___x_1672_);
                    v___x_1675_ = lean_st_ref_take(v___y_1666_);
                    v_cache_1676_ = leanh::lean_ctor_get(v___x_1675_, 1);
                    v_zetaDeltaFVarIds_1677_ = leanh::lean_ctor_get(v___x_1675_, 2);
                    v_postponed_1678_ = leanh::lean_ctor_get(v___x_1675_, 3);
                    v_diag_1679_ = leanh::lean_ctor_get(v___x_1675_, 4);
                    v_isSharedCheck_1688_ = (!leanh::lean_is_exclusive(v___x_1675_)) as u8;
                    if v_isSharedCheck_1688_ == 0 {
                        v_unused_1689_ = leanh::lean_ctor_get(v___x_1675_, 0);
                        leanh::lean_dec(v_unused_1689_);
                        v___x_1681_ = v___x_1675_;
                        v_isShared_1682_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1679_);
                        leanh::lean_inc(v_postponed_1678_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1677_);
                        leanh::lean_inc(v_cache_1676_);
                        leanh::lean_dec(v___x_1675_);
                        v___x_1681_ = leanh::lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1682_ == 0 {
                    leanh::lean_ctor_set(v___x_1681_, 0, v_snd_1674_);
                    v___x_1684_ = v___x_1681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1687_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_snd_1674_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_cache_1676_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1687_,
                        2,
                        v_zetaDeltaFVarIds_1677_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_postponed_1678_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_diag_1679_);
                    v___x_1684_ = v_reuseFailAlloc_1687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1685_ = lean_st_ref_set(v___y_1666_, v___x_1684_);
                v___x_1686_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1686_, 0, v_fst_1673_);
                return v___x_1686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(
    mut v_e_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
    mut v___y_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1690_, v___y_1691_);
    leanh::lean_dec(v___y_1691_);
    return v_res_1693_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(
    mut v_e_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: u8,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
    mut v___y_1699_: *mut leanh::LeanObject,
    mut v___y_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1694_, v___y_1698_);
    return v___x_1702_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(
    mut v_e_1703_: *mut leanh::LeanObject,
    mut v___y_1704_: *mut leanh::LeanObject,
    mut v___y_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
    mut v___y_1708_: *mut leanh::LeanObject,
    mut v___y_1709_: *mut leanh::LeanObject,
    mut v___y_1710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_13173__boxed_1711_: u8 = 0;
    let mut v_res_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_13173__boxed_1711_ = (leanh::lean_unbox(v___y_1704_) as u8);
    v_res_1712_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(v_e_1703_, v___y_13173__boxed_1711_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
    leanh::lean_dec(v___y_1709_);
    leanh::lean_dec_ref(v___y_1708_);
    leanh::lean_dec(v___y_1707_);
    leanh::lean_dec_ref(v___y_1706_);
    leanh::lean_dec(v___y_1705_);
    return v_res_1712_;
}
pub unsafe fn _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0()
-> u64 {
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: u64 = 0;
    v___x_1713_ = leanh::lean_unsigned_to_nat(1723);
    v___x_1714_ = lean_uint64_of_nat(v___x_1713_);
    return v___x_1714_;
}
pub unsafe fn _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_1715_: u64 = 0;
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_once
        ),
        _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0,
    );
    v___x_1716_ = leanh::lean_box_uint64(v___x_1715_);
    return v___x_1716_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
    mut v_e_1721_: *mut leanh::LeanObject,
    mut v_a_1722_: u8,
    mut v_a_1723_: *mut leanh::LeanObject,
    mut v_a_1724_: *mut leanh::LeanObject,
    mut v_a_1725_: *mut leanh::LeanObject,
    mut v_a_1726_: *mut leanh::LeanObject,
    mut v_a_1727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1732_: u8 = 0;
    let mut v___y_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: u64 = 0;
    let mut v___x_1746_: u64 = 0;
    let mut v___x_1747_: u64 = 0;
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut v_key_1754_: u64 = 0;
    let mut v___y_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut v_unused_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u64 = 0;
    let mut v___x_1793_: u64 = 0;
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut v_a_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_declName_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_1810_: u64 = 0;
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1816_: u8 = 0;
    let mut v___y_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u64 = 0;
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1829_: u8 = 0;
    let mut v___y_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut v_a_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1856_: u8 = 0;
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1860_: u8 = 0;
    let mut v_binderType_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1874_: u64 = 0;
    let mut v___x_1875_: u64 = 0;
    let mut v___x_1876_: u64 = 0;
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut v_expr_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u64 = 0;
    let mut v_idx_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v___x_1893_: u64 = 0;
    let mut v___x_1894_: u64 = 0;
    let mut v___x_1895_: u64 = 0;
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut v___x_1901_: u64 = 0;
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                leanh::lean_dec(v___x_1774_);
                if leanh::lean_obj_tag(v___x_1775_) == 1 {
                    leanh::lean_dec_ref(v_e_1721_);
                    v_val_1776_ = leanh::lean_ctor_get(v___x_1775_, 0);
                    v_isSharedCheck_1783_ = (!leanh::lean_is_exclusive(v___x_1775_)) as u8;
                    if v_isSharedCheck_1783_ == 0 {
                        v___x_1778_ = v___x_1775_;
                        v_isShared_1779_ = v_isSharedCheck_1783_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1776_);
                        leanh::lean_dec(v___x_1775_);
                        v___x_1778_ = leanh::lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_1783_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1775_);
                    match leanh::lean_obj_tag(v_e_1721_) {
                        2 => {
                            leanh::lean_inc_ref(v_e_1721_);
                            v___x_1784_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1721_, v_a_1725_);
                            if leanh::lean_obj_tag(v___x_1784_) == 0 {
                                v_a_1785_ = leanh::lean_ctor_get(v___x_1784_, 0);
                                v_isSharedCheck_1798_ =
                                    (!leanh::lean_is_exclusive(v___x_1784_)) as u8;
                                if v_isSharedCheck_1798_ == 0 {
                                    v___x_1787_ = v___x_1784_;
                                    v_isShared_1788_ = v_isSharedCheck_1798_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1785_);
                                    leanh::lean_dec(v___x_1784_);
                                    v___x_1787_ = leanh::lean_box(0);
                                    v_isShared_1788_ = v_isSharedCheck_1798_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_e_1721_, 1);
                                v_a_1799_ = leanh::lean_ctor_get(v___x_1784_, 0);
                                v_isSharedCheck_1806_ =
                                    (!leanh::lean_is_exclusive(v___x_1784_)) as u8;
                                if v_isSharedCheck_1806_ == 0 {
                                    v___x_1801_ = v___x_1784_;
                                    v_isShared_1802_ = v_isSharedCheck_1806_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1799_);
                                    leanh::lean_dec(v___x_1784_);
                                    v___x_1801_ = leanh::lean_box(0);
                                    v_isShared_1802_ = v_isSharedCheck_1806_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                        4 => {
                            v_declName_1807_ = leanh::lean_ctor_get(v_e_1721_, 0);
                            leanh::lean_inc(v_declName_1807_);
                            leanh::lean_dec_ref_known(v_e_1721_, 2);
                            if leanh::lean_obj_tag(v_declName_1807_) == 0 {
                                v___x_1808_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1;
                                v___x_1809_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1809_, 0, v___x_1808_);
                                return v___x_1809_;
                            } else {
                                v_hash_1810_ = leanh::lean_ctor_get_uint64(
                                    v_declName_1807_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                                        as u32,
                                );
                                leanh::lean_dec(v_declName_1807_);
                                v___x_1811_ = leanh::lean_box_uint64(v_hash_1810_);
                                v___x_1812_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1812_, 0, v___x_1811_);
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
                                leanh::lean_inc_ref(v_e_1721_);
                                v___x_1849_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1721_, v_a_1725_);
                                if leanh::lean_obj_tag(v___x_1849_) == 0 {
                                    v_a_1850_ = leanh::lean_ctor_get(v___x_1849_, 0);
                                    leanh::lean_inc(v_a_1850_);
                                    leanh::lean_dec_ref_known(v___x_1849_, 1);
                                    v___x_1851_ = lean_expr_eqv(v_a_1850_, v_e_1721_);
                                    if v___x_1851_ == 0 {
                                        leanh::lean_dec_ref(v___x_1813_);
                                        leanh::lean_dec_ref_known(v_e_1721_, 2);
                                        v_e_1721_ = v_a_1850_;
                                        state = 0;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_1850_);
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
                                    leanh::lean_dec_ref(v___x_1813_);
                                    leanh::lean_dec_ref_known(v_e_1721_, 2);
                                    v_a_1853_ = leanh::lean_ctor_get(v___x_1849_, 0);
                                    v_isSharedCheck_1860_ =
                                        (!leanh::lean_is_exclusive(v___x_1849_)) as u8;
                                    if v_isSharedCheck_1860_ == 0 {
                                        v___x_1855_ = v___x_1849_;
                                        v_isShared_1856_ = v_isSharedCheck_1860_;
                                        state = 19;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1853_);
                                        leanh::lean_dec(v___x_1849_);
                                        v___x_1855_ = leanh::lean_box(0);
                                        v_isShared_1856_ = v_isSharedCheck_1860_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            }
                        }
                        6 => {
                            v_binderType_1861_ = leanh::lean_ctor_get(v_e_1721_, 1);
                            leanh::lean_inc_ref(v_binderType_1861_);
                            v_body_1862_ = leanh::lean_ctor_get(v_e_1721_, 2);
                            leanh::lean_inc_ref(v_body_1862_);
                            leanh::lean_dec_ref_known(v_e_1721_, 3);
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
                            v_binderType_1863_ = leanh::lean_ctor_get(v_e_1721_, 1);
                            leanh::lean_inc_ref(v_binderType_1863_);
                            v_body_1864_ = leanh::lean_ctor_get(v_e_1721_, 2);
                            leanh::lean_inc_ref(v_body_1864_);
                            leanh::lean_dec_ref_known(v_e_1721_, 3);
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
                            v_value_1865_ = leanh::lean_ctor_get(v_e_1721_, 2);
                            leanh::lean_inc_ref(v_value_1865_);
                            v_body_1866_ = leanh::lean_ctor_get(v_e_1721_, 3);
                            leanh::lean_inc_ref(v_body_1866_);
                            leanh::lean_dec_ref_known(v_e_1721_, 4);
                            v___x_1867_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_value_1865_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                            if leanh::lean_obj_tag(v___x_1867_) == 0 {
                                v_a_1868_ = leanh::lean_ctor_get(v___x_1867_, 0);
                                leanh::lean_inc(v_a_1868_);
                                leanh::lean_dec_ref_known(v___x_1867_, 1);
                                v___x_1869_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_body_1866_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                                if leanh::lean_obj_tag(v___x_1869_) == 0 {
                                    v_a_1870_ = leanh::lean_ctor_get(v___x_1869_, 0);
                                    v_isSharedCheck_1881_ =
                                        (!leanh::lean_is_exclusive(v___x_1869_)) as u8;
                                    if v_isSharedCheck_1881_ == 0 {
                                        v___x_1872_ = v___x_1869_;
                                        v_isShared_1873_ = v_isSharedCheck_1881_;
                                        state = 21;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1870_);
                                        leanh::lean_dec(v___x_1869_);
                                        v___x_1872_ = leanh::lean_box(0);
                                        v_isShared_1873_ = v_isSharedCheck_1881_;
                                        state = 21;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1868_);
                                    return v___x_1869_;
                                }
                            } else {
                                leanh::lean_dec_ref(v_body_1866_);
                                return v___x_1867_;
                            }
                        }
                        10 => {
                            v_expr_1882_ = leanh::lean_ctor_get(v_e_1721_, 1);
                            leanh::lean_inc_ref(v_expr_1882_);
                            v___x_1883_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_expr_1882_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                            if leanh::lean_obj_tag(v___x_1883_) == 0 {
                                v_a_1884_ = leanh::lean_ctor_get(v___x_1883_, 0);
                                leanh::lean_inc(v_a_1884_);
                                leanh::lean_dec_ref_known(v___x_1883_, 1);
                                v___x_1885_ = leanh::lean_unbox_uint64(v_a_1884_);
                                leanh::lean_dec(v_a_1884_);
                                v_key_1754_ = v___x_1885_;
                                v___y_1755_ = v_a_1723_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_e_1721_, 2);
                                return v___x_1883_;
                            }
                        }
                        11 => {
                            v_idx_1886_ = leanh::lean_ctor_get(v_e_1721_, 1);
                            leanh::lean_inc(v_idx_1886_);
                            v_struct_1887_ = leanh::lean_ctor_get(v_e_1721_, 2);
                            leanh::lean_inc_ref(v_struct_1887_);
                            leanh::lean_dec_ref_known(v_e_1721_, 3);
                            v___x_1888_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_struct_1887_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                            if leanh::lean_obj_tag(v___x_1888_) == 0 {
                                v_a_1889_ = leanh::lean_ctor_get(v___x_1888_, 0);
                                v_isSharedCheck_1900_ =
                                    (!leanh::lean_is_exclusive(v___x_1888_)) as u8;
                                if v_isSharedCheck_1900_ == 0 {
                                    v___x_1891_ = v___x_1888_;
                                    v_isShared_1892_ = v_isSharedCheck_1900_;
                                    state = 23;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1889_);
                                    leanh::lean_dec(v___x_1888_);
                                    v___x_1891_ = leanh::lean_box(0);
                                    v_isShared_1892_ = v_isSharedCheck_1900_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_idx_1886_);
                                return v___x_1888_;
                            }
                        }
                        _ => {
                            v___x_1901_ = l_Lean_Expr_hash(v_e_1721_);
                            leanh::lean_dec_ref(v_e_1721_);
                            v___x_1902_ = leanh::lean_box_uint64(v___x_1901_);
                            v___x_1903_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1903_, 0, v___x_1902_);
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
                if leanh::lean_obj_tag(v___x_1738_) == 0 {
                    v_a_1739_ = leanh::lean_ctor_get(v___x_1738_, 0);
                    leanh::lean_inc(v_a_1739_);
                    leanh::lean_dec_ref_known(v___x_1738_, 1);
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
                    if leanh::lean_obj_tag(v___x_1740_) == 0 {
                        v_a_1741_ = leanh::lean_ctor_get(v___x_1740_, 0);
                        v_isSharedCheck_1752_ =
                            (!leanh::lean_is_exclusive(v___x_1740_)) as u8;
                        if v_isSharedCheck_1752_ == 0 {
                            v___x_1743_ = v___x_1740_;
                            v_isShared_1744_ = v_isSharedCheck_1752_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1741_);
                            leanh::lean_dec(v___x_1740_);
                            v___x_1743_ = leanh::lean_box(0);
                            v_isShared_1744_ = v_isSharedCheck_1752_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1739_);
                        return v___x_1740_;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_1731_);
                    return v___x_1738_;
                }
            }
            2 => {
                v___x_1745_ = leanh::lean_unbox_uint64(v_a_1739_);
                leanh::lean_dec(v_a_1739_);
                v___x_1746_ = leanh::lean_unbox_uint64(v_a_1741_);
                leanh::lean_dec(v_a_1741_);
                v___x_1747_ = lean_uint64_mix_hash(v___x_1745_, v___x_1746_);
                v___x_1748_ = leanh::lean_box_uint64(v___x_1747_);
                if v_isShared_1744_ == 0 {
                    leanh::lean_ctor_set(v___x_1743_, 0, v___x_1748_);
                    v___x_1750_ = v___x_1743_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1751_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
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
                if leanh::lean_obj_tag(v___x_1756_) == 0 {
                    v_isSharedCheck_1764_ = (!leanh::lean_is_exclusive(v___x_1756_)) as u8;
                    if v_isSharedCheck_1764_ == 0 {
                        v_unused_1765_ = leanh::lean_ctor_get(v___x_1756_, 0);
                        leanh::lean_dec(v_unused_1765_);
                        v___x_1758_ = v___x_1756_;
                        v_isShared_1759_ = v_isSharedCheck_1764_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1756_);
                        v___x_1758_ = leanh::lean_box(0);
                        v_isShared_1759_ = v_isSharedCheck_1764_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_1766_ = leanh::lean_ctor_get(v___x_1756_, 0);
                    v_isSharedCheck_1773_ = (!leanh::lean_is_exclusive(v___x_1756_)) as u8;
                    if v_isSharedCheck_1773_ == 0 {
                        v___x_1768_ = v___x_1756_;
                        v_isShared_1769_ = v_isSharedCheck_1773_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1766_);
                        leanh::lean_dec(v___x_1756_);
                        v___x_1768_ = leanh::lean_box(0);
                        v_isShared_1769_ = v_isSharedCheck_1773_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1760_ = leanh::lean_box_uint64(v_key_1754_);
                if v_isShared_1759_ == 0 {
                    leanh::lean_ctor_set(v___x_1758_, 0, v___x_1760_);
                    v___x_1762_ = v___x_1758_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
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
                    v_reuseFailAlloc_1772_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
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
                    leanh::lean_ctor_set_tag(v___x_1778_, 0);
                    v___x_1781_ = v___x_1778_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1782_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_val_1776_);
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
                    leanh::lean_del_object(v___x_1787_);
                    v___x_1790_ =
                        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
                            v_a_1785_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_,
                            v_a_1727_,
                        );
                    if leanh::lean_obj_tag(v___x_1790_) == 0 {
                        v_a_1791_ = leanh::lean_ctor_get(v___x_1790_, 0);
                        leanh::lean_inc(v_a_1791_);
                        leanh::lean_dec_ref_known(v___x_1790_, 1);
                        v___x_1792_ = leanh::lean_unbox_uint64(v_a_1791_);
                        leanh::lean_dec(v_a_1791_);
                        v_key_1754_ = v___x_1792_;
                        v___y_1755_ = v_a_1723_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_e_1721_, 1);
                        return v___x_1790_;
                    }
                } else {
                    leanh::lean_dec(v_a_1785_);
                    v___x_1793_ = l_Lean_Expr_hash(v_e_1721_);
                    leanh::lean_dec_ref_known(v_e_1721_, 1);
                    v___x_1794_ = leanh::lean_box_uint64(v___x_1793_);
                    if v_isShared_1788_ == 0 {
                        leanh::lean_ctor_set(v___x_1787_, 0, v___x_1794_);
                        v___x_1796_ = v___x_1787_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1797_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
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
                    v_reuseFailAlloc_1805_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
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
                if leanh::lean_obj_tag(v___x_1822_) == 0 {
                    v_a_1823_ = leanh::lean_ctor_get(v___x_1822_, 0);
                    leanh::lean_inc(v_a_1823_);
                    leanh::lean_dec_ref_known(v___x_1822_, 1);
                    v___x_1824_ = l_Lean_Expr_getAppNumArgs(v_e_1721_);
                    v___x_1825_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1826_ = leanh::lean_unbox_uint64(v_a_1823_);
                    leanh::lean_dec(v_a_1823_);
                    v___x_1827_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_1824_, v_e_1721_, v___x_1824_, v_info_1815_, v___x_1825_, v___x_1826_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
                    leanh::lean_dec_ref(v_info_1815_);
                    leanh::lean_dec_ref_known(v_e_1721_, 2);
                    leanh::lean_dec(v___x_1824_);
                    return v___x_1827_;
                } else {
                    leanh::lean_dec_ref(v_info_1815_);
                    leanh::lean_dec_ref_known(v_e_1721_, 2);
                    return v___x_1822_;
                }
            }
            16 => {
                v___x_1835_ = l_Lean_Expr_hasLooseBVars(v___x_1813_);
                if v___x_1835_ == 0 {
                    v___x_1836_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v___x_1813_);
                    v___x_1837_ = l_Lean_Meta_getFunInfo(
                        v___x_1813_,
                        v___x_1836_,
                        v___y_1831_,
                        v___y_1832_,
                        v___y_1833_,
                        v___y_1834_,
                    );
                    if leanh::lean_obj_tag(v___x_1837_) == 0 {
                        v_a_1838_ = leanh::lean_ctor_get(v___x_1837_, 0);
                        leanh::lean_inc(v_a_1838_);
                        leanh::lean_dec_ref_known(v___x_1837_, 1);
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
                        leanh::lean_dec_ref(v___x_1813_);
                        leanh::lean_dec_ref_known(v_e_1721_, 2);
                        v_a_1839_ = leanh::lean_ctor_get(v___x_1837_, 0);
                        v_isSharedCheck_1846_ =
                            (!leanh::lean_is_exclusive(v___x_1837_)) as u8;
                        if v_isSharedCheck_1846_ == 0 {
                            v___x_1841_ = v___x_1837_;
                            v_isShared_1842_ = v_isSharedCheck_1846_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1839_);
                            leanh::lean_dec(v___x_1837_);
                            v___x_1841_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1845_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
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
                    v_reuseFailAlloc_1859_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
                    v___x_1858_ = v_reuseFailAlloc_1859_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1858_;
            }
            21 => {
                v___x_1874_ = leanh::lean_unbox_uint64(v_a_1868_);
                leanh::lean_dec(v_a_1868_);
                v___x_1875_ = leanh::lean_unbox_uint64(v_a_1870_);
                leanh::lean_dec(v_a_1870_);
                v___x_1876_ = lean_uint64_mix_hash(v___x_1874_, v___x_1875_);
                v___x_1877_ = leanh::lean_box_uint64(v___x_1876_);
                if v_isShared_1873_ == 0 {
                    leanh::lean_ctor_set(v___x_1872_, 0, v___x_1877_);
                    v___x_1879_ = v___x_1872_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1880_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
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
                leanh::lean_dec(v_idx_1886_);
                v___x_1894_ = leanh::lean_unbox_uint64(v_a_1889_);
                leanh::lean_dec(v_a_1889_);
                v___x_1895_ = lean_uint64_mix_hash(v___x_1893_, v___x_1894_);
                v___x_1896_ = leanh::lean_box_uint64(v___x_1895_);
                if v_isShared_1892_ == 0 {
                    leanh::lean_ctor_set(v___x_1891_, 0, v___x_1896_);
                    v___x_1898_ = v___x_1891_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1899_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
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
    mut v___x_1904_: *mut leanh::LeanObject,
    mut v_e_1905_: *mut leanh::LeanObject,
    mut v_upperBound_1906_: *mut leanh::LeanObject,
    mut v_info_1907_: *mut leanh::LeanObject,
    mut v_a_1908_: *mut leanh::LeanObject,
    mut v_b_1909_: u64,
    mut v___y_1910_: u8,
    mut v___y_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
    mut v___y_1913_: *mut leanh::LeanObject,
    mut v___y_1914_: *mut leanh::LeanObject,
    mut v___y_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1918_: u64 = 0;
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: u8 = 0;
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u64 = 0;
    let mut v___x_1931_: u64 = 0;
    let mut v___x_1932_: u8 = 0;
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: u8 = 0;
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u64 = 0;
    let mut v___x_1945_: u64 = 0;
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: u8 = 0;
    let mut v_isProp_1948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1932_ = lean_nat_dec_lt(v_a_1908_, v_upperBound_1906_);
                if v___x_1932_ == 0 {
                    leanh::lean_dec(v_a_1908_);
                    v___x_1933_ = leanh::lean_box_uint64(v_b_1909_);
                    v___x_1934_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1934_, 0, v___x_1933_);
                    return v___x_1934_;
                } else {
                    v_paramInfo_1935_ = leanh::lean_ctor_get(v_info_1907_, 0);
                    v___x_1936_ = lean_array_get_size(v_paramInfo_1935_);
                    v___x_1937_ = lean_nat_dec_lt(v_a_1908_, v___x_1936_);
                    if v___x_1937_ == 0 {
                        v___x_1938_ = lean_nat_sub(v___x_1904_, v_a_1908_);
                        v___x_1939_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1940_ = lean_nat_sub(v___x_1938_, v___x_1939_);
                        leanh::lean_dec(v___x_1938_);
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
                        if leanh::lean_obj_tag(v___x_1942_) == 0 {
                            v_a_1943_ = leanh::lean_ctor_get(v___x_1942_, 0);
                            leanh::lean_inc(v_a_1943_);
                            leanh::lean_dec_ref_known(v___x_1942_, 1);
                            v___x_1944_ = leanh::lean_unbox_uint64(v_a_1943_);
                            leanh::lean_dec(v_a_1943_);
                            v___x_1945_ = lean_uint64_mix_hash(v_b_1909_, v___x_1944_);
                            v_a_1918_ = v___x_1945_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_1908_);
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
                            v_isProp_1948_ = leanh::lean_ctor_get_uint8(
                                v___x_1946_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2)
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
                v___x_1919_ = leanh::lean_unsigned_to_nat(1);
                v___x_1920_ = lean_nat_add(v_a_1908_, v___x_1919_);
                leanh::lean_dec(v_a_1908_);
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
                    v___x_1925_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1926_ = lean_nat_sub(v___x_1924_, v___x_1925_);
                    leanh::lean_dec(v___x_1924_);
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
                    if leanh::lean_obj_tag(v___x_1928_) == 0 {
                        v_a_1929_ = leanh::lean_ctor_get(v___x_1928_, 0);
                        leanh::lean_inc(v_a_1929_);
                        leanh::lean_dec_ref_known(v___x_1928_, 1);
                        v___x_1930_ = leanh::lean_unbox_uint64(v_a_1929_);
                        leanh::lean_dec(v_a_1929_);
                        v___x_1931_ = lean_uint64_mix_hash(v_b_1909_, v___x_1930_);
                        v_a_1918_ = v___x_1931_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_1908_);
                        return v___x_1928_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(
    mut v___x_1949_: *mut leanh::LeanObject,
    mut v_e_1950_: *mut leanh::LeanObject,
    mut v_upperBound_1951_: *mut leanh::LeanObject,
    mut v_info_1952_: *mut leanh::LeanObject,
    mut v_a_1953_: *mut leanh::LeanObject,
    mut v_b_1954_: *mut leanh::LeanObject,
    mut v___y_1955_: *mut leanh::LeanObject,
    mut v___y_1956_: *mut leanh::LeanObject,
    mut v___y_1957_: *mut leanh::LeanObject,
    mut v___y_1958_: *mut leanh::LeanObject,
    mut v___y_1959_: *mut leanh::LeanObject,
    mut v___y_1960_: *mut leanh::LeanObject,
    mut v___y_1961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1962_: u64 = 0;
    let mut v___y_13205__boxed_1963_: u8 = 0;
    let mut v_res_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1962_ = leanh::lean_unbox_uint64(v_b_1954_);
    leanh::lean_dec_ref(v_b_1954_);
    v___y_13205__boxed_1963_ = (leanh::lean_unbox(v___y_1955_) as u8);
    v_res_1964_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_1949_, v_e_1950_, v_upperBound_1951_, v_info_1952_, v_a_1953_, v_b_boxed_1962_, v___y_13205__boxed_1963_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
    leanh::lean_dec(v___y_1960_);
    leanh::lean_dec_ref(v___y_1959_);
    leanh::lean_dec(v___y_1958_);
    leanh::lean_dec_ref(v___y_1957_);
    leanh::lean_dec(v___y_1956_);
    leanh::lean_dec_ref(v_info_1952_);
    leanh::lean_dec(v_upperBound_1951_);
    leanh::lean_dec_ref(v_e_1950_);
    leanh::lean_dec(v___x_1949_);
    return v_res_1964_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(
    mut v_e_1965_: *mut leanh::LeanObject,
    mut v_a_1966_: *mut leanh::LeanObject,
    mut v_a_1967_: *mut leanh::LeanObject,
    mut v_a_1968_: *mut leanh::LeanObject,
    mut v_a_1969_: *mut leanh::LeanObject,
    mut v_a_1970_: *mut leanh::LeanObject,
    mut v_a_1971_: *mut leanh::LeanObject,
    mut v_a_1972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1973_: u8 = 0;
    let mut v_res_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1973_ = (leanh::lean_unbox(v_a_1966_) as u8);
    v_res_1974_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
        v_e_1965_,
        v_a_boxed_1973_,
        v_a_1967_,
        v_a_1968_,
        v_a_1969_,
        v_a_1970_,
        v_a_1971_,
    );
    leanh::lean_dec(v_a_1971_);
    leanh::lean_dec_ref(v_a_1970_);
    leanh::lean_dec(v_a_1969_);
    leanh::lean_dec_ref(v_a_1968_);
    leanh::lean_dec(v_a_1967_);
    return v_res_1974_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(
    mut v___x_1975_: *mut leanh::LeanObject,
    mut v_e_1976_: *mut leanh::LeanObject,
    mut v_upperBound_1977_: *mut leanh::LeanObject,
    mut v_info_1978_: *mut leanh::LeanObject,
    mut v_inst_1979_: *mut leanh::LeanObject,
    mut v_R_1980_: *mut leanh::LeanObject,
    mut v_a_1981_: *mut leanh::LeanObject,
    mut v_b_1982_: u64,
    mut v_c_1983_: *mut leanh::LeanObject,
    mut v___y_1984_: u8,
    mut v___y_1985_: *mut leanh::LeanObject,
    mut v___y_1986_: *mut leanh::LeanObject,
    mut v___y_1987_: *mut leanh::LeanObject,
    mut v___y_1988_: *mut leanh::LeanObject,
    mut v___y_1989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_1975_, v_e_1976_, v_upperBound_1977_, v_info_1978_, v_a_1981_, v_b_1982_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
    return v___x_1991_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(
    mut v___x_1992_: *mut leanh::LeanObject,
    mut v_e_1993_: *mut leanh::LeanObject,
    mut v_upperBound_1994_: *mut leanh::LeanObject,
    mut v_info_1995_: *mut leanh::LeanObject,
    mut v_inst_1996_: *mut leanh::LeanObject,
    mut v_R_1997_: *mut leanh::LeanObject,
    mut v_a_1998_: *mut leanh::LeanObject,
    mut v_b_1999_: *mut leanh::LeanObject,
    mut v_c_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
    mut v___y_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
    mut v___y_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
    mut v___y_2006_: *mut leanh::LeanObject,
    mut v___y_2007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_2008_: u64 = 0;
    let mut v___y_13678__boxed_2009_: u8 = 0;
    let mut v_res_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2008_ = leanh::lean_unbox_uint64(v_b_1999_);
    leanh::lean_dec_ref(v_b_1999_);
    v___y_13678__boxed_2009_ = (leanh::lean_unbox(v___y_2001_) as u8);
    v_res_2010_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(v___x_1992_, v_e_1993_, v_upperBound_1994_, v_info_1995_, v_inst_1996_, v_R_1997_, v_a_1998_, v_b_boxed_2008_, v_c_2000_, v___y_13678__boxed_2009_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
    leanh::lean_dec(v___y_2006_);
    leanh::lean_dec_ref(v___y_2005_);
    leanh::lean_dec(v___y_2004_);
    leanh::lean_dec_ref(v___y_2003_);
    leanh::lean_dec(v___y_2002_);
    leanh::lean_dec_ref(v_info_1995_);
    leanh::lean_dec(v_upperBound_1994_);
    leanh::lean_dec_ref(v_e_1993_);
    leanh::lean_dec(v___x_1992_);
    return v_res_2010_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(
    mut v_a_2011_: u64,
    mut v_x_2012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: u64 = 0;
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2012_) == 0 {
                    v___x_2013_ = leanh::lean_box(0);
                    return v___x_2013_;
                } else {
                    v_key_2014_ = leanh::lean_ctor_get(v_x_2012_, 0);
                    v_value_2015_ = leanh::lean_ctor_get(v_x_2012_, 1);
                    v_tail_2016_ = leanh::lean_ctor_get(v_x_2012_, 2);
                    v___x_2017_ = leanh::lean_unbox_uint64(v_key_2014_);
                    v___x_2018_ = lean_uint64_dec_eq(v___x_2017_, v_a_2011_);
                    if v___x_2018_ == 0 {
                        v_x_2012_ = v_tail_2016_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_2015_);
                        v___x_2020_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2020_, 0, v_value_2015_);
                        return v___x_2020_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg___boxed(
    mut v_a_2021_: *mut leanh::LeanObject,
    mut v_x_2022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2023_: u64 = 0;
    let mut v_res_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2023_ = leanh::lean_unbox_uint64(v_a_2021_);
    leanh::lean_dec_ref(v_a_2021_);
    v_res_2024_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_boxed_2023_, v_x_2022_);
    leanh::lean_dec(v_x_2022_);
    return v_res_2024_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(
    mut v_m_2025_: *mut leanh::LeanObject,
    mut v_a_2026_: u64,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2027_ = leanh::lean_ctor_get(v_m_2025_, 1);
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
    mut v_m_2042_: *mut leanh::LeanObject,
    mut v_a_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2044_: u64 = 0;
    let mut v_res_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2044_ = leanh::lean_unbox_uint64(v_a_2043_);
    leanh::lean_dec_ref(v_a_2043_);
    v_res_2045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_m_2042_, v_a_boxed_2044_);
    leanh::lean_dec_ref(v_m_2042_);
    return v_res_2045_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(
    mut v_k_2046_: u64,
    mut v_____do__lift_2047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyToExprs_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyToExprs_2048_ = leanh::lean_ctor_get(v_____do__lift_2047_, 1);
    v___x_2049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_keyToExprs_2048_, v_k_2046_);
    return v___x_2049_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(
    mut v_k_2050_: *mut leanh::LeanObject,
    mut v_____do__lift_2051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_boxed_2052_: u64 = 0;
    let mut v_res_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_2052_ = leanh::lean_unbox_uint64(v_k_2050_);
    leanh::lean_dec_ref(v_k_2050_);
    v_res_2053_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(
        v_k_boxed_2052_,
        v_____do__lift_2051_,
    );
    leanh::lean_dec_ref(v_____do__lift_2051_);
    return v_res_2053_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(
    mut v_00_u03b2_2054_: *mut leanh::LeanObject,
    mut v_m_2055_: *mut leanh::LeanObject,
    mut v_a_2056_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_m_2055_, v_a_2056_);
    return v___x_2057_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___boxed(
    mut v_00_u03b2_2058_: *mut leanh::LeanObject,
    mut v_m_2059_: *mut leanh::LeanObject,
    mut v_a_2060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2061_: u64 = 0;
    let mut v_res_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2061_ = leanh::lean_unbox_uint64(v_a_2060_);
    leanh::lean_dec_ref(v_a_2060_);
    v_res_2062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(v_00_u03b2_2058_, v_m_2059_, v_a_boxed_2061_);
    leanh::lean_dec_ref(v_m_2059_);
    return v_res_2062_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0(
    mut v_00_u03b2_2063_: *mut leanh::LeanObject,
    mut v_a_2064_: u64,
    mut v_x_2065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_2064_, v_x_2065_);
    return v___x_2066_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___boxed(
    mut v_00_u03b2_2067_: *mut leanh::LeanObject,
    mut v_a_2068_: *mut leanh::LeanObject,
    mut v_x_2069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2070_: u64 = 0;
    let mut v_res_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2070_ = leanh::lean_unbox_uint64(v_a_2068_);
    leanh::lean_dec_ref(v_a_2068_);
    v_res_2071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0(v_00_u03b2_2067_, v_a_boxed_2070_, v_x_2069_);
    leanh::lean_dec(v_x_2069_);
    return v_res_2071_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(
    mut v_a_2072_: u64,
    mut v_b_2073_: *mut leanh::LeanObject,
    mut v_x_2074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2081_: u64 = 0;
    let mut v___x_2082_: u8 = 0;
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2074_) == 0 {
                    leanh::lean_dec(v_b_2073_);
                    return v_x_2074_;
                } else {
                    v_key_2075_ = leanh::lean_ctor_get(v_x_2074_, 0);
                    v_value_2076_ = leanh::lean_ctor_get(v_x_2074_, 1);
                    v_tail_2077_ = leanh::lean_ctor_get(v_x_2074_, 2);
                    v_isSharedCheck_2091_ = (!leanh::lean_is_exclusive(v_x_2074_)) as u8;
                    if v_isSharedCheck_2091_ == 0 {
                        v___x_2079_ = v_x_2074_;
                        v_isShared_2080_ = v_isSharedCheck_2091_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2077_);
                        leanh::lean_inc(v_value_2076_);
                        leanh::lean_inc(v_key_2075_);
                        leanh::lean_dec(v_x_2074_);
                        v___x_2079_ = leanh::lean_box(0);
                        v_isShared_2080_ = v_isSharedCheck_2091_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2081_ = leanh::lean_unbox_uint64(v_key_2075_);
                v___x_2082_ = lean_uint64_dec_eq(v___x_2081_, v_a_2072_);
                if v___x_2082_ == 0 {
                    v___x_2083_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_2072_, v_b_2073_, v_tail_2077_);
                    if v_isShared_2080_ == 0 {
                        leanh::lean_ctor_set(v___x_2079_, 2, v___x_2083_);
                        v___x_2085_ = v___x_2079_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2086_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_key_2075_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_value_2076_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 2, v___x_2083_);
                        v___x_2085_ = v_reuseFailAlloc_2086_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_2076_);
                    leanh::lean_dec(v_key_2075_);
                    v___x_2087_ = leanh::lean_box_uint64(v_a_2072_);
                    if v_isShared_2080_ == 0 {
                        leanh::lean_ctor_set(v___x_2079_, 1, v_b_2073_);
                        leanh::lean_ctor_set(v___x_2079_, 0, v___x_2087_);
                        v___x_2089_ = v___x_2079_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2090_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_b_2073_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_tail_2077_);
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
    mut v_a_2092_: *mut leanh::LeanObject,
    mut v_b_2093_: *mut leanh::LeanObject,
    mut v_x_2094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2095_: u64 = 0;
    let mut v_res_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2095_ = leanh::lean_unbox_uint64(v_a_2092_);
    leanh::lean_dec_ref(v_a_2092_);
    v_res_2096_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_boxed_2095_, v_b_2093_, v_x_2094_);
    return v_res_2096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_2097_: *mut leanh::LeanObject,
    mut v_x_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2098_) == 0 {
                    return v_x_2097_;
                } else {
                    v_key_2099_ = leanh::lean_ctor_get(v_x_2098_, 0);
                    v_value_2100_ = leanh::lean_ctor_get(v_x_2098_, 1);
                    v_tail_2101_ = leanh::lean_ctor_get(v_x_2098_, 2);
                    v_isSharedCheck_2125_ = (!leanh::lean_is_exclusive(v_x_2098_)) as u8;
                    if v_isSharedCheck_2125_ == 0 {
                        v___x_2103_ = v_x_2098_;
                        v_isShared_2104_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2101_);
                        leanh::lean_inc(v_value_2100_);
                        leanh::lean_inc(v_key_2099_);
                        leanh::lean_dec(v_x_2098_);
                        v___x_2103_ = leanh::lean_box(0);
                        v_isShared_2104_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2105_ = lean_array_get_size(v_x_2097_);
                v___x_2106_ = 32u64;
                v___x_2107_ = leanh::lean_unbox_uint64(v_key_2099_);
                v___x_2108_ = lean_uint64_shift_right(v___x_2107_, v___x_2106_);
                v___x_2109_ = leanh::lean_unbox_uint64(v_key_2099_);
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
                leanh::lean_inc(v___x_2119_);
                if v_isShared_2104_ == 0 {
                    leanh::lean_ctor_set(v___x_2103_, 2, v___x_2119_);
                    v___x_2121_ = v___x_2103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2124_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_key_2099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_value_2100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 2, v___x_2119_);
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
    mut v_i_2126_: *mut leanh::LeanObject,
    mut v_source_2127_: *mut leanh::LeanObject,
    mut v_target_2128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u8 = 0;
    let mut v_es_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2129_ = lean_array_get_size(v_source_2127_);
                v___x_2130_ = lean_nat_dec_lt(v_i_2126_, v___x_2129_);
                if v___x_2130_ == 0 {
                    leanh::lean_dec_ref(v_source_2127_);
                    leanh::lean_dec(v_i_2126_);
                    return v_target_2128_;
                } else {
                    v_es_2131_ = lean_array_fget(v_source_2127_, v_i_2126_);
                    v___x_2132_ = leanh::lean_box(0);
                    v_source_2133_ = lean_array_fset(v_source_2127_, v_i_2126_, v___x_2132_);
                    v_target_2134_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(v_target_2128_, v_es_2131_);
                    v___x_2135_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2136_ = lean_nat_add(v_i_2126_, v___x_2135_);
                    leanh::lean_dec(v_i_2126_);
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
    mut v_data_2138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2139_ = lean_array_get_size(v_data_2138_);
    v___x_2140_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2141_ = lean_nat_mul(v___x_2139_, v___x_2140_);
    v___x_2142_ = leanh::lean_unsigned_to_nat(0);
    v___x_2143_ = leanh::lean_box(0);
    v___x_2144_ = lean_mk_array(v_nbuckets_2141_, v___x_2143_);
    v___x_2145_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(v___x_2142_, v_data_2138_, v___x_2144_);
    return v___x_2145_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(
    mut v_a_2146_: u64,
    mut v_x_2147_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2148_: u8 = 0;
    let mut v_key_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u64 = 0;
    let mut v___x_2152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2147_) == 0 {
                    v___x_2148_ = 0;
                    return v___x_2148_;
                } else {
                    v_key_2149_ = leanh::lean_ctor_get(v_x_2147_, 0);
                    v_tail_2150_ = leanh::lean_ctor_get(v_x_2147_, 2);
                    v___x_2151_ = leanh::lean_unbox_uint64(v_key_2149_);
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
    mut v_a_2154_: *mut leanh::LeanObject,
    mut v_x_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2156_: u64 = 0;
    let mut v_res_2157_: u8 = 0;
    let mut v_r_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2156_ = leanh::lean_unbox_uint64(v_a_2154_);
    leanh::lean_dec_ref(v_a_2154_);
    v_res_2157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_boxed_2156_, v_x_2155_);
    leanh::lean_dec(v_x_2155_);
    v_r_2158_ = leanh::lean_box((v_res_2157_) as usize);
    return v_r_2158_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(
    mut v_m_2159_: *mut leanh::LeanObject,
    mut v_a_2160_: u64,
    mut v_b_2161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2166_: u8 = 0;
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: u8 = 0;
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u8 = 0;
    let mut v_val_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2162_ = leanh::lean_ctor_get(v_m_2159_, 0);
                v_buckets_2163_ = leanh::lean_ctor_get(v_m_2159_, 1);
                v_isSharedCheck_2206_ = (!leanh::lean_is_exclusive(v_m_2159_)) as u8;
                if v_isSharedCheck_2206_ == 0 {
                    v___x_2165_ = v_m_2159_;
                    v_isShared_2166_ = v_isSharedCheck_2206_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2163_);
                    leanh::lean_inc(v_size_2162_);
                    leanh::lean_dec(v_m_2159_);
                    v___x_2165_ = leanh::lean_box(0);
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
                    v___x_2181_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2182_ = lean_nat_add(v_size_2162_, v___x_2181_);
                    leanh::lean_dec(v_size_2162_);
                    v___x_2183_ = leanh::lean_box_uint64(v_a_2160_);
                    leanh::lean_inc(v_bkt_2179_);
                    v___x_2184_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2184_, 0, v___x_2183_);
                    leanh::lean_ctor_set(v___x_2184_, 1, v_b_2161_);
                    leanh::lean_ctor_set(v___x_2184_, 2, v_bkt_2179_);
                    v_buckets_x27_2185_ =
                        lean_array_uset(v_buckets_2163_, v___x_2178_, v___x_2184_);
                    v___x_2186_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2187_ = lean_nat_mul(v_size_x27_2182_, v___x_2186_);
                    v___x_2188_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2189_ = lean_nat_div(v___x_2187_, v___x_2188_);
                    leanh::lean_dec(v___x_2187_);
                    v___x_2190_ = lean_array_get_size(v_buckets_x27_2185_);
                    v___x_2191_ = lean_nat_dec_le(v___x_2189_, v___x_2190_);
                    leanh::lean_dec(v___x_2189_);
                    if v___x_2191_ == 0 {
                        v_val_2192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(v_buckets_x27_2185_);
                        if v_isShared_2166_ == 0 {
                            leanh::lean_ctor_set(v___x_2165_, 1, v_val_2192_);
                            leanh::lean_ctor_set(v___x_2165_, 0, v_size_x27_2182_);
                            v___x_2194_ = v___x_2165_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2195_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2195_,
                                0,
                                v_size_x27_2182_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_val_2192_);
                            v___x_2194_ = v_reuseFailAlloc_2195_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2166_ == 0 {
                            leanh::lean_ctor_set(v___x_2165_, 1, v_buckets_x27_2185_);
                            leanh::lean_ctor_set(v___x_2165_, 0, v_size_x27_2182_);
                            v___x_2197_ = v___x_2165_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2198_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2198_,
                                0,
                                v_size_x27_2182_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_2179_);
                    v___x_2199_ = leanh::lean_box(0);
                    v_buckets_x27_2200_ =
                        lean_array_uset(v_buckets_2163_, v___x_2178_, v___x_2199_);
                    v___x_2201_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_2160_, v_b_2161_, v_bkt_2179_);
                    v___x_2202_ = lean_array_uset(v_buckets_x27_2200_, v___x_2178_, v___x_2201_);
                    if v_isShared_2166_ == 0 {
                        leanh::lean_ctor_set(v___x_2165_, 1, v___x_2202_);
                        v___x_2204_ = v___x_2165_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2205_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_size_2162_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2202_);
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
    mut v_m_2207_: *mut leanh::LeanObject,
    mut v_a_2208_: *mut leanh::LeanObject,
    mut v_b_2209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2210_: u64 = 0;
    let mut v_res_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2210_ = leanh::lean_unbox_uint64(v_a_2208_);
    leanh::lean_dec_ref(v_a_2208_);
    v_res_2211_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_m_2207_, v_a_boxed_2210_, v_b_2209_);
    return v_res_2211_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(
    mut v_e_2215_: *mut leanh::LeanObject,
    mut v_as_x27_2216_: *mut leanh::LeanObject,
    mut v_b_2217_: *mut leanh::LeanObject,
    mut v___y_2218_: *mut leanh::LeanObject,
    mut v___y_2219_: *mut leanh::LeanObject,
    mut v___y_2220_: *mut leanh::LeanObject,
    mut v___y_2221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_a_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2244_: u8 = 0;
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_2216_) == 0 {
                    leanh::lean_dec_ref(v_e_2215_);
                    v___x_2223_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2223_, 0, v_b_2217_);
                    return v___x_2223_;
                } else {
                    leanh::lean_dec_ref(v_b_2217_);
                    v_head_2224_ = leanh::lean_ctor_get(v_as_x27_2216_, 0);
                    v_tail_2225_ = leanh::lean_ctor_get(v_as_x27_2216_, 1);
                    leanh::lean_inc(v_head_2224_);
                    leanh::lean_inc_ref(v_e_2215_);
                    v___x_2226_ = l_Lean_Meta_isExprDefEq(
                        v_e_2215_,
                        v_head_2224_,
                        v___y_2218_,
                        v___y_2219_,
                        v___y_2220_,
                        v___y_2221_,
                    );
                    if leanh::lean_obj_tag(v___x_2226_) == 0 {
                        v_a_2227_ = leanh::lean_ctor_get(v___x_2226_, 0);
                        v_isSharedCheck_2240_ =
                            (!leanh::lean_is_exclusive(v___x_2226_)) as u8;
                        if v_isSharedCheck_2240_ == 0 {
                            v___x_2229_ = v___x_2226_;
                            v_isShared_2230_ = v_isSharedCheck_2240_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2227_);
                            leanh::lean_dec(v___x_2226_);
                            v___x_2229_ = leanh::lean_box(0);
                            v_isShared_2230_ = v_isSharedCheck_2240_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_2215_);
                        v_a_2241_ = leanh::lean_ctor_get(v___x_2226_, 0);
                        v_isSharedCheck_2248_ =
                            (!leanh::lean_is_exclusive(v___x_2226_)) as u8;
                        if v_isSharedCheck_2248_ == 0 {
                            v___x_2243_ = v___x_2226_;
                            v_isShared_2244_ = v_isSharedCheck_2248_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2241_);
                            leanh::lean_dec(v___x_2226_);
                            v___x_2243_ = leanh::lean_box(0);
                            v_isShared_2244_ = v_isSharedCheck_2248_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2231_ = leanh::lean_box(0);
                v___x_2232_ = (leanh::lean_unbox(v_a_2227_) as u8);
                leanh::lean_dec(v_a_2227_);
                if v___x_2232_ == 0 {
                    leanh::lean_del_object(v___x_2229_);
                    v___x_2233_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0;
                    v_as_x27_2216_ = v_tail_2225_;
                    v_b_2217_ = v___x_2233_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_2215_);
                    leanh::lean_inc(v_head_2224_);
                    v___x_2235_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2235_, 0, v_head_2224_);
                    v___x_2236_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2236_, 0, v___x_2235_);
                    leanh::lean_ctor_set(v___x_2236_, 1, v___x_2231_);
                    if v_isShared_2230_ == 0 {
                        leanh::lean_ctor_set(v___x_2229_, 0, v___x_2236_);
                        v___x_2238_ = v___x_2229_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2239_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
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
                    v_reuseFailAlloc_2247_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
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
    mut v_e_2249_: *mut leanh::LeanObject,
    mut v_as_x27_2250_: *mut leanh::LeanObject,
    mut v_b_2251_: *mut leanh::LeanObject,
    mut v___y_2252_: *mut leanh::LeanObject,
    mut v___y_2253_: *mut leanh::LeanObject,
    mut v___y_2254_: *mut leanh::LeanObject,
    mut v___y_2255_: *mut leanh::LeanObject,
    mut v___y_2256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2257_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(
        v_e_2249_,
        v_as_x27_2250_,
        v_b_2251_,
        v___y_2252_,
        v___y_2253_,
        v___y_2254_,
        v___y_2255_,
    );
    leanh::lean_dec(v___y_2255_);
    leanh::lean_dec_ref(v___y_2254_);
    leanh::lean_dec(v___y_2253_);
    leanh::lean_dec_ref(v___y_2252_);
    leanh::lean_dec(v_as_x27_2250_);
    return v_res_2257_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_canon(
    mut v_e_2258_: *mut leanh::LeanObject,
    mut v_a_2259_: u8,
    mut v_a_2260_: *mut leanh::LeanObject,
    mut v_a_2261_: *mut leanh::LeanObject,
    mut v_a_2262_: *mut leanh::LeanObject,
    mut v_a_2263_: *mut leanh::LeanObject,
    mut v_a_2264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2270_: u8 = 0;
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: u64 = 0;
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2296_: u8 = 0;
    let mut v_trackZetaDelta_2297_: u8 = 0;
    let mut v_zetaDeltaSet_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2304_: u8 = 0;
    let mut v_inTypeClassResolution_2305_: u8 = 0;
    let mut v_cacheInferType_2306_: u8 = 0;
    let mut v_config_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: u64 = 0;
    let mut v___x_2310_: u64 = 0;
    let mut v___x_2311_: u64 = 0;
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u64 = 0;
    let mut v___x_2314_: u64 = 0;
    let mut v_key_2315_: u64 = 0;
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v_fst_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2326_: u8 = 0;
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyToExprs_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2332_: u8 = 0;
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u64 = 0;
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2345_: u8 = 0;
    let mut v_val_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2350_: u8 = 0;
    let mut v_unused_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2352_: u8 = 0;
    let mut v_a_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_reuseFailAlloc_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2362_: u8 = 0;
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyToExprs_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2368_: u8 = 0;
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u64 = 0;
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut v_a_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2385_: u8 = 0;
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_2258_);
                v___x_2266_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
                    v_e_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_,
                );
                if leanh::lean_obj_tag(v___x_2266_) == 0 {
                    v_a_2267_ = leanh::lean_ctor_get(v___x_2266_, 0);
                    v_isSharedCheck_2381_ = (!leanh::lean_is_exclusive(v___x_2266_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v___x_2269_ = v___x_2266_;
                        v_isShared_2270_ = v_isSharedCheck_2381_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2267_);
                        leanh::lean_dec(v___x_2266_);
                        v___x_2269_ = leanh::lean_box(0);
                        v_isShared_2270_ = v_isSharedCheck_2381_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_2258_);
                    v_a_2382_ = leanh::lean_ctor_get(v___x_2266_, 0);
                    v_isSharedCheck_2389_ = (!leanh::lean_is_exclusive(v___x_2266_)) as u8;
                    if v_isSharedCheck_2389_ == 0 {
                        v___x_2384_ = v___x_2266_;
                        v_isShared_2385_ = v_isSharedCheck_2389_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2382_);
                        leanh::lean_dec(v___x_2266_);
                        v___x_2384_ = leanh::lean_box(0);
                        v_isShared_2385_ = v_isSharedCheck_2389_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2271_ = lean_st_ref_get(v_a_2260_);
                v___x_2272_ = leanh::lean_unbox_uint64(v_a_2267_);
                v___x_2273_ =
                    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(
                        v___x_2272_,
                        v___x_2271_,
                    );
                leanh::lean_dec(v___x_2271_);
                if leanh::lean_obj_tag(v___x_2273_) == 1 {
                    leanh::lean_del_object(v___x_2269_);
                    v_val_2274_ = leanh::lean_ctor_get(v___x_2273_, 0);
                    leanh::lean_inc(v_val_2274_);
                    leanh::lean_dec_ref_known(v___x_2273_, 1);
                    v___x_2275_ = l_Lean_Meta_Context_config(v_a_2261_);
                    v_foApprox_2276_ = leanh::lean_ctor_get_uint8(v___x_2275_, 0 as u32);
                    v_ctxApprox_2277_ = leanh::lean_ctor_get_uint8(v___x_2275_, 1 as u32);
                    v_quasiPatternApprox_2278_ =
                        leanh::lean_ctor_get_uint8(v___x_2275_, 2 as u32);
                    v_constApprox_2279_ = leanh::lean_ctor_get_uint8(v___x_2275_, 3 as u32);
                    v_isDefEqStuckEx_2280_ =
                        leanh::lean_ctor_get_uint8(v___x_2275_, 4 as u32);
                    v_unificationHints_2281_ =
                        leanh::lean_ctor_get_uint8(v___x_2275_, 5 as u32);
                    v_proofIrrelevance_2282_ =
                        leanh::lean_ctor_get_uint8(v___x_2275_, 6 as u32);
                    v_assignSyntheticOpaque_2283_ =
                        leanh::lean_ctor_get_uint8(v___x_2275_, 7 as u32);
                    v_offsetCnstrs_2284_ = leanh::lean_ctor_get_uint8(v___x_2275_, 8 as u32);
                    v_etaStruct_2285_ = leanh::lean_ctor_get_uint8(v___x_2275_, 10 as u32);
                    v_univApprox_2286_ = leanh::lean_ctor_get_uint8(v___x_2275_, 11 as u32);
                    v_iota_2287_ = leanh::lean_ctor_get_uint8(v___x_2275_, 12 as u32);
                    v_beta_2288_ = leanh::lean_ctor_get_uint8(v___x_2275_, 13 as u32);
                    v_proj_2289_ = leanh::lean_ctor_get_uint8(v___x_2275_, 14 as u32);
                    v_zeta_2290_ = leanh::lean_ctor_get_uint8(v___x_2275_, 15 as u32);
                    v_zetaDelta_2291_ = leanh::lean_ctor_get_uint8(v___x_2275_, 16 as u32);
                    v_zetaUnused_2292_ = leanh::lean_ctor_get_uint8(v___x_2275_, 17 as u32);
                    v_zetaHave_2293_ = leanh::lean_ctor_get_uint8(v___x_2275_, 18 as u32);
                    v_isSharedCheck_2362_ = (!leanh::lean_is_exclusive(v___x_2275_)) as u8;
                    if v_isSharedCheck_2362_ == 0 {
                        v___x_2295_ = v___x_2275_;
                        v_isShared_2296_ = v_isSharedCheck_2362_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2275_);
                        v___x_2295_ = leanh::lean_box(0);
                        v_isShared_2296_ = v_isSharedCheck_2362_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2273_);
                    v___x_2363_ = lean_st_ref_take(v_a_2260_);
                    v_cache_2364_ = leanh::lean_ctor_get(v___x_2363_, 0);
                    v_keyToExprs_2365_ = leanh::lean_ctor_get(v___x_2363_, 1);
                    v_isSharedCheck_2380_ = (!leanh::lean_is_exclusive(v___x_2363_)) as u8;
                    if v_isSharedCheck_2380_ == 0 {
                        v___x_2367_ = v___x_2363_;
                        v_isShared_2368_ = v_isSharedCheck_2380_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_keyToExprs_2365_);
                        leanh::lean_inc(v_cache_2364_);
                        leanh::lean_dec(v___x_2363_);
                        v___x_2367_ = leanh::lean_box(0);
                        v_isShared_2368_ = v_isSharedCheck_2380_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v_trackZetaDelta_2297_ = leanh::lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2298_ = leanh::lean_ctor_get(v_a_2261_, 1);
                v_lctx_2299_ = leanh::lean_ctor_get(v_a_2261_, 2);
                v_localInstances_2300_ = leanh::lean_ctor_get(v_a_2261_, 3);
                v_defEqCtx_x3f_2301_ = leanh::lean_ctor_get(v_a_2261_, 4);
                v_synthPendingDepth_2302_ = leanh::lean_ctor_get(v_a_2261_, 5);
                v_canUnfold_x3f_2303_ = leanh::lean_ctor_get(v_a_2261_, 6);
                v_univApprox_2304_ = leanh::lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2305_ = leanh::lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2306_ = leanh::lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2296_ == 0 {
                    v_config_2308_ = v___x_2295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2361_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        0 as u32,
                        v_foApprox_2276_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        1 as u32,
                        v_ctxApprox_2277_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        2 as u32,
                        v_quasiPatternApprox_2278_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        3 as u32,
                        v_constApprox_2279_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        4 as u32,
                        v_isDefEqStuckEx_2280_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        5 as u32,
                        v_unificationHints_2281_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        6 as u32,
                        v_proofIrrelevance_2282_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        7 as u32,
                        v_assignSyntheticOpaque_2283_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        8 as u32,
                        v_offsetCnstrs_2284_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        10 as u32,
                        v_etaStruct_2285_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        11 as u32,
                        v_univApprox_2286_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        12 as u32,
                        v_iota_2287_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        13 as u32,
                        v_beta_2288_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        14 as u32,
                        v_proj_2289_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        15 as u32,
                        v_zeta_2290_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        16 as u32,
                        v_zetaDelta_2291_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        17 as u32,
                        v_zetaUnused_2292_,
                    );
                    leanh::lean_ctor_set_uint8(
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
                leanh::lean_ctor_set_uint8(v_config_2308_, 9 as u32, v_a_2259_);
                v___x_2309_ = l_Lean_Meta_Context_configKey(v_a_2261_);
                v___x_2310_ = 3u64;
                v___x_2311_ = lean_uint64_shift_right(v___x_2309_, v___x_2310_);
                v___x_2312_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0;
                v___x_2313_ = lean_uint64_shift_left(v___x_2311_, v___x_2310_);
                v___x_2314_ = l_Lean_Meta_TransparencyMode_toUInt64(v_a_2259_);
                v_key_2315_ = lean_uint64_lor(v___x_2313_, v___x_2314_);
                v___x_2316_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2316_, 0, v_config_2308_);
                leanh::lean_ctor_set_uint64(
                    v___x_2316_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2315_,
                );
                leanh::lean_inc(v_canUnfold_x3f_2303_);
                leanh::lean_inc(v_synthPendingDepth_2302_);
                leanh::lean_inc(v_defEqCtx_x3f_2301_);
                leanh::lean_inc_ref(v_localInstances_2300_);
                leanh::lean_inc_ref(v_lctx_2299_);
                leanh::lean_inc(v_zetaDeltaSet_2298_);
                v___x_2317_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2317_, 0, v___x_2316_);
                leanh::lean_ctor_set(v___x_2317_, 1, v_zetaDeltaSet_2298_);
                leanh::lean_ctor_set(v___x_2317_, 2, v_lctx_2299_);
                leanh::lean_ctor_set(v___x_2317_, 3, v_localInstances_2300_);
                leanh::lean_ctor_set(v___x_2317_, 4, v_defEqCtx_x3f_2301_);
                leanh::lean_ctor_set(v___x_2317_, 5, v_synthPendingDepth_2302_);
                leanh::lean_ctor_set(v___x_2317_, 6, v_canUnfold_x3f_2303_);
                leanh::lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2297_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2304_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2305_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2306_,
                );
                leanh::lean_inc_ref(v_e_2258_);
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
                leanh::lean_dec_ref_known(v___x_2317_, 7);
                if leanh::lean_obj_tag(v___x_2318_) == 0 {
                    v_a_2319_ = leanh::lean_ctor_get(v___x_2318_, 0);
                    v_isSharedCheck_2352_ = (!leanh::lean_is_exclusive(v___x_2318_)) as u8;
                    if v_isSharedCheck_2352_ == 0 {
                        v___x_2321_ = v___x_2318_;
                        v_isShared_2322_ = v_isSharedCheck_2352_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2319_);
                        leanh::lean_dec(v___x_2318_);
                        v___x_2321_ = leanh::lean_box(0);
                        v_isShared_2322_ = v_isSharedCheck_2352_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_val_2274_);
                    leanh::lean_dec(v_a_2267_);
                    leanh::lean_dec_ref(v_e_2258_);
                    v_a_2353_ = leanh::lean_ctor_get(v___x_2318_, 0);
                    v_isSharedCheck_2360_ = (!leanh::lean_is_exclusive(v___x_2318_)) as u8;
                    if v_isSharedCheck_2360_ == 0 {
                        v___x_2355_ = v___x_2318_;
                        v_isShared_2356_ = v_isSharedCheck_2360_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2353_);
                        leanh::lean_dec(v___x_2318_);
                        v___x_2355_ = leanh::lean_box(0);
                        v_isShared_2356_ = v_isSharedCheck_2360_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_2323_ = leanh::lean_ctor_get(v_a_2319_, 0);
                v_isSharedCheck_2350_ = (!leanh::lean_is_exclusive(v_a_2319_)) as u8;
                if v_isSharedCheck_2350_ == 0 {
                    v_unused_2351_ = leanh::lean_ctor_get(v_a_2319_, 1);
                    leanh::lean_dec(v_unused_2351_);
                    v___x_2325_ = v_a_2319_;
                    v_isShared_2326_ = v_isSharedCheck_2350_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_2323_);
                    leanh::lean_dec(v_a_2319_);
                    v___x_2325_ = leanh::lean_box(0);
                    v_isShared_2326_ = v_isSharedCheck_2350_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_fst_2323_) == 0 {
                    v___x_2327_ = lean_st_ref_take(v_a_2260_);
                    v_cache_2328_ = leanh::lean_ctor_get(v___x_2327_, 0);
                    v_keyToExprs_2329_ = leanh::lean_ctor_get(v___x_2327_, 1);
                    v_isSharedCheck_2345_ = (!leanh::lean_is_exclusive(v___x_2327_)) as u8;
                    if v_isSharedCheck_2345_ == 0 {
                        v___x_2331_ = v___x_2327_;
                        v_isShared_2332_ = v_isSharedCheck_2345_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_keyToExprs_2329_);
                        leanh::lean_inc(v_cache_2328_);
                        leanh::lean_dec(v___x_2327_);
                        v___x_2331_ = leanh::lean_box(0);
                        v_isShared_2332_ = v_isSharedCheck_2345_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2325_);
                    leanh::lean_dec(v_val_2274_);
                    leanh::lean_dec(v_a_2267_);
                    leanh::lean_dec_ref(v_e_2258_);
                    v_val_2346_ = leanh::lean_ctor_get(v_fst_2323_, 0);
                    leanh::lean_inc(v_val_2346_);
                    leanh::lean_dec_ref_known(v_fst_2323_, 1);
                    if v_isShared_2322_ == 0 {
                        leanh::lean_ctor_set(v___x_2321_, 0, v_val_2346_);
                        v___x_2348_ = v___x_2321_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2349_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_val_2346_);
                        v___x_2348_ = v_reuseFailAlloc_2349_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                leanh::lean_inc_ref(v_e_2258_);
                if v_isShared_2326_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2325_, 1);
                    leanh::lean_ctor_set(v___x_2325_, 1, v_val_2274_);
                    leanh::lean_ctor_set(v___x_2325_, 0, v_e_2258_);
                    v___x_2334_ = v___x_2325_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2344_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_e_2258_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_val_2274_);
                    v___x_2334_ = v_reuseFailAlloc_2344_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2335_ = leanh::lean_unbox_uint64(v_a_2267_);
                leanh::lean_dec(v_a_2267_);
                v___x_2336_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_keyToExprs_2329_, v___x_2335_, v___x_2334_);
                if v_isShared_2332_ == 0 {
                    leanh::lean_ctor_set(v___x_2331_, 1, v___x_2336_);
                    v___x_2338_ = v___x_2331_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2343_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_cache_2328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2336_);
                    v___x_2338_ = v_reuseFailAlloc_2343_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2339_ = lean_st_ref_set(v_a_2260_, v___x_2338_);
                if v_isShared_2322_ == 0 {
                    leanh::lean_ctor_set(v___x_2321_, 0, v_e_2258_);
                    v___x_2341_ = v___x_2321_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_e_2258_);
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
                    v_reuseFailAlloc_2359_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
                    v___x_2358_ = v_reuseFailAlloc_2359_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2358_;
            }
            13 => {
                v___x_2369_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_e_2258_);
                v___x_2370_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2370_, 0, v_e_2258_);
                leanh::lean_ctor_set(v___x_2370_, 1, v___x_2369_);
                v___x_2371_ = leanh::lean_unbox_uint64(v_a_2267_);
                leanh::lean_dec(v_a_2267_);
                v___x_2372_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_keyToExprs_2365_, v___x_2371_, v___x_2370_);
                if v_isShared_2368_ == 0 {
                    leanh::lean_ctor_set(v___x_2367_, 1, v___x_2372_);
                    v___x_2374_ = v___x_2367_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_cache_2364_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2372_);
                    v___x_2374_ = v_reuseFailAlloc_2379_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2375_ = lean_st_ref_set(v_a_2260_, v___x_2374_);
                if v_isShared_2270_ == 0 {
                    leanh::lean_ctor_set(v___x_2269_, 0, v_e_2258_);
                    v___x_2377_ = v___x_2269_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2378_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_e_2258_);
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
                    v_reuseFailAlloc_2388_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
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
    mut v_e_2390_: *mut leanh::LeanObject,
    mut v_a_2391_: *mut leanh::LeanObject,
    mut v_a_2392_: *mut leanh::LeanObject,
    mut v_a_2393_: *mut leanh::LeanObject,
    mut v_a_2394_: *mut leanh::LeanObject,
    mut v_a_2395_: *mut leanh::LeanObject,
    mut v_a_2396_: *mut leanh::LeanObject,
    mut v_a_2397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2398_: u8 = 0;
    let mut v_res_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2398_ = (leanh::lean_unbox(v_a_2391_) as u8);
    v_res_2399_ = l_Lean_Meta_Canonicalizer_canon(
        v_e_2390_,
        v_a_boxed_2398_,
        v_a_2392_,
        v_a_2393_,
        v_a_2394_,
        v_a_2395_,
        v_a_2396_,
    );
    leanh::lean_dec(v_a_2396_);
    leanh::lean_dec_ref(v_a_2395_);
    leanh::lean_dec(v_a_2394_);
    leanh::lean_dec_ref(v_a_2393_);
    leanh::lean_dec(v_a_2392_);
    return v_res_2399_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0(
    mut v_e_2400_: *mut leanh::LeanObject,
    mut v_as_2401_: *mut leanh::LeanObject,
    mut v_as_x27_2402_: *mut leanh::LeanObject,
    mut v_b_2403_: *mut leanh::LeanObject,
    mut v_a_2404_: *mut leanh::LeanObject,
    mut v___y_2405_: u8,
    mut v___y_2406_: *mut leanh::LeanObject,
    mut v___y_2407_: *mut leanh::LeanObject,
    mut v___y_2408_: *mut leanh::LeanObject,
    mut v___y_2409_: *mut leanh::LeanObject,
    mut v___y_2410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_2413_: *mut leanh::LeanObject,
    mut v_as_2414_: *mut leanh::LeanObject,
    mut v_as_x27_2415_: *mut leanh::LeanObject,
    mut v_b_2416_: *mut leanh::LeanObject,
    mut v_a_2417_: *mut leanh::LeanObject,
    mut v___y_2418_: *mut leanh::LeanObject,
    mut v___y_2419_: *mut leanh::LeanObject,
    mut v___y_2420_: *mut leanh::LeanObject,
    mut v___y_2421_: *mut leanh::LeanObject,
    mut v___y_2422_: *mut leanh::LeanObject,
    mut v___y_2423_: *mut leanh::LeanObject,
    mut v___y_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_10919__boxed_2425_: u8 = 0;
    let mut v_res_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_10919__boxed_2425_ = (leanh::lean_unbox(v___y_2418_) as u8);
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
    leanh::lean_dec(v___y_2423_);
    leanh::lean_dec_ref(v___y_2422_);
    leanh::lean_dec(v___y_2421_);
    leanh::lean_dec_ref(v___y_2420_);
    leanh::lean_dec(v___y_2419_);
    leanh::lean_dec(v_as_x27_2415_);
    leanh::lean_dec(v_as_2414_);
    return v_res_2426_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1(
    mut v_00_u03b2_2427_: *mut leanh::LeanObject,
    mut v_m_2428_: *mut leanh::LeanObject,
    mut v_a_2429_: u64,
    mut v_b_2430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2431_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_m_2428_, v_a_2429_, v_b_2430_);
    return v___x_2431_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___boxed(
    mut v_00_u03b2_2432_: *mut leanh::LeanObject,
    mut v_m_2433_: *mut leanh::LeanObject,
    mut v_a_2434_: *mut leanh::LeanObject,
    mut v_b_2435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2436_: u64 = 0;
    let mut v_res_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2436_ = leanh::lean_unbox_uint64(v_a_2434_);
    leanh::lean_dec_ref(v_a_2434_);
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
    mut v_00_u03b2_2438_: *mut leanh::LeanObject,
    mut v_a_2439_: u64,
    mut v_x_2440_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2441_: u8 = 0;
    v___x_2441_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_2439_, v_x_2440_);
    return v___x_2441_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___boxed(
    mut v_00_u03b2_2442_: *mut leanh::LeanObject,
    mut v_a_2443_: *mut leanh::LeanObject,
    mut v_x_2444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2445_: u64 = 0;
    let mut v_res_2446_: u8 = 0;
    let mut v_r_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2445_ = leanh::lean_unbox_uint64(v_a_2443_);
    leanh::lean_dec_ref(v_a_2443_);
    v_res_2446_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1(v_00_u03b2_2442_, v_a_boxed_2445_, v_x_2444_);
    leanh::lean_dec(v_x_2444_);
    v_r_2447_ = leanh::lean_box((v_res_2446_) as usize);
    return v_r_2447_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2(
    mut v_00_u03b2_2448_: *mut leanh::LeanObject,
    mut v_data_2449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(v_data_2449_);
    return v___x_2450_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3(
    mut v_00_u03b2_2451_: *mut leanh::LeanObject,
    mut v_a_2452_: u64,
    mut v_b_2453_: *mut leanh::LeanObject,
    mut v_x_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_2452_, v_b_2453_, v_x_2454_);
    return v___x_2455_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___boxed(
    mut v_00_u03b2_2456_: *mut leanh::LeanObject,
    mut v_a_2457_: *mut leanh::LeanObject,
    mut v_b_2458_: *mut leanh::LeanObject,
    mut v_x_2459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2460_: u64 = 0;
    let mut v_res_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2460_ = leanh::lean_unbox_uint64(v_a_2457_);
    leanh::lean_dec_ref(v_a_2457_);
    v_res_2461_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3(v_00_u03b2_2456_, v_a_boxed_2460_, v_b_2458_, v_x_2459_);
    return v_res_2461_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2462_: *mut leanh::LeanObject,
    mut v_i_2463_: *mut leanh::LeanObject,
    mut v_source_2464_: *mut leanh::LeanObject,
    mut v_target_2465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(v_i_2463_, v_source_2464_, v_target_2465_);
    return v___x_2466_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2467_: *mut leanh::LeanObject,
    mut v_x_2468_: *mut leanh::LeanObject,
    mut v_x_2469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2470_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2468_, v_x_2469_);
    return v___x_2470_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Canonicalizer(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_ShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default =
        _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default);
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited =
        _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited();
    leanh::lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited);
    l_Lean_Meta_Canonicalizer_instInhabitedState =
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState();
    leanh::lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState);
    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1 = _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Canonicalizer(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Canonicalizer(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_ShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_FunInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Canonicalizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Canonicalizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Canonicalizer(builtin);
}