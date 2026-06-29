// Lean compiler output
// Module: Lean.Meta.Sym.AlphaShareCommon
// Imports: Lean.Meta.Sym.ExprPtr
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Data::KVMap::l_Lean_KVMap_eqv;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_findEntry_x3f___redArg, l_Lean_PersistentHashMap_findKeyDAux___redArg,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_hash,
    l_Lean_Expr_lam___override, l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override,
    l_Lean_Expr_proj___override, l_Lean_instBEqBinderInfo_beq, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    initialize_Lean_Meta_Sym_ExprPtr,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1, l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed,
    runtime_initialize_Lean_Meta_Sym_ExprPtr,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_uint64_mix_hash, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0: u64 =
    0;
pub static l_Lean_Meta_Sym_instHashableAlphaKey___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_instHashableAlphaKey___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instHashableAlphaKey: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instBEqAlphaKey___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instBEqAlphaKey___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instBEqAlphaKey: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [95, 95, 100, 117, 109, 109, 121, 95, 95, 0],
};
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1_value:
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
            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        9304292590189383094 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0_value:
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
    m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1_value:
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
    m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_shareCommonAlpha___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_shareCommonAlpha___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_shareCommonAlpha___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_shareCommonAlpha___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
    mut v_e_1186_: *mut crate::leanh::LeanObject,
) -> u64 {
    match crate::leanh::lean_obj_tag(v_e_1186_) {
        5 => {
            let mut v___x_1187_: u64 = 0;
            v___x_1187_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1187_;
        }
        6 => {
            let mut v___x_1188_: u64 = 0;
            v___x_1188_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1188_;
        }
        7 => {
            let mut v___x_1189_: u64 = 0;
            v___x_1189_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1189_;
        }
        8 => {
            let mut v___x_1190_: u64 = 0;
            v___x_1190_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1190_;
        }
        10 => {
            let mut v___x_1191_: u64 = 0;
            v___x_1191_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1191_;
        }
        11 => {
            let mut v___x_1192_: u64 = 0;
            v___x_1192_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1186_);
            return v___x_1192_;
        }
        _ => {
            let mut v___x_1193_: u64 = 0;
            v___x_1193_ = l_Lean_Expr_hash(v_e_1186_);
            return v___x_1193_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild___boxed(
    mut v_e_1194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1195_: u64 = 0;
    let mut v_r_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1195_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_e_1194_);
    crate::leanh::lean_dec_ref(v_e_1194_);
    v_r_1196_ = crate::leanh::lean_box_uint64(v_res_1195_);
    return v_r_1196_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0()
-> u64 {
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: u64 = 0;
    v___x_1197_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1198_ = lean_uint64_of_nat(v___x_1197_);
    return v___x_1198_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
    mut v_e_1199_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_d_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u64 = 0;
    let mut v___x_1204_: u64 = 0;
    let mut v___x_1205_: u64 = 0;
    let mut v_fn_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: u64 = 0;
    let mut v___x_1209_: u64 = 0;
    let mut v___x_1210_: u64 = 0;
    let mut v_binderType_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u64 = 0;
    let mut v___x_1218_: u64 = 0;
    let mut v___x_1219_: u64 = 0;
    let mut v_expr_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: u64 = 0;
    let mut v___x_1222_: u64 = 0;
    let mut v___x_1223_: u64 = 0;
    let mut v_typeName_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1228_: u64 = 0;
    let mut v___x_1229_: u64 = 0;
    let mut v___x_1230_: u64 = 0;
    let mut v___x_1231_: u64 = 0;
    let mut v___x_1232_: u64 = 0;
    let mut v___x_1233_: u64 = 0;
    let mut v_hash_1234_: u64 = 0;
    let mut v___x_1235_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_1199_) {
                5 => {
                    v_fn_1206_ = crate::leanh::lean_ctor_get(v_e_1199_, 0);
                    v_arg_1207_ = crate::leanh::lean_ctor_get(v_e_1199_, 1);
                    v___x_1208_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                            v_fn_1206_,
                        );
                    v___x_1209_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                            v_arg_1207_,
                        );
                    v___x_1210_ = lean_uint64_mix_hash(v___x_1208_, v___x_1209_);
                    return v___x_1210_;
                }
                6 => {
                    v_binderType_1211_ = crate::leanh::lean_ctor_get(v_e_1199_, 1);
                    v_body_1212_ = crate::leanh::lean_ctor_get(v_e_1199_, 2);
                    v_d_1201_ = v_binderType_1211_;
                    v_b_1202_ = v_body_1212_;
                    state = 1;
                    continue;
                }
                7 => {
                    v_binderType_1213_ = crate::leanh::lean_ctor_get(v_e_1199_, 1);
                    v_body_1214_ = crate::leanh::lean_ctor_get(v_e_1199_, 2);
                    v_d_1201_ = v_binderType_1213_;
                    v_b_1202_ = v_body_1214_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_value_1215_ = crate::leanh::lean_ctor_get(v_e_1199_, 2);
                    v_body_1216_ = crate::leanh::lean_ctor_get(v_e_1199_, 3);
                    v___x_1217_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                            v_value_1215_,
                        );
                    v___x_1218_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                            v_body_1216_,
                        );
                    v___x_1219_ = lean_uint64_mix_hash(v___x_1217_, v___x_1218_);
                    return v___x_1219_;
                }
                10 => {
                    v_expr_1220_ = crate::leanh::lean_ctor_get(v_e_1199_, 1);
                    v___x_1221_ = 13u64;
                    v___x_1222_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                            v_expr_1220_,
                        );
                    v___x_1223_ = lean_uint64_mix_hash(v___x_1221_, v___x_1222_);
                    return v___x_1223_;
                }
                11 => {
                    v_typeName_1224_ = crate::leanh::lean_ctor_get(v_e_1199_, 0);
                    v_idx_1225_ = crate::leanh::lean_ctor_get(v_e_1199_, 1);
                    v_struct_1226_ = crate::leanh::lean_ctor_get(v_e_1199_, 2);
                    if crate::leanh::lean_obj_tag(v_typeName_1224_) == 0 {
                        v___x_1233_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0_once), _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0);
                        v___y_1228_ = v___x_1233_;
                        state = 2;
                        continue;
                    } else {
                        v_hash_1234_ = crate::leanh::lean_ctor_get_uint64(
                            v_typeName_1224_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_1228_ = v_hash_1234_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_1235_ = l_Lean_Expr_hash(v_e_1199_);
                    return v___x_1235_;
                }
            },
            1 => {
                v___x_1203_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                    v_d_1201_,
                );
                v___x_1204_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                    v_b_1202_,
                );
                v___x_1205_ = lean_uint64_mix_hash(v___x_1203_, v___x_1204_);
                return v___x_1205_;
            }
            2 => {
                v___x_1229_ = lean_uint64_of_nat(v_idx_1225_);
                v___x_1230_ = lean_uint64_mix_hash(v___y_1228_, v___x_1229_);
                v___x_1231_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(
                    v_struct_1226_,
                );
                v___x_1232_ = lean_uint64_mix_hash(v___x_1230_, v___x_1231_);
                return v___x_1232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(
    mut v_e_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1237_: u64 = 0;
    let mut v_r_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1236_);
    crate::leanh::lean_dec_ref(v_e_1236_);
    v_r_1238_ = crate::leanh::lean_box_uint64(v_res_1237_);
    return v_r_1238_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
    mut v_e_u2081_1239_: *mut crate::leanh::LeanObject,
    mut v_e_u2082_1240_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fn_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1246_: u8 = 0;
    let mut v___x_1247_: u8 = 0;
    let mut v_binderType_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: u8 = 0;
    let mut v___x_1253_: u8 = 0;
    let mut v___x_1254_: u8 = 0;
    let mut v_binderType_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: u8 = 0;
    let mut v___x_1260_: u8 = 0;
    let mut v___x_1261_: u8 = 0;
    let mut v_value_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: u8 = 0;
    let mut v___x_1268_: u8 = 0;
    let mut v_data_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u8 = 0;
    let mut v___x_1274_: u8 = 0;
    let mut v___x_1275_: u8 = 0;
    let mut v_typeName_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1283_: u8 = 0;
    let mut v___x_1284_: u8 = 0;
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: u8 = 0;
    let mut v___x_1287_: u8 = 0;
    let mut v___x_1288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_e_u2081_1239_) {
                    5 => {
                        if crate::leanh::lean_obj_tag(v_e_u2082_1240_) == 5 {
                            v_fn_1241_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 0);
                            crate::leanh::lean_inc_ref(v_fn_1241_);
                            v_arg_1242_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 1);
                            crate::leanh::lean_inc_ref(v_arg_1242_);
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 2);
                            v_fn_1243_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 0);
                            crate::leanh::lean_inc_ref(v_fn_1243_);
                            v_arg_1244_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 1);
                            crate::leanh::lean_inc_ref(v_arg_1244_);
                            crate::leanh::lean_dec_ref_known(v_e_u2082_1240_, 2);
                            v___x_1245_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1241_, v_fn_1243_);
                            crate::leanh::lean_dec_ref(v_fn_1243_);
                            crate::leanh::lean_dec_ref(v_fn_1241_);
                            if v___x_1245_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_1244_);
                                crate::leanh::lean_dec_ref(v_arg_1242_);
                                return v___x_1245_;
                            } else {
                                v___x_1246_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1242_, v_arg_1244_);
                                crate::leanh::lean_dec_ref(v_arg_1244_);
                                crate::leanh::lean_dec_ref(v_arg_1242_);
                                return v___x_1246_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 2);
                            crate::leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1247_ = 0;
                            return v___x_1247_;
                        }
                    }
                    6 => {
                        if crate::leanh::lean_obj_tag(v_e_u2082_1240_) == 6 {
                            v_binderType_1248_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_1248_);
                            v_body_1249_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 2);
                            crate::leanh::lean_inc_ref(v_body_1249_);
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            v_binderType_1250_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_1250_);
                            v_body_1251_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 2);
                            crate::leanh::lean_inc_ref(v_body_1251_);
                            crate::leanh::lean_dec_ref_known(v_e_u2082_1240_, 3);
                            v___x_1252_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1248_, v_binderType_1250_);
                            crate::leanh::lean_dec_ref(v_binderType_1250_);
                            crate::leanh::lean_dec_ref(v_binderType_1248_);
                            if v___x_1252_ == 0 {
                                crate::leanh::lean_dec_ref(v_body_1251_);
                                crate::leanh::lean_dec_ref(v_body_1249_);
                                return v___x_1252_;
                            } else {
                                v___x_1253_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1249_, v_body_1251_);
                                crate::leanh::lean_dec_ref(v_body_1251_);
                                crate::leanh::lean_dec_ref(v_body_1249_);
                                return v___x_1253_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            crate::leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1254_ = 0;
                            return v___x_1254_;
                        }
                    }
                    7 => {
                        if crate::leanh::lean_obj_tag(v_e_u2082_1240_) == 7 {
                            v_binderType_1255_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_1255_);
                            v_body_1256_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 2);
                            crate::leanh::lean_inc_ref(v_body_1256_);
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            v_binderType_1257_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_1257_);
                            v_body_1258_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 2);
                            crate::leanh::lean_inc_ref(v_body_1258_);
                            crate::leanh::lean_dec_ref_known(v_e_u2082_1240_, 3);
                            v___x_1259_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1255_, v_binderType_1257_);
                            crate::leanh::lean_dec_ref(v_binderType_1257_);
                            crate::leanh::lean_dec_ref(v_binderType_1255_);
                            if v___x_1259_ == 0 {
                                crate::leanh::lean_dec_ref(v_body_1258_);
                                crate::leanh::lean_dec_ref(v_body_1256_);
                                return v___x_1259_;
                            } else {
                                v___x_1260_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1256_, v_body_1258_);
                                crate::leanh::lean_dec_ref(v_body_1258_);
                                crate::leanh::lean_dec_ref(v_body_1256_);
                                return v___x_1260_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            crate::leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1261_ = 0;
                            return v___x_1261_;
                        }
                    }
                    8 => {
                        if crate::leanh::lean_obj_tag(v_e_u2082_1240_) == 8 {
                            v_value_1262_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 2);
                            crate::leanh::lean_inc_ref(v_value_1262_);
                            v_body_1263_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 3);
                            crate::leanh::lean_inc_ref(v_body_1263_);
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 4);
                            v_value_1264_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 2);
                            crate::leanh::lean_inc_ref(v_value_1264_);
                            v_body_1265_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 3);
                            crate::leanh::lean_inc_ref(v_body_1265_);
                            crate::leanh::lean_dec_ref_known(v_e_u2082_1240_, 4);
                            v___x_1266_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1262_, v_value_1264_);
                            crate::leanh::lean_dec_ref(v_value_1264_);
                            crate::leanh::lean_dec_ref(v_value_1262_);
                            if v___x_1266_ == 0 {
                                crate::leanh::lean_dec_ref(v_body_1265_);
                                crate::leanh::lean_dec_ref(v_body_1263_);
                                return v___x_1266_;
                            } else {
                                v___x_1267_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1263_, v_body_1265_);
                                crate::leanh::lean_dec_ref(v_body_1265_);
                                crate::leanh::lean_dec_ref(v_body_1263_);
                                return v___x_1267_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 4);
                            crate::leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1268_ = 0;
                            return v___x_1268_;
                        }
                    }
                    10 => {
                        if crate::leanh::lean_obj_tag(v_e_u2082_1240_) == 10 {
                            v_data_1269_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 0);
                            crate::leanh::lean_inc(v_data_1269_);
                            v_expr_1270_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 1);
                            crate::leanh::lean_inc_ref(v_expr_1270_);
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 2);
                            v_data_1271_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 0);
                            crate::leanh::lean_inc(v_data_1271_);
                            v_expr_1272_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 1);
                            crate::leanh::lean_inc_ref(v_expr_1272_);
                            crate::leanh::lean_dec_ref_known(v_e_u2082_1240_, 2);
                            v___x_1273_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1270_, v_expr_1272_);
                            crate::leanh::lean_dec_ref(v_expr_1272_);
                            crate::leanh::lean_dec_ref(v_expr_1270_);
                            if v___x_1273_ == 0 {
                                crate::leanh::lean_dec(v_data_1271_);
                                crate::leanh::lean_dec(v_data_1269_);
                                return v___x_1273_;
                            } else {
                                v___x_1274_ = l_Lean_KVMap_eqv(v_data_1269_, v_data_1271_);
                                return v___x_1274_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 2);
                            crate::leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1275_ = 0;
                            return v___x_1275_;
                        }
                    }
                    11 => {
                        if crate::leanh::lean_obj_tag(v_e_u2082_1240_) == 11 {
                            v_typeName_1276_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 0);
                            crate::leanh::lean_inc(v_typeName_1276_);
                            v_idx_1277_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 1);
                            crate::leanh::lean_inc(v_idx_1277_);
                            v_struct_1278_ = crate::leanh::lean_ctor_get(v_e_u2081_1239_, 2);
                            crate::leanh::lean_inc_ref(v_struct_1278_);
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            v_typeName_1279_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 0);
                            crate::leanh::lean_inc(v_typeName_1279_);
                            v_idx_1280_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 1);
                            crate::leanh::lean_inc(v_idx_1280_);
                            v_struct_1281_ = crate::leanh::lean_ctor_get(v_e_u2082_1240_, 2);
                            crate::leanh::lean_inc_ref(v_struct_1281_);
                            crate::leanh::lean_dec_ref_known(v_e_u2082_1240_, 3);
                            v___x_1285_ = lean_name_eq(v_typeName_1276_, v_typeName_1279_);
                            crate::leanh::lean_dec(v_typeName_1279_);
                            crate::leanh::lean_dec(v_typeName_1276_);
                            if v___x_1285_ == 0 {
                                crate::leanh::lean_dec(v_idx_1280_);
                                crate::leanh::lean_dec(v_idx_1277_);
                                v___y_1283_ = v___x_1285_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1286_ = lean_nat_dec_eq(v_idx_1277_, v_idx_1280_);
                                crate::leanh::lean_dec(v_idx_1280_);
                                crate::leanh::lean_dec(v_idx_1277_);
                                v___y_1283_ = v___x_1286_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_u2081_1239_, 3);
                            crate::leanh::lean_dec_ref(v_e_u2082_1240_);
                            v___x_1287_ = 0;
                            return v___x_1287_;
                        }
                    }
                    _ => {
                        v___x_1288_ = lean_expr_eqv(v_e_u2081_1239_, v_e_u2082_1240_);
                        crate::leanh::lean_dec_ref(v_e_u2082_1240_);
                        crate::leanh::lean_dec_ref(v_e_u2081_1239_);
                        return v___x_1288_;
                    }
                }
            }
            1 => {
                if v___y_1283_ == 0 {
                    crate::leanh::lean_dec_ref(v_struct_1281_);
                    crate::leanh::lean_dec_ref(v_struct_1278_);
                    return v___y_1283_;
                } else {
                    v___x_1284_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_struct_1278_,
                            v_struct_1281_,
                        );
                    crate::leanh::lean_dec_ref(v_struct_1281_);
                    crate::leanh::lean_dec_ref(v_struct_1278_);
                    return v___x_1284_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(
    mut v_e_u2081_1289_: *mut crate::leanh::LeanObject,
    mut v_e_u2082_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1291_: u8 = 0;
    let mut v_r_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1291_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
        v_e_u2081_1289_,
        v_e_u2082_1290_,
    );
    v_r_1292_ = crate::leanh::lean_box((v_res_1291_) as usize);
    return v_r_1292_;
}
pub unsafe fn l_Lean_Meta_Sym_instHashableAlphaKey___private__1(
    mut v_k_1293_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_1294_: u64 = 0;
    v___x_1294_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_1293_);
    return v___x_1294_;
}
pub unsafe fn l_Lean_Meta_Sym_instHashableAlphaKey___private__1___boxed(
    mut v_k_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1296_: u64 = 0;
    let mut v_r_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1296_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_1295_);
    crate::leanh::lean_dec_ref(v_k_1295_);
    v_r_1297_ = crate::leanh::lean_box_uint64(v_res_1296_);
    return v_r_1297_;
}
pub unsafe fn l_Lean_Meta_Sym_instBEqAlphaKey___private__1(
    mut v_k_u2081_1300_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_1301_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1302_: u8 = 0;
    v___x_1302_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
        v_k_u2081_1300_,
        v_k_u2082_1301_,
    );
    return v___x_1302_;
}
pub unsafe fn l_Lean_Meta_Sym_instBEqAlphaKey___private__1___boxed(
    mut v_k_u2081_1303_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1305_: u8 = 0;
    let mut v_r_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1305_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_u2081_1303_, v_k_u2082_1304_);
    v_r_1306_ = crate::leanh::lean_box((v_res_1305_) as usize);
    return v_r_1306_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = crate::leanh::lean_box(0);
    v___x_1313_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1;
    v___x_1314_ = l_Lean_mkConst(v___x_1313_, v___x_1312_);
    return v___x_1314_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once
        ),
        _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2,
    );
    return v___x_1315_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(
    mut v_keys_1316_: *mut crate::leanh::LeanObject,
    mut v_i_1317_: *mut crate::leanh::LeanObject,
    mut v_k_1318_: *mut crate::leanh::LeanObject,
    mut v_k_u2080_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v_k_x27_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1320_ = lean_array_get_size(v_keys_1316_);
                v___x_1321_ = lean_nat_dec_lt(v_i_1317_, v___x_1320_);
                if v___x_1321_ == 0 {
                    crate::leanh::lean_dec_ref(v_k_1318_);
                    crate::leanh::lean_dec(v_i_1317_);
                    crate::leanh::lean_inc_ref(v_k_u2080_1319_);
                    return v_k_u2080_1319_;
                } else {
                    v_k_x27_1322_ = lean_array_fget_borrowed(v_keys_1316_, v_i_1317_);
                    crate::leanh::lean_inc(v_k_x27_1322_);
                    crate::leanh::lean_inc_ref(v_k_1318_);
                    v___x_1323_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_k_1318_,
                            v_k_x27_1322_,
                        );
                    if v___x_1323_ == 0 {
                        v___x_1324_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1325_ = lean_nat_add(v_i_1317_, v___x_1324_);
                        crate::leanh::lean_dec(v_i_1317_);
                        v_i_1317_ = v___x_1325_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_1318_);
                        crate::leanh::lean_dec(v_i_1317_);
                        crate::leanh::lean_inc(v_k_x27_1322_);
                        return v_k_x27_1322_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(
    mut v_keys_1327_: *mut crate::leanh::LeanObject,
    mut v_i_1328_: *mut crate::leanh::LeanObject,
    mut v_k_1329_: *mut crate::leanh::LeanObject,
    mut v_k_u2080_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1331_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_1327_, v_i_1328_, v_k_1329_, v_k_u2080_1330_);
    crate::leanh::lean_dec_ref(v_k_u2080_1330_);
    crate::leanh::lean_dec_ref(v_keys_1327_);
    return v_res_1331_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_1332_: usize = 0;
    let mut v___x_1333_: usize = 0;
    let mut v___x_1334_: usize = 0;
    v___x_1332_ = 5usize;
    v___x_1333_ = 1usize;
    v___x_1334_ = lean_usize_shift_left(v___x_1333_, v___x_1332_);
    return v___x_1334_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_1335_: usize = 0;
    let mut v___x_1336_: usize = 0;
    let mut v___x_1337_: usize = 0;
    v___x_1335_ = 1usize;
    v___x_1336_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0);
    v___x_1337_ = lean_usize_sub(v___x_1336_, v___x_1335_);
    return v___x_1337_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(
    mut v_x_1338_: *mut crate::leanh::LeanObject,
    mut v_x_1339_: usize,
    mut v_x_1340_: *mut crate::leanh::LeanObject,
    mut v_x_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: usize = 0;
    let mut v___x_1345_: usize = 0;
    let mut v___x_1346_: usize = 0;
    let mut v_j_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: u8 = 0;
    let mut v_node_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: usize = 0;
    let mut v_ks_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1338_) == 0 {
                    v_es_1342_ = crate::leanh::lean_ctor_get(v_x_1338_, 0);
                    crate::leanh::lean_inc_ref(v_es_1342_);
                    crate::leanh::lean_dec_ref_known(v_x_1338_, 1);
                    v___x_1343_ = crate::leanh::lean_box(2);
                    v___x_1344_ = 5usize;
                    v___x_1345_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1);
                    v___x_1346_ = lean_usize_land(v_x_1339_, v___x_1345_);
                    v_j_1347_ = lean_usize_to_nat(v___x_1346_);
                    v___x_1348_ = lean_array_get(v___x_1343_, v_es_1342_, v_j_1347_);
                    crate::leanh::lean_dec(v_j_1347_);
                    crate::leanh::lean_dec_ref(v_es_1342_);
                    match crate::leanh::lean_obj_tag(v___x_1348_) {
                        0 => {
                            v_key_1349_ = crate::leanh::lean_ctor_get(v___x_1348_, 0);
                            crate::leanh::lean_inc_n(v_key_1349_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_1348_, 2);
                            v___x_1350_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                                    v_x_1340_,
                                    v_key_1349_,
                                );
                            if v___x_1350_ == 0 {
                                crate::leanh::lean_dec(v_key_1349_);
                                crate::leanh::lean_inc_ref(v_x_1341_);
                                return v_x_1341_;
                            } else {
                                return v_key_1349_;
                            }
                        }
                        1 => {
                            v_node_1351_ = crate::leanh::lean_ctor_get(v___x_1348_, 0);
                            crate::leanh::lean_inc(v_node_1351_);
                            crate::leanh::lean_dec_ref_known(v___x_1348_, 1);
                            v___x_1352_ = lean_usize_shift_right(v_x_1339_, v___x_1344_);
                            v_x_1338_ = v_node_1351_;
                            v_x_1339_ = v___x_1352_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_x_1340_);
                            crate::leanh::lean_inc_ref(v_x_1341_);
                            return v_x_1341_;
                        }
                    }
                } else {
                    v_ks_1354_ = crate::leanh::lean_ctor_get(v_x_1338_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1354_);
                    crate::leanh::lean_dec_ref_known(v_x_1338_, 2);
                    v___x_1355_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1356_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_ks_1354_, v___x_1355_, v_x_1340_, v_x_1341_);
                    crate::leanh::lean_dec_ref(v_ks_1354_);
                    return v___x_1356_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(
    mut v_x_1357_: *mut crate::leanh::LeanObject,
    mut v_x_1358_: *mut crate::leanh::LeanObject,
    mut v_x_1359_: *mut crate::leanh::LeanObject,
    mut v_x_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1916__boxed_1361_: usize = 0;
    let mut v_res_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1916__boxed_1361_ = crate::leanh::lean_unbox_usize(v_x_1358_);
    crate::leanh::lean_dec(v_x_1358_);
    v_res_1362_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_1357_, v_x_1916__boxed_1361_, v_x_1359_, v_x_1360_);
    crate::leanh::lean_dec_ref(v_x_1360_);
    return v_res_1362_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(
    mut v_x_1363_: *mut crate::leanh::LeanObject,
    mut v_x_1364_: *mut crate::leanh::LeanObject,
    mut v_x_1365_: *mut crate::leanh::LeanObject,
    mut v_x_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1371_: u8 = 0;
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1367_ = crate::leanh::lean_ctor_get(v_x_1363_, 0);
                v_vs_1368_ = crate::leanh::lean_ctor_get(v_x_1363_, 1);
                v_isSharedCheck_1392_ = (!crate::leanh::lean_is_exclusive(v_x_1363_)) as u8;
                if v_isSharedCheck_1392_ == 0 {
                    v___x_1370_ = v_x_1363_;
                    v_isShared_1371_ = v_isSharedCheck_1392_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1368_);
                    crate::leanh::lean_inc(v_ks_1367_);
                    crate::leanh::lean_dec(v_x_1363_);
                    v___x_1370_ = crate::leanh::lean_box(0);
                    v_isShared_1371_ = v_isSharedCheck_1392_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1372_ = lean_array_get_size(v_ks_1367_);
                v___x_1373_ = lean_nat_dec_lt(v_x_1364_, v___x_1372_);
                if v___x_1373_ == 0 {
                    crate::leanh::lean_dec(v_x_1364_);
                    v___x_1374_ = lean_array_push(v_ks_1367_, v_x_1365_);
                    v___x_1375_ = lean_array_push(v_vs_1368_, v_x_1366_);
                    if v_isShared_1371_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1370_, 1, v___x_1375_);
                        crate::leanh::lean_ctor_set(v___x_1370_, 0, v___x_1374_);
                        v___x_1377_ = v___x_1370_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1378_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1374_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1375_);
                        v___x_1377_ = v_reuseFailAlloc_1378_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1379_ = lean_array_fget_borrowed(v_ks_1367_, v_x_1364_);
                    crate::leanh::lean_inc(v_k_x27_1379_);
                    crate::leanh::lean_inc_ref(v_x_1365_);
                    v___x_1380_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_x_1365_,
                            v_k_x27_1379_,
                        );
                    if v___x_1380_ == 0 {
                        if v_isShared_1371_ == 0 {
                            v___x_1382_ = v___x_1370_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1386_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_ks_1367_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_vs_1368_);
                            v___x_1382_ = v_reuseFailAlloc_1386_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1387_ = lean_array_fset(v_ks_1367_, v_x_1364_, v_x_1365_);
                        v___x_1388_ = lean_array_fset(v_vs_1368_, v_x_1364_, v_x_1366_);
                        crate::leanh::lean_dec(v_x_1364_);
                        if v_isShared_1371_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1370_, 1, v___x_1388_);
                            crate::leanh::lean_ctor_set(v___x_1370_, 0, v___x_1387_);
                            v___x_1390_ = v___x_1370_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1391_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1387_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 1, v___x_1388_);
                            v___x_1390_ = v_reuseFailAlloc_1391_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1377_;
            }
            3 => {
                v___x_1383_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1384_ = lean_nat_add(v_x_1364_, v___x_1383_);
                crate::leanh::lean_dec(v_x_1364_);
                v_x_1363_ = v___x_1382_;
                v_x_1364_ = v___x_1384_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(
    mut v_n_1393_: *mut crate::leanh::LeanObject,
    mut v_k_1394_: *mut crate::leanh::LeanObject,
    mut v_v_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1397_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_n_1393_, v___x_1396_, v_k_1394_, v_v_1395_);
    return v___x_1397_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1398_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1398_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(
    mut v_x_1399_: *mut crate::leanh::LeanObject,
    mut v_x_1400_: usize,
    mut v_x_1401_: usize,
    mut v_x_1402_: *mut crate::leanh::LeanObject,
    mut v_x_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: usize = 0;
    let mut v___x_1406_: usize = 0;
    let mut v___x_1407_: usize = 0;
    let mut v___x_1408_: usize = 0;
    let mut v_j_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: u8 = 0;
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v_v_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1428_: u8 = 0;
    let mut v___x_1429_: u8 = 0;
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1435_: u8 = 0;
    let mut v_node_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1440_: usize = 0;
    let mut v___x_1441_: usize = 0;
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1448_: u8 = 0;
    let mut v_unused_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1454_: u8 = 0;
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: u8 = 0;
    let mut v_ks_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: usize = 0;
    let mut v___x_1466_: u8 = 0;
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v_reuseFailAlloc_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1399_) == 0 {
                    v_es_1404_ = crate::leanh::lean_ctor_get(v_x_1399_, 0);
                    v___x_1405_ = 5usize;
                    v___x_1406_ = 1usize;
                    v___x_1407_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1);
                    v___x_1408_ = lean_usize_land(v_x_1400_, v___x_1407_);
                    v_j_1409_ = lean_usize_to_nat(v___x_1408_);
                    v___x_1410_ = lean_array_get_size(v_es_1404_);
                    v___x_1411_ = lean_nat_dec_lt(v_j_1409_, v___x_1410_);
                    if v___x_1411_ == 0 {
                        crate::leanh::lean_dec(v_j_1409_);
                        crate::leanh::lean_dec(v_x_1403_);
                        crate::leanh::lean_dec_ref(v_x_1402_);
                        return v_x_1399_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1404_);
                        v_isSharedCheck_1448_ = (!crate::leanh::lean_is_exclusive(v_x_1399_)) as u8;
                        if v_isSharedCheck_1448_ == 0 {
                            v_unused_1449_ = crate::leanh::lean_ctor_get(v_x_1399_, 0);
                            crate::leanh::lean_dec(v_unused_1449_);
                            v___x_1413_ = v_x_1399_;
                            v_isShared_1414_ = v_isSharedCheck_1448_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1399_);
                            v___x_1413_ = crate::leanh::lean_box(0);
                            v_isShared_1414_ = v_isSharedCheck_1448_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1450_ = crate::leanh::lean_ctor_get(v_x_1399_, 0);
                    v_vs_1451_ = crate::leanh::lean_ctor_get(v_x_1399_, 1);
                    v_isSharedCheck_1471_ = (!crate::leanh::lean_is_exclusive(v_x_1399_)) as u8;
                    if v_isSharedCheck_1471_ == 0 {
                        v___x_1453_ = v_x_1399_;
                        v_isShared_1454_ = v_isSharedCheck_1471_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1451_);
                        crate::leanh::lean_inc(v_ks_1450_);
                        crate::leanh::lean_dec(v_x_1399_);
                        v___x_1453_ = crate::leanh::lean_box(0);
                        v_isShared_1454_ = v_isSharedCheck_1471_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1415_ = lean_array_fget(v_es_1404_, v_j_1409_);
                v___x_1416_ = crate::leanh::lean_box(0);
                v_xs_x27_1417_ = lean_array_fset(v_es_1404_, v_j_1409_, v___x_1416_);
                match crate::leanh::lean_obj_tag(v_v_1415_) {
                    0 => {
                        v_key_1424_ = crate::leanh::lean_ctor_get(v_v_1415_, 0);
                        v_val_1425_ = crate::leanh::lean_ctor_get(v_v_1415_, 1);
                        v_isSharedCheck_1435_ = (!crate::leanh::lean_is_exclusive(v_v_1415_)) as u8;
                        if v_isSharedCheck_1435_ == 0 {
                            v___x_1427_ = v_v_1415_;
                            v_isShared_1428_ = v_isSharedCheck_1435_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1425_);
                            crate::leanh::lean_inc(v_key_1424_);
                            crate::leanh::lean_dec(v_v_1415_);
                            v___x_1427_ = crate::leanh::lean_box(0);
                            v_isShared_1428_ = v_isSharedCheck_1435_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1436_ = crate::leanh::lean_ctor_get(v_v_1415_, 0);
                        v_isSharedCheck_1446_ = (!crate::leanh::lean_is_exclusive(v_v_1415_)) as u8;
                        if v_isSharedCheck_1446_ == 0 {
                            v___x_1438_ = v_v_1415_;
                            v_isShared_1439_ = v_isSharedCheck_1446_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1436_);
                            crate::leanh::lean_dec(v_v_1415_);
                            v___x_1438_ = crate::leanh::lean_box(0);
                            v_isShared_1439_ = v_isSharedCheck_1446_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1447_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1447_, 0, v_x_1402_);
                        crate::leanh::lean_ctor_set(v___x_1447_, 1, v_x_1403_);
                        v___y_1419_ = v___x_1447_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1420_ = lean_array_fset(v_xs_x27_1417_, v_j_1409_, v___y_1419_);
                crate::leanh::lean_dec(v_j_1409_);
                if v_isShared_1414_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1413_, 0, v___x_1420_);
                    v___x_1422_ = v___x_1413_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
                    v___x_1422_ = v_reuseFailAlloc_1423_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1422_;
            }
            4 => {
                crate::leanh::lean_inc(v_key_1424_);
                crate::leanh::lean_inc_ref(v_x_1402_);
                v___x_1429_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                    v_x_1402_,
                    v_key_1424_,
                );
                if v___x_1429_ == 0 {
                    crate::leanh::lean_del_object(v___x_1427_);
                    v___x_1430_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1424_,
                        v_val_1425_,
                        v_x_1402_,
                        v_x_1403_,
                    );
                    v___x_1431_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1431_, 0, v___x_1430_);
                    v___y_1419_ = v___x_1431_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1425_);
                    crate::leanh::lean_dec(v_key_1424_);
                    if v_isShared_1428_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1427_, 1, v_x_1403_);
                        crate::leanh::lean_ctor_set(v___x_1427_, 0, v_x_1402_);
                        v___x_1433_ = v___x_1427_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1434_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_x_1402_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_x_1403_);
                        v___x_1433_ = v_reuseFailAlloc_1434_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1419_ = v___x_1433_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1440_ = lean_usize_shift_right(v_x_1400_, v___x_1405_);
                v___x_1441_ = lean_usize_add(v_x_1401_, v___x_1406_);
                v___x_1442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_node_1436_, v___x_1440_, v___x_1441_, v_x_1402_, v_x_1403_);
                if v_isShared_1439_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1438_, 0, v___x_1442_);
                    v___x_1444_ = v___x_1438_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
                    v___x_1444_ = v_reuseFailAlloc_1445_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1419_ = v___x_1444_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1454_ == 0 {
                    v___x_1456_ = v___x_1453_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_ks_1450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_vs_1451_);
                    v___x_1456_ = v_reuseFailAlloc_1470_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1457_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_1456_, v_x_1402_, v_x_1403_);
                v___x_1465_ = 7usize;
                v___x_1466_ = lean_usize_dec_le(v___x_1465_, v_x_1401_);
                if v___x_1466_ == 0 {
                    v___x_1467_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1457_);
                    v___x_1468_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1469_ = lean_nat_dec_lt(v___x_1467_, v___x_1468_);
                    crate::leanh::lean_dec(v___x_1467_);
                    v___y_1459_ = v___x_1469_;
                    state = 10;
                    continue;
                } else {
                    v___y_1459_ = v___x_1466_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1459_ == 0 {
                    v_ks_1460_ = crate::leanh::lean_ctor_get(v_newNode_1457_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1460_);
                    v_vs_1461_ = crate::leanh::lean_ctor_get(v_newNode_1457_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1461_);
                    crate::leanh::lean_dec_ref(v_newNode_1457_);
                    v___x_1462_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1463_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
                    v___x_1464_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_1401_, v_ks_1460_, v_vs_1461_, v___x_1462_, v___x_1463_);
                    crate::leanh::lean_dec_ref(v_vs_1461_);
                    crate::leanh::lean_dec_ref(v_ks_1460_);
                    return v___x_1464_;
                } else {
                    return v_newNode_1457_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(
    mut v_depth_1472_: usize,
    mut v_keys_1473_: *mut crate::leanh::LeanObject,
    mut v_vals_1474_: *mut crate::leanh::LeanObject,
    mut v_i_1475_: *mut crate::leanh::LeanObject,
    mut v_entries_1476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v_k_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u64 = 0;
    let mut v_h_1482_: usize = 0;
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: usize = 0;
    let mut v___x_1486_: usize = 0;
    let mut v___x_1487_: usize = 0;
    let mut v_h_1488_: usize = 0;
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1477_ = lean_array_get_size(v_keys_1473_);
                v___x_1478_ = lean_nat_dec_lt(v_i_1475_, v___x_1477_);
                if v___x_1478_ == 0 {
                    crate::leanh::lean_dec(v_i_1475_);
                    return v_entries_1476_;
                } else {
                    v_k_1479_ = lean_array_fget_borrowed(v_keys_1473_, v_i_1475_);
                    v_v_1480_ = lean_array_fget_borrowed(v_vals_1474_, v_i_1475_);
                    v___x_1481_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                            v_k_1479_,
                        );
                    v_h_1482_ = lean_uint64_to_usize(v___x_1481_);
                    v___x_1483_ = 5usize;
                    v___x_1484_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1485_ = 1usize;
                    v___x_1486_ = lean_usize_sub(v_depth_1472_, v___x_1485_);
                    v___x_1487_ = lean_usize_mul(v___x_1483_, v___x_1486_);
                    v_h_1488_ = lean_usize_shift_right(v_h_1482_, v___x_1487_);
                    v___x_1489_ = lean_nat_add(v_i_1475_, v___x_1484_);
                    crate::leanh::lean_dec(v_i_1475_);
                    crate::leanh::lean_inc(v_v_1480_);
                    crate::leanh::lean_inc(v_k_1479_);
                    v___x_1490_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_1476_, v_h_1488_, v_depth_1472_, v_k_1479_, v_v_1480_);
                    v_i_1475_ = v___x_1489_;
                    v_entries_1476_ = v___x_1490_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(
    mut v_depth_1492_: *mut crate::leanh::LeanObject,
    mut v_keys_1493_: *mut crate::leanh::LeanObject,
    mut v_vals_1494_: *mut crate::leanh::LeanObject,
    mut v_i_1495_: *mut crate::leanh::LeanObject,
    mut v_entries_1496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1497_: usize = 0;
    let mut v_res_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1497_ = crate::leanh::lean_unbox_usize(v_depth_1492_);
    crate::leanh::lean_dec(v_depth_1492_);
    v_res_1498_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_1497_, v_keys_1493_, v_vals_1494_, v_i_1495_, v_entries_1496_);
    crate::leanh::lean_dec_ref(v_vals_1494_);
    crate::leanh::lean_dec_ref(v_keys_1493_);
    return v_res_1498_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(
    mut v_x_1499_: *mut crate::leanh::LeanObject,
    mut v_x_1500_: *mut crate::leanh::LeanObject,
    mut v_x_1501_: *mut crate::leanh::LeanObject,
    mut v_x_1502_: *mut crate::leanh::LeanObject,
    mut v_x_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2046__boxed_1504_: usize = 0;
    let mut v_x_2047__boxed_1505_: usize = 0;
    let mut v_res_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2046__boxed_1504_ = crate::leanh::lean_unbox_usize(v_x_1500_);
    crate::leanh::lean_dec(v_x_1500_);
    v_x_2047__boxed_1505_ = crate::leanh::lean_unbox_usize(v_x_1501_);
    crate::leanh::lean_dec(v_x_1501_);
    v_res_1506_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_1499_, v_x_2046__boxed_1504_, v_x_2047__boxed_1505_, v_x_1502_, v_x_1503_);
    return v_res_1506_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(
    mut v_x_1507_: *mut crate::leanh::LeanObject,
    mut v_x_1508_: *mut crate::leanh::LeanObject,
    mut v_x_1509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1510_: u64 = 0;
    let mut v___x_1511_: usize = 0;
    let mut v___x_1512_: usize = 0;
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_1508_);
    v___x_1511_ = lean_uint64_to_usize(v___x_1510_);
    v___x_1512_ = 1usize;
    v___x_1513_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_1507_, v___x_1511_, v___x_1512_, v_x_1508_, v_x_1509_);
    return v___x_1513_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(
    mut v_a_1514_: *mut crate::leanh::LeanObject,
    mut v_b_1515_: *mut crate::leanh::LeanObject,
    mut v_x_1516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1522_: u8 = 0;
    let mut v___x_1523_: u8 = 0;
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1516_) == 0 {
                    crate::leanh::lean_dec(v_b_1515_);
                    crate::leanh::lean_dec_ref(v_a_1514_);
                    return v_x_1516_;
                } else {
                    v_key_1517_ = crate::leanh::lean_ctor_get(v_x_1516_, 0);
                    v_value_1518_ = crate::leanh::lean_ctor_get(v_x_1516_, 1);
                    v_tail_1519_ = crate::leanh::lean_ctor_get(v_x_1516_, 2);
                    v_isSharedCheck_1531_ = (!crate::leanh::lean_is_exclusive(v_x_1516_)) as u8;
                    if v_isSharedCheck_1531_ == 0 {
                        v___x_1521_ = v_x_1516_;
                        v_isShared_1522_ = v_isSharedCheck_1531_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1519_);
                        crate::leanh::lean_inc(v_value_1518_);
                        crate::leanh::lean_inc(v_key_1517_);
                        crate::leanh::lean_dec(v_x_1516_);
                        v___x_1521_ = crate::leanh::lean_box(0);
                        v_isShared_1522_ = v_isSharedCheck_1531_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1523_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_key_1517_,
                        v_a_1514_,
                    );
                if v___x_1523_ == 0 {
                    v___x_1524_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_1514_, v_b_1515_, v_tail_1519_);
                    if v_isShared_1522_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1521_, 2, v___x_1524_);
                        v___x_1526_ = v___x_1521_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1527_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_key_1517_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_value_1518_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 2, v___x_1524_);
                        v___x_1526_ = v_reuseFailAlloc_1527_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1518_);
                    crate::leanh::lean_dec(v_key_1517_);
                    if v_isShared_1522_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1521_, 1, v_b_1515_);
                        crate::leanh::lean_ctor_set(v___x_1521_, 0, v_a_1514_);
                        v___x_1529_ = v___x_1521_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1530_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1514_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_b_1515_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_tail_1519_);
                        v___x_1529_ = v_reuseFailAlloc_1530_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1526_;
            }
            3 => {
                return v___x_1529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(
    mut v_x_1532_: *mut crate::leanh::LeanObject,
    mut v_x_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1539_: u8 = 0;
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u64 = 0;
    let mut v___x_1542_: u64 = 0;
    let mut v___x_1543_: u64 = 0;
    let mut v_fold_1544_: u64 = 0;
    let mut v___x_1545_: u64 = 0;
    let mut v___x_1546_: u64 = 0;
    let mut v___x_1547_: u64 = 0;
    let mut v___x_1548_: usize = 0;
    let mut v___x_1549_: usize = 0;
    let mut v___x_1550_: usize = 0;
    let mut v___x_1551_: usize = 0;
    let mut v___x_1552_: usize = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1533_) == 0 {
                    return v_x_1532_;
                } else {
                    v_key_1534_ = crate::leanh::lean_ctor_get(v_x_1533_, 0);
                    v_value_1535_ = crate::leanh::lean_ctor_get(v_x_1533_, 1);
                    v_tail_1536_ = crate::leanh::lean_ctor_get(v_x_1533_, 2);
                    v_isSharedCheck_1559_ = (!crate::leanh::lean_is_exclusive(v_x_1533_)) as u8;
                    if v_isSharedCheck_1559_ == 0 {
                        v___x_1538_ = v_x_1533_;
                        v_isShared_1539_ = v_isSharedCheck_1559_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1536_);
                        crate::leanh::lean_inc(v_value_1535_);
                        crate::leanh::lean_inc(v_key_1534_);
                        crate::leanh::lean_dec(v_x_1533_);
                        v___x_1538_ = crate::leanh::lean_box(0);
                        v_isShared_1539_ = v_isSharedCheck_1559_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1540_ = lean_array_get_size(v_x_1532_);
                v___x_1541_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_1534_);
                v___x_1542_ = 32u64;
                v___x_1543_ = lean_uint64_shift_right(v___x_1541_, v___x_1542_);
                v_fold_1544_ = lean_uint64_xor(v___x_1541_, v___x_1543_);
                v___x_1545_ = 16u64;
                v___x_1546_ = lean_uint64_shift_right(v_fold_1544_, v___x_1545_);
                v___x_1547_ = lean_uint64_xor(v_fold_1544_, v___x_1546_);
                v___x_1548_ = lean_uint64_to_usize(v___x_1547_);
                v___x_1549_ = lean_usize_of_nat(v___x_1540_);
                v___x_1550_ = 1usize;
                v___x_1551_ = lean_usize_sub(v___x_1549_, v___x_1550_);
                v___x_1552_ = lean_usize_land(v___x_1548_, v___x_1551_);
                v___x_1553_ = lean_array_uget_borrowed(v_x_1532_, v___x_1552_);
                crate::leanh::lean_inc(v___x_1553_);
                if v_isShared_1539_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1538_, 2, v___x_1553_);
                    v___x_1555_ = v___x_1538_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_key_1534_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_value_1535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 2, v___x_1553_);
                    v___x_1555_ = v_reuseFailAlloc_1558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1556_ = lean_array_uset(v_x_1532_, v___x_1552_, v___x_1555_);
                v_x_1532_ = v___x_1556_;
                v_x_1533_ = v_tail_1536_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(
    mut v_i_1560_: *mut crate::leanh::LeanObject,
    mut v_source_1561_: *mut crate::leanh::LeanObject,
    mut v_target_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: u8 = 0;
    let mut v_es_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1563_ = lean_array_get_size(v_source_1561_);
                v___x_1564_ = lean_nat_dec_lt(v_i_1560_, v___x_1563_);
                if v___x_1564_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1561_);
                    crate::leanh::lean_dec(v_i_1560_);
                    return v_target_1562_;
                } else {
                    v_es_1565_ = lean_array_fget(v_source_1561_, v_i_1560_);
                    v___x_1566_ = crate::leanh::lean_box(0);
                    v_source_1567_ = lean_array_fset(v_source_1561_, v_i_1560_, v___x_1566_);
                    v_target_1568_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_1562_, v_es_1565_);
                    v___x_1569_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1570_ = lean_nat_add(v_i_1560_, v___x_1569_);
                    crate::leanh::lean_dec(v_i_1560_);
                    v_i_1560_ = v___x_1570_;
                    v_source_1561_ = v_source_1567_;
                    v_target_1562_ = v_target_1568_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(
    mut v_data_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ = lean_array_get_size(v_data_1572_);
    v___x_1574_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1575_ = lean_nat_mul(v___x_1573_, v___x_1574_);
    v___x_1576_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1577_ = crate::leanh::lean_box(0);
    v___x_1578_ = lean_mk_array(v_nbuckets_1575_, v___x_1577_);
    v___x_1579_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_1576_, v_data_1572_, v___x_1578_);
    return v___x_1579_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(
    mut v_a_1580_: *mut crate::leanh::LeanObject,
    mut v_x_1581_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1582_: u8 = 0;
    let mut v_key_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1581_) == 0 {
                    v___x_1582_ = 0;
                    return v___x_1582_;
                } else {
                    v_key_1583_ = crate::leanh::lean_ctor_get(v_x_1581_, 0);
                    v_tail_1584_ = crate::leanh::lean_ctor_get(v_x_1581_, 2);
                    v___x_1585_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_key_1583_,
                            v_a_1580_,
                        );
                    if v___x_1585_ == 0 {
                        v_x_1581_ = v_tail_1584_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1585_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(
    mut v_a_1587_: *mut crate::leanh::LeanObject,
    mut v_x_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1589_: u8 = 0;
    let mut v_r_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1589_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_1587_, v_x_1588_);
    crate::leanh::lean_dec(v_x_1588_);
    crate::leanh::lean_dec_ref(v_a_1587_);
    v_r_1590_ = crate::leanh::lean_box((v_res_1589_) as usize);
    return v_r_1590_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(
    mut v_m_1591_: *mut crate::leanh::LeanObject,
    mut v_a_1592_: *mut crate::leanh::LeanObject,
    mut v_b_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1598_: u8 = 0;
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: u64 = 0;
    let mut v___x_1601_: u64 = 0;
    let mut v___x_1602_: u64 = 0;
    let mut v_fold_1603_: u64 = 0;
    let mut v___x_1604_: u64 = 0;
    let mut v___x_1605_: u64 = 0;
    let mut v___x_1606_: u64 = 0;
    let mut v___x_1607_: usize = 0;
    let mut v___x_1608_: usize = 0;
    let mut v___x_1609_: usize = 0;
    let mut v___x_1610_: usize = 0;
    let mut v___x_1611_: usize = 0;
    let mut v_bkt_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: u8 = 0;
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v_val_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1594_ = crate::leanh::lean_ctor_get(v_m_1591_, 0);
                v_buckets_1595_ = crate::leanh::lean_ctor_get(v_m_1591_, 1);
                v_isSharedCheck_1638_ = (!crate::leanh::lean_is_exclusive(v_m_1591_)) as u8;
                if v_isSharedCheck_1638_ == 0 {
                    v___x_1597_ = v_m_1591_;
                    v_isShared_1598_ = v_isSharedCheck_1638_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1595_);
                    crate::leanh::lean_inc(v_size_1594_);
                    crate::leanh::lean_dec(v_m_1591_);
                    v___x_1597_ = crate::leanh::lean_box(0);
                    v_isShared_1598_ = v_isSharedCheck_1638_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1599_ = lean_array_get_size(v_buckets_1595_);
                v___x_1600_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_1592_);
                v___x_1601_ = 32u64;
                v___x_1602_ = lean_uint64_shift_right(v___x_1600_, v___x_1601_);
                v_fold_1603_ = lean_uint64_xor(v___x_1600_, v___x_1602_);
                v___x_1604_ = 16u64;
                v___x_1605_ = lean_uint64_shift_right(v_fold_1603_, v___x_1604_);
                v___x_1606_ = lean_uint64_xor(v_fold_1603_, v___x_1605_);
                v___x_1607_ = lean_uint64_to_usize(v___x_1606_);
                v___x_1608_ = lean_usize_of_nat(v___x_1599_);
                v___x_1609_ = 1usize;
                v___x_1610_ = lean_usize_sub(v___x_1608_, v___x_1609_);
                v___x_1611_ = lean_usize_land(v___x_1607_, v___x_1610_);
                v_bkt_1612_ = lean_array_uget_borrowed(v_buckets_1595_, v___x_1611_);
                v___x_1613_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_1592_, v_bkt_1612_);
                if v___x_1613_ == 0 {
                    v___x_1614_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1615_ = lean_nat_add(v_size_1594_, v___x_1614_);
                    crate::leanh::lean_dec(v_size_1594_);
                    crate::leanh::lean_inc(v_bkt_1612_);
                    v___x_1616_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1616_, 0, v_a_1592_);
                    crate::leanh::lean_ctor_set(v___x_1616_, 1, v_b_1593_);
                    crate::leanh::lean_ctor_set(v___x_1616_, 2, v_bkt_1612_);
                    v_buckets_x27_1617_ =
                        lean_array_uset(v_buckets_1595_, v___x_1611_, v___x_1616_);
                    v___x_1618_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1619_ = lean_nat_mul(v_size_x27_1615_, v___x_1618_);
                    v___x_1620_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1621_ = lean_nat_div(v___x_1619_, v___x_1620_);
                    crate::leanh::lean_dec(v___x_1619_);
                    v___x_1622_ = lean_array_get_size(v_buckets_x27_1617_);
                    v___x_1623_ = lean_nat_dec_le(v___x_1621_, v___x_1622_);
                    crate::leanh::lean_dec(v___x_1621_);
                    if v___x_1623_ == 0 {
                        v_val_1624_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_1617_);
                        if v_isShared_1598_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1597_, 1, v_val_1624_);
                            crate::leanh::lean_ctor_set(v___x_1597_, 0, v_size_x27_1615_);
                            v___x_1626_ = v___x_1597_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1627_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1627_,
                                0,
                                v_size_x27_1615_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_val_1624_);
                            v___x_1626_ = v_reuseFailAlloc_1627_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1598_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1597_, 1, v_buckets_x27_1617_);
                            crate::leanh::lean_ctor_set(v___x_1597_, 0, v_size_x27_1615_);
                            v___x_1629_ = v___x_1597_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1630_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1630_,
                                0,
                                v_size_x27_1615_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1630_,
                                1,
                                v_buckets_x27_1617_,
                            );
                            v___x_1629_ = v_reuseFailAlloc_1630_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1612_);
                    v___x_1631_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1632_ =
                        lean_array_uset(v_buckets_1595_, v___x_1611_, v___x_1631_);
                    v___x_1633_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_1592_, v_b_1593_, v_bkt_1612_);
                    v___x_1634_ = lean_array_uset(v_buckets_x27_1632_, v___x_1611_, v___x_1633_);
                    if v_isShared_1598_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1597_, 1, v___x_1634_);
                        v___x_1636_ = v___x_1597_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1637_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_size_1594_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 1, v___x_1634_);
                        v___x_1636_ = v_reuseFailAlloc_1637_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1626_;
            }
            3 => {
                return v___x_1629_;
            }
            4 => {
                return v___x_1636_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
    mut v_e_1639_: *mut crate::leanh::LeanObject,
    mut v_r_1640_: *mut crate::leanh::LeanObject,
    mut v_a_1641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1646_: u8 = 0;
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u64 = 0;
    let mut v___x_1649_: usize = 0;
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: u8 = 0;
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1642_ = crate::leanh::lean_ctor_get(v_a_1641_, 0);
                v_set_1643_ = crate::leanh::lean_ctor_get(v_a_1641_, 1);
                v_isSharedCheck_1665_ = (!crate::leanh::lean_is_exclusive(v_a_1641_)) as u8;
                if v_isSharedCheck_1665_ == 0 {
                    v___x_1645_ = v_a_1641_;
                    v_isShared_1646_ = v_isSharedCheck_1665_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_set_1643_);
                    crate::leanh::lean_inc(v_map_1642_);
                    crate::leanh::lean_dec(v_a_1641_);
                    v___x_1645_ = crate::leanh::lean_box(0);
                    v_isShared_1646_ = v_isSharedCheck_1665_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1647_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                v___x_1648_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                    v_r_1640_,
                );
                v___x_1649_ = lean_uint64_to_usize(v___x_1648_);
                crate::leanh::lean_inc_ref(v_r_1640_);
                crate::leanh::lean_inc_ref(v_set_1643_);
                v___x_1650_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1643_, v___x_1649_, v_r_1640_, v___x_1647_);
                v___x_1651_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v___x_1650_,
                        v___x_1647_,
                    );
                if v___x_1651_ == 0 {
                    crate::leanh::lean_dec_ref(v_r_1640_);
                    crate::leanh::lean_inc_ref(v___x_1650_);
                    v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_1642_, v_e_1639_, v___x_1650_);
                    if v_isShared_1646_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1645_, 0, v___x_1652_);
                        v___x_1654_ = v___x_1645_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1656_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1652_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_set_1643_);
                        v___x_1654_ = v_reuseFailAlloc_1656_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1650_);
                    crate::leanh::lean_inc_ref_n(v_r_1640_, 4);
                    v___x_1657_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_1642_, v_e_1639_, v_r_1640_);
                    v___x_1658_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_1657_, v_r_1640_, v_r_1640_);
                    v___x_1659_ = crate::leanh::lean_box(0);
                    v___x_1660_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1643_, v_r_1640_, v___x_1659_);
                    if v_isShared_1646_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1645_, 1, v___x_1660_);
                        crate::leanh::lean_ctor_set(v___x_1645_, 0, v___x_1658_);
                        v___x_1662_ = v___x_1645_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1664_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1658_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___x_1660_);
                        v___x_1662_ = v_reuseFailAlloc_1664_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1655_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1655_, 0, v___x_1650_);
                crate::leanh::lean_ctor_set(v___x_1655_, 1, v___x_1654_);
                return v___x_1655_;
            }
            3 => {
                v___x_1663_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1663_, 0, v_r_1640_);
                crate::leanh::lean_ctor_set(v___x_1663_, 1, v___x_1662_);
                return v___x_1663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(
    mut v_00_u03b2_1666_: *mut crate::leanh::LeanObject,
    mut v_x_1667_: *mut crate::leanh::LeanObject,
    mut v_x_1668_: usize,
    mut v_x_1669_: *mut crate::leanh::LeanObject,
    mut v_x_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_1667_, v_x_1668_, v_x_1669_, v_x_1670_);
    return v___x_1671_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(
    mut v_00_u03b2_1672_: *mut crate::leanh::LeanObject,
    mut v_x_1673_: *mut crate::leanh::LeanObject,
    mut v_x_1674_: *mut crate::leanh::LeanObject,
    mut v_x_1675_: *mut crate::leanh::LeanObject,
    mut v_x_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2466__boxed_1677_: usize = 0;
    let mut v_res_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2466__boxed_1677_ = crate::leanh::lean_unbox_usize(v_x_1674_);
    crate::leanh::lean_dec(v_x_1674_);
    v_res_1678_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_1672_, v_x_1673_, v_x_2466__boxed_1677_, v_x_1675_, v_x_1676_);
    crate::leanh::lean_dec_ref(v_x_1676_);
    return v_res_1678_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(
    mut v_00_u03b2_1679_: *mut crate::leanh::LeanObject,
    mut v_m_1680_: *mut crate::leanh::LeanObject,
    mut v_a_1681_: *mut crate::leanh::LeanObject,
    mut v_b_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_1680_, v_a_1681_, v_b_1682_);
    return v___x_1683_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(
    mut v_00_u03b2_1684_: *mut crate::leanh::LeanObject,
    mut v_x_1685_: *mut crate::leanh::LeanObject,
    mut v_x_1686_: *mut crate::leanh::LeanObject,
    mut v_x_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_1685_, v_x_1686_, v_x_1687_);
    return v___x_1688_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(
    mut v_00_u03b2_1689_: *mut crate::leanh::LeanObject,
    mut v_keys_1690_: *mut crate::leanh::LeanObject,
    mut v_vals_1691_: *mut crate::leanh::LeanObject,
    mut v_heq_1692_: *mut crate::leanh::LeanObject,
    mut v_i_1693_: *mut crate::leanh::LeanObject,
    mut v_k_1694_: *mut crate::leanh::LeanObject,
    mut v_k_u2080_1695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1696_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_1690_, v_i_1693_, v_k_1694_, v_k_u2080_1695_);
    return v___x_1696_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(
    mut v_00_u03b2_1697_: *mut crate::leanh::LeanObject,
    mut v_keys_1698_: *mut crate::leanh::LeanObject,
    mut v_vals_1699_: *mut crate::leanh::LeanObject,
    mut v_heq_1700_: *mut crate::leanh::LeanObject,
    mut v_i_1701_: *mut crate::leanh::LeanObject,
    mut v_k_1702_: *mut crate::leanh::LeanObject,
    mut v_k_u2080_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1704_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1697_, v_keys_1698_, v_vals_1699_, v_heq_1700_, v_i_1701_, v_k_1702_, v_k_u2080_1703_);
    crate::leanh::lean_dec_ref(v_k_u2080_1703_);
    crate::leanh::lean_dec_ref(v_vals_1699_);
    crate::leanh::lean_dec_ref(v_keys_1698_);
    return v_res_1704_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(
    mut v_00_u03b2_1705_: *mut crate::leanh::LeanObject,
    mut v_a_1706_: *mut crate::leanh::LeanObject,
    mut v_x_1707_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1708_: u8 = 0;
    v___x_1708_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_1706_, v_x_1707_);
    return v___x_1708_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(
    mut v_00_u03b2_1709_: *mut crate::leanh::LeanObject,
    mut v_a_1710_: *mut crate::leanh::LeanObject,
    mut v_x_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1712_: u8 = 0;
    let mut v_r_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_1709_, v_a_1710_, v_x_1711_);
    crate::leanh::lean_dec(v_x_1711_);
    crate::leanh::lean_dec_ref(v_a_1710_);
    v_r_1713_ = crate::leanh::lean_box((v_res_1712_) as usize);
    return v_r_1713_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(
    mut v_00_u03b2_1714_: *mut crate::leanh::LeanObject,
    mut v_data_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_1715_);
    return v___x_1716_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(
    mut v_00_u03b2_1717_: *mut crate::leanh::LeanObject,
    mut v_a_1718_: *mut crate::leanh::LeanObject,
    mut v_b_1719_: *mut crate::leanh::LeanObject,
    mut v_x_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_1718_, v_b_1719_, v_x_1720_);
    return v___x_1721_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(
    mut v_00_u03b2_1722_: *mut crate::leanh::LeanObject,
    mut v_x_1723_: *mut crate::leanh::LeanObject,
    mut v_x_1724_: usize,
    mut v_x_1725_: usize,
    mut v_x_1726_: *mut crate::leanh::LeanObject,
    mut v_x_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_1723_, v_x_1724_, v_x_1725_, v_x_1726_, v_x_1727_);
    return v___x_1728_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(
    mut v_00_u03b2_1729_: *mut crate::leanh::LeanObject,
    mut v_x_1730_: *mut crate::leanh::LeanObject,
    mut v_x_1731_: *mut crate::leanh::LeanObject,
    mut v_x_1732_: *mut crate::leanh::LeanObject,
    mut v_x_1733_: *mut crate::leanh::LeanObject,
    mut v_x_1734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2503__boxed_1735_: usize = 0;
    let mut v_x_2504__boxed_1736_: usize = 0;
    let mut v_res_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2503__boxed_1735_ = crate::leanh::lean_unbox_usize(v_x_1731_);
    crate::leanh::lean_dec(v_x_1731_);
    v_x_2504__boxed_1736_ = crate::leanh::lean_unbox_usize(v_x_1732_);
    crate::leanh::lean_dec(v_x_1732_);
    v_res_1737_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_1729_, v_x_1730_, v_x_2503__boxed_1735_, v_x_2504__boxed_1736_, v_x_1733_, v_x_1734_);
    return v_res_1737_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(
    mut v_00_u03b2_1738_: *mut crate::leanh::LeanObject,
    mut v_i_1739_: *mut crate::leanh::LeanObject,
    mut v_source_1740_: *mut crate::leanh::LeanObject,
    mut v_target_1741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_1739_, v_source_1740_, v_target_1741_);
    return v___x_1742_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(
    mut v_00_u03b2_1743_: *mut crate::leanh::LeanObject,
    mut v_n_1744_: *mut crate::leanh::LeanObject,
    mut v_k_1745_: *mut crate::leanh::LeanObject,
    mut v_v_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1747_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_1744_, v_k_1745_, v_v_1746_);
    return v___x_1747_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(
    mut v_00_u03b2_1748_: *mut crate::leanh::LeanObject,
    mut v_depth_1749_: usize,
    mut v_keys_1750_: *mut crate::leanh::LeanObject,
    mut v_vals_1751_: *mut crate::leanh::LeanObject,
    mut v_heq_1752_: *mut crate::leanh::LeanObject,
    mut v_i_1753_: *mut crate::leanh::LeanObject,
    mut v_entries_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_1749_, v_keys_1750_, v_vals_1751_, v_i_1753_, v_entries_1754_);
    return v___x_1755_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(
    mut v_00_u03b2_1756_: *mut crate::leanh::LeanObject,
    mut v_depth_1757_: *mut crate::leanh::LeanObject,
    mut v_keys_1758_: *mut crate::leanh::LeanObject,
    mut v_vals_1759_: *mut crate::leanh::LeanObject,
    mut v_heq_1760_: *mut crate::leanh::LeanObject,
    mut v_i_1761_: *mut crate::leanh::LeanObject,
    mut v_entries_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1763_: usize = 0;
    let mut v_res_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1763_ = crate::leanh::lean_unbox_usize(v_depth_1757_);
    crate::leanh::lean_dec(v_depth_1757_);
    v_res_1764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_1756_, v_depth_boxed_1763_, v_keys_1758_, v_vals_1759_, v_heq_1760_, v_i_1761_, v_entries_1762_);
    crate::leanh::lean_dec_ref(v_vals_1759_);
    crate::leanh::lean_dec_ref(v_keys_1758_);
    return v_res_1764_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(
    mut v_00_u03b2_1765_: *mut crate::leanh::LeanObject,
    mut v_x_1766_: *mut crate::leanh::LeanObject,
    mut v_x_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_1766_, v_x_1767_);
    return v___x_1768_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(
    mut v_00_u03b2_1769_: *mut crate::leanh::LeanObject,
    mut v_x_1770_: *mut crate::leanh::LeanObject,
    mut v_x_1771_: *mut crate::leanh::LeanObject,
    mut v_x_1772_: *mut crate::leanh::LeanObject,
    mut v_x_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_1770_, v_x_1771_, v_x_1772_, v_x_1773_);
    return v___x_1774_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(
    mut v_e_1777_: *mut crate::leanh::LeanObject,
    mut v_k_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1780_ = crate::leanh::lean_ctor_get(v_a_1779_, 0);
    v_set_1781_ = crate::leanh::lean_ctor_get(v_a_1779_, 1);
    v___f_1782_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0;
    v___f_1783_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1;
    crate::leanh::lean_inc_ref(v_e_1777_);
    v___x_1784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___f_1782_,
        v___f_1783_,
        v_map_1780_,
        v_e_1777_,
    );
    if crate::leanh::lean_obj_tag(v___x_1784_) == 1 {
        let mut v_val_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_1778_);
        crate::leanh::lean_dec_ref(v_e_1777_);
        v_val_1785_ = crate::leanh::lean_ctor_get(v___x_1784_, 0);
        crate::leanh::lean_inc(v_val_1785_);
        crate::leanh::lean_dec_ref_known(v___x_1784_, 1);
        v___x_1786_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1786_, 0, v_val_1785_);
        crate::leanh::lean_ctor_set(v___x_1786_, 1, v_a_1779_);
        return v___x_1786_;
    } else {
        let mut v___f_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1789_: u64 = 0;
        let mut v___x_1790_: usize = 0;
        let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1792_: u8 = 0;
        crate::leanh::lean_dec(v___x_1784_);
        v___f_1787_ = l_Lean_Meta_Sym_instBEqAlphaKey___closed__0;
        v___x_1788_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
        v___x_1789_ =
            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1777_);
        v___x_1790_ = lean_uint64_to_usize(v___x_1789_);
        crate::leanh::lean_inc_ref(v_e_1777_);
        crate::leanh::lean_inc_ref(v_set_1781_);
        v___x_1791_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(
            v___f_1787_,
            v_set_1781_,
            v___x_1790_,
            v_e_1777_,
            v___x_1788_,
        );
        v___x_1792_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v___x_1791_,
            v___x_1788_,
        );
        if v___x_1792_ == 0 {
            let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_k_1778_);
            crate::leanh::lean_dec_ref(v_e_1777_);
            v___x_1793_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1793_, 0, v___x_1791_);
            crate::leanh::lean_ctor_set(v___x_1793_, 1, v_a_1779_);
            return v___x_1793_;
        } else {
            let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1791_);
            v___x_1794_ = crate::leanh::lean_apply_1(v_k_1778_, v_a_1779_);
            v_fst_1795_ = crate::leanh::lean_ctor_get(v___x_1794_, 0);
            crate::leanh::lean_inc(v_fst_1795_);
            v_snd_1796_ = crate::leanh::lean_ctor_get(v___x_1794_, 1);
            crate::leanh::lean_inc(v_snd_1796_);
            crate::leanh::lean_dec_ref(v___x_1794_);
            v___x_1797_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                v_e_1777_,
                v_fst_1795_,
                v_snd_1796_,
            );
            return v___x_1797_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(
    mut v_keys_1798_: *mut crate::leanh::LeanObject,
    mut v_vals_1799_: *mut crate::leanh::LeanObject,
    mut v_i_1800_: *mut crate::leanh::LeanObject,
    mut v_k_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: u8 = 0;
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1802_ = lean_array_get_size(v_keys_1798_);
                v___x_1803_ = lean_nat_dec_lt(v_i_1800_, v___x_1802_);
                if v___x_1803_ == 0 {
                    crate::leanh::lean_dec_ref(v_k_1801_);
                    crate::leanh::lean_dec(v_i_1800_);
                    v___x_1804_ = crate::leanh::lean_box(0);
                    return v___x_1804_;
                } else {
                    v_k_x27_1805_ = lean_array_fget_borrowed(v_keys_1798_, v_i_1800_);
                    crate::leanh::lean_inc(v_k_x27_1805_);
                    crate::leanh::lean_inc_ref(v_k_1801_);
                    v___x_1806_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_k_1801_,
                            v_k_x27_1805_,
                        );
                    if v___x_1806_ == 0 {
                        v___x_1807_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1808_ = lean_nat_add(v_i_1800_, v___x_1807_);
                        crate::leanh::lean_dec(v_i_1800_);
                        v_i_1800_ = v___x_1808_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_1801_);
                        v___x_1810_ = lean_array_fget_borrowed(v_vals_1799_, v_i_1800_);
                        crate::leanh::lean_dec(v_i_1800_);
                        crate::leanh::lean_inc(v___x_1810_);
                        crate::leanh::lean_inc(v_k_x27_1805_);
                        v___x_1811_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1811_, 0, v_k_x27_1805_);
                        crate::leanh::lean_ctor_set(v___x_1811_, 1, v___x_1810_);
                        v___x_1812_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1812_, 0, v___x_1811_);
                        return v___x_1812_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_keys_1813_: *mut crate::leanh::LeanObject,
    mut v_vals_1814_: *mut crate::leanh::LeanObject,
    mut v_i_1815_: *mut crate::leanh::LeanObject,
    mut v_k_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1817_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_keys_1813_, v_vals_1814_, v_i_1815_, v_k_1816_);
    crate::leanh::lean_dec_ref(v_vals_1814_);
    crate::leanh::lean_dec_ref(v_keys_1813_);
    return v_res_1817_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(
    mut v_x_1818_: *mut crate::leanh::LeanObject,
    mut v_x_1819_: usize,
    mut v_x_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: usize = 0;
    let mut v___x_1824_: usize = 0;
    let mut v___x_1825_: usize = 0;
    let mut v_j_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: u8 = 0;
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: usize = 0;
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1818_) == 0 {
                    v_es_1821_ = crate::leanh::lean_ctor_get(v_x_1818_, 0);
                    crate::leanh::lean_inc_ref(v_es_1821_);
                    crate::leanh::lean_dec_ref_known(v_x_1818_, 1);
                    v___x_1822_ = crate::leanh::lean_box(2);
                    v___x_1823_ = 5usize;
                    v___x_1824_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1);
                    v___x_1825_ = lean_usize_land(v_x_1819_, v___x_1824_);
                    v_j_1826_ = lean_usize_to_nat(v___x_1825_);
                    v___x_1827_ = lean_array_get(v___x_1822_, v_es_1821_, v_j_1826_);
                    crate::leanh::lean_dec(v_j_1826_);
                    crate::leanh::lean_dec_ref(v_es_1821_);
                    match crate::leanh::lean_obj_tag(v___x_1827_) {
                        0 => {
                            v_key_1828_ = crate::leanh::lean_ctor_get(v___x_1827_, 0);
                            crate::leanh::lean_inc_n(v_key_1828_, 2);
                            v_val_1829_ = crate::leanh::lean_ctor_get(v___x_1827_, 1);
                            crate::leanh::lean_inc(v_val_1829_);
                            crate::leanh::lean_dec_ref_known(v___x_1827_, 2);
                            v___x_1830_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                                    v_x_1820_,
                                    v_key_1828_,
                                );
                            if v___x_1830_ == 0 {
                                crate::leanh::lean_dec(v_val_1829_);
                                crate::leanh::lean_dec(v_key_1828_);
                                v___x_1831_ = crate::leanh::lean_box(0);
                                return v___x_1831_;
                            } else {
                                v___x_1832_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1832_, 0, v_key_1828_);
                                crate::leanh::lean_ctor_set(v___x_1832_, 1, v_val_1829_);
                                v___x_1833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1833_, 0, v___x_1832_);
                                return v___x_1833_;
                            }
                        }
                        1 => {
                            v_node_1834_ = crate::leanh::lean_ctor_get(v___x_1827_, 0);
                            crate::leanh::lean_inc(v_node_1834_);
                            crate::leanh::lean_dec_ref_known(v___x_1827_, 1);
                            v___x_1835_ = lean_usize_shift_right(v_x_1819_, v___x_1823_);
                            v_x_1818_ = v_node_1834_;
                            v_x_1819_ = v___x_1835_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_x_1820_);
                            v___x_1837_ = crate::leanh::lean_box(0);
                            return v___x_1837_;
                        }
                    }
                } else {
                    v_ks_1838_ = crate::leanh::lean_ctor_get(v_x_1818_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1838_);
                    v_vs_1839_ = crate::leanh::lean_ctor_get(v_x_1818_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1839_);
                    crate::leanh::lean_dec_ref_known(v_x_1818_, 2);
                    v___x_1840_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1841_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_ks_1838_, v_vs_1839_, v___x_1840_, v_x_1820_);
                    crate::leanh::lean_dec_ref(v_vs_1839_);
                    crate::leanh::lean_dec_ref(v_ks_1838_);
                    return v___x_1841_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(
    mut v_x_1842_: *mut crate::leanh::LeanObject,
    mut v_x_1843_: *mut crate::leanh::LeanObject,
    mut v_x_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_8780__boxed_1845_: usize = 0;
    let mut v_res_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_8780__boxed_1845_ = crate::leanh::lean_unbox_usize(v_x_1843_);
    crate::leanh::lean_dec(v_x_1843_);
    v_res_1846_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_1842_, v_x_8780__boxed_1845_, v_x_1844_);
    return v_res_1846_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(
    mut v_x_1847_: *mut crate::leanh::LeanObject,
    mut v_x_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1849_: u64 = 0;
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_1848_);
    v___x_1850_ = lean_uint64_to_usize(v___x_1849_);
    crate::leanh::lean_inc_ref(v_x_1847_);
    v___x_1851_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_1847_, v___x_1850_, v_x_1848_);
    return v___x_1851_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(
    mut v_x_1852_: *mut crate::leanh::LeanObject,
    mut v_x_1853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1854_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_x_1852_, v_x_1853_);
    crate::leanh::lean_dec_ref(v_x_1852_);
    return v_res_1854_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(
    mut v_a_1855_: *mut crate::leanh::LeanObject,
    mut v_x_1856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: u8 = 0;
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1856_) == 0 {
                    v___x_1857_ = crate::leanh::lean_box(0);
                    return v___x_1857_;
                } else {
                    v_key_1858_ = crate::leanh::lean_ctor_get(v_x_1856_, 0);
                    v_value_1859_ = crate::leanh::lean_ctor_get(v_x_1856_, 1);
                    v_tail_1860_ = crate::leanh::lean_ctor_get(v_x_1856_, 2);
                    v___x_1861_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_key_1858_,
                            v_a_1855_,
                        );
                    if v___x_1861_ == 0 {
                        v_x_1856_ = v_tail_1860_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1859_);
                        v___x_1863_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1863_, 0, v_value_1859_);
                        return v___x_1863_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(
    mut v_a_1864_: *mut crate::leanh::LeanObject,
    mut v_x_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_1864_, v_x_1865_);
    crate::leanh::lean_dec(v_x_1865_);
    crate::leanh::lean_dec_ref(v_a_1864_);
    return v_res_1866_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(
    mut v_m_1867_: *mut crate::leanh::LeanObject,
    mut v_a_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u64 = 0;
    let mut v___x_1872_: u64 = 0;
    let mut v___x_1873_: u64 = 0;
    let mut v_fold_1874_: u64 = 0;
    let mut v___x_1875_: u64 = 0;
    let mut v___x_1876_: u64 = 0;
    let mut v___x_1877_: u64 = 0;
    let mut v___x_1878_: usize = 0;
    let mut v___x_1879_: usize = 0;
    let mut v___x_1880_: usize = 0;
    let mut v___x_1881_: usize = 0;
    let mut v___x_1882_: usize = 0;
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1869_ = crate::leanh::lean_ctor_get(v_m_1867_, 1);
    v___x_1870_ = lean_array_get_size(v_buckets_1869_);
    v___x_1871_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_1868_);
    v___x_1872_ = 32u64;
    v___x_1873_ = lean_uint64_shift_right(v___x_1871_, v___x_1872_);
    v_fold_1874_ = lean_uint64_xor(v___x_1871_, v___x_1873_);
    v___x_1875_ = 16u64;
    v___x_1876_ = lean_uint64_shift_right(v_fold_1874_, v___x_1875_);
    v___x_1877_ = lean_uint64_xor(v_fold_1874_, v___x_1876_);
    v___x_1878_ = lean_uint64_to_usize(v___x_1877_);
    v___x_1879_ = lean_usize_of_nat(v___x_1870_);
    v___x_1880_ = 1usize;
    v___x_1881_ = lean_usize_sub(v___x_1879_, v___x_1880_);
    v___x_1882_ = lean_usize_land(v___x_1878_, v___x_1881_);
    v___x_1883_ = lean_array_uget_borrowed(v_buckets_1869_, v___x_1882_);
    v___x_1884_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_1868_, v___x_1883_);
    return v___x_1884_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(
    mut v_m_1885_: *mut crate::leanh::LeanObject,
    mut v_a_1886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_m_1885_, v_a_1886_);
    crate::leanh::lean_dec_ref(v_a_1886_);
    crate::leanh::lean_dec_ref(v_m_1885_);
    return v_res_1887_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
    mut v_e_1888_: *mut crate::leanh::LeanObject,
    mut v_a_1889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: u64 = 0;
    let mut v___x_1899_: usize = 0;
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1910_: u8 = 0;
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: usize = 0;
    let mut v___x_1915_: usize = 0;
    let mut v___x_1916_: u8 = 0;
    let mut v___x_1917_: usize = 0;
    let mut v___x_1918_: usize = 0;
    let mut v___x_1919_: u8 = 0;
    let mut v_binderName_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1923_: u8 = 0;
    let mut v_map_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u64 = 0;
    let mut v___x_1931_: usize = 0;
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: u8 = 0;
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1942_: u8 = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: u8 = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: usize = 0;
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: usize = 0;
    let mut v___x_1953_: usize = 0;
    let mut v___x_1954_: u8 = 0;
    let mut v_binderName_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1958_: u8 = 0;
    let mut v_map_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u64 = 0;
    let mut v___x_1966_: usize = 0;
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1977_: u8 = 0;
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: usize = 0;
    let mut v___x_1985_: usize = 0;
    let mut v___x_1986_: u8 = 0;
    let mut v___x_1987_: usize = 0;
    let mut v___x_1988_: usize = 0;
    let mut v___x_1989_: u8 = 0;
    let mut v_declName_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1994_: u8 = 0;
    let mut v_map_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: u64 = 0;
    let mut v___x_2002_: usize = 0;
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2016_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: usize = 0;
    let mut v___x_2020_: usize = 0;
    let mut v___x_2021_: u8 = 0;
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: usize = 0;
    let mut v___x_2026_: usize = 0;
    let mut v___x_2027_: u8 = 0;
    let mut v___x_2028_: usize = 0;
    let mut v___x_2029_: usize = 0;
    let mut v___x_2030_: u8 = 0;
    let mut v_data_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u64 = 0;
    let mut v___x_2040_: usize = 0;
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: u8 = 0;
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: usize = 0;
    let mut v___x_2048_: usize = 0;
    let mut v___x_2049_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u64 = 0;
    let mut v___x_2063_: usize = 0;
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: usize = 0;
    let mut v___x_2071_: usize = 0;
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2081_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v_unused_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2095_: u8 = 0;
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2099_: u8 = 0;
    let mut v_unused_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_e_1888_) {
                    5 => {
                        v_fn_1890_ = crate::leanh::lean_ctor_get(v_e_1888_, 0);
                        v_arg_1891_ = crate::leanh::lean_ctor_get(v_e_1888_, 1);
                        v_map_1892_ = crate::leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_1893_ = crate::leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_1894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_1892_, v_e_1888_);
                        if crate::leanh::lean_obj_tag(v___x_1894_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_1888_, 2);
                            v_val_1895_ = crate::leanh::lean_ctor_get(v___x_1894_, 0);
                            crate::leanh::lean_inc(v_val_1895_);
                            crate::leanh::lean_dec_ref_known(v___x_1894_, 1);
                            v___x_1896_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1896_, 0, v_val_1895_);
                            crate::leanh::lean_ctor_set(v___x_1896_, 1, v_a_1889_);
                            return v___x_1896_;
                        } else {
                            crate::leanh::lean_dec(v___x_1894_);
                            v___x_1897_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_1898_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_1899_ = lean_uint64_to_usize(v___x_1898_);
                            crate::leanh::lean_inc_ref(v_e_1888_);
                            crate::leanh::lean_inc_ref(v_set_1893_);
                            v___x_1900_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1893_, v___x_1899_, v_e_1888_, v___x_1897_);
                            v___x_1901_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1900_, v___x_1897_);
                            if v___x_1901_ == 0 {
                                crate::leanh::lean_dec_ref_known(v_e_1888_, 2);
                                v___x_1902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1902_, 0, v___x_1900_);
                                crate::leanh::lean_ctor_set(v___x_1902_, 1, v_a_1889_);
                                return v___x_1902_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1900_);
                                crate::leanh::lean_inc_ref(v_fn_1890_);
                                v___x_1903_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_fn_1890_, v_a_1889_,
                                    );
                                v_fst_1904_ = crate::leanh::lean_ctor_get(v___x_1903_, 0);
                                crate::leanh::lean_inc(v_fst_1904_);
                                v_snd_1905_ = crate::leanh::lean_ctor_get(v___x_1903_, 1);
                                crate::leanh::lean_inc(v_snd_1905_);
                                crate::leanh::lean_dec_ref(v___x_1903_);
                                crate::leanh::lean_inc_ref(v_arg_1891_);
                                v___x_1906_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_arg_1891_,
                                        v_snd_1905_,
                                    );
                                v_fst_1907_ = crate::leanh::lean_ctor_get(v___x_1906_, 0);
                                crate::leanh::lean_inc(v_fst_1907_);
                                v_snd_1908_ = crate::leanh::lean_ctor_get(v___x_1906_, 1);
                                crate::leanh::lean_inc(v_snd_1908_);
                                crate::leanh::lean_dec_ref(v___x_1906_);
                                v___x_1914_ = lean_ptr_addr(v_fn_1890_);
                                v___x_1915_ = lean_ptr_addr(v_fst_1904_);
                                v___x_1916_ = lean_usize_dec_eq(v___x_1914_, v___x_1915_);
                                if v___x_1916_ == 0 {
                                    v___y_1910_ = v___x_1916_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1917_ = lean_ptr_addr(v_arg_1891_);
                                    v___x_1918_ = lean_ptr_addr(v_fst_1907_);
                                    v___x_1919_ = lean_usize_dec_eq(v___x_1917_, v___x_1918_);
                                    v___y_1910_ = v___x_1919_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                    6 => {
                        v_binderName_1920_ = crate::leanh::lean_ctor_get(v_e_1888_, 0);
                        v_binderType_1921_ = crate::leanh::lean_ctor_get(v_e_1888_, 1);
                        v_body_1922_ = crate::leanh::lean_ctor_get(v_e_1888_, 2);
                        v_binderInfo_1923_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_1888_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        v_map_1924_ = crate::leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_1925_ = crate::leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_1926_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_1924_, v_e_1888_);
                        if crate::leanh::lean_obj_tag(v___x_1926_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_1888_, 3);
                            v_val_1927_ = crate::leanh::lean_ctor_get(v___x_1926_, 0);
                            crate::leanh::lean_inc(v_val_1927_);
                            crate::leanh::lean_dec_ref_known(v___x_1926_, 1);
                            v___x_1928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1928_, 0, v_val_1927_);
                            crate::leanh::lean_ctor_set(v___x_1928_, 1, v_a_1889_);
                            return v___x_1928_;
                        } else {
                            crate::leanh::lean_dec(v___x_1926_);
                            v___x_1929_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_1930_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_1931_ = lean_uint64_to_usize(v___x_1930_);
                            crate::leanh::lean_inc_ref(v_e_1888_);
                            crate::leanh::lean_inc_ref(v_set_1925_);
                            v___x_1932_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1925_, v___x_1931_, v_e_1888_, v___x_1929_);
                            v___x_1933_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1932_, v___x_1929_);
                            if v___x_1933_ == 0 {
                                crate::leanh::lean_dec_ref_known(v_e_1888_, 3);
                                v___x_1934_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1934_, 0, v___x_1932_);
                                crate::leanh::lean_ctor_set(v___x_1934_, 1, v_a_1889_);
                                return v___x_1934_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1932_);
                                crate::leanh::lean_inc_ref(v_binderType_1921_);
                                v___x_1935_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_binderType_1921_,
                                        v_a_1889_,
                                    );
                                v_fst_1936_ = crate::leanh::lean_ctor_get(v___x_1935_, 0);
                                crate::leanh::lean_inc(v_fst_1936_);
                                v_snd_1937_ = crate::leanh::lean_ctor_get(v___x_1935_, 1);
                                crate::leanh::lean_inc(v_snd_1937_);
                                crate::leanh::lean_dec_ref(v___x_1935_);
                                crate::leanh::lean_inc_ref(v_body_1922_);
                                v___x_1938_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_body_1922_,
                                        v_snd_1937_,
                                    );
                                v_fst_1939_ = crate::leanh::lean_ctor_get(v___x_1938_, 0);
                                crate::leanh::lean_inc(v_fst_1939_);
                                v_snd_1940_ = crate::leanh::lean_ctor_get(v___x_1938_, 1);
                                crate::leanh::lean_inc(v_snd_1940_);
                                crate::leanh::lean_dec_ref(v___x_1938_);
                                v___x_1949_ = lean_ptr_addr(v_binderType_1921_);
                                v___x_1950_ = lean_ptr_addr(v_fst_1936_);
                                v___x_1951_ = lean_usize_dec_eq(v___x_1949_, v___x_1950_);
                                if v___x_1951_ == 0 {
                                    v___y_1942_ = v___x_1951_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_1952_ = lean_ptr_addr(v_body_1922_);
                                    v___x_1953_ = lean_ptr_addr(v_fst_1939_);
                                    v___x_1954_ = lean_usize_dec_eq(v___x_1952_, v___x_1953_);
                                    v___y_1942_ = v___x_1954_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                    7 => {
                        v_binderName_1955_ = crate::leanh::lean_ctor_get(v_e_1888_, 0);
                        v_binderType_1956_ = crate::leanh::lean_ctor_get(v_e_1888_, 1);
                        v_body_1957_ = crate::leanh::lean_ctor_get(v_e_1888_, 2);
                        v_binderInfo_1958_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_1888_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        v_map_1959_ = crate::leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_1960_ = crate::leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_1961_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_1959_, v_e_1888_);
                        if crate::leanh::lean_obj_tag(v___x_1961_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_1888_, 3);
                            v_val_1962_ = crate::leanh::lean_ctor_get(v___x_1961_, 0);
                            crate::leanh::lean_inc(v_val_1962_);
                            crate::leanh::lean_dec_ref_known(v___x_1961_, 1);
                            v___x_1963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1963_, 0, v_val_1962_);
                            crate::leanh::lean_ctor_set(v___x_1963_, 1, v_a_1889_);
                            return v___x_1963_;
                        } else {
                            crate::leanh::lean_dec(v___x_1961_);
                            v___x_1964_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_1965_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_1966_ = lean_uint64_to_usize(v___x_1965_);
                            crate::leanh::lean_inc_ref(v_e_1888_);
                            crate::leanh::lean_inc_ref(v_set_1960_);
                            v___x_1967_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1960_, v___x_1966_, v_e_1888_, v___x_1964_);
                            v___x_1968_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1967_, v___x_1964_);
                            if v___x_1968_ == 0 {
                                crate::leanh::lean_dec_ref_known(v_e_1888_, 3);
                                v___x_1969_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1969_, 0, v___x_1967_);
                                crate::leanh::lean_ctor_set(v___x_1969_, 1, v_a_1889_);
                                return v___x_1969_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1967_);
                                crate::leanh::lean_inc_ref(v_binderType_1956_);
                                v___x_1970_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_binderType_1956_,
                                        v_a_1889_,
                                    );
                                v_fst_1971_ = crate::leanh::lean_ctor_get(v___x_1970_, 0);
                                crate::leanh::lean_inc(v_fst_1971_);
                                v_snd_1972_ = crate::leanh::lean_ctor_get(v___x_1970_, 1);
                                crate::leanh::lean_inc(v_snd_1972_);
                                crate::leanh::lean_dec_ref(v___x_1970_);
                                crate::leanh::lean_inc_ref(v_body_1957_);
                                v___x_1973_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_body_1957_,
                                        v_snd_1972_,
                                    );
                                v_fst_1974_ = crate::leanh::lean_ctor_get(v___x_1973_, 0);
                                crate::leanh::lean_inc(v_fst_1974_);
                                v_snd_1975_ = crate::leanh::lean_ctor_get(v___x_1973_, 1);
                                crate::leanh::lean_inc(v_snd_1975_);
                                crate::leanh::lean_dec_ref(v___x_1973_);
                                v___x_1984_ = lean_ptr_addr(v_binderType_1956_);
                                v___x_1985_ = lean_ptr_addr(v_fst_1971_);
                                v___x_1986_ = lean_usize_dec_eq(v___x_1984_, v___x_1985_);
                                if v___x_1986_ == 0 {
                                    v___y_1977_ = v___x_1986_;
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_1987_ = lean_ptr_addr(v_body_1957_);
                                    v___x_1988_ = lean_ptr_addr(v_fst_1974_);
                                    v___x_1989_ = lean_usize_dec_eq(v___x_1987_, v___x_1988_);
                                    v___y_1977_ = v___x_1989_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    }
                    8 => {
                        v_declName_1990_ = crate::leanh::lean_ctor_get(v_e_1888_, 0);
                        v_type_1991_ = crate::leanh::lean_ctor_get(v_e_1888_, 1);
                        v_value_1992_ = crate::leanh::lean_ctor_get(v_e_1888_, 2);
                        v_body_1993_ = crate::leanh::lean_ctor_get(v_e_1888_, 3);
                        v_nondep_1994_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_1888_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                        );
                        v_map_1995_ = crate::leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_1996_ = crate::leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_1997_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_1995_, v_e_1888_);
                        if crate::leanh::lean_obj_tag(v___x_1997_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_1888_, 4);
                            v_val_1998_ = crate::leanh::lean_ctor_get(v___x_1997_, 0);
                            crate::leanh::lean_inc(v_val_1998_);
                            crate::leanh::lean_dec_ref_known(v___x_1997_, 1);
                            v___x_1999_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1999_, 0, v_val_1998_);
                            crate::leanh::lean_ctor_set(v___x_1999_, 1, v_a_1889_);
                            return v___x_1999_;
                        } else {
                            crate::leanh::lean_dec(v___x_1997_);
                            v___x_2000_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_2001_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_2002_ = lean_uint64_to_usize(v___x_2001_);
                            crate::leanh::lean_inc_ref(v_e_1888_);
                            crate::leanh::lean_inc_ref(v_set_1996_);
                            v___x_2003_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1996_, v___x_2002_, v_e_1888_, v___x_2000_);
                            v___x_2004_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2003_, v___x_2000_);
                            if v___x_2004_ == 0 {
                                crate::leanh::lean_dec_ref_known(v_e_1888_, 4);
                                v___x_2005_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2005_, 0, v___x_2003_);
                                crate::leanh::lean_ctor_set(v___x_2005_, 1, v_a_1889_);
                                return v___x_2005_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2003_);
                                crate::leanh::lean_inc_ref(v_type_1991_);
                                v___x_2006_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_type_1991_,
                                        v_a_1889_,
                                    );
                                v_fst_2007_ = crate::leanh::lean_ctor_get(v___x_2006_, 0);
                                crate::leanh::lean_inc(v_fst_2007_);
                                v_snd_2008_ = crate::leanh::lean_ctor_get(v___x_2006_, 1);
                                crate::leanh::lean_inc(v_snd_2008_);
                                crate::leanh::lean_dec_ref(v___x_2006_);
                                crate::leanh::lean_inc_ref(v_value_1992_);
                                v___x_2009_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_value_1992_,
                                        v_snd_2008_,
                                    );
                                v_fst_2010_ = crate::leanh::lean_ctor_get(v___x_2009_, 0);
                                crate::leanh::lean_inc(v_fst_2010_);
                                v_snd_2011_ = crate::leanh::lean_ctor_get(v___x_2009_, 1);
                                crate::leanh::lean_inc(v_snd_2011_);
                                crate::leanh::lean_dec_ref(v___x_2009_);
                                crate::leanh::lean_inc_ref(v_body_1993_);
                                v___x_2012_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_body_1993_,
                                        v_snd_2011_,
                                    );
                                v_fst_2013_ = crate::leanh::lean_ctor_get(v___x_2012_, 0);
                                crate::leanh::lean_inc(v_fst_2013_);
                                v_snd_2014_ = crate::leanh::lean_ctor_get(v___x_2012_, 1);
                                crate::leanh::lean_inc(v_snd_2014_);
                                crate::leanh::lean_dec_ref(v___x_2012_);
                                v___x_2025_ = lean_ptr_addr(v_type_1991_);
                                v___x_2026_ = lean_ptr_addr(v_fst_2007_);
                                v___x_2027_ = lean_usize_dec_eq(v___x_2025_, v___x_2026_);
                                if v___x_2027_ == 0 {
                                    v___y_2016_ = v___x_2027_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_2028_ = lean_ptr_addr(v_value_1992_);
                                    v___x_2029_ = lean_ptr_addr(v_fst_2010_);
                                    v___x_2030_ = lean_usize_dec_eq(v___x_2028_, v___x_2029_);
                                    v___y_2016_ = v___x_2030_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                    10 => {
                        v_data_2031_ = crate::leanh::lean_ctor_get(v_e_1888_, 0);
                        v_expr_2032_ = crate::leanh::lean_ctor_get(v_e_1888_, 1);
                        v_map_2033_ = crate::leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_2034_ = crate::leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_2035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_2033_, v_e_1888_);
                        if crate::leanh::lean_obj_tag(v___x_2035_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_1888_, 2);
                            v_val_2036_ = crate::leanh::lean_ctor_get(v___x_2035_, 0);
                            crate::leanh::lean_inc(v_val_2036_);
                            crate::leanh::lean_dec_ref_known(v___x_2035_, 1);
                            v___x_2037_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2037_, 0, v_val_2036_);
                            crate::leanh::lean_ctor_set(v___x_2037_, 1, v_a_1889_);
                            return v___x_2037_;
                        } else {
                            crate::leanh::lean_dec(v___x_2035_);
                            v___x_2038_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_2039_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_2040_ = lean_uint64_to_usize(v___x_2039_);
                            crate::leanh::lean_inc_ref(v_e_1888_);
                            crate::leanh::lean_inc_ref(v_set_2034_);
                            v___x_2041_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_2034_, v___x_2040_, v_e_1888_, v___x_2038_);
                            v___x_2042_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2041_, v___x_2038_);
                            if v___x_2042_ == 0 {
                                crate::leanh::lean_dec_ref_known(v_e_1888_, 2);
                                v___x_2043_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2043_, 0, v___x_2041_);
                                crate::leanh::lean_ctor_set(v___x_2043_, 1, v_a_1889_);
                                return v___x_2043_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2041_);
                                crate::leanh::lean_inc_ref(v_expr_2032_);
                                v___x_2044_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_expr_2032_,
                                        v_a_1889_,
                                    );
                                v_fst_2045_ = crate::leanh::lean_ctor_get(v___x_2044_, 0);
                                crate::leanh::lean_inc(v_fst_2045_);
                                v_snd_2046_ = crate::leanh::lean_ctor_get(v___x_2044_, 1);
                                crate::leanh::lean_inc(v_snd_2046_);
                                crate::leanh::lean_dec_ref(v___x_2044_);
                                v___x_2047_ = lean_ptr_addr(v_expr_2032_);
                                v___x_2048_ = lean_ptr_addr(v_fst_2045_);
                                v___x_2049_ = lean_usize_dec_eq(v___x_2047_, v___x_2048_);
                                if v___x_2049_ == 0 {
                                    crate::leanh::lean_inc(v_data_2031_);
                                    v___x_2050_ =
                                        l_Lean_Expr_mdata___override(v_data_2031_, v_fst_2045_);
                                    v___x_2051_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_1888_, v___x_2050_, v_snd_2046_);
                                    return v___x_2051_;
                                } else {
                                    crate::leanh::lean_dec(v_fst_2045_);
                                    crate::leanh::lean_inc_ref(v_e_1888_);
                                    v___x_2052_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_1888_, v_e_1888_, v_snd_2046_);
                                    return v___x_2052_;
                                }
                            }
                        }
                    }
                    11 => {
                        v_typeName_2053_ = crate::leanh::lean_ctor_get(v_e_1888_, 0);
                        v_idx_2054_ = crate::leanh::lean_ctor_get(v_e_1888_, 1);
                        v_struct_2055_ = crate::leanh::lean_ctor_get(v_e_1888_, 2);
                        v_map_2056_ = crate::leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_2057_ = crate::leanh::lean_ctor_get(v_a_1889_, 1);
                        v___x_2058_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_2056_, v_e_1888_);
                        if crate::leanh::lean_obj_tag(v___x_2058_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_1888_, 3);
                            v_val_2059_ = crate::leanh::lean_ctor_get(v___x_2058_, 0);
                            crate::leanh::lean_inc(v_val_2059_);
                            crate::leanh::lean_dec_ref_known(v___x_2058_, 1);
                            v___x_2060_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2060_, 0, v_val_2059_);
                            crate::leanh::lean_ctor_set(v___x_2060_, 1, v_a_1889_);
                            return v___x_2060_;
                        } else {
                            crate::leanh::lean_dec(v___x_2058_);
                            v___x_2061_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                            v___x_2062_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1888_);
                            v___x_2063_ = lean_uint64_to_usize(v___x_2062_);
                            crate::leanh::lean_inc_ref(v_e_1888_);
                            crate::leanh::lean_inc_ref(v_set_2057_);
                            v___x_2064_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_2057_, v___x_2063_, v_e_1888_, v___x_2061_);
                            v___x_2065_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2064_, v___x_2061_);
                            if v___x_2065_ == 0 {
                                crate::leanh::lean_dec_ref_known(v_e_1888_, 3);
                                v___x_2066_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2066_, 0, v___x_2064_);
                                crate::leanh::lean_ctor_set(v___x_2066_, 1, v_a_1889_);
                                return v___x_2066_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2064_);
                                crate::leanh::lean_inc_ref(v_struct_2055_);
                                v___x_2067_ =
                                    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                                        v_struct_2055_,
                                        v_a_1889_,
                                    );
                                v_fst_2068_ = crate::leanh::lean_ctor_get(v___x_2067_, 0);
                                crate::leanh::lean_inc(v_fst_2068_);
                                v_snd_2069_ = crate::leanh::lean_ctor_get(v___x_2067_, 1);
                                crate::leanh::lean_inc(v_snd_2069_);
                                crate::leanh::lean_dec_ref(v___x_2067_);
                                v___x_2070_ = lean_ptr_addr(v_struct_2055_);
                                v___x_2071_ = lean_ptr_addr(v_fst_2068_);
                                v___x_2072_ = lean_usize_dec_eq(v___x_2070_, v___x_2071_);
                                if v___x_2072_ == 0 {
                                    crate::leanh::lean_inc(v_idx_2054_);
                                    crate::leanh::lean_inc(v_typeName_2053_);
                                    v___x_2073_ = l_Lean_Expr_proj___override(
                                        v_typeName_2053_,
                                        v_idx_2054_,
                                        v_fst_2068_,
                                    );
                                    v___x_2074_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_1888_, v___x_2073_, v_snd_2069_);
                                    return v___x_2074_;
                                } else {
                                    crate::leanh::lean_dec(v_fst_2068_);
                                    crate::leanh::lean_inc_ref(v_e_1888_);
                                    v___x_2075_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_1888_, v_e_1888_, v_snd_2069_);
                                    return v___x_2075_;
                                }
                            }
                        }
                    }
                    _ => {
                        v_map_2076_ = crate::leanh::lean_ctor_get(v_a_1889_, 0);
                        v_set_2077_ = crate::leanh::lean_ctor_get(v_a_1889_, 1);
                        crate::leanh::lean_inc_ref(v_e_1888_);
                        v___x_2078_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_set_2077_, v_e_1888_);
                        if crate::leanh::lean_obj_tag(v___x_2078_) == 0 {
                            crate::leanh::lean_inc_ref(v_set_2077_);
                            crate::leanh::lean_inc_ref(v_map_2076_);
                            v_isSharedCheck_2088_ =
                                (!crate::leanh::lean_is_exclusive(v_a_1889_)) as u8;
                            if v_isSharedCheck_2088_ == 0 {
                                v_unused_2089_ = crate::leanh::lean_ctor_get(v_a_1889_, 1);
                                crate::leanh::lean_dec(v_unused_2089_);
                                v_unused_2090_ = crate::leanh::lean_ctor_get(v_a_1889_, 0);
                                crate::leanh::lean_dec(v_unused_2090_);
                                v___x_2080_ = v_a_1889_;
                                v_isShared_2081_ = v_isSharedCheck_2088_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1889_);
                                v___x_2080_ = crate::leanh::lean_box(0);
                                v_isShared_2081_ = v_isSharedCheck_2088_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_1888_);
                            v_val_2091_ = crate::leanh::lean_ctor_get(v___x_2078_, 0);
                            crate::leanh::lean_inc(v_val_2091_);
                            crate::leanh::lean_dec_ref_known(v___x_2078_, 1);
                            v_fst_2092_ = crate::leanh::lean_ctor_get(v_val_2091_, 0);
                            v_isSharedCheck_2099_ =
                                (!crate::leanh::lean_is_exclusive(v_val_2091_)) as u8;
                            if v_isSharedCheck_2099_ == 0 {
                                v_unused_2100_ = crate::leanh::lean_ctor_get(v_val_2091_, 1);
                                crate::leanh::lean_dec(v_unused_2100_);
                                v___x_2094_ = v_val_2091_;
                                v_isShared_2095_ = v_isSharedCheck_2099_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_fst_2092_);
                                crate::leanh::lean_dec(v_val_2091_);
                                v___x_2094_ = crate::leanh::lean_box(0);
                                v_isShared_2095_ = v_isSharedCheck_2099_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v___y_1910_ == 0 {
                    v___x_1911_ = l_Lean_Expr_app___override(v_fst_1904_, v_fst_1907_);
                    v___x_1912_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                        v_e_1888_,
                        v___x_1911_,
                        v_snd_1908_,
                    );
                    return v___x_1912_;
                } else {
                    crate::leanh::lean_dec(v_fst_1907_);
                    crate::leanh::lean_dec(v_fst_1904_);
                    crate::leanh::lean_inc_ref(v_e_1888_);
                    v___x_1913_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                        v_e_1888_,
                        v_e_1888_,
                        v_snd_1908_,
                    );
                    return v___x_1913_;
                }
            }
            2 => {
                if v___y_1942_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1920_);
                    v___x_1943_ = l_Lean_Expr_lam___override(
                        v_binderName_1920_,
                        v_fst_1936_,
                        v_fst_1939_,
                        v_binderInfo_1923_,
                    );
                    v___x_1944_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                        v_e_1888_,
                        v___x_1943_,
                        v_snd_1940_,
                    );
                    return v___x_1944_;
                } else {
                    v___x_1945_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1923_, v_binderInfo_1923_);
                    if v___x_1945_ == 0 {
                        crate::leanh::lean_inc(v_binderName_1920_);
                        v___x_1946_ = l_Lean_Expr_lam___override(
                            v_binderName_1920_,
                            v_fst_1936_,
                            v_fst_1939_,
                            v_binderInfo_1923_,
                        );
                        v___x_1947_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v___x_1946_,
                                v_snd_1940_,
                            );
                        return v___x_1947_;
                    } else {
                        crate::leanh::lean_dec(v_fst_1939_);
                        crate::leanh::lean_dec(v_fst_1936_);
                        crate::leanh::lean_inc_ref(v_e_1888_);
                        v___x_1948_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v_e_1888_,
                                v_snd_1940_,
                            );
                        return v___x_1948_;
                    }
                }
            }
            3 => {
                if v___y_1977_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1955_);
                    v___x_1978_ = l_Lean_Expr_forallE___override(
                        v_binderName_1955_,
                        v_fst_1971_,
                        v_fst_1974_,
                        v_binderInfo_1958_,
                    );
                    v___x_1979_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                        v_e_1888_,
                        v___x_1978_,
                        v_snd_1975_,
                    );
                    return v___x_1979_;
                } else {
                    v___x_1980_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1958_, v_binderInfo_1958_);
                    if v___x_1980_ == 0 {
                        crate::leanh::lean_inc(v_binderName_1955_);
                        v___x_1981_ = l_Lean_Expr_forallE___override(
                            v_binderName_1955_,
                            v_fst_1971_,
                            v_fst_1974_,
                            v_binderInfo_1958_,
                        );
                        v___x_1982_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v___x_1981_,
                                v_snd_1975_,
                            );
                        return v___x_1982_;
                    } else {
                        crate::leanh::lean_dec(v_fst_1974_);
                        crate::leanh::lean_dec(v_fst_1971_);
                        crate::leanh::lean_inc_ref(v_e_1888_);
                        v___x_1983_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v_e_1888_,
                                v_snd_1975_,
                            );
                        return v___x_1983_;
                    }
                }
            }
            4 => {
                if v___y_2016_ == 0 {
                    crate::leanh::lean_inc(v_declName_1990_);
                    v___x_2017_ = l_Lean_Expr_letE___override(
                        v_declName_1990_,
                        v_fst_2007_,
                        v_fst_2010_,
                        v_fst_2013_,
                        v_nondep_1994_,
                    );
                    v___x_2018_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                        v_e_1888_,
                        v___x_2017_,
                        v_snd_2014_,
                    );
                    return v___x_2018_;
                } else {
                    v___x_2019_ = lean_ptr_addr(v_body_1993_);
                    v___x_2020_ = lean_ptr_addr(v_fst_2013_);
                    v___x_2021_ = lean_usize_dec_eq(v___x_2019_, v___x_2020_);
                    if v___x_2021_ == 0 {
                        crate::leanh::lean_inc(v_declName_1990_);
                        v___x_2022_ = l_Lean_Expr_letE___override(
                            v_declName_1990_,
                            v_fst_2007_,
                            v_fst_2010_,
                            v_fst_2013_,
                            v_nondep_1994_,
                        );
                        v___x_2023_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v___x_2022_,
                                v_snd_2014_,
                            );
                        return v___x_2023_;
                    } else {
                        crate::leanh::lean_dec(v_fst_2013_);
                        crate::leanh::lean_dec(v_fst_2010_);
                        crate::leanh::lean_dec(v_fst_2007_);
                        crate::leanh::lean_inc_ref(v_e_1888_);
                        v___x_2024_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(
                                v_e_1888_,
                                v_e_1888_,
                                v_snd_2014_,
                            );
                        return v___x_2024_;
                    }
                }
            }
            5 => {
                v___x_2082_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_1888_);
                v___x_2083_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_2077_, v_e_1888_, v___x_2082_);
                if v_isShared_2081_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2080_, 1, v___x_2083_);
                    v___x_2085_ = v___x_2080_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_map_2076_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 1, v___x_2083_);
                    v___x_2085_ = v_reuseFailAlloc_2087_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2086_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2086_, 0, v_e_1888_);
                crate::leanh::lean_ctor_set(v___x_2086_, 1, v___x_2085_);
                return v___x_2086_;
            }
            7 => {
                if v_isShared_2095_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2094_, 1, v_a_1889_);
                    v___x_2097_ = v___x_2094_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2098_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_fst_2092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_a_1889_);
                    v___x_2097_ = v_reuseFailAlloc_2098_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(
    mut v_00_u03b2_2101_: *mut crate::leanh::LeanObject,
    mut v_m_2102_: *mut crate::leanh::LeanObject,
    mut v_a_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_m_2102_, v_a_2103_);
    return v___x_2104_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(
    mut v_00_u03b2_2105_: *mut crate::leanh::LeanObject,
    mut v_m_2106_: *mut crate::leanh::LeanObject,
    mut v_a_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_2105_, v_m_2106_, v_a_2107_);
    crate::leanh::lean_dec_ref(v_a_2107_);
    crate::leanh::lean_dec_ref(v_m_2106_);
    return v_res_2108_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(
    mut v_00_u03b2_2109_: *mut crate::leanh::LeanObject,
    mut v_x_2110_: *mut crate::leanh::LeanObject,
    mut v_x_2111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_x_2110_, v_x_2111_);
    return v___x_2112_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(
    mut v_00_u03b2_2113_: *mut crate::leanh::LeanObject,
    mut v_x_2114_: *mut crate::leanh::LeanObject,
    mut v_x_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2116_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_2113_, v_x_2114_, v_x_2115_);
    crate::leanh::lean_dec_ref(v_x_2114_);
    return v_res_2116_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(
    mut v_00_u03b2_2117_: *mut crate::leanh::LeanObject,
    mut v_a_2118_: *mut crate::leanh::LeanObject,
    mut v_x_2119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2120_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_2118_, v_x_2119_);
    return v___x_2120_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_2121_: *mut crate::leanh::LeanObject,
    mut v_a_2122_: *mut crate::leanh::LeanObject,
    mut v_x_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2124_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_2121_, v_a_2122_, v_x_2123_);
    crate::leanh::lean_dec(v_x_2123_);
    crate::leanh::lean_dec_ref(v_a_2122_);
    return v_res_2124_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(
    mut v_00_u03b2_2125_: *mut crate::leanh::LeanObject,
    mut v_x_2126_: *mut crate::leanh::LeanObject,
    mut v_x_2127_: usize,
    mut v_x_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_x_2126_);
    v___x_2129_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_2126_, v_x_2127_, v_x_2128_);
    return v___x_2129_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(
    mut v_00_u03b2_2130_: *mut crate::leanh::LeanObject,
    mut v_x_2131_: *mut crate::leanh::LeanObject,
    mut v_x_2132_: *mut crate::leanh::LeanObject,
    mut v_x_2133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_9303__boxed_2134_: usize = 0;
    let mut v_res_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_9303__boxed_2134_ = crate::leanh::lean_unbox_usize(v_x_2132_);
    crate::leanh::lean_dec(v_x_2132_);
    v_res_2135_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_2130_, v_x_2131_, v_x_9303__boxed_2134_, v_x_2133_);
    crate::leanh::lean_dec_ref(v_x_2131_);
    return v_res_2135_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2136_: *mut crate::leanh::LeanObject,
    mut v_keys_2137_: *mut crate::leanh::LeanObject,
    mut v_vals_2138_: *mut crate::leanh::LeanObject,
    mut v_heq_2139_: *mut crate::leanh::LeanObject,
    mut v_i_2140_: *mut crate::leanh::LeanObject,
    mut v_k_2141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2142_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_keys_2137_, v_vals_2138_, v_i_2140_, v_k_2141_);
    return v___x_2142_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_2143_: *mut crate::leanh::LeanObject,
    mut v_keys_2144_: *mut crate::leanh::LeanObject,
    mut v_vals_2145_: *mut crate::leanh::LeanObject,
    mut v_heq_2146_: *mut crate::leanh::LeanObject,
    mut v_i_2147_: *mut crate::leanh::LeanObject,
    mut v_k_2148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2149_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3(v_00_u03b2_2143_, v_keys_2144_, v_vals_2145_, v_heq_2146_, v_i_2147_, v_k_2148_);
    crate::leanh::lean_dec_ref(v_vals_2145_);
    crate::leanh::lean_dec_ref(v_keys_2144_);
    return v_res_2149_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2150_ = crate::leanh::lean_box(0);
    v___x_2151_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2152_ = lean_mk_array(v___x_2151_, v___x_2150_);
    return v___x_2152_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_shareCommonAlpha___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_shareCommonAlpha___closed__0_once),
        _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__0,
    );
    v___x_2154_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2155_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2155_, 0, v___x_2154_);
    crate::leanh::lean_ctor_set(v___x_2155_, 1, v___x_2153_);
    return v___x_2155_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonAlpha(
    mut v_e_2156_: *mut crate::leanh::LeanObject,
    mut v_s_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v_set_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_val_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2178_: u8 = 0;
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v_unused_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2158_ = l_Lean_Meta_Sym_instBEqAlphaKey___closed__0;
                v___f_2159_ = l_Lean_Meta_Sym_instHashableAlphaKey___closed__0;
                crate::leanh::lean_inc_ref(v_e_2156_);
                v___x_2160_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(
                    v___f_2158_,
                    v___f_2159_,
                    v_s_2157_,
                    v_e_2156_,
                );
                if crate::leanh::lean_obj_tag(v___x_2160_) == 0 {
                    v___x_2161_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_shareCommonAlpha___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_shareCommonAlpha___closed__1_once),
                        _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__1,
                    );
                    v___x_2162_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2162_, 0, v___x_2161_);
                    crate::leanh::lean_ctor_set(v___x_2162_, 1, v_s_2157_);
                    v___x_2163_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                        v_e_2156_,
                        v___x_2162_,
                    );
                    v_snd_2164_ = crate::leanh::lean_ctor_get(v___x_2163_, 1);
                    v_fst_2165_ = crate::leanh::lean_ctor_get(v___x_2163_, 0);
                    v_isSharedCheck_2173_ = (!crate::leanh::lean_is_exclusive(v___x_2163_)) as u8;
                    if v_isSharedCheck_2173_ == 0 {
                        v___x_2167_ = v___x_2163_;
                        v_isShared_2168_ = v_isSharedCheck_2173_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2164_);
                        crate::leanh::lean_inc(v_fst_2165_);
                        crate::leanh::lean_dec(v___x_2163_);
                        v___x_2167_ = crate::leanh::lean_box(0);
                        v_isShared_2168_ = v_isSharedCheck_2173_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2156_);
                    v_val_2174_ = crate::leanh::lean_ctor_get(v___x_2160_, 0);
                    crate::leanh::lean_inc(v_val_2174_);
                    crate::leanh::lean_dec_ref_known(v___x_2160_, 1);
                    v_fst_2175_ = crate::leanh::lean_ctor_get(v_val_2174_, 0);
                    v_isSharedCheck_2182_ = (!crate::leanh::lean_is_exclusive(v_val_2174_)) as u8;
                    if v_isSharedCheck_2182_ == 0 {
                        v_unused_2183_ = crate::leanh::lean_ctor_get(v_val_2174_, 1);
                        crate::leanh::lean_dec(v_unused_2183_);
                        v___x_2177_ = v_val_2174_;
                        v_isShared_2178_ = v_isSharedCheck_2182_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2175_);
                        crate::leanh::lean_dec(v_val_2174_);
                        v___x_2177_ = crate::leanh::lean_box(0);
                        v_isShared_2178_ = v_isSharedCheck_2182_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_set_2169_ = crate::leanh::lean_ctor_get(v_snd_2164_, 1);
                crate::leanh::lean_inc_ref(v_set_2169_);
                crate::leanh::lean_dec(v_snd_2164_);
                if v_isShared_2168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2167_, 1, v_set_2169_);
                    v___x_2171_ = v___x_2167_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_fst_2165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_set_2169_);
                    v___x_2171_ = v_reuseFailAlloc_2172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2171_;
            }
            3 => {
                if v_isShared_2178_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2177_, 1, v_s_2157_);
                    v___x_2180_ = v___x_2177_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_fst_2175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_s_2157_);
                    v___x_2180_ = v_reuseFailAlloc_2181_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
    mut v_e_2184_: *mut crate::leanh::LeanObject,
    mut v_a_2185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: u64 = 0;
    let mut v___x_2188_: usize = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    v___x_2186_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
    v___x_2187_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_2184_);
    v___x_2188_ = lean_uint64_to_usize(v___x_2187_);
    crate::leanh::lean_inc_ref(v_e_2184_);
    crate::leanh::lean_inc_ref(v_a_2185_);
    v___x_2189_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2185_, v___x_2188_, v_e_2184_, v___x_2186_);
    v___x_2190_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_2189_,
        v___x_2186_,
    );
    if v___x_2190_ == 0 {
        let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_2184_);
        v___x_2191_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2191_, 0, v___x_2189_);
        crate::leanh::lean_ctor_set(v___x_2191_, 1, v_a_2185_);
        return v___x_2191_;
    } else {
        let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_2189_);
        v___x_2192_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc_ref(v_e_2184_);
        v___x_2193_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_2185_, v_e_2184_, v___x_2192_);
        v___x_2194_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2194_, 0, v_e_2184_);
        crate::leanh::lean_ctor_set(v___x_2194_, 1, v___x_2193_);
        return v___x_2194_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(
    mut v_e_2195_: *mut crate::leanh::LeanObject,
    mut v_k_2196_: *mut crate::leanh::LeanObject,
    mut v_a_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u64 = 0;
    let mut v___x_2201_: usize = 0;
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: u8 = 0;
    v___f_2198_ = l_Lean_Meta_Sym_instBEqAlphaKey___closed__0;
    v___x_2199_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
    v___x_2200_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_2195_);
    v___x_2201_ = lean_uint64_to_usize(v___x_2200_);
    crate::leanh::lean_inc_ref(v_a_2197_);
    v___x_2202_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(
        v___f_2198_,
        v_a_2197_,
        v___x_2201_,
        v_e_2195_,
        v___x_2199_,
    );
    v___x_2203_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_2202_,
        v___x_2199_,
    );
    if v___x_2203_ == 0 {
        let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_2196_);
        v___x_2204_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2204_, 0, v___x_2202_);
        crate::leanh::lean_ctor_set(v___x_2204_, 1, v_a_2197_);
        return v___x_2204_;
    } else {
        let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_2202_);
        v___x_2205_ = crate::leanh::lean_apply_1(v_k_2196_, v_a_2197_);
        v_fst_2206_ = crate::leanh::lean_ctor_get(v___x_2205_, 0);
        crate::leanh::lean_inc(v_fst_2206_);
        v_snd_2207_ = crate::leanh::lean_ctor_get(v___x_2205_, 1);
        crate::leanh::lean_inc(v_snd_2207_);
        crate::leanh::lean_dec_ref(v___x_2205_);
        v___x_2208_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
            v_fst_2206_,
            v_snd_2207_,
        );
        return v___x_2208_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(
    mut v_e_2209_: *mut crate::leanh::LeanObject,
    mut v_a_2210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: u64 = 0;
    let mut v___x_2215_: usize = 0;
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: u8 = 0;
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: u8 = 0;
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: usize = 0;
    let mut v___x_2231_: usize = 0;
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: usize = 0;
    let mut v___x_2234_: usize = 0;
    let mut v___x_2235_: u8 = 0;
    let mut v_binderName_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2239_: u8 = 0;
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u64 = 0;
    let mut v___x_2242_: usize = 0;
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: u8 = 0;
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2253_: u8 = 0;
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: u8 = 0;
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: usize = 0;
    let mut v___x_2261_: usize = 0;
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2263_: usize = 0;
    let mut v___x_2264_: usize = 0;
    let mut v___x_2265_: u8 = 0;
    let mut v_binderName_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2269_: u8 = 0;
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u64 = 0;
    let mut v___x_2272_: usize = 0;
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: u8 = 0;
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: usize = 0;
    let mut v___x_2291_: usize = 0;
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: usize = 0;
    let mut v___x_2294_: usize = 0;
    let mut v___x_2295_: u8 = 0;
    let mut v_declName_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_2300_: u8 = 0;
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u64 = 0;
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u8 = 0;
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2317_: u8 = 0;
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: usize = 0;
    let mut v___x_2321_: usize = 0;
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: usize = 0;
    let mut v___x_2327_: usize = 0;
    let mut v___x_2328_: u8 = 0;
    let mut v___x_2329_: usize = 0;
    let mut v___x_2330_: usize = 0;
    let mut v___x_2331_: u8 = 0;
    let mut v_data_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u64 = 0;
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: u8 = 0;
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: usize = 0;
    let mut v___x_2344_: usize = 0;
    let mut v___x_2345_: u8 = 0;
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: u64 = 0;
    let mut v___x_2354_: usize = 0;
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: usize = 0;
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_e_2209_) {
                    5 => {
                        v_fn_2211_ = crate::leanh::lean_ctor_get(v_e_2209_, 0);
                        v_arg_2212_ = crate::leanh::lean_ctor_get(v_e_2209_, 1);
                        v___x_2213_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2214_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2215_ = lean_uint64_to_usize(v___x_2214_);
                        crate::leanh::lean_inc_ref(v_e_2209_);
                        crate::leanh::lean_inc_ref(v_a_2210_);
                        v___x_2216_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2215_, v_e_2209_, v___x_2213_);
                        v___x_2217_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2216_,
                                v___x_2213_,
                            );
                        if v___x_2217_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_e_2209_, 2);
                            v___x_2218_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2218_, 0, v___x_2216_);
                            crate::leanh::lean_ctor_set(v___x_2218_, 1, v_a_2210_);
                            return v___x_2218_;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2216_);
                            crate::leanh::lean_inc_ref(v_fn_2211_);
                            v___x_2219_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_2211_, v_a_2210_);
                            v_fst_2220_ = crate::leanh::lean_ctor_get(v___x_2219_, 0);
                            crate::leanh::lean_inc(v_fst_2220_);
                            v_snd_2221_ = crate::leanh::lean_ctor_get(v___x_2219_, 1);
                            crate::leanh::lean_inc(v_snd_2221_);
                            crate::leanh::lean_dec_ref(v___x_2219_);
                            crate::leanh::lean_inc_ref(v_arg_2212_);
                            v___x_2222_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_2212_, v_snd_2221_);
                            v_fst_2223_ = crate::leanh::lean_ctor_get(v___x_2222_, 0);
                            crate::leanh::lean_inc(v_fst_2223_);
                            v_snd_2224_ = crate::leanh::lean_ctor_get(v___x_2222_, 1);
                            crate::leanh::lean_inc(v_snd_2224_);
                            crate::leanh::lean_dec_ref(v___x_2222_);
                            v___x_2230_ = lean_ptr_addr(v_fn_2211_);
                            v___x_2231_ = lean_ptr_addr(v_fst_2220_);
                            v___x_2232_ = lean_usize_dec_eq(v___x_2230_, v___x_2231_);
                            if v___x_2232_ == 0 {
                                v___y_2226_ = v___x_2232_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2233_ = lean_ptr_addr(v_arg_2212_);
                                v___x_2234_ = lean_ptr_addr(v_fst_2223_);
                                v___x_2235_ = lean_usize_dec_eq(v___x_2233_, v___x_2234_);
                                v___y_2226_ = v___x_2235_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                    6 => {
                        v_binderName_2236_ = crate::leanh::lean_ctor_get(v_e_2209_, 0);
                        v_binderType_2237_ = crate::leanh::lean_ctor_get(v_e_2209_, 1);
                        v_body_2238_ = crate::leanh::lean_ctor_get(v_e_2209_, 2);
                        v_binderInfo_2239_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_2209_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        v___x_2240_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2241_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2242_ = lean_uint64_to_usize(v___x_2241_);
                        crate::leanh::lean_inc_ref(v_e_2209_);
                        crate::leanh::lean_inc_ref(v_a_2210_);
                        v___x_2243_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2242_, v_e_2209_, v___x_2240_);
                        v___x_2244_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2243_,
                                v___x_2240_,
                            );
                        if v___x_2244_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_e_2209_, 3);
                            v___x_2245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2243_);
                            crate::leanh::lean_ctor_set(v___x_2245_, 1, v_a_2210_);
                            return v___x_2245_;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2243_);
                            crate::leanh::lean_inc_ref(v_binderType_2237_);
                            v___x_2246_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_2237_, v_a_2210_);
                            v_fst_2247_ = crate::leanh::lean_ctor_get(v___x_2246_, 0);
                            crate::leanh::lean_inc(v_fst_2247_);
                            v_snd_2248_ = crate::leanh::lean_ctor_get(v___x_2246_, 1);
                            crate::leanh::lean_inc(v_snd_2248_);
                            crate::leanh::lean_dec_ref(v___x_2246_);
                            crate::leanh::lean_inc_ref(v_body_2238_);
                            v___x_2249_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_2238_, v_snd_2248_);
                            v_fst_2250_ = crate::leanh::lean_ctor_get(v___x_2249_, 0);
                            crate::leanh::lean_inc(v_fst_2250_);
                            v_snd_2251_ = crate::leanh::lean_ctor_get(v___x_2249_, 1);
                            crate::leanh::lean_inc(v_snd_2251_);
                            crate::leanh::lean_dec_ref(v___x_2249_);
                            v___x_2260_ = lean_ptr_addr(v_binderType_2237_);
                            v___x_2261_ = lean_ptr_addr(v_fst_2247_);
                            v___x_2262_ = lean_usize_dec_eq(v___x_2260_, v___x_2261_);
                            if v___x_2262_ == 0 {
                                v___y_2253_ = v___x_2262_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2263_ = lean_ptr_addr(v_body_2238_);
                                v___x_2264_ = lean_ptr_addr(v_fst_2250_);
                                v___x_2265_ = lean_usize_dec_eq(v___x_2263_, v___x_2264_);
                                v___y_2253_ = v___x_2265_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                    7 => {
                        v_binderName_2266_ = crate::leanh::lean_ctor_get(v_e_2209_, 0);
                        v_binderType_2267_ = crate::leanh::lean_ctor_get(v_e_2209_, 1);
                        v_body_2268_ = crate::leanh::lean_ctor_get(v_e_2209_, 2);
                        v_binderInfo_2269_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_2209_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        v___x_2270_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2271_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2272_ = lean_uint64_to_usize(v___x_2271_);
                        crate::leanh::lean_inc_ref(v_e_2209_);
                        crate::leanh::lean_inc_ref(v_a_2210_);
                        v___x_2273_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2272_, v_e_2209_, v___x_2270_);
                        v___x_2274_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2273_,
                                v___x_2270_,
                            );
                        if v___x_2274_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_e_2209_, 3);
                            v___x_2275_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2275_, 0, v___x_2273_);
                            crate::leanh::lean_ctor_set(v___x_2275_, 1, v_a_2210_);
                            return v___x_2275_;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2273_);
                            crate::leanh::lean_inc_ref(v_binderType_2267_);
                            v___x_2276_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_2267_, v_a_2210_);
                            v_fst_2277_ = crate::leanh::lean_ctor_get(v___x_2276_, 0);
                            crate::leanh::lean_inc(v_fst_2277_);
                            v_snd_2278_ = crate::leanh::lean_ctor_get(v___x_2276_, 1);
                            crate::leanh::lean_inc(v_snd_2278_);
                            crate::leanh::lean_dec_ref(v___x_2276_);
                            crate::leanh::lean_inc_ref(v_body_2268_);
                            v___x_2279_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_2268_, v_snd_2278_);
                            v_fst_2280_ = crate::leanh::lean_ctor_get(v___x_2279_, 0);
                            crate::leanh::lean_inc(v_fst_2280_);
                            v_snd_2281_ = crate::leanh::lean_ctor_get(v___x_2279_, 1);
                            crate::leanh::lean_inc(v_snd_2281_);
                            crate::leanh::lean_dec_ref(v___x_2279_);
                            v___x_2290_ = lean_ptr_addr(v_binderType_2267_);
                            v___x_2291_ = lean_ptr_addr(v_fst_2277_);
                            v___x_2292_ = lean_usize_dec_eq(v___x_2290_, v___x_2291_);
                            if v___x_2292_ == 0 {
                                v___y_2283_ = v___x_2292_;
                                state = 3;
                                continue;
                            } else {
                                v___x_2293_ = lean_ptr_addr(v_body_2268_);
                                v___x_2294_ = lean_ptr_addr(v_fst_2280_);
                                v___x_2295_ = lean_usize_dec_eq(v___x_2293_, v___x_2294_);
                                v___y_2283_ = v___x_2295_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    8 => {
                        v_declName_2296_ = crate::leanh::lean_ctor_get(v_e_2209_, 0);
                        v_type_2297_ = crate::leanh::lean_ctor_get(v_e_2209_, 1);
                        v_value_2298_ = crate::leanh::lean_ctor_get(v_e_2209_, 2);
                        v_body_2299_ = crate::leanh::lean_ctor_get(v_e_2209_, 3);
                        v_nondep_2300_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_2209_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                        );
                        v___x_2301_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2302_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2303_ = lean_uint64_to_usize(v___x_2302_);
                        crate::leanh::lean_inc_ref(v_e_2209_);
                        crate::leanh::lean_inc_ref(v_a_2210_);
                        v___x_2304_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2303_, v_e_2209_, v___x_2301_);
                        v___x_2305_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2304_,
                                v___x_2301_,
                            );
                        if v___x_2305_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_e_2209_, 4);
                            v___x_2306_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2306_, 0, v___x_2304_);
                            crate::leanh::lean_ctor_set(v___x_2306_, 1, v_a_2210_);
                            return v___x_2306_;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2304_);
                            crate::leanh::lean_inc_ref(v_type_2297_);
                            v___x_2307_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_2297_, v_a_2210_);
                            v_fst_2308_ = crate::leanh::lean_ctor_get(v___x_2307_, 0);
                            crate::leanh::lean_inc(v_fst_2308_);
                            v_snd_2309_ = crate::leanh::lean_ctor_get(v___x_2307_, 1);
                            crate::leanh::lean_inc(v_snd_2309_);
                            crate::leanh::lean_dec_ref(v___x_2307_);
                            crate::leanh::lean_inc_ref(v_value_2298_);
                            v___x_2310_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_2298_, v_snd_2309_);
                            v_fst_2311_ = crate::leanh::lean_ctor_get(v___x_2310_, 0);
                            crate::leanh::lean_inc(v_fst_2311_);
                            v_snd_2312_ = crate::leanh::lean_ctor_get(v___x_2310_, 1);
                            crate::leanh::lean_inc(v_snd_2312_);
                            crate::leanh::lean_dec_ref(v___x_2310_);
                            crate::leanh::lean_inc_ref(v_body_2299_);
                            v___x_2313_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_2299_, v_snd_2312_);
                            v_fst_2314_ = crate::leanh::lean_ctor_get(v___x_2313_, 0);
                            crate::leanh::lean_inc(v_fst_2314_);
                            v_snd_2315_ = crate::leanh::lean_ctor_get(v___x_2313_, 1);
                            crate::leanh::lean_inc(v_snd_2315_);
                            crate::leanh::lean_dec_ref(v___x_2313_);
                            v___x_2326_ = lean_ptr_addr(v_type_2297_);
                            v___x_2327_ = lean_ptr_addr(v_fst_2308_);
                            v___x_2328_ = lean_usize_dec_eq(v___x_2326_, v___x_2327_);
                            if v___x_2328_ == 0 {
                                v___y_2317_ = v___x_2328_;
                                state = 4;
                                continue;
                            } else {
                                v___x_2329_ = lean_ptr_addr(v_value_2298_);
                                v___x_2330_ = lean_ptr_addr(v_fst_2311_);
                                v___x_2331_ = lean_usize_dec_eq(v___x_2329_, v___x_2330_);
                                v___y_2317_ = v___x_2331_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                    10 => {
                        v_data_2332_ = crate::leanh::lean_ctor_get(v_e_2209_, 0);
                        v_expr_2333_ = crate::leanh::lean_ctor_get(v_e_2209_, 1);
                        v___x_2334_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2335_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2336_ = lean_uint64_to_usize(v___x_2335_);
                        crate::leanh::lean_inc_ref(v_e_2209_);
                        crate::leanh::lean_inc_ref(v_a_2210_);
                        v___x_2337_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2336_, v_e_2209_, v___x_2334_);
                        v___x_2338_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2337_,
                                v___x_2334_,
                            );
                        if v___x_2338_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_e_2209_, 2);
                            v___x_2339_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2339_, 0, v___x_2337_);
                            crate::leanh::lean_ctor_set(v___x_2339_, 1, v_a_2210_);
                            return v___x_2339_;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2337_);
                            crate::leanh::lean_inc_ref(v_expr_2333_);
                            v___x_2340_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_2333_, v_a_2210_);
                            v_fst_2341_ = crate::leanh::lean_ctor_get(v___x_2340_, 0);
                            crate::leanh::lean_inc(v_fst_2341_);
                            v_snd_2342_ = crate::leanh::lean_ctor_get(v___x_2340_, 1);
                            crate::leanh::lean_inc(v_snd_2342_);
                            crate::leanh::lean_dec_ref(v___x_2340_);
                            v___x_2343_ = lean_ptr_addr(v_expr_2333_);
                            v___x_2344_ = lean_ptr_addr(v_fst_2341_);
                            v___x_2345_ = lean_usize_dec_eq(v___x_2343_, v___x_2344_);
                            if v___x_2345_ == 0 {
                                crate::leanh::lean_inc(v_data_2332_);
                                crate::leanh::lean_dec_ref_known(v_e_2209_, 2);
                                v___x_2346_ =
                                    l_Lean_Expr_mdata___override(v_data_2332_, v_fst_2341_);
                                v___x_2347_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_2346_, v_snd_2342_);
                                return v___x_2347_;
                            } else {
                                crate::leanh::lean_dec(v_fst_2341_);
                                v___x_2348_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_2209_, v_snd_2342_);
                                return v___x_2348_;
                            }
                        }
                    }
                    11 => {
                        v_typeName_2349_ = crate::leanh::lean_ctor_get(v_e_2209_, 0);
                        v_idx_2350_ = crate::leanh::lean_ctor_get(v_e_2209_, 1);
                        v_struct_2351_ = crate::leanh::lean_ctor_get(v_e_2209_, 2);
                        v___x_2352_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
                        v___x_2353_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                                v_e_2209_,
                            );
                        v___x_2354_ = lean_uint64_to_usize(v___x_2353_);
                        crate::leanh::lean_inc_ref(v_e_2209_);
                        crate::leanh::lean_inc_ref(v_a_2210_);
                        v___x_2355_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_2210_, v___x_2354_, v_e_2209_, v___x_2352_);
                        v___x_2356_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_2355_,
                                v___x_2352_,
                            );
                        if v___x_2356_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_e_2209_, 3);
                            v___x_2357_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2357_, 0, v___x_2355_);
                            crate::leanh::lean_ctor_set(v___x_2357_, 1, v_a_2210_);
                            return v___x_2357_;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2355_);
                            crate::leanh::lean_inc_ref(v_struct_2351_);
                            v___x_2358_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_2351_, v_a_2210_);
                            v_fst_2359_ = crate::leanh::lean_ctor_get(v___x_2358_, 0);
                            crate::leanh::lean_inc(v_fst_2359_);
                            v_snd_2360_ = crate::leanh::lean_ctor_get(v___x_2358_, 1);
                            crate::leanh::lean_inc(v_snd_2360_);
                            crate::leanh::lean_dec_ref(v___x_2358_);
                            v___x_2361_ = lean_ptr_addr(v_struct_2351_);
                            v___x_2362_ = lean_ptr_addr(v_fst_2359_);
                            v___x_2363_ = lean_usize_dec_eq(v___x_2361_, v___x_2362_);
                            if v___x_2363_ == 0 {
                                crate::leanh::lean_inc(v_idx_2350_);
                                crate::leanh::lean_inc(v_typeName_2349_);
                                crate::leanh::lean_dec_ref_known(v_e_2209_, 3);
                                v___x_2364_ = l_Lean_Expr_proj___override(
                                    v_typeName_2349_,
                                    v_idx_2350_,
                                    v_fst_2359_,
                                );
                                v___x_2365_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_2364_, v_snd_2360_);
                                return v___x_2365_;
                            } else {
                                crate::leanh::lean_dec(v_fst_2359_);
                                v___x_2366_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_2209_, v_snd_2360_);
                                return v___x_2366_;
                            }
                        }
                    }
                    _ => {
                        v___x_2367_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v_e_2209_, v_a_2210_,
                            );
                        return v___x_2367_;
                    }
                }
            }
            1 => {
                if v___y_2226_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_2209_, 2);
                    v___x_2227_ = l_Lean_Expr_app___override(v_fst_2220_, v_fst_2223_);
                    v___x_2228_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                            v___x_2227_,
                            v_snd_2224_,
                        );
                    return v___x_2228_;
                } else {
                    crate::leanh::lean_dec(v_fst_2223_);
                    crate::leanh::lean_dec(v_fst_2220_);
                    v___x_2229_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                            v_e_2209_,
                            v_snd_2224_,
                        );
                    return v___x_2229_;
                }
            }
            2 => {
                if v___y_2253_ == 0 {
                    crate::leanh::lean_inc(v_binderName_2236_);
                    crate::leanh::lean_dec_ref_known(v_e_2209_, 3);
                    v___x_2254_ = l_Lean_Expr_lam___override(
                        v_binderName_2236_,
                        v_fst_2247_,
                        v_fst_2250_,
                        v_binderInfo_2239_,
                    );
                    v___x_2255_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                            v___x_2254_,
                            v_snd_2251_,
                        );
                    return v___x_2255_;
                } else {
                    v___x_2256_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_2239_, v_binderInfo_2239_);
                    if v___x_2256_ == 0 {
                        crate::leanh::lean_inc(v_binderName_2236_);
                        crate::leanh::lean_dec_ref_known(v_e_2209_, 3);
                        v___x_2257_ = l_Lean_Expr_lam___override(
                            v_binderName_2236_,
                            v_fst_2247_,
                            v_fst_2250_,
                            v_binderInfo_2239_,
                        );
                        v___x_2258_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v___x_2257_,
                                v_snd_2251_,
                            );
                        return v___x_2258_;
                    } else {
                        crate::leanh::lean_dec(v_fst_2250_);
                        crate::leanh::lean_dec(v_fst_2247_);
                        v___x_2259_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v_e_2209_,
                                v_snd_2251_,
                            );
                        return v___x_2259_;
                    }
                }
            }
            3 => {
                if v___y_2283_ == 0 {
                    crate::leanh::lean_inc(v_binderName_2266_);
                    crate::leanh::lean_dec_ref_known(v_e_2209_, 3);
                    v___x_2284_ = l_Lean_Expr_forallE___override(
                        v_binderName_2266_,
                        v_fst_2277_,
                        v_fst_2280_,
                        v_binderInfo_2269_,
                    );
                    v___x_2285_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                            v___x_2284_,
                            v_snd_2281_,
                        );
                    return v___x_2285_;
                } else {
                    v___x_2286_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_2269_, v_binderInfo_2269_);
                    if v___x_2286_ == 0 {
                        crate::leanh::lean_inc(v_binderName_2266_);
                        crate::leanh::lean_dec_ref_known(v_e_2209_, 3);
                        v___x_2287_ = l_Lean_Expr_forallE___override(
                            v_binderName_2266_,
                            v_fst_2277_,
                            v_fst_2280_,
                            v_binderInfo_2269_,
                        );
                        v___x_2288_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v___x_2287_,
                                v_snd_2281_,
                            );
                        return v___x_2288_;
                    } else {
                        crate::leanh::lean_dec(v_fst_2280_);
                        crate::leanh::lean_dec(v_fst_2277_);
                        v___x_2289_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v_e_2209_,
                                v_snd_2281_,
                            );
                        return v___x_2289_;
                    }
                }
            }
            4 => {
                if v___y_2317_ == 0 {
                    crate::leanh::lean_inc(v_declName_2296_);
                    crate::leanh::lean_dec_ref_known(v_e_2209_, 4);
                    v___x_2318_ = l_Lean_Expr_letE___override(
                        v_declName_2296_,
                        v_fst_2308_,
                        v_fst_2311_,
                        v_fst_2314_,
                        v_nondep_2300_,
                    );
                    v___x_2319_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                            v___x_2318_,
                            v_snd_2315_,
                        );
                    return v___x_2319_;
                } else {
                    v___x_2320_ = lean_ptr_addr(v_body_2299_);
                    v___x_2321_ = lean_ptr_addr(v_fst_2314_);
                    v___x_2322_ = lean_usize_dec_eq(v___x_2320_, v___x_2321_);
                    if v___x_2322_ == 0 {
                        crate::leanh::lean_inc(v_declName_2296_);
                        crate::leanh::lean_dec_ref_known(v_e_2209_, 4);
                        v___x_2323_ = l_Lean_Expr_letE___override(
                            v_declName_2296_,
                            v_fst_2308_,
                            v_fst_2311_,
                            v_fst_2314_,
                            v_nondep_2300_,
                        );
                        v___x_2324_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v___x_2323_,
                                v_snd_2315_,
                            );
                        return v___x_2324_;
                    } else {
                        crate::leanh::lean_dec(v_fst_2314_);
                        crate::leanh::lean_dec(v_fst_2311_);
                        crate::leanh::lean_dec(v_fst_2308_);
                        v___x_2325_ =
                            l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(
                                v_e_2209_,
                                v_snd_2315_,
                            );
                        return v___x_2325_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonAlphaInc(
    mut v_e_2368_: *mut crate::leanh::LeanObject,
    mut v_a_2369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2370_ =
        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(
            v_e_2368_, v_a_2369_,
        );
    return v___x_2370_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy =
        _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_AlphaShareCommon(
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
pub unsafe fn initialize_Lean_Meta_Sym_AlphaShareCommon(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
}
