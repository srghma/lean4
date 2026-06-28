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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_7, lean_box, lean_box_uint64,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_uint64, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value
        ) as *mut LeanObject,
        17542774118954891045 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1_value
)
    as *mut LeanObject;
static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Canonicalizer_instInhabitedExprVisited: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Canonicalizer_instBEqExprVisited: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Canonicalizer_instHashableExprVisited: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Canonicalizer_instInhabitedState: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0: u64 =
    0;
pub static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2_value
) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2()
-> *mut LeanObject {
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    v___x_1239_ = lean_box(0);
    v___x_1240_ = l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1;
    v___x_1241_ = l_Lean_Expr_const___override(v___x_1240_, v___x_1239_);
    return v___x_1241_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default() -> *mut LeanObject
{
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    v___x_1242_ = lean_obj_once(
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
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited() -> *mut LeanObject {
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    v___x_1243_ = l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default;
    return v___x_1243_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(
    mut v_a_1244_: *mut LeanObject,
    mut v_b_1245_: *mut LeanObject,
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
    mut v_a_1249_: *mut LeanObject,
    mut v_b_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1251_: u8 = 0;
    let mut v_r_1252_: *mut LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(v_a_1249_, v_b_1250_);
    lean_dec_ref(v_b_1250_);
    lean_dec_ref(v_a_1249_);
    v_r_1252_ = lean_box((v_res_1251_) as usize);
    return v_r_1252_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(
    mut v_a_1255_: *mut LeanObject,
) -> u64 {
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: u64 = 0;
    v___x_1256_ = lean_ptr_addr(v_a_1255_);
    v___x_1257_ = lean_usize_to_uint64(v___x_1256_);
    return v___x_1257_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed(
    mut v_a_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1259_: u64 = 0;
    let mut v_r_1260_: *mut LeanObject = core::ptr::null_mut();
    v_res_1259_ = l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(v_a_1258_);
    lean_dec_ref(v_a_1258_);
    v_r_1260_ = lean_box_uint64(v_res_1259_);
    return v_r_1260_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0() -> *mut LeanObject {
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    v___x_1263_ = lean_box(0);
    v___x_1264_ = lean_unsigned_to_nat(16);
    v___x_1265_ = lean_mk_array(v___x_1264_, v___x_1263_);
    return v___x_1265_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1() -> *mut LeanObject {
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    v___x_1266_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0_once),
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0,
    );
    v___x_1267_ = lean_unsigned_to_nat(0);
    v___x_1268_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1268_, 0, v___x_1267_);
    lean_ctor_set(v___x_1268_, 1, v___x_1266_);
    return v___x_1268_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2() -> *mut LeanObject {
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    v___x_1269_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1_once),
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1,
    );
    v___x_1270_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1270_, 0, v___x_1269_);
    lean_ctor_set(v___x_1270_, 1, v___x_1269_);
    return v___x_1270_;
}
pub unsafe fn _init_l_Lean_Meta_Canonicalizer_instInhabitedState() -> *mut LeanObject {
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    v___x_1271_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2_once),
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2,
    );
    return v___x_1271_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(
    mut v_x_1272_: *mut LeanObject,
    mut v_transparency_1273_: u8,
    mut v_s_1274_: *mut LeanObject,
    mut v_a_1275_: *mut LeanObject,
    mut v_a_1276_: *mut LeanObject,
    mut v_a_1277_: *mut LeanObject,
    mut v_a_1278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1280_ = lean_st_mk_ref(v_s_1274_);
                v___x_1281_ = lean_box((v_transparency_1273_) as usize);
                lean_inc(v_a_1278_);
                lean_inc_ref(v_a_1277_);
                lean_inc(v_a_1276_);
                lean_inc_ref(v_a_1275_);
                lean_inc(v___x_1280_);
                v___x_1282_ = lean_apply_7(
                    v_x_1272_,
                    v___x_1281_,
                    v___x_1280_,
                    v_a_1275_,
                    v_a_1276_,
                    v_a_1277_,
                    v_a_1278_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1282_) == 0 {
                    v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
                    v_isSharedCheck_1291_ = (!lean_is_exclusive(v___x_1282_)) as u8;
                    if v_isSharedCheck_1291_ == 0 {
                        v___x_1285_ = v___x_1282_;
                        v_isShared_1286_ = v_isSharedCheck_1291_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1283_);
                        lean_dec(v___x_1282_);
                        v___x_1285_ = lean_box(0);
                        v_isShared_1286_ = v_isSharedCheck_1291_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1280_);
                    return v___x_1282_;
                }
            }
            1 => {
                v___x_1287_ = lean_st_ref_get(v___x_1280_);
                lean_dec(v___x_1280_);
                lean_dec(v___x_1287_);
                if v_isShared_1286_ == 0 {
                    v___x_1289_ = v___x_1285_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1283_);
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
    mut v_x_1292_: *mut LeanObject,
    mut v_transparency_1293_: *mut LeanObject,
    mut v_s_1294_: *mut LeanObject,
    mut v_a_1295_: *mut LeanObject,
    mut v_a_1296_: *mut LeanObject,
    mut v_a_1297_: *mut LeanObject,
    mut v_a_1298_: *mut LeanObject,
    mut v_a_1299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_transparency_boxed_1300_: u8 = 0;
    let mut v_res_1301_: *mut LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1300_ = (lean_unbox(v_transparency_1293_) as u8);
    v_res_1301_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(
        v_x_1292_,
        v_transparency_boxed_1300_,
        v_s_1294_,
        v_a_1295_,
        v_a_1296_,
        v_a_1297_,
        v_a_1298_,
    );
    lean_dec(v_a_1298_);
    lean_dec_ref(v_a_1297_);
    lean_dec(v_a_1296_);
    lean_dec_ref(v_a_1295_);
    return v_res_1301_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run_x27(
    mut v_00_u03b1_1302_: *mut LeanObject,
    mut v_x_1303_: *mut LeanObject,
    mut v_transparency_1304_: u8,
    mut v_s_1305_: *mut LeanObject,
    mut v_a_1306_: *mut LeanObject,
    mut v_a_1307_: *mut LeanObject,
    mut v_a_1308_: *mut LeanObject,
    mut v_a_1309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1312_: *mut LeanObject,
    mut v_x_1313_: *mut LeanObject,
    mut v_transparency_1314_: *mut LeanObject,
    mut v_s_1315_: *mut LeanObject,
    mut v_a_1316_: *mut LeanObject,
    mut v_a_1317_: *mut LeanObject,
    mut v_a_1318_: *mut LeanObject,
    mut v_a_1319_: *mut LeanObject,
    mut v_a_1320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_transparency_boxed_1321_: u8 = 0;
    let mut v_res_1322_: *mut LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1321_ = (lean_unbox(v_transparency_1314_) as u8);
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
    lean_dec(v_a_1319_);
    lean_dec_ref(v_a_1318_);
    lean_dec(v_a_1317_);
    lean_dec_ref(v_a_1316_);
    return v_res_1322_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run___redArg(
    mut v_x_1323_: *mut LeanObject,
    mut v_transparency_1324_: u8,
    mut v_s_1325_: *mut LeanObject,
    mut v_a_1326_: *mut LeanObject,
    mut v_a_1327_: *mut LeanObject,
    mut v_a_1328_: *mut LeanObject,
    mut v_a_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1337_: u8 = 0;
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v_a_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1351_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1331_ = lean_st_mk_ref(v_s_1325_);
                v___x_1332_ = lean_box((v_transparency_1324_) as usize);
                lean_inc(v_a_1329_);
                lean_inc_ref(v_a_1328_);
                lean_inc(v_a_1327_);
                lean_inc_ref(v_a_1326_);
                lean_inc(v___x_1331_);
                v___x_1333_ = lean_apply_7(
                    v_x_1323_,
                    v___x_1332_,
                    v___x_1331_,
                    v_a_1326_,
                    v_a_1327_,
                    v_a_1328_,
                    v_a_1329_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1333_) == 0 {
                    v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
                    v_isSharedCheck_1343_ = (!lean_is_exclusive(v___x_1333_)) as u8;
                    if v_isSharedCheck_1343_ == 0 {
                        v___x_1336_ = v___x_1333_;
                        v_isShared_1337_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1334_);
                        lean_dec(v___x_1333_);
                        v___x_1336_ = lean_box(0);
                        v_isShared_1337_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1331_);
                    v_a_1344_ = lean_ctor_get(v___x_1333_, 0);
                    v_isSharedCheck_1351_ = (!lean_is_exclusive(v___x_1333_)) as u8;
                    if v_isSharedCheck_1351_ == 0 {
                        v___x_1346_ = v___x_1333_;
                        v_isShared_1347_ = v_isSharedCheck_1351_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1344_);
                        lean_dec(v___x_1333_);
                        v___x_1346_ = lean_box(0);
                        v_isShared_1347_ = v_isSharedCheck_1351_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1338_ = lean_st_ref_get(v___x_1331_);
                lean_dec(v___x_1331_);
                v___x_1339_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1339_, 0, v_a_1334_);
                lean_ctor_set(v___x_1339_, 1, v___x_1338_);
                if v_isShared_1337_ == 0 {
                    lean_ctor_set(v___x_1336_, 0, v___x_1339_);
                    v___x_1341_ = v___x_1336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
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
                    v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
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
    mut v_x_1352_: *mut LeanObject,
    mut v_transparency_1353_: *mut LeanObject,
    mut v_s_1354_: *mut LeanObject,
    mut v_a_1355_: *mut LeanObject,
    mut v_a_1356_: *mut LeanObject,
    mut v_a_1357_: *mut LeanObject,
    mut v_a_1358_: *mut LeanObject,
    mut v_a_1359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_transparency_boxed_1360_: u8 = 0;
    let mut v_res_1361_: *mut LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1360_ = (lean_unbox(v_transparency_1353_) as u8);
    v_res_1361_ = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(
        v_x_1352_,
        v_transparency_boxed_1360_,
        v_s_1354_,
        v_a_1355_,
        v_a_1356_,
        v_a_1357_,
        v_a_1358_,
    );
    lean_dec(v_a_1358_);
    lean_dec_ref(v_a_1357_);
    lean_dec(v_a_1356_);
    lean_dec_ref(v_a_1355_);
    return v_res_1361_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_CanonM_run(
    mut v_00_u03b1_1362_: *mut LeanObject,
    mut v_x_1363_: *mut LeanObject,
    mut v_transparency_1364_: u8,
    mut v_s_1365_: *mut LeanObject,
    mut v_a_1366_: *mut LeanObject,
    mut v_a_1367_: *mut LeanObject,
    mut v_a_1368_: *mut LeanObject,
    mut v_a_1369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1372_: *mut LeanObject,
    mut v_x_1373_: *mut LeanObject,
    mut v_transparency_1374_: *mut LeanObject,
    mut v_s_1375_: *mut LeanObject,
    mut v_a_1376_: *mut LeanObject,
    mut v_a_1377_: *mut LeanObject,
    mut v_a_1378_: *mut LeanObject,
    mut v_a_1379_: *mut LeanObject,
    mut v_a_1380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_transparency_boxed_1381_: u8 = 0;
    let mut v_res_1382_: *mut LeanObject = core::ptr::null_mut();
    v_transparency_boxed_1381_ = (lean_unbox(v_transparency_1374_) as u8);
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
    lean_dec(v_a_1379_);
    lean_dec_ref(v_a_1378_);
    lean_dec(v_a_1377_);
    lean_dec_ref(v_a_1376_);
    return v_res_1382_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(
    mut v_a_1383_: *mut LeanObject,
    mut v_x_1384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: usize = 0;
    let mut v___x_1390_: usize = 0;
    let mut v___x_1391_: u8 = 0;
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1384_) == 0 {
                    v___x_1385_ = lean_box(0);
                    return v___x_1385_;
                } else {
                    v_key_1386_ = lean_ctor_get(v_x_1384_, 0);
                    v_value_1387_ = lean_ctor_get(v_x_1384_, 1);
                    v_tail_1388_ = lean_ctor_get(v_x_1384_, 2);
                    v___x_1389_ = lean_ptr_addr(v_key_1386_);
                    v___x_1390_ = lean_ptr_addr(v_a_1383_);
                    v___x_1391_ = lean_usize_dec_eq(v___x_1389_, v___x_1390_);
                    if v___x_1391_ == 0 {
                        v_x_1384_ = v_tail_1388_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1387_);
                        v___x_1393_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1393_, 0, v_value_1387_);
                        return v___x_1393_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg___boxed(
    mut v_a_1394_: *mut LeanObject,
    mut v_x_1395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1396_: *mut LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(v_a_1394_, v_x_1395_);
    lean_dec(v_x_1395_);
    lean_dec_ref(v_a_1394_);
    return v_res_1396_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(
    mut v_m_1397_: *mut LeanObject,
    mut v_a_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_1399_ = lean_ctor_get(v_m_1397_, 1);
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
    mut v_m_1416_: *mut LeanObject,
    mut v_a_1417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1418_: *mut LeanObject = core::ptr::null_mut();
    v_res_1418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_m_1416_, v_a_1417_);
    lean_dec_ref(v_a_1417_);
    lean_dec_ref(v_m_1416_);
    return v_res_1418_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(
    mut v_e_1419_: *mut LeanObject,
    mut v_____do__lift_1420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cache_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: u8 = 0;
    v_cache_1421_ = lean_ctor_get(v_____do__lift_1420_, 0);
    v_buckets_1422_ = lean_ctor_get(v_cache_1421_, 1);
    v___x_1423_ = lean_unsigned_to_nat(0);
    v___x_1424_ = lean_array_get_size(v_buckets_1422_);
    v___x_1425_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
    if v___x_1425_ == 0 {
        let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
        v___x_1426_ = lean_box(0);
        return v___x_1426_;
    } else {
        let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
        v___x_1427_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_cache_1421_, v_e_1419_);
        return v___x_1427_;
    }
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(
    mut v_e_1428_: *mut LeanObject,
    mut v_____do__lift_1429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1430_: *mut LeanObject = core::ptr::null_mut();
    v_res_1430_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(
        v_e_1428_,
        v_____do__lift_1429_,
    );
    lean_dec_ref(v_____do__lift_1429_);
    lean_dec_ref(v_e_1428_);
    return v_res_1430_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(
    mut v_00_u03b2_1431_: *mut LeanObject,
    mut v_m_1432_: *mut LeanObject,
    mut v_a_1433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    v___x_1434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_m_1432_, v_a_1433_);
    return v___x_1434_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___boxed(
    mut v_00_u03b2_1435_: *mut LeanObject,
    mut v_m_1436_: *mut LeanObject,
    mut v_a_1437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1438_: *mut LeanObject = core::ptr::null_mut();
    v_res_1438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(v_00_u03b2_1435_, v_m_1436_, v_a_1437_);
    lean_dec_ref(v_a_1437_);
    lean_dec_ref(v_m_1436_);
    return v_res_1438_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0(
    mut v_00_u03b2_1439_: *mut LeanObject,
    mut v_a_1440_: *mut LeanObject,
    mut v_x_1441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    v___x_1442_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(v_a_1440_, v_x_1441_);
    return v___x_1442_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___boxed(
    mut v_00_u03b2_1443_: *mut LeanObject,
    mut v_a_1444_: *mut LeanObject,
    mut v_x_1445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1446_: *mut LeanObject = core::ptr::null_mut();
    v_res_1446_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0(v_00_u03b2_1443_, v_a_1444_, v_x_1445_);
    lean_dec(v_x_1445_);
    lean_dec_ref(v_a_1444_);
    return v_res_1446_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(
    mut v_a_1447_: *mut LeanObject,
    mut v_x_1448_: *mut LeanObject,
) -> u8 {
    let mut v___x_1449_: u8 = 0;
    let mut v_key_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: usize = 0;
    let mut v___x_1453_: usize = 0;
    let mut v___x_1454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1448_) == 0 {
                    v___x_1449_ = 0;
                    return v___x_1449_;
                } else {
                    v_key_1450_ = lean_ctor_get(v_x_1448_, 0);
                    v_tail_1451_ = lean_ctor_get(v_x_1448_, 2);
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
    mut v_a_1456_: *mut LeanObject,
    mut v_x_1457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1458_: u8 = 0;
    let mut v_r_1459_: *mut LeanObject = core::ptr::null_mut();
    v_res_1458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(v_a_1456_, v_x_1457_);
    lean_dec(v_x_1457_);
    lean_dec_ref(v_a_1456_);
    v_r_1459_ = lean_box((v_res_1458_) as usize);
    return v_r_1459_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1460_: *mut LeanObject,
    mut v_x_1461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1467_: u8 = 0;
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1461_) == 0 {
                    return v_x_1460_;
                } else {
                    v_key_1462_ = lean_ctor_get(v_x_1461_, 0);
                    v_value_1463_ = lean_ctor_get(v_x_1461_, 1);
                    v_tail_1464_ = lean_ctor_get(v_x_1461_, 2);
                    v_isSharedCheck_1488_ = (!lean_is_exclusive(v_x_1461_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v___x_1466_ = v_x_1461_;
                        v_isShared_1467_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1464_);
                        lean_inc(v_value_1463_);
                        lean_inc(v_key_1462_);
                        lean_dec(v_x_1461_);
                        v___x_1466_ = lean_box(0);
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
                lean_inc(v___x_1482_);
                if v_isShared_1467_ == 0 {
                    lean_ctor_set(v___x_1466_, 2, v___x_1482_);
                    v___x_1484_ = v___x_1466_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_key_1462_);
                    lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_value_1463_);
                    lean_ctor_set(v_reuseFailAlloc_1487_, 2, v___x_1482_);
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
    mut v_i_1489_: *mut LeanObject,
    mut v_source_1490_: *mut LeanObject,
    mut v_target_1491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v_es_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1492_ = lean_array_get_size(v_source_1490_);
                v___x_1493_ = lean_nat_dec_lt(v_i_1489_, v___x_1492_);
                if v___x_1493_ == 0 {
                    lean_dec_ref(v_source_1490_);
                    lean_dec(v_i_1489_);
                    return v_target_1491_;
                } else {
                    v_es_1494_ = lean_array_fget(v_source_1490_, v_i_1489_);
                    v___x_1495_ = lean_box(0);
                    v_source_1496_ = lean_array_fset(v_source_1490_, v_i_1489_, v___x_1495_);
                    v_target_1497_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1491_, v_es_1494_);
                    v___x_1498_ = lean_unsigned_to_nat(1);
                    v___x_1499_ = lean_nat_add(v_i_1489_, v___x_1498_);
                    lean_dec(v_i_1489_);
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
    mut v_data_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    v___x_1502_ = lean_array_get_size(v_data_1501_);
    v___x_1503_ = lean_unsigned_to_nat(2);
    v_nbuckets_1504_ = lean_nat_mul(v___x_1502_, v___x_1503_);
    v___x_1505_ = lean_unsigned_to_nat(0);
    v___x_1506_ = lean_box(0);
    v___x_1507_ = lean_mk_array(v_nbuckets_1504_, v___x_1506_);
    v___x_1508_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2___redArg(v___x_1505_, v_data_1501_, v___x_1507_);
    return v___x_1508_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(
    mut v_a_1509_: *mut LeanObject,
    mut v_b_1510_: *mut LeanObject,
    mut v_x_1511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1517_: u8 = 0;
    let mut v___x_1518_: usize = 0;
    let mut v___x_1519_: usize = 0;
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1511_) == 0 {
                    lean_dec(v_b_1510_);
                    lean_dec_ref(v_a_1509_);
                    return v_x_1511_;
                } else {
                    v_key_1512_ = lean_ctor_get(v_x_1511_, 0);
                    v_value_1513_ = lean_ctor_get(v_x_1511_, 1);
                    v_tail_1514_ = lean_ctor_get(v_x_1511_, 2);
                    v_isSharedCheck_1528_ = (!lean_is_exclusive(v_x_1511_)) as u8;
                    if v_isSharedCheck_1528_ == 0 {
                        v___x_1516_ = v_x_1511_;
                        v_isShared_1517_ = v_isSharedCheck_1528_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1514_);
                        lean_inc(v_value_1513_);
                        lean_inc(v_key_1512_);
                        lean_dec(v_x_1511_);
                        v___x_1516_ = lean_box(0);
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
                        lean_ctor_set(v___x_1516_, 2, v___x_1521_);
                        v___x_1523_ = v___x_1516_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_key_1512_);
                        lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_value_1513_);
                        lean_ctor_set(v_reuseFailAlloc_1524_, 2, v___x_1521_);
                        v___x_1523_ = v_reuseFailAlloc_1524_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1513_);
                    lean_dec(v_key_1512_);
                    if v_isShared_1517_ == 0 {
                        lean_ctor_set(v___x_1516_, 1, v_b_1510_);
                        lean_ctor_set(v___x_1516_, 0, v_a_1509_);
                        v___x_1526_ = v___x_1516_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1509_);
                        lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_b_1510_);
                        lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_tail_1514_);
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
    mut v_m_1529_: *mut LeanObject,
    mut v_a_1530_: *mut LeanObject,
    mut v_b_1531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v_val_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1532_ = lean_ctor_get(v_m_1529_, 0);
                v_buckets_1533_ = lean_ctor_get(v_m_1529_, 1);
                v_isSharedCheck_1577_ = (!lean_is_exclusive(v_m_1529_)) as u8;
                if v_isSharedCheck_1577_ == 0 {
                    v___x_1535_ = v_m_1529_;
                    v_isShared_1536_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1533_);
                    lean_inc(v_size_1532_);
                    lean_dec(v_m_1529_);
                    v___x_1535_ = lean_box(0);
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
                    v___x_1553_ = lean_unsigned_to_nat(1);
                    v_size_x27_1554_ = lean_nat_add(v_size_1532_, v___x_1553_);
                    lean_dec(v_size_1532_);
                    lean_inc(v_bkt_1551_);
                    v___x_1555_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1555_, 0, v_a_1530_);
                    lean_ctor_set(v___x_1555_, 1, v_b_1531_);
                    lean_ctor_set(v___x_1555_, 2, v_bkt_1551_);
                    v_buckets_x27_1556_ =
                        lean_array_uset(v_buckets_1533_, v___x_1550_, v___x_1555_);
                    v___x_1557_ = lean_unsigned_to_nat(4);
                    v___x_1558_ = lean_nat_mul(v_size_x27_1554_, v___x_1557_);
                    v___x_1559_ = lean_unsigned_to_nat(3);
                    v___x_1560_ = lean_nat_div(v___x_1558_, v___x_1559_);
                    lean_dec(v___x_1558_);
                    v___x_1561_ = lean_array_get_size(v_buckets_x27_1556_);
                    v___x_1562_ = lean_nat_dec_le(v___x_1560_, v___x_1561_);
                    lean_dec(v___x_1560_);
                    if v___x_1562_ == 0 {
                        v_val_1563_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1___redArg(v_buckets_x27_1556_);
                        if v_isShared_1536_ == 0 {
                            lean_ctor_set(v___x_1535_, 1, v_val_1563_);
                            lean_ctor_set(v___x_1535_, 0, v_size_x27_1554_);
                            v___x_1565_ = v___x_1535_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_size_x27_1554_);
                            lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_val_1563_);
                            v___x_1565_ = v_reuseFailAlloc_1566_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1536_ == 0 {
                            lean_ctor_set(v___x_1535_, 1, v_buckets_x27_1556_);
                            lean_ctor_set(v___x_1535_, 0, v_size_x27_1554_);
                            v___x_1568_ = v___x_1535_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_size_x27_1554_);
                            lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_buckets_x27_1556_);
                            v___x_1568_ = v_reuseFailAlloc_1569_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1551_);
                    v___x_1570_ = lean_box(0);
                    v_buckets_x27_1571_ =
                        lean_array_uset(v_buckets_1533_, v___x_1550_, v___x_1570_);
                    v___x_1572_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(v_a_1530_, v_b_1531_, v_bkt_1551_);
                    v___x_1573_ = lean_array_uset(v_buckets_x27_1571_, v___x_1550_, v___x_1572_);
                    if v_isShared_1536_ == 0 {
                        lean_ctor_set(v___x_1535_, 1, v___x_1573_);
                        v___x_1575_ = v___x_1535_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_size_1532_);
                        lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1573_);
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
    mut v_e_1578_: *mut LeanObject,
    mut v_key_1579_: u64,
    mut v_a_1580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyToExprs_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1597_: u8 = 0;
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_unused_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1582_ = lean_st_ref_take(v_a_1580_);
                v_cache_1588_ = lean_ctor_get(v___x_1582_, 0);
                lean_inc_ref(v_cache_1588_);
                v_keyToExprs_1589_ = lean_ctor_get(v___x_1582_, 1);
                lean_inc_ref(v_keyToExprs_1589_);
                v_buckets_1590_ = lean_ctor_get(v_cache_1588_, 1);
                v___x_1591_ = lean_box(0);
                v___x_1592_ = lean_unsigned_to_nat(0);
                v___x_1593_ = lean_array_get_size(v_buckets_1590_);
                v___x_1594_ = lean_nat_dec_lt(v___x_1592_, v___x_1593_);
                if v___x_1594_ == 0 {
                    lean_dec_ref(v_keyToExprs_1589_);
                    lean_dec_ref(v_cache_1588_);
                    lean_dec_ref(v_e_1578_);
                    v_fst_1584_ = v___x_1591_;
                    v_snd_1585_ = v___x_1582_;
                    state = 1;
                    continue;
                } else {
                    v_isSharedCheck_1603_ = (!lean_is_exclusive(v___x_1582_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v_unused_1604_ = lean_ctor_get(v___x_1582_, 1);
                        lean_dec(v_unused_1604_);
                        v_unused_1605_ = lean_ctor_get(v___x_1582_, 0);
                        lean_dec(v_unused_1605_);
                        v___x_1596_ = v___x_1582_;
                        v_isShared_1597_ = v_isSharedCheck_1603_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_1582_);
                        v___x_1596_ = lean_box(0);
                        v_isShared_1597_ = v_isSharedCheck_1603_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1586_ = lean_st_ref_set(v_a_1580_, v_snd_1585_);
                v___x_1587_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1587_, 0, v_fst_1584_);
                return v___x_1587_;
            }
            2 => {
                v___x_1598_ = lean_box_uint64(v_key_1579_);
                v___x_1599_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(v_cache_1588_, v_e_1578_, v___x_1598_);
                if v_isShared_1597_ == 0 {
                    lean_ctor_set(v___x_1596_, 0, v___x_1599_);
                    v___x_1601_ = v___x_1596_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_keyToExprs_1589_);
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
    mut v_e_1606_: *mut LeanObject,
    mut v_key_1607_: *mut LeanObject,
    mut v_a_1608_: *mut LeanObject,
    mut v_a_1609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_boxed_1610_: u64 = 0;
    let mut v_res_1611_: *mut LeanObject = core::ptr::null_mut();
    v_key_boxed_1610_ = lean_unbox_uint64(v_key_1607_);
    lean_dec_ref(v_key_1607_);
    v_res_1611_ =
        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(
            v_e_1606_,
            v_key_boxed_1610_,
            v_a_1608_,
        );
    lean_dec(v_a_1608_);
    return v_res_1611_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(
    mut v_e_1612_: *mut LeanObject,
    mut v_key_1613_: u64,
    mut v_a_1614_: u8,
    mut v_a_1615_: *mut LeanObject,
    mut v_a_1616_: *mut LeanObject,
    mut v_a_1617_: *mut LeanObject,
    mut v_a_1618_: *mut LeanObject,
    mut v_a_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    v___x_1621_ =
        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(
            v_e_1612_,
            v_key_1613_,
            v_a_1615_,
        );
    return v___x_1621_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___boxed(
    mut v_e_1622_: *mut LeanObject,
    mut v_key_1623_: *mut LeanObject,
    mut v_a_1624_: *mut LeanObject,
    mut v_a_1625_: *mut LeanObject,
    mut v_a_1626_: *mut LeanObject,
    mut v_a_1627_: *mut LeanObject,
    mut v_a_1628_: *mut LeanObject,
    mut v_a_1629_: *mut LeanObject,
    mut v_a_1630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_boxed_1631_: u64 = 0;
    let mut v_a_boxed_1632_: u8 = 0;
    let mut v_res_1633_: *mut LeanObject = core::ptr::null_mut();
    v_key_boxed_1631_ = lean_unbox_uint64(v_key_1623_);
    lean_dec_ref(v_key_1623_);
    v_a_boxed_1632_ = (lean_unbox(v_a_1624_) as u8);
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
    lean_dec(v_a_1629_);
    lean_dec_ref(v_a_1628_);
    lean_dec(v_a_1627_);
    lean_dec_ref(v_a_1626_);
    lean_dec(v_a_1625_);
    return v_res_1633_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0(
    mut v_00_u03b2_1634_: *mut LeanObject,
    mut v_m_1635_: *mut LeanObject,
    mut v_a_1636_: *mut LeanObject,
    mut v_b_1637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    v___x_1638_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(v_m_1635_, v_a_1636_, v_b_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0(
    mut v_00_u03b2_1639_: *mut LeanObject,
    mut v_a_1640_: *mut LeanObject,
    mut v_x_1641_: *mut LeanObject,
) -> u8 {
    let mut v___x_1642_: u8 = 0;
    v___x_1642_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(v_a_1640_, v_x_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___boxed(
    mut v_00_u03b2_1643_: *mut LeanObject,
    mut v_a_1644_: *mut LeanObject,
    mut v_x_1645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1646_: u8 = 0;
    let mut v_r_1647_: *mut LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0(v_00_u03b2_1643_, v_a_1644_, v_x_1645_);
    lean_dec(v_x_1645_);
    lean_dec_ref(v_a_1644_);
    v_r_1647_ = lean_box((v_res_1646_) as usize);
    return v_r_1647_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1(
    mut v_00_u03b2_1648_: *mut LeanObject,
    mut v_data_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    v___x_1650_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1___redArg(v_data_1649_);
    return v___x_1650_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2(
    mut v_00_u03b2_1651_: *mut LeanObject,
    mut v_a_1652_: *mut LeanObject,
    mut v_b_1653_: *mut LeanObject,
    mut v_x_1654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(v_a_1652_, v_b_1653_, v_x_1654_);
    return v___x_1655_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1656_: *mut LeanObject,
    mut v_i_1657_: *mut LeanObject,
    mut v_source_1658_: *mut LeanObject,
    mut v_target_1659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    v___x_1660_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2___redArg(v_i_1657_, v_source_1658_, v_target_1659_);
    return v___x_1660_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1661_: *mut LeanObject,
    mut v_x_1662_: *mut LeanObject,
    mut v_x_1663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    v___x_1664_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1662_, v_x_1663_);
    return v___x_1664_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(
    mut v_e_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut v_unused_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1668_ = l_Lean_Expr_hasMVar(v_e_1665_);
                if v___x_1668_ == 0 {
                    v___x_1669_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1669_, 0, v_e_1665_);
                    return v___x_1669_;
                } else {
                    v___x_1670_ = lean_st_ref_get(v___y_1666_);
                    v_mctx_1671_ = lean_ctor_get(v___x_1670_, 0);
                    lean_inc_ref(v_mctx_1671_);
                    lean_dec(v___x_1670_);
                    v___x_1672_ = l_Lean_instantiateMVarsCore(v_mctx_1671_, v_e_1665_);
                    v_fst_1673_ = lean_ctor_get(v___x_1672_, 0);
                    lean_inc(v_fst_1673_);
                    v_snd_1674_ = lean_ctor_get(v___x_1672_, 1);
                    lean_inc(v_snd_1674_);
                    lean_dec_ref(v___x_1672_);
                    v___x_1675_ = lean_st_ref_take(v___y_1666_);
                    v_cache_1676_ = lean_ctor_get(v___x_1675_, 1);
                    v_zetaDeltaFVarIds_1677_ = lean_ctor_get(v___x_1675_, 2);
                    v_postponed_1678_ = lean_ctor_get(v___x_1675_, 3);
                    v_diag_1679_ = lean_ctor_get(v___x_1675_, 4);
                    v_isSharedCheck_1688_ = (!lean_is_exclusive(v___x_1675_)) as u8;
                    if v_isSharedCheck_1688_ == 0 {
                        v_unused_1689_ = lean_ctor_get(v___x_1675_, 0);
                        lean_dec(v_unused_1689_);
                        v___x_1681_ = v___x_1675_;
                        v_isShared_1682_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1679_);
                        lean_inc(v_postponed_1678_);
                        lean_inc(v_zetaDeltaFVarIds_1677_);
                        lean_inc(v_cache_1676_);
                        lean_dec(v___x_1675_);
                        v___x_1681_ = lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1688_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1682_ == 0 {
                    lean_ctor_set(v___x_1681_, 0, v_snd_1674_);
                    v___x_1684_ = v___x_1681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_snd_1674_);
                    lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_cache_1676_);
                    lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_zetaDeltaFVarIds_1677_);
                    lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_postponed_1678_);
                    lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_diag_1679_);
                    v___x_1684_ = v_reuseFailAlloc_1687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1685_ = lean_st_ref_set(v___y_1666_, v___x_1684_);
                v___x_1686_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1686_, 0, v_fst_1673_);
                return v___x_1686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(
    mut v_e_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1693_: *mut LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1690_, v___y_1691_);
    lean_dec(v___y_1691_);
    return v_res_1693_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(
    mut v_e_1694_: *mut LeanObject,
    mut v___y_1695_: u8,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    v___x_1702_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1694_, v___y_1698_);
    return v___x_1702_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(
    mut v_e_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
    mut v___y_1710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_13173__boxed_1711_: u8 = 0;
    let mut v_res_1712_: *mut LeanObject = core::ptr::null_mut();
    v___y_13173__boxed_1711_ = (lean_unbox(v___y_1704_) as u8);
    v_res_1712_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(v_e_1703_, v___y_13173__boxed_1711_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
    lean_dec(v___y_1709_);
    lean_dec_ref(v___y_1708_);
    lean_dec(v___y_1707_);
    lean_dec_ref(v___y_1706_);
    lean_dec(v___y_1705_);
    return v_res_1712_;
}
pub unsafe fn _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0()
-> u64 {
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: u64 = 0;
    v___x_1713_ = lean_unsigned_to_nat(1723);
    v___x_1714_ = lean_uint64_of_nat(v___x_1713_);
    return v___x_1714_;
}
pub unsafe fn _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1()
-> *mut LeanObject {
    let mut v___x_1715_: u64 = 0;
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    v___x_1715_ = lean_uint64_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_once
        ),
        _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0,
    );
    v___x_1716_ = lean_box_uint64(v___x_1715_);
    return v___x_1716_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
    mut v_e_1721_: *mut LeanObject,
    mut v_a_1722_: u8,
    mut v_a_1723_: *mut LeanObject,
    mut v_a_1724_: *mut LeanObject,
    mut v_a_1725_: *mut LeanObject,
    mut v_a_1726_: *mut LeanObject,
    mut v_a_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1732_: u8 = 0;
    let mut v___y_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: u64 = 0;
    let mut v___x_1746_: u64 = 0;
    let mut v___x_1747_: u64 = 0;
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut v_key_1754_: u64 = 0;
    let mut v___y_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut v_unused_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u64 = 0;
    let mut v___x_1793_: u64 = 0;
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut v_a_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_declName_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_1810_: u64 = 0;
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1816_: u8 = 0;
    let mut v___y_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u64 = 0;
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1829_: u8 = 0;
    let mut v___y_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut v_a_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1856_: u8 = 0;
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1860_: u8 = 0;
    let mut v_binderType_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1874_: u64 = 0;
    let mut v___x_1875_: u64 = 0;
    let mut v___x_1876_: u64 = 0;
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut v_expr_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u64 = 0;
    let mut v_idx_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v___x_1893_: u64 = 0;
    let mut v___x_1894_: u64 = 0;
    let mut v___x_1895_: u64 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut v___x_1901_: u64 = 0;
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
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
                lean_dec(v___x_1774_);
                if lean_obj_tag(v___x_1775_) == 1 {
                    lean_dec_ref(v_e_1721_);
                    v_val_1776_ = lean_ctor_get(v___x_1775_, 0);
                    v_isSharedCheck_1783_ = (!lean_is_exclusive(v___x_1775_)) as u8;
                    if v_isSharedCheck_1783_ == 0 {
                        v___x_1778_ = v___x_1775_;
                        v_isShared_1779_ = v_isSharedCheck_1783_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_val_1776_);
                        lean_dec(v___x_1775_);
                        v___x_1778_ = lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_1783_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1775_);
                    match lean_obj_tag(v_e_1721_) {
                        2 => {
                            lean_inc_ref(v_e_1721_);
                            v___x_1784_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1721_, v_a_1725_);
                            if lean_obj_tag(v___x_1784_) == 0 {
                                v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
                                v_isSharedCheck_1798_ = (!lean_is_exclusive(v___x_1784_)) as u8;
                                if v_isSharedCheck_1798_ == 0 {
                                    v___x_1787_ = v___x_1784_;
                                    v_isShared_1788_ = v_isSharedCheck_1798_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_1785_);
                                    lean_dec(v___x_1784_);
                                    v___x_1787_ = lean_box(0);
                                    v_isShared_1788_ = v_isSharedCheck_1798_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_e_1721_, 1);
                                v_a_1799_ = lean_ctor_get(v___x_1784_, 0);
                                v_isSharedCheck_1806_ = (!lean_is_exclusive(v___x_1784_)) as u8;
                                if v_isSharedCheck_1806_ == 0 {
                                    v___x_1801_ = v___x_1784_;
                                    v_isShared_1802_ = v_isSharedCheck_1806_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_1799_);
                                    lean_dec(v___x_1784_);
                                    v___x_1801_ = lean_box(0);
                                    v_isShared_1802_ = v_isSharedCheck_1806_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                        4 => {
                            v_declName_1807_ = lean_ctor_get(v_e_1721_, 0);
                            lean_inc(v_declName_1807_);
                            lean_dec_ref_known(v_e_1721_, 2);
                            if lean_obj_tag(v_declName_1807_) == 0 {
                                v___x_1808_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1;
                                v___x_1809_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1809_, 0, v___x_1808_);
                                return v___x_1809_;
                            } else {
                                v_hash_1810_ = lean_ctor_get_uint64(
                                    v_declName_1807_,
                                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                );
                                lean_dec(v_declName_1807_);
                                v___x_1811_ = lean_box_uint64(v_hash_1810_);
                                v___x_1812_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1812_, 0, v___x_1811_);
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
                                lean_inc_ref(v_e_1721_);
                                v___x_1849_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_1721_, v_a_1725_);
                                if lean_obj_tag(v___x_1849_) == 0 {
                                    v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
                                    lean_inc(v_a_1850_);
                                    lean_dec_ref_known(v___x_1849_, 1);
                                    v___x_1851_ = lean_expr_eqv(v_a_1850_, v_e_1721_);
                                    if v___x_1851_ == 0 {
                                        lean_dec_ref(v___x_1813_);
                                        lean_dec_ref_known(v_e_1721_, 2);
                                        v_e_1721_ = v_a_1850_;
                                        state = 0;
                                        continue;
                                    } else {
                                        lean_dec(v_a_1850_);
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
                                    lean_dec_ref(v___x_1813_);
                                    lean_dec_ref_known(v_e_1721_, 2);
                                    v_a_1853_ = lean_ctor_get(v___x_1849_, 0);
                                    v_isSharedCheck_1860_ = (!lean_is_exclusive(v___x_1849_)) as u8;
                                    if v_isSharedCheck_1860_ == 0 {
                                        v___x_1855_ = v___x_1849_;
                                        v_isShared_1856_ = v_isSharedCheck_1860_;
                                        state = 19;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1853_);
                                        lean_dec(v___x_1849_);
                                        v___x_1855_ = lean_box(0);
                                        v_isShared_1856_ = v_isSharedCheck_1860_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            }
                        }
                        6 => {
                            v_binderType_1861_ = lean_ctor_get(v_e_1721_, 1);
                            lean_inc_ref(v_binderType_1861_);
                            v_body_1862_ = lean_ctor_get(v_e_1721_, 2);
                            lean_inc_ref(v_body_1862_);
                            lean_dec_ref_known(v_e_1721_, 3);
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
                            v_binderType_1863_ = lean_ctor_get(v_e_1721_, 1);
                            lean_inc_ref(v_binderType_1863_);
                            v_body_1864_ = lean_ctor_get(v_e_1721_, 2);
                            lean_inc_ref(v_body_1864_);
                            lean_dec_ref_known(v_e_1721_, 3);
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
                            v_value_1865_ = lean_ctor_get(v_e_1721_, 2);
                            lean_inc_ref(v_value_1865_);
                            v_body_1866_ = lean_ctor_get(v_e_1721_, 3);
                            lean_inc_ref(v_body_1866_);
                            lean_dec_ref_known(v_e_1721_, 4);
                            v___x_1867_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_value_1865_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                            if lean_obj_tag(v___x_1867_) == 0 {
                                v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
                                lean_inc(v_a_1868_);
                                lean_dec_ref_known(v___x_1867_, 1);
                                v___x_1869_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_body_1866_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                                if lean_obj_tag(v___x_1869_) == 0 {
                                    v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
                                    v_isSharedCheck_1881_ = (!lean_is_exclusive(v___x_1869_)) as u8;
                                    if v_isSharedCheck_1881_ == 0 {
                                        v___x_1872_ = v___x_1869_;
                                        v_isShared_1873_ = v_isSharedCheck_1881_;
                                        state = 21;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1870_);
                                        lean_dec(v___x_1869_);
                                        v___x_1872_ = lean_box(0);
                                        v_isShared_1873_ = v_isSharedCheck_1881_;
                                        state = 21;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_1868_);
                                    return v___x_1869_;
                                }
                            } else {
                                lean_dec_ref(v_body_1866_);
                                return v___x_1867_;
                            }
                        }
                        10 => {
                            v_expr_1882_ = lean_ctor_get(v_e_1721_, 1);
                            lean_inc_ref(v_expr_1882_);
                            v___x_1883_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_expr_1882_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                            if lean_obj_tag(v___x_1883_) == 0 {
                                v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
                                lean_inc(v_a_1884_);
                                lean_dec_ref_known(v___x_1883_, 1);
                                v___x_1885_ = lean_unbox_uint64(v_a_1884_);
                                lean_dec(v_a_1884_);
                                v_key_1754_ = v___x_1885_;
                                v___y_1755_ = v_a_1723_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec_ref_known(v_e_1721_, 2);
                                return v___x_1883_;
                            }
                        }
                        11 => {
                            v_idx_1886_ = lean_ctor_get(v_e_1721_, 1);
                            lean_inc(v_idx_1886_);
                            v_struct_1887_ = lean_ctor_get(v_e_1721_, 2);
                            lean_inc_ref(v_struct_1887_);
                            lean_dec_ref_known(v_e_1721_, 3);
                            v___x_1888_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_struct_1887_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
                            if lean_obj_tag(v___x_1888_) == 0 {
                                v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
                                v_isSharedCheck_1900_ = (!lean_is_exclusive(v___x_1888_)) as u8;
                                if v_isSharedCheck_1900_ == 0 {
                                    v___x_1891_ = v___x_1888_;
                                    v_isShared_1892_ = v_isSharedCheck_1900_;
                                    state = 23;
                                    continue;
                                } else {
                                    lean_inc(v_a_1889_);
                                    lean_dec(v___x_1888_);
                                    v___x_1891_ = lean_box(0);
                                    v_isShared_1892_ = v_isSharedCheck_1900_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                lean_dec(v_idx_1886_);
                                return v___x_1888_;
                            }
                        }
                        _ => {
                            v___x_1901_ = l_Lean_Expr_hash(v_e_1721_);
                            lean_dec_ref(v_e_1721_);
                            v___x_1902_ = lean_box_uint64(v___x_1901_);
                            v___x_1903_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1903_, 0, v___x_1902_);
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
                if lean_obj_tag(v___x_1738_) == 0 {
                    v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
                    lean_inc(v_a_1739_);
                    lean_dec_ref_known(v___x_1738_, 1);
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
                    if lean_obj_tag(v___x_1740_) == 0 {
                        v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
                        v_isSharedCheck_1752_ = (!lean_is_exclusive(v___x_1740_)) as u8;
                        if v_isSharedCheck_1752_ == 0 {
                            v___x_1743_ = v___x_1740_;
                            v_isShared_1744_ = v_isSharedCheck_1752_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1741_);
                            lean_dec(v___x_1740_);
                            v___x_1743_ = lean_box(0);
                            v_isShared_1744_ = v_isSharedCheck_1752_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1739_);
                        return v___x_1740_;
                    }
                } else {
                    lean_dec_ref(v_b_1731_);
                    return v___x_1738_;
                }
            }
            2 => {
                v___x_1745_ = lean_unbox_uint64(v_a_1739_);
                lean_dec(v_a_1739_);
                v___x_1746_ = lean_unbox_uint64(v_a_1741_);
                lean_dec(v_a_1741_);
                v___x_1747_ = lean_uint64_mix_hash(v___x_1745_, v___x_1746_);
                v___x_1748_ = lean_box_uint64(v___x_1747_);
                if v_isShared_1744_ == 0 {
                    lean_ctor_set(v___x_1743_, 0, v___x_1748_);
                    v___x_1750_ = v___x_1743_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
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
                if lean_obj_tag(v___x_1756_) == 0 {
                    v_isSharedCheck_1764_ = (!lean_is_exclusive(v___x_1756_)) as u8;
                    if v_isSharedCheck_1764_ == 0 {
                        v_unused_1765_ = lean_ctor_get(v___x_1756_, 0);
                        lean_dec(v_unused_1765_);
                        v___x_1758_ = v___x_1756_;
                        v_isShared_1759_ = v_isSharedCheck_1764_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v___x_1756_);
                        v___x_1758_ = lean_box(0);
                        v_isShared_1759_ = v_isSharedCheck_1764_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_1766_ = lean_ctor_get(v___x_1756_, 0);
                    v_isSharedCheck_1773_ = (!lean_is_exclusive(v___x_1756_)) as u8;
                    if v_isSharedCheck_1773_ == 0 {
                        v___x_1768_ = v___x_1756_;
                        v_isShared_1769_ = v_isSharedCheck_1773_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1766_);
                        lean_dec(v___x_1756_);
                        v___x_1768_ = lean_box(0);
                        v_isShared_1769_ = v_isSharedCheck_1773_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1760_ = lean_box_uint64(v_key_1754_);
                if v_isShared_1759_ == 0 {
                    lean_ctor_set(v___x_1758_, 0, v___x_1760_);
                    v___x_1762_ = v___x_1758_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
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
                    v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
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
                    lean_ctor_set_tag(v___x_1778_, 0);
                    v___x_1781_ = v___x_1778_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_val_1776_);
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
                    lean_del_object(v___x_1787_);
                    v___x_1790_ =
                        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
                            v_a_1785_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_,
                            v_a_1727_,
                        );
                    if lean_obj_tag(v___x_1790_) == 0 {
                        v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
                        lean_inc(v_a_1791_);
                        lean_dec_ref_known(v___x_1790_, 1);
                        v___x_1792_ = lean_unbox_uint64(v_a_1791_);
                        lean_dec(v_a_1791_);
                        v_key_1754_ = v___x_1792_;
                        v___y_1755_ = v_a_1723_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec_ref_known(v_e_1721_, 1);
                        return v___x_1790_;
                    }
                } else {
                    lean_dec(v_a_1785_);
                    v___x_1793_ = l_Lean_Expr_hash(v_e_1721_);
                    lean_dec_ref_known(v_e_1721_, 1);
                    v___x_1794_ = lean_box_uint64(v___x_1793_);
                    if v_isShared_1788_ == 0 {
                        lean_ctor_set(v___x_1787_, 0, v___x_1794_);
                        v___x_1796_ = v___x_1787_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
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
                    v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
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
                if lean_obj_tag(v___x_1822_) == 0 {
                    v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
                    lean_inc(v_a_1823_);
                    lean_dec_ref_known(v___x_1822_, 1);
                    v___x_1824_ = l_Lean_Expr_getAppNumArgs(v_e_1721_);
                    v___x_1825_ = lean_unsigned_to_nat(0);
                    v___x_1826_ = lean_unbox_uint64(v_a_1823_);
                    lean_dec(v_a_1823_);
                    v___x_1827_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_1824_, v_e_1721_, v___x_1824_, v_info_1815_, v___x_1825_, v___x_1826_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
                    lean_dec_ref(v_info_1815_);
                    lean_dec_ref_known(v_e_1721_, 2);
                    lean_dec(v___x_1824_);
                    return v___x_1827_;
                } else {
                    lean_dec_ref(v_info_1815_);
                    lean_dec_ref_known(v_e_1721_, 2);
                    return v___x_1822_;
                }
            }
            16 => {
                v___x_1835_ = l_Lean_Expr_hasLooseBVars(v___x_1813_);
                if v___x_1835_ == 0 {
                    v___x_1836_ = lean_box(0);
                    lean_inc_ref(v___x_1813_);
                    v___x_1837_ = l_Lean_Meta_getFunInfo(
                        v___x_1813_,
                        v___x_1836_,
                        v___y_1831_,
                        v___y_1832_,
                        v___y_1833_,
                        v___y_1834_,
                    );
                    if lean_obj_tag(v___x_1837_) == 0 {
                        v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
                        lean_inc(v_a_1838_);
                        lean_dec_ref_known(v___x_1837_, 1);
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
                        lean_dec_ref(v___x_1813_);
                        lean_dec_ref_known(v_e_1721_, 2);
                        v_a_1839_ = lean_ctor_get(v___x_1837_, 0);
                        v_isSharedCheck_1846_ = (!lean_is_exclusive(v___x_1837_)) as u8;
                        if v_isSharedCheck_1846_ == 0 {
                            v___x_1841_ = v___x_1837_;
                            v_isShared_1842_ = v_isSharedCheck_1846_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_1839_);
                            lean_dec(v___x_1837_);
                            v___x_1841_ = lean_box(0);
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
                    v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
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
                    v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
                    v___x_1858_ = v_reuseFailAlloc_1859_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1858_;
            }
            21 => {
                v___x_1874_ = lean_unbox_uint64(v_a_1868_);
                lean_dec(v_a_1868_);
                v___x_1875_ = lean_unbox_uint64(v_a_1870_);
                lean_dec(v_a_1870_);
                v___x_1876_ = lean_uint64_mix_hash(v___x_1874_, v___x_1875_);
                v___x_1877_ = lean_box_uint64(v___x_1876_);
                if v_isShared_1873_ == 0 {
                    lean_ctor_set(v___x_1872_, 0, v___x_1877_);
                    v___x_1879_ = v___x_1872_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
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
                lean_dec(v_idx_1886_);
                v___x_1894_ = lean_unbox_uint64(v_a_1889_);
                lean_dec(v_a_1889_);
                v___x_1895_ = lean_uint64_mix_hash(v___x_1893_, v___x_1894_);
                v___x_1896_ = lean_box_uint64(v___x_1895_);
                if v_isShared_1892_ == 0 {
                    lean_ctor_set(v___x_1891_, 0, v___x_1896_);
                    v___x_1898_ = v___x_1891_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
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
    mut v___x_1904_: *mut LeanObject,
    mut v_e_1905_: *mut LeanObject,
    mut v_upperBound_1906_: *mut LeanObject,
    mut v_info_1907_: *mut LeanObject,
    mut v_a_1908_: *mut LeanObject,
    mut v_b_1909_: u64,
    mut v___y_1910_: u8,
    mut v___y_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
    mut v___y_1915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1918_: u64 = 0;
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: u8 = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u64 = 0;
    let mut v___x_1931_: u64 = 0;
    let mut v___x_1932_: u8 = 0;
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: u8 = 0;
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u64 = 0;
    let mut v___x_1945_: u64 = 0;
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: u8 = 0;
    let mut v_isProp_1948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1932_ = lean_nat_dec_lt(v_a_1908_, v_upperBound_1906_);
                if v___x_1932_ == 0 {
                    lean_dec(v_a_1908_);
                    v___x_1933_ = lean_box_uint64(v_b_1909_);
                    v___x_1934_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1934_, 0, v___x_1933_);
                    return v___x_1934_;
                } else {
                    v_paramInfo_1935_ = lean_ctor_get(v_info_1907_, 0);
                    v___x_1936_ = lean_array_get_size(v_paramInfo_1935_);
                    v___x_1937_ = lean_nat_dec_lt(v_a_1908_, v___x_1936_);
                    if v___x_1937_ == 0 {
                        v___x_1938_ = lean_nat_sub(v___x_1904_, v_a_1908_);
                        v___x_1939_ = lean_unsigned_to_nat(1);
                        v___x_1940_ = lean_nat_sub(v___x_1938_, v___x_1939_);
                        lean_dec(v___x_1938_);
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
                        if lean_obj_tag(v___x_1942_) == 0 {
                            v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
                            lean_inc(v_a_1943_);
                            lean_dec_ref_known(v___x_1942_, 1);
                            v___x_1944_ = lean_unbox_uint64(v_a_1943_);
                            lean_dec(v_a_1943_);
                            v___x_1945_ = lean_uint64_mix_hash(v_b_1909_, v___x_1944_);
                            v_a_1918_ = v___x_1945_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_1908_);
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
                            v_isProp_1948_ = lean_ctor_get_uint8(
                                v___x_1946_,
                                (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
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
                v___x_1919_ = lean_unsigned_to_nat(1);
                v___x_1920_ = lean_nat_add(v_a_1908_, v___x_1919_);
                lean_dec(v_a_1908_);
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
                    v___x_1925_ = lean_unsigned_to_nat(1);
                    v___x_1926_ = lean_nat_sub(v___x_1924_, v___x_1925_);
                    lean_dec(v___x_1924_);
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
                    if lean_obj_tag(v___x_1928_) == 0 {
                        v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
                        lean_inc(v_a_1929_);
                        lean_dec_ref_known(v___x_1928_, 1);
                        v___x_1930_ = lean_unbox_uint64(v_a_1929_);
                        lean_dec(v_a_1929_);
                        v___x_1931_ = lean_uint64_mix_hash(v_b_1909_, v___x_1930_);
                        v_a_1918_ = v___x_1931_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_1908_);
                        return v___x_1928_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(
    mut v___x_1949_: *mut LeanObject,
    mut v_e_1950_: *mut LeanObject,
    mut v_upperBound_1951_: *mut LeanObject,
    mut v_info_1952_: *mut LeanObject,
    mut v_a_1953_: *mut LeanObject,
    mut v_b_1954_: *mut LeanObject,
    mut v___y_1955_: *mut LeanObject,
    mut v___y_1956_: *mut LeanObject,
    mut v___y_1957_: *mut LeanObject,
    mut v___y_1958_: *mut LeanObject,
    mut v___y_1959_: *mut LeanObject,
    mut v___y_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_1962_: u64 = 0;
    let mut v___y_13205__boxed_1963_: u8 = 0;
    let mut v_res_1964_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_1962_ = lean_unbox_uint64(v_b_1954_);
    lean_dec_ref(v_b_1954_);
    v___y_13205__boxed_1963_ = (lean_unbox(v___y_1955_) as u8);
    v_res_1964_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_1949_, v_e_1950_, v_upperBound_1951_, v_info_1952_, v_a_1953_, v_b_boxed_1962_, v___y_13205__boxed_1963_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
    lean_dec(v___y_1960_);
    lean_dec_ref(v___y_1959_);
    lean_dec(v___y_1958_);
    lean_dec_ref(v___y_1957_);
    lean_dec(v___y_1956_);
    lean_dec_ref(v_info_1952_);
    lean_dec(v_upperBound_1951_);
    lean_dec_ref(v_e_1950_);
    lean_dec(v___x_1949_);
    return v_res_1964_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(
    mut v_e_1965_: *mut LeanObject,
    mut v_a_1966_: *mut LeanObject,
    mut v_a_1967_: *mut LeanObject,
    mut v_a_1968_: *mut LeanObject,
    mut v_a_1969_: *mut LeanObject,
    mut v_a_1970_: *mut LeanObject,
    mut v_a_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1973_: u8 = 0;
    let mut v_res_1974_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1973_ = (lean_unbox(v_a_1966_) as u8);
    v_res_1974_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
        v_e_1965_,
        v_a_boxed_1973_,
        v_a_1967_,
        v_a_1968_,
        v_a_1969_,
        v_a_1970_,
        v_a_1971_,
    );
    lean_dec(v_a_1971_);
    lean_dec_ref(v_a_1970_);
    lean_dec(v_a_1969_);
    lean_dec_ref(v_a_1968_);
    lean_dec(v_a_1967_);
    return v_res_1974_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(
    mut v___x_1975_: *mut LeanObject,
    mut v_e_1976_: *mut LeanObject,
    mut v_upperBound_1977_: *mut LeanObject,
    mut v_info_1978_: *mut LeanObject,
    mut v_inst_1979_: *mut LeanObject,
    mut v_R_1980_: *mut LeanObject,
    mut v_a_1981_: *mut LeanObject,
    mut v_b_1982_: u64,
    mut v_c_1983_: *mut LeanObject,
    mut v___y_1984_: u8,
    mut v___y_1985_: *mut LeanObject,
    mut v___y_1986_: *mut LeanObject,
    mut v___y_1987_: *mut LeanObject,
    mut v___y_1988_: *mut LeanObject,
    mut v___y_1989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    v___x_1991_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_1975_, v_e_1976_, v_upperBound_1977_, v_info_1978_, v_a_1981_, v_b_1982_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
    return v___x_1991_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(
    mut v___x_1992_: *mut LeanObject,
    mut v_e_1993_: *mut LeanObject,
    mut v_upperBound_1994_: *mut LeanObject,
    mut v_info_1995_: *mut LeanObject,
    mut v_inst_1996_: *mut LeanObject,
    mut v_R_1997_: *mut LeanObject,
    mut v_a_1998_: *mut LeanObject,
    mut v_b_1999_: *mut LeanObject,
    mut v_c_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_2008_: u64 = 0;
    let mut v___y_13678__boxed_2009_: u8 = 0;
    let mut v_res_2010_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_2008_ = lean_unbox_uint64(v_b_1999_);
    lean_dec_ref(v_b_1999_);
    v___y_13678__boxed_2009_ = (lean_unbox(v___y_2001_) as u8);
    v_res_2010_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(v___x_1992_, v_e_1993_, v_upperBound_1994_, v_info_1995_, v_inst_1996_, v_R_1997_, v_a_1998_, v_b_boxed_2008_, v_c_2000_, v___y_13678__boxed_2009_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
    lean_dec(v___y_2006_);
    lean_dec_ref(v___y_2005_);
    lean_dec(v___y_2004_);
    lean_dec_ref(v___y_2003_);
    lean_dec(v___y_2002_);
    lean_dec_ref(v_info_1995_);
    lean_dec(v_upperBound_1994_);
    lean_dec_ref(v_e_1993_);
    lean_dec(v___x_1992_);
    return v_res_2010_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(
    mut v_a_2011_: u64,
    mut v_x_2012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: u64 = 0;
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2012_) == 0 {
                    v___x_2013_ = lean_box(0);
                    return v___x_2013_;
                } else {
                    v_key_2014_ = lean_ctor_get(v_x_2012_, 0);
                    v_value_2015_ = lean_ctor_get(v_x_2012_, 1);
                    v_tail_2016_ = lean_ctor_get(v_x_2012_, 2);
                    v___x_2017_ = lean_unbox_uint64(v_key_2014_);
                    v___x_2018_ = lean_uint64_dec_eq(v___x_2017_, v_a_2011_);
                    if v___x_2018_ == 0 {
                        v_x_2012_ = v_tail_2016_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2015_);
                        v___x_2020_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2020_, 0, v_value_2015_);
                        return v___x_2020_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg___boxed(
    mut v_a_2021_: *mut LeanObject,
    mut v_x_2022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2023_: u64 = 0;
    let mut v_res_2024_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2023_ = lean_unbox_uint64(v_a_2021_);
    lean_dec_ref(v_a_2021_);
    v_res_2024_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_boxed_2023_, v_x_2022_);
    lean_dec(v_x_2022_);
    return v_res_2024_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(
    mut v_m_2025_: *mut LeanObject,
    mut v_a_2026_: u64,
) -> *mut LeanObject {
    let mut v_buckets_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2027_ = lean_ctor_get(v_m_2025_, 1);
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
    mut v_m_2042_: *mut LeanObject,
    mut v_a_2043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2044_: u64 = 0;
    let mut v_res_2045_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2044_ = lean_unbox_uint64(v_a_2043_);
    lean_dec_ref(v_a_2043_);
    v_res_2045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_m_2042_, v_a_boxed_2044_);
    lean_dec_ref(v_m_2042_);
    return v_res_2045_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(
    mut v_k_2046_: u64,
    mut v_____do__lift_2047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keyToExprs_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    v_keyToExprs_2048_ = lean_ctor_get(v_____do__lift_2047_, 1);
    v___x_2049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_keyToExprs_2048_, v_k_2046_);
    return v___x_2049_;
}
pub unsafe fn l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(
    mut v_k_2050_: *mut LeanObject,
    mut v_____do__lift_2051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_boxed_2052_: u64 = 0;
    let mut v_res_2053_: *mut LeanObject = core::ptr::null_mut();
    v_k_boxed_2052_ = lean_unbox_uint64(v_k_2050_);
    lean_dec_ref(v_k_2050_);
    v_res_2053_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(
        v_k_boxed_2052_,
        v_____do__lift_2051_,
    );
    lean_dec_ref(v_____do__lift_2051_);
    return v_res_2053_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(
    mut v_00_u03b2_2054_: *mut LeanObject,
    mut v_m_2055_: *mut LeanObject,
    mut v_a_2056_: u64,
) -> *mut LeanObject {
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    v___x_2057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_m_2055_, v_a_2056_);
    return v___x_2057_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___boxed(
    mut v_00_u03b2_2058_: *mut LeanObject,
    mut v_m_2059_: *mut LeanObject,
    mut v_a_2060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2061_: u64 = 0;
    let mut v_res_2062_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2061_ = lean_unbox_uint64(v_a_2060_);
    lean_dec_ref(v_a_2060_);
    v_res_2062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(v_00_u03b2_2058_, v_m_2059_, v_a_boxed_2061_);
    lean_dec_ref(v_m_2059_);
    return v_res_2062_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0(
    mut v_00_u03b2_2063_: *mut LeanObject,
    mut v_a_2064_: u64,
    mut v_x_2065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    v___x_2066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_2064_, v_x_2065_);
    return v___x_2066_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___boxed(
    mut v_00_u03b2_2067_: *mut LeanObject,
    mut v_a_2068_: *mut LeanObject,
    mut v_x_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2070_: u64 = 0;
    let mut v_res_2071_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2070_ = lean_unbox_uint64(v_a_2068_);
    lean_dec_ref(v_a_2068_);
    v_res_2071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0(v_00_u03b2_2067_, v_a_boxed_2070_, v_x_2069_);
    lean_dec(v_x_2069_);
    return v_res_2071_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(
    mut v_a_2072_: u64,
    mut v_b_2073_: *mut LeanObject,
    mut v_x_2074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2081_: u64 = 0;
    let mut v___x_2082_: u8 = 0;
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2074_) == 0 {
                    lean_dec(v_b_2073_);
                    return v_x_2074_;
                } else {
                    v_key_2075_ = lean_ctor_get(v_x_2074_, 0);
                    v_value_2076_ = lean_ctor_get(v_x_2074_, 1);
                    v_tail_2077_ = lean_ctor_get(v_x_2074_, 2);
                    v_isSharedCheck_2091_ = (!lean_is_exclusive(v_x_2074_)) as u8;
                    if v_isSharedCheck_2091_ == 0 {
                        v___x_2079_ = v_x_2074_;
                        v_isShared_2080_ = v_isSharedCheck_2091_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2077_);
                        lean_inc(v_value_2076_);
                        lean_inc(v_key_2075_);
                        lean_dec(v_x_2074_);
                        v___x_2079_ = lean_box(0);
                        v_isShared_2080_ = v_isSharedCheck_2091_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2081_ = lean_unbox_uint64(v_key_2075_);
                v___x_2082_ = lean_uint64_dec_eq(v___x_2081_, v_a_2072_);
                if v___x_2082_ == 0 {
                    v___x_2083_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_2072_, v_b_2073_, v_tail_2077_);
                    if v_isShared_2080_ == 0 {
                        lean_ctor_set(v___x_2079_, 2, v___x_2083_);
                        v___x_2085_ = v___x_2079_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_key_2075_);
                        lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_value_2076_);
                        lean_ctor_set(v_reuseFailAlloc_2086_, 2, v___x_2083_);
                        v___x_2085_ = v_reuseFailAlloc_2086_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2076_);
                    lean_dec(v_key_2075_);
                    v___x_2087_ = lean_box_uint64(v_a_2072_);
                    if v_isShared_2080_ == 0 {
                        lean_ctor_set(v___x_2079_, 1, v_b_2073_);
                        lean_ctor_set(v___x_2079_, 0, v___x_2087_);
                        v___x_2089_ = v___x_2079_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
                        lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_b_2073_);
                        lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_tail_2077_);
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
    mut v_a_2092_: *mut LeanObject,
    mut v_b_2093_: *mut LeanObject,
    mut v_x_2094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2095_: u64 = 0;
    let mut v_res_2096_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2095_ = lean_unbox_uint64(v_a_2092_);
    lean_dec_ref(v_a_2092_);
    v_res_2096_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_boxed_2095_, v_b_2093_, v_x_2094_);
    return v_res_2096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_2097_: *mut LeanObject,
    mut v_x_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2098_) == 0 {
                    return v_x_2097_;
                } else {
                    v_key_2099_ = lean_ctor_get(v_x_2098_, 0);
                    v_value_2100_ = lean_ctor_get(v_x_2098_, 1);
                    v_tail_2101_ = lean_ctor_get(v_x_2098_, 2);
                    v_isSharedCheck_2125_ = (!lean_is_exclusive(v_x_2098_)) as u8;
                    if v_isSharedCheck_2125_ == 0 {
                        v___x_2103_ = v_x_2098_;
                        v_isShared_2104_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2101_);
                        lean_inc(v_value_2100_);
                        lean_inc(v_key_2099_);
                        lean_dec(v_x_2098_);
                        v___x_2103_ = lean_box(0);
                        v_isShared_2104_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2105_ = lean_array_get_size(v_x_2097_);
                v___x_2106_ = 32u64;
                v___x_2107_ = lean_unbox_uint64(v_key_2099_);
                v___x_2108_ = lean_uint64_shift_right(v___x_2107_, v___x_2106_);
                v___x_2109_ = lean_unbox_uint64(v_key_2099_);
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
                lean_inc(v___x_2119_);
                if v_isShared_2104_ == 0 {
                    lean_ctor_set(v___x_2103_, 2, v___x_2119_);
                    v___x_2121_ = v___x_2103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_key_2099_);
                    lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_value_2100_);
                    lean_ctor_set(v_reuseFailAlloc_2124_, 2, v___x_2119_);
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
    mut v_i_2126_: *mut LeanObject,
    mut v_source_2127_: *mut LeanObject,
    mut v_target_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u8 = 0;
    let mut v_es_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2129_ = lean_array_get_size(v_source_2127_);
                v___x_2130_ = lean_nat_dec_lt(v_i_2126_, v___x_2129_);
                if v___x_2130_ == 0 {
                    lean_dec_ref(v_source_2127_);
                    lean_dec(v_i_2126_);
                    return v_target_2128_;
                } else {
                    v_es_2131_ = lean_array_fget(v_source_2127_, v_i_2126_);
                    v___x_2132_ = lean_box(0);
                    v_source_2133_ = lean_array_fset(v_source_2127_, v_i_2126_, v___x_2132_);
                    v_target_2134_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(v_target_2128_, v_es_2131_);
                    v___x_2135_ = lean_unsigned_to_nat(1);
                    v___x_2136_ = lean_nat_add(v_i_2126_, v___x_2135_);
                    lean_dec(v_i_2126_);
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
    mut v_data_2138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    v___x_2139_ = lean_array_get_size(v_data_2138_);
    v___x_2140_ = lean_unsigned_to_nat(2);
    v_nbuckets_2141_ = lean_nat_mul(v___x_2139_, v___x_2140_);
    v___x_2142_ = lean_unsigned_to_nat(0);
    v___x_2143_ = lean_box(0);
    v___x_2144_ = lean_mk_array(v_nbuckets_2141_, v___x_2143_);
    v___x_2145_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(v___x_2142_, v_data_2138_, v___x_2144_);
    return v___x_2145_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(
    mut v_a_2146_: u64,
    mut v_x_2147_: *mut LeanObject,
) -> u8 {
    let mut v___x_2148_: u8 = 0;
    let mut v_key_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u64 = 0;
    let mut v___x_2152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2147_) == 0 {
                    v___x_2148_ = 0;
                    return v___x_2148_;
                } else {
                    v_key_2149_ = lean_ctor_get(v_x_2147_, 0);
                    v_tail_2150_ = lean_ctor_get(v_x_2147_, 2);
                    v___x_2151_ = lean_unbox_uint64(v_key_2149_);
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
    mut v_a_2154_: *mut LeanObject,
    mut v_x_2155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2156_: u64 = 0;
    let mut v_res_2157_: u8 = 0;
    let mut v_r_2158_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2156_ = lean_unbox_uint64(v_a_2154_);
    lean_dec_ref(v_a_2154_);
    v_res_2157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_boxed_2156_, v_x_2155_);
    lean_dec(v_x_2155_);
    v_r_2158_ = lean_box((v_res_2157_) as usize);
    return v_r_2158_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(
    mut v_m_2159_: *mut LeanObject,
    mut v_a_2160_: u64,
    mut v_b_2161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2166_: u8 = 0;
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: u8 = 0;
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u8 = 0;
    let mut v_val_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2162_ = lean_ctor_get(v_m_2159_, 0);
                v_buckets_2163_ = lean_ctor_get(v_m_2159_, 1);
                v_isSharedCheck_2206_ = (!lean_is_exclusive(v_m_2159_)) as u8;
                if v_isSharedCheck_2206_ == 0 {
                    v___x_2165_ = v_m_2159_;
                    v_isShared_2166_ = v_isSharedCheck_2206_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2163_);
                    lean_inc(v_size_2162_);
                    lean_dec(v_m_2159_);
                    v___x_2165_ = lean_box(0);
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
                    v___x_2181_ = lean_unsigned_to_nat(1);
                    v_size_x27_2182_ = lean_nat_add(v_size_2162_, v___x_2181_);
                    lean_dec(v_size_2162_);
                    v___x_2183_ = lean_box_uint64(v_a_2160_);
                    lean_inc(v_bkt_2179_);
                    v___x_2184_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2184_, 0, v___x_2183_);
                    lean_ctor_set(v___x_2184_, 1, v_b_2161_);
                    lean_ctor_set(v___x_2184_, 2, v_bkt_2179_);
                    v_buckets_x27_2185_ =
                        lean_array_uset(v_buckets_2163_, v___x_2178_, v___x_2184_);
                    v___x_2186_ = lean_unsigned_to_nat(4);
                    v___x_2187_ = lean_nat_mul(v_size_x27_2182_, v___x_2186_);
                    v___x_2188_ = lean_unsigned_to_nat(3);
                    v___x_2189_ = lean_nat_div(v___x_2187_, v___x_2188_);
                    lean_dec(v___x_2187_);
                    v___x_2190_ = lean_array_get_size(v_buckets_x27_2185_);
                    v___x_2191_ = lean_nat_dec_le(v___x_2189_, v___x_2190_);
                    lean_dec(v___x_2189_);
                    if v___x_2191_ == 0 {
                        v_val_2192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(v_buckets_x27_2185_);
                        if v_isShared_2166_ == 0 {
                            lean_ctor_set(v___x_2165_, 1, v_val_2192_);
                            lean_ctor_set(v___x_2165_, 0, v_size_x27_2182_);
                            v___x_2194_ = v___x_2165_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_size_x27_2182_);
                            lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_val_2192_);
                            v___x_2194_ = v_reuseFailAlloc_2195_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2166_ == 0 {
                            lean_ctor_set(v___x_2165_, 1, v_buckets_x27_2185_);
                            lean_ctor_set(v___x_2165_, 0, v_size_x27_2182_);
                            v___x_2197_ = v___x_2165_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_size_x27_2182_);
                            lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_buckets_x27_2185_);
                            v___x_2197_ = v_reuseFailAlloc_2198_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2179_);
                    v___x_2199_ = lean_box(0);
                    v_buckets_x27_2200_ =
                        lean_array_uset(v_buckets_2163_, v___x_2178_, v___x_2199_);
                    v___x_2201_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_2160_, v_b_2161_, v_bkt_2179_);
                    v___x_2202_ = lean_array_uset(v_buckets_x27_2200_, v___x_2178_, v___x_2201_);
                    if v_isShared_2166_ == 0 {
                        lean_ctor_set(v___x_2165_, 1, v___x_2202_);
                        v___x_2204_ = v___x_2165_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_size_2162_);
                        lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2202_);
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
    mut v_m_2207_: *mut LeanObject,
    mut v_a_2208_: *mut LeanObject,
    mut v_b_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2210_: u64 = 0;
    let mut v_res_2211_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2210_ = lean_unbox_uint64(v_a_2208_);
    lean_dec_ref(v_a_2208_);
    v_res_2211_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_m_2207_, v_a_boxed_2210_, v_b_2209_);
    return v_res_2211_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(
    mut v_e_2215_: *mut LeanObject,
    mut v_as_x27_2216_: *mut LeanObject,
    mut v_b_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
    mut v___y_2219_: *mut LeanObject,
    mut v___y_2220_: *mut LeanObject,
    mut v___y_2221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_a_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2244_: u8 = 0;
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2216_) == 0 {
                    lean_dec_ref(v_e_2215_);
                    v___x_2223_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2223_, 0, v_b_2217_);
                    return v___x_2223_;
                } else {
                    lean_dec_ref(v_b_2217_);
                    v_head_2224_ = lean_ctor_get(v_as_x27_2216_, 0);
                    v_tail_2225_ = lean_ctor_get(v_as_x27_2216_, 1);
                    lean_inc(v_head_2224_);
                    lean_inc_ref(v_e_2215_);
                    v___x_2226_ = l_Lean_Meta_isExprDefEq(
                        v_e_2215_,
                        v_head_2224_,
                        v___y_2218_,
                        v___y_2219_,
                        v___y_2220_,
                        v___y_2221_,
                    );
                    if lean_obj_tag(v___x_2226_) == 0 {
                        v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
                        v_isSharedCheck_2240_ = (!lean_is_exclusive(v___x_2226_)) as u8;
                        if v_isSharedCheck_2240_ == 0 {
                            v___x_2229_ = v___x_2226_;
                            v_isShared_2230_ = v_isSharedCheck_2240_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2227_);
                            lean_dec(v___x_2226_);
                            v___x_2229_ = lean_box(0);
                            v_isShared_2230_ = v_isSharedCheck_2240_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_2215_);
                        v_a_2241_ = lean_ctor_get(v___x_2226_, 0);
                        v_isSharedCheck_2248_ = (!lean_is_exclusive(v___x_2226_)) as u8;
                        if v_isSharedCheck_2248_ == 0 {
                            v___x_2243_ = v___x_2226_;
                            v_isShared_2244_ = v_isSharedCheck_2248_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2241_);
                            lean_dec(v___x_2226_);
                            v___x_2243_ = lean_box(0);
                            v_isShared_2244_ = v_isSharedCheck_2248_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2231_ = lean_box(0);
                v___x_2232_ = (lean_unbox(v_a_2227_) as u8);
                lean_dec(v_a_2227_);
                if v___x_2232_ == 0 {
                    lean_del_object(v___x_2229_);
                    v___x_2233_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0;
                    v_as_x27_2216_ = v_tail_2225_;
                    v_b_2217_ = v___x_2233_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_e_2215_);
                    lean_inc(v_head_2224_);
                    v___x_2235_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2235_, 0, v_head_2224_);
                    v___x_2236_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2236_, 0, v___x_2235_);
                    lean_ctor_set(v___x_2236_, 1, v___x_2231_);
                    if v_isShared_2230_ == 0 {
                        lean_ctor_set(v___x_2229_, 0, v___x_2236_);
                        v___x_2238_ = v___x_2229_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
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
                    v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
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
    mut v_e_2249_: *mut LeanObject,
    mut v_as_x27_2250_: *mut LeanObject,
    mut v_b_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
    mut v___y_2253_: *mut LeanObject,
    mut v___y_2254_: *mut LeanObject,
    mut v___y_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2257_: *mut LeanObject = core::ptr::null_mut();
    v_res_2257_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(
        v_e_2249_,
        v_as_x27_2250_,
        v_b_2251_,
        v___y_2252_,
        v___y_2253_,
        v___y_2254_,
        v___y_2255_,
    );
    lean_dec(v___y_2255_);
    lean_dec_ref(v___y_2254_);
    lean_dec(v___y_2253_);
    lean_dec_ref(v___y_2252_);
    lean_dec(v_as_x27_2250_);
    return v_res_2257_;
}
pub unsafe fn l_Lean_Meta_Canonicalizer_canon(
    mut v_e_2258_: *mut LeanObject,
    mut v_a_2259_: u8,
    mut v_a_2260_: *mut LeanObject,
    mut v_a_2261_: *mut LeanObject,
    mut v_a_2262_: *mut LeanObject,
    mut v_a_2263_: *mut LeanObject,
    mut v_a_2264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2270_: u8 = 0;
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: u64 = 0;
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2296_: u8 = 0;
    let mut v_trackZetaDelta_2297_: u8 = 0;
    let mut v_zetaDeltaSet_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2304_: u8 = 0;
    let mut v_inTypeClassResolution_2305_: u8 = 0;
    let mut v_cacheInferType_2306_: u8 = 0;
    let mut v_config_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: u64 = 0;
    let mut v___x_2310_: u64 = 0;
    let mut v___x_2311_: u64 = 0;
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u64 = 0;
    let mut v___x_2314_: u64 = 0;
    let mut v_key_2315_: u64 = 0;
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v_fst_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2326_: u8 = 0;
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyToExprs_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2332_: u8 = 0;
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u64 = 0;
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2345_: u8 = 0;
    let mut v_val_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2350_: u8 = 0;
    let mut v_unused_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2352_: u8 = 0;
    let mut v_a_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_reuseFailAlloc_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2362_: u8 = 0;
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyToExprs_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2368_: u8 = 0;
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u64 = 0;
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut v_a_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2385_: u8 = 0;
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_2258_);
                v___x_2266_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(
                    v_e_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_,
                );
                if lean_obj_tag(v___x_2266_) == 0 {
                    v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
                    v_isSharedCheck_2381_ = (!lean_is_exclusive(v___x_2266_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v___x_2269_ = v___x_2266_;
                        v_isShared_2270_ = v_isSharedCheck_2381_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2267_);
                        lean_dec(v___x_2266_);
                        v___x_2269_ = lean_box(0);
                        v_isShared_2270_ = v_isSharedCheck_2381_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_2258_);
                    v_a_2382_ = lean_ctor_get(v___x_2266_, 0);
                    v_isSharedCheck_2389_ = (!lean_is_exclusive(v___x_2266_)) as u8;
                    if v_isSharedCheck_2389_ == 0 {
                        v___x_2384_ = v___x_2266_;
                        v_isShared_2385_ = v_isSharedCheck_2389_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_2382_);
                        lean_dec(v___x_2266_);
                        v___x_2384_ = lean_box(0);
                        v_isShared_2385_ = v_isSharedCheck_2389_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2271_ = lean_st_ref_get(v_a_2260_);
                v___x_2272_ = lean_unbox_uint64(v_a_2267_);
                v___x_2273_ =
                    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(
                        v___x_2272_,
                        v___x_2271_,
                    );
                lean_dec(v___x_2271_);
                if lean_obj_tag(v___x_2273_) == 1 {
                    lean_del_object(v___x_2269_);
                    v_val_2274_ = lean_ctor_get(v___x_2273_, 0);
                    lean_inc(v_val_2274_);
                    lean_dec_ref_known(v___x_2273_, 1);
                    v___x_2275_ = l_Lean_Meta_Context_config(v_a_2261_);
                    v_foApprox_2276_ = lean_ctor_get_uint8(v___x_2275_, 0 as u32);
                    v_ctxApprox_2277_ = lean_ctor_get_uint8(v___x_2275_, 1 as u32);
                    v_quasiPatternApprox_2278_ = lean_ctor_get_uint8(v___x_2275_, 2 as u32);
                    v_constApprox_2279_ = lean_ctor_get_uint8(v___x_2275_, 3 as u32);
                    v_isDefEqStuckEx_2280_ = lean_ctor_get_uint8(v___x_2275_, 4 as u32);
                    v_unificationHints_2281_ = lean_ctor_get_uint8(v___x_2275_, 5 as u32);
                    v_proofIrrelevance_2282_ = lean_ctor_get_uint8(v___x_2275_, 6 as u32);
                    v_assignSyntheticOpaque_2283_ = lean_ctor_get_uint8(v___x_2275_, 7 as u32);
                    v_offsetCnstrs_2284_ = lean_ctor_get_uint8(v___x_2275_, 8 as u32);
                    v_etaStruct_2285_ = lean_ctor_get_uint8(v___x_2275_, 10 as u32);
                    v_univApprox_2286_ = lean_ctor_get_uint8(v___x_2275_, 11 as u32);
                    v_iota_2287_ = lean_ctor_get_uint8(v___x_2275_, 12 as u32);
                    v_beta_2288_ = lean_ctor_get_uint8(v___x_2275_, 13 as u32);
                    v_proj_2289_ = lean_ctor_get_uint8(v___x_2275_, 14 as u32);
                    v_zeta_2290_ = lean_ctor_get_uint8(v___x_2275_, 15 as u32);
                    v_zetaDelta_2291_ = lean_ctor_get_uint8(v___x_2275_, 16 as u32);
                    v_zetaUnused_2292_ = lean_ctor_get_uint8(v___x_2275_, 17 as u32);
                    v_zetaHave_2293_ = lean_ctor_get_uint8(v___x_2275_, 18 as u32);
                    v_isSharedCheck_2362_ = (!lean_is_exclusive(v___x_2275_)) as u8;
                    if v_isSharedCheck_2362_ == 0 {
                        v___x_2295_ = v___x_2275_;
                        v_isShared_2296_ = v_isSharedCheck_2362_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_2275_);
                        v___x_2295_ = lean_box(0);
                        v_isShared_2296_ = v_isSharedCheck_2362_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2273_);
                    v___x_2363_ = lean_st_ref_take(v_a_2260_);
                    v_cache_2364_ = lean_ctor_get(v___x_2363_, 0);
                    v_keyToExprs_2365_ = lean_ctor_get(v___x_2363_, 1);
                    v_isSharedCheck_2380_ = (!lean_is_exclusive(v___x_2363_)) as u8;
                    if v_isSharedCheck_2380_ == 0 {
                        v___x_2367_ = v___x_2363_;
                        v_isShared_2368_ = v_isSharedCheck_2380_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_keyToExprs_2365_);
                        lean_inc(v_cache_2364_);
                        lean_dec(v___x_2363_);
                        v___x_2367_ = lean_box(0);
                        v_isShared_2368_ = v_isSharedCheck_2380_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v_trackZetaDelta_2297_ = lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2298_ = lean_ctor_get(v_a_2261_, 1);
                v_lctx_2299_ = lean_ctor_get(v_a_2261_, 2);
                v_localInstances_2300_ = lean_ctor_get(v_a_2261_, 3);
                v_defEqCtx_x3f_2301_ = lean_ctor_get(v_a_2261_, 4);
                v_synthPendingDepth_2302_ = lean_ctor_get(v_a_2261_, 5);
                v_canUnfold_x3f_2303_ = lean_ctor_get(v_a_2261_, 6);
                v_univApprox_2304_ = lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2305_ = lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2306_ = lean_ctor_get_uint8(
                    v_a_2261_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2296_ == 0 {
                    v_config_2308_ = v___x_2295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 0 as u32, v_foApprox_2276_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 1 as u32, v_ctxApprox_2277_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        2 as u32,
                        v_quasiPatternApprox_2278_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 3 as u32, v_constApprox_2279_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 4 as u32, v_isDefEqStuckEx_2280_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 5 as u32, v_unificationHints_2281_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 6 as u32, v_proofIrrelevance_2282_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2361_,
                        7 as u32,
                        v_assignSyntheticOpaque_2283_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 8 as u32, v_offsetCnstrs_2284_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 10 as u32, v_etaStruct_2285_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 11 as u32, v_univApprox_2286_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 12 as u32, v_iota_2287_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 13 as u32, v_beta_2288_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 14 as u32, v_proj_2289_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 15 as u32, v_zeta_2290_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 16 as u32, v_zetaDelta_2291_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 17 as u32, v_zetaUnused_2292_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2361_, 18 as u32, v_zetaHave_2293_);
                    v_config_2308_ = v_reuseFailAlloc_2361_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(v_config_2308_, 9 as u32, v_a_2259_);
                v___x_2309_ = l_Lean_Meta_Context_configKey(v_a_2261_);
                v___x_2310_ = 3u64;
                v___x_2311_ = lean_uint64_shift_right(v___x_2309_, v___x_2310_);
                v___x_2312_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0;
                v___x_2313_ = lean_uint64_shift_left(v___x_2311_, v___x_2310_);
                v___x_2314_ = l_Lean_Meta_TransparencyMode_toUInt64(v_a_2259_);
                v_key_2315_ = lean_uint64_lor(v___x_2313_, v___x_2314_);
                v___x_2316_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_2316_, 0, v_config_2308_);
                lean_ctor_set_uint64(
                    v___x_2316_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_2315_,
                );
                lean_inc(v_canUnfold_x3f_2303_);
                lean_inc(v_synthPendingDepth_2302_);
                lean_inc(v_defEqCtx_x3f_2301_);
                lean_inc_ref(v_localInstances_2300_);
                lean_inc_ref(v_lctx_2299_);
                lean_inc(v_zetaDeltaSet_2298_);
                v___x_2317_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_2317_, 0, v___x_2316_);
                lean_ctor_set(v___x_2317_, 1, v_zetaDeltaSet_2298_);
                lean_ctor_set(v___x_2317_, 2, v_lctx_2299_);
                lean_ctor_set(v___x_2317_, 3, v_localInstances_2300_);
                lean_ctor_set(v___x_2317_, 4, v_defEqCtx_x3f_2301_);
                lean_ctor_set(v___x_2317_, 5, v_synthPendingDepth_2302_);
                lean_ctor_set(v___x_2317_, 6, v_canUnfold_x3f_2303_);
                lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2297_,
                );
                lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2304_,
                );
                lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2305_,
                );
                lean_ctor_set_uint8(
                    v___x_2317_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2306_,
                );
                lean_inc_ref(v_e_2258_);
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
                lean_dec_ref_known(v___x_2317_, 7);
                if lean_obj_tag(v___x_2318_) == 0 {
                    v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
                    v_isSharedCheck_2352_ = (!lean_is_exclusive(v___x_2318_)) as u8;
                    if v_isSharedCheck_2352_ == 0 {
                        v___x_2321_ = v___x_2318_;
                        v_isShared_2322_ = v_isSharedCheck_2352_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2319_);
                        lean_dec(v___x_2318_);
                        v___x_2321_ = lean_box(0);
                        v_isShared_2322_ = v_isSharedCheck_2352_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_val_2274_);
                    lean_dec(v_a_2267_);
                    lean_dec_ref(v_e_2258_);
                    v_a_2353_ = lean_ctor_get(v___x_2318_, 0);
                    v_isSharedCheck_2360_ = (!lean_is_exclusive(v___x_2318_)) as u8;
                    if v_isSharedCheck_2360_ == 0 {
                        v___x_2355_ = v___x_2318_;
                        v_isShared_2356_ = v_isSharedCheck_2360_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2353_);
                        lean_dec(v___x_2318_);
                        v___x_2355_ = lean_box(0);
                        v_isShared_2356_ = v_isSharedCheck_2360_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_2323_ = lean_ctor_get(v_a_2319_, 0);
                v_isSharedCheck_2350_ = (!lean_is_exclusive(v_a_2319_)) as u8;
                if v_isSharedCheck_2350_ == 0 {
                    v_unused_2351_ = lean_ctor_get(v_a_2319_, 1);
                    lean_dec(v_unused_2351_);
                    v___x_2325_ = v_a_2319_;
                    v_isShared_2326_ = v_isSharedCheck_2350_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_fst_2323_);
                    lean_dec(v_a_2319_);
                    v___x_2325_ = lean_box(0);
                    v_isShared_2326_ = v_isSharedCheck_2350_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if lean_obj_tag(v_fst_2323_) == 0 {
                    v___x_2327_ = lean_st_ref_take(v_a_2260_);
                    v_cache_2328_ = lean_ctor_get(v___x_2327_, 0);
                    v_keyToExprs_2329_ = lean_ctor_get(v___x_2327_, 1);
                    v_isSharedCheck_2345_ = (!lean_is_exclusive(v___x_2327_)) as u8;
                    if v_isSharedCheck_2345_ == 0 {
                        v___x_2331_ = v___x_2327_;
                        v_isShared_2332_ = v_isSharedCheck_2345_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_keyToExprs_2329_);
                        lean_inc(v_cache_2328_);
                        lean_dec(v___x_2327_);
                        v___x_2331_ = lean_box(0);
                        v_isShared_2332_ = v_isSharedCheck_2345_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2325_);
                    lean_dec(v_val_2274_);
                    lean_dec(v_a_2267_);
                    lean_dec_ref(v_e_2258_);
                    v_val_2346_ = lean_ctor_get(v_fst_2323_, 0);
                    lean_inc(v_val_2346_);
                    lean_dec_ref_known(v_fst_2323_, 1);
                    if v_isShared_2322_ == 0 {
                        lean_ctor_set(v___x_2321_, 0, v_val_2346_);
                        v___x_2348_ = v___x_2321_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_val_2346_);
                        v___x_2348_ = v_reuseFailAlloc_2349_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                lean_inc_ref(v_e_2258_);
                if v_isShared_2326_ == 0 {
                    lean_ctor_set_tag(v___x_2325_, 1);
                    lean_ctor_set(v___x_2325_, 1, v_val_2274_);
                    lean_ctor_set(v___x_2325_, 0, v_e_2258_);
                    v___x_2334_ = v___x_2325_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_e_2258_);
                    lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_val_2274_);
                    v___x_2334_ = v_reuseFailAlloc_2344_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2335_ = lean_unbox_uint64(v_a_2267_);
                lean_dec(v_a_2267_);
                v___x_2336_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_keyToExprs_2329_, v___x_2335_, v___x_2334_);
                if v_isShared_2332_ == 0 {
                    lean_ctor_set(v___x_2331_, 1, v___x_2336_);
                    v___x_2338_ = v___x_2331_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_cache_2328_);
                    lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2336_);
                    v___x_2338_ = v_reuseFailAlloc_2343_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2339_ = lean_st_ref_set(v_a_2260_, v___x_2338_);
                if v_isShared_2322_ == 0 {
                    lean_ctor_set(v___x_2321_, 0, v_e_2258_);
                    v___x_2341_ = v___x_2321_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_e_2258_);
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
                    v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
                    v___x_2358_ = v_reuseFailAlloc_2359_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2358_;
            }
            13 => {
                v___x_2369_ = lean_box(0);
                lean_inc_ref(v_e_2258_);
                v___x_2370_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2370_, 0, v_e_2258_);
                lean_ctor_set(v___x_2370_, 1, v___x_2369_);
                v___x_2371_ = lean_unbox_uint64(v_a_2267_);
                lean_dec(v_a_2267_);
                v___x_2372_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_keyToExprs_2365_, v___x_2371_, v___x_2370_);
                if v_isShared_2368_ == 0 {
                    lean_ctor_set(v___x_2367_, 1, v___x_2372_);
                    v___x_2374_ = v___x_2367_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_cache_2364_);
                    lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2372_);
                    v___x_2374_ = v_reuseFailAlloc_2379_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2375_ = lean_st_ref_set(v_a_2260_, v___x_2374_);
                if v_isShared_2270_ == 0 {
                    lean_ctor_set(v___x_2269_, 0, v_e_2258_);
                    v___x_2377_ = v___x_2269_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_e_2258_);
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
                    v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
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
    mut v_e_2390_: *mut LeanObject,
    mut v_a_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
    mut v_a_2393_: *mut LeanObject,
    mut v_a_2394_: *mut LeanObject,
    mut v_a_2395_: *mut LeanObject,
    mut v_a_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2398_: u8 = 0;
    let mut v_res_2399_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2398_ = (lean_unbox(v_a_2391_) as u8);
    v_res_2399_ = l_Lean_Meta_Canonicalizer_canon(
        v_e_2390_,
        v_a_boxed_2398_,
        v_a_2392_,
        v_a_2393_,
        v_a_2394_,
        v_a_2395_,
        v_a_2396_,
    );
    lean_dec(v_a_2396_);
    lean_dec_ref(v_a_2395_);
    lean_dec(v_a_2394_);
    lean_dec_ref(v_a_2393_);
    lean_dec(v_a_2392_);
    return v_res_2399_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0(
    mut v_e_2400_: *mut LeanObject,
    mut v_as_2401_: *mut LeanObject,
    mut v_as_x27_2402_: *mut LeanObject,
    mut v_b_2403_: *mut LeanObject,
    mut v_a_2404_: *mut LeanObject,
    mut v___y_2405_: u8,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
    mut v___y_2408_: *mut LeanObject,
    mut v___y_2409_: *mut LeanObject,
    mut v___y_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_e_2413_: *mut LeanObject,
    mut v_as_2414_: *mut LeanObject,
    mut v_as_x27_2415_: *mut LeanObject,
    mut v_b_2416_: *mut LeanObject,
    mut v_a_2417_: *mut LeanObject,
    mut v___y_2418_: *mut LeanObject,
    mut v___y_2419_: *mut LeanObject,
    mut v___y_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_10919__boxed_2425_: u8 = 0;
    let mut v_res_2426_: *mut LeanObject = core::ptr::null_mut();
    v___y_10919__boxed_2425_ = (lean_unbox(v___y_2418_) as u8);
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
    lean_dec(v___y_2423_);
    lean_dec_ref(v___y_2422_);
    lean_dec(v___y_2421_);
    lean_dec_ref(v___y_2420_);
    lean_dec(v___y_2419_);
    lean_dec(v_as_x27_2415_);
    lean_dec(v_as_2414_);
    return v_res_2426_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1(
    mut v_00_u03b2_2427_: *mut LeanObject,
    mut v_m_2428_: *mut LeanObject,
    mut v_a_2429_: u64,
    mut v_b_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    v___x_2431_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_m_2428_, v_a_2429_, v_b_2430_);
    return v___x_2431_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___boxed(
    mut v_00_u03b2_2432_: *mut LeanObject,
    mut v_m_2433_: *mut LeanObject,
    mut v_a_2434_: *mut LeanObject,
    mut v_b_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2436_: u64 = 0;
    let mut v_res_2437_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2436_ = lean_unbox_uint64(v_a_2434_);
    lean_dec_ref(v_a_2434_);
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
    mut v_00_u03b2_2438_: *mut LeanObject,
    mut v_a_2439_: u64,
    mut v_x_2440_: *mut LeanObject,
) -> u8 {
    let mut v___x_2441_: u8 = 0;
    v___x_2441_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_2439_, v_x_2440_);
    return v___x_2441_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___boxed(
    mut v_00_u03b2_2442_: *mut LeanObject,
    mut v_a_2443_: *mut LeanObject,
    mut v_x_2444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2445_: u64 = 0;
    let mut v_res_2446_: u8 = 0;
    let mut v_r_2447_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2445_ = lean_unbox_uint64(v_a_2443_);
    lean_dec_ref(v_a_2443_);
    v_res_2446_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1(v_00_u03b2_2442_, v_a_boxed_2445_, v_x_2444_);
    lean_dec(v_x_2444_);
    v_r_2447_ = lean_box((v_res_2446_) as usize);
    return v_r_2447_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2(
    mut v_00_u03b2_2448_: *mut LeanObject,
    mut v_data_2449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    v___x_2450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(v_data_2449_);
    return v___x_2450_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3(
    mut v_00_u03b2_2451_: *mut LeanObject,
    mut v_a_2452_: u64,
    mut v_b_2453_: *mut LeanObject,
    mut v_x_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    v___x_2455_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_2452_, v_b_2453_, v_x_2454_);
    return v___x_2455_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___boxed(
    mut v_00_u03b2_2456_: *mut LeanObject,
    mut v_a_2457_: *mut LeanObject,
    mut v_b_2458_: *mut LeanObject,
    mut v_x_2459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2460_: u64 = 0;
    let mut v_res_2461_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2460_ = lean_unbox_uint64(v_a_2457_);
    lean_dec_ref(v_a_2457_);
    v_res_2461_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3(v_00_u03b2_2456_, v_a_boxed_2460_, v_b_2458_, v_x_2459_);
    return v_res_2461_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2462_: *mut LeanObject,
    mut v_i_2463_: *mut LeanObject,
    mut v_source_2464_: *mut LeanObject,
    mut v_target_2465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    v___x_2466_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(v_i_2463_, v_source_2464_, v_target_2465_);
    return v___x_2466_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2467_: *mut LeanObject,
    mut v_x_2468_: *mut LeanObject,
    mut v_x_2469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    v___x_2470_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2468_, v_x_2469_);
    return v___x_2470_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Canonicalizer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_ShareCommon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default =
        _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default();
    lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default);
    l_Lean_Meta_Canonicalizer_instInhabitedExprVisited =
        _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited();
    lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited);
    l_Lean_Meta_Canonicalizer_instInhabitedState =
        _init_l_Lean_Meta_Canonicalizer_instInhabitedState();
    lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState);
    l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1 = _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1();
    lean_mark_persistent(
        l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1,
    );
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Canonicalizer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Canonicalizer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_ShareCommon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Canonicalizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Canonicalizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Canonicalizer(builtin);
}
