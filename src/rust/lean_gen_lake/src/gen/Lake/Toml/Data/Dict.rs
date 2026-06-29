// Lean compiler output
// Module: Lake.Toml.Data.Dict
// Imports: Lean.Data.NameMap.Basic Init.Data.Nat.Fold
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_isEqvAux___redArg,
};
use crate::r#gen::Init::Data::Nat::Fold::{
    initialize_Init_Data_Nat_Fold, runtime_initialize_Init_Data_Nat_Fold,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    initialize_Lean_Data_NameMap_Basic, runtime_initialize_Lean_Data_NameMap_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
pub static l_Lake_Toml_instInhabitedRBDict_default___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_Toml_instInhabitedRBDict_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedRBDict_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_instInhabitedRBDict_default___closed__1_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_instInhabitedRBDict_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_Toml_instInhabitedRBDict_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedRBDict_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_empty___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_Toml_RBDict_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_empty___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_empty___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_RBDict_empty___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_RBDict_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_empty___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_RBDict_map___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_RBDict_map___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_RBDict_map___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_Toml_instInhabitedRBDict_default(
    mut v_00_u03b1_1218_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1219_: *mut crate::leanh::LeanObject,
    mut v_cmp_1220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = l_Lake_Toml_instInhabitedRBDict_default___closed__1;
    return v___x_1221_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict_default___boxed(
    mut v_00_u03b1_1222_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1223_: *mut crate::leanh::LeanObject,
    mut v_cmp_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1225_ =
        l_Lake_Toml_instInhabitedRBDict_default(v_00_u03b1_1222_, v_00_u03b2_1223_, v_cmp_1224_);
    crate::leanh::lean_dec_ref(v_cmp_1224_);
    return v_res_1225_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict___redArg(
    mut v_a_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1227_ = l_Lake_Toml_instInhabitedRBDict_default(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_a_1226_,
    );
    return v___x_1227_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict___redArg___boxed(
    mut v_a_1228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Lake_Toml_instInhabitedRBDict___redArg(v_a_1228_);
    crate::leanh::lean_dec_ref(v_a_1228_);
    return v_res_1229_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict(
    mut v_a_1230_: *mut crate::leanh::LeanObject,
    mut v_a_1231_: *mut crate::leanh::LeanObject,
    mut v_a_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ = l_Lake_Toml_instInhabitedRBDict_default(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_a_1232_,
    );
    return v___x_1233_;
}
pub unsafe fn l_Lake_Toml_instInhabitedRBDict___boxed(
    mut v_a_1234_: *mut crate::leanh::LeanObject,
    mut v_a_1235_: *mut crate::leanh::LeanObject,
    mut v_a_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l_Lake_Toml_instInhabitedRBDict(v_a_1234_, v_a_1235_, v_a_1236_);
    crate::leanh::lean_dec_ref(v_a_1236_);
    return v_res_1237_;
}
pub unsafe fn l_Lake_Toml_RBDict_empty(
    mut v_00_u03b1_1243_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1244_: *mut crate::leanh::LeanObject,
    mut v_cmp_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lake_Toml_RBDict_empty___closed__1;
    return v___x_1246_;
}
pub unsafe fn l_Lake_Toml_RBDict_empty___boxed(
    mut v_00_u03b1_1247_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1248_: *mut crate::leanh::LeanObject,
    mut v_cmp_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1250_ = l_Lake_Toml_RBDict_empty(v_00_u03b1_1247_, v_00_u03b2_1248_, v_cmp_1249_);
    crate::leanh::lean_dec_ref(v_cmp_1249_);
    return v_res_1250_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection___redArg(
    mut v_cmp_1251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Lake_Toml_RBDict_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_cmp_1251_,
    );
    return v___x_1252_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection___redArg___boxed(
    mut v_cmp_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_Lake_Toml_RBDict_instEmptyCollection___redArg(v_cmp_1253_);
    crate::leanh::lean_dec_ref(v_cmp_1253_);
    return v_res_1254_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection(
    mut v_00_u03b1_1255_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1256_: *mut crate::leanh::LeanObject,
    mut v_cmp_1257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1258_ = l_Lake_Toml_RBDict_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_cmp_1257_,
    );
    return v___x_1258_;
}
pub unsafe fn l_Lake_Toml_RBDict_instEmptyCollection___boxed(
    mut v_00_u03b1_1259_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1260_: *mut crate::leanh::LeanObject,
    mut v_cmp_1261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1262_ =
        l_Lake_Toml_RBDict_instEmptyCollection(v_00_u03b1_1259_, v_00_u03b2_1260_, v_cmp_1261_);
    crate::leanh::lean_dec_ref(v_cmp_1261_);
    return v_res_1262_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty___redArg(
    mut v_capacity_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1264_ = lean_mk_empty_array_with_capacity(v_capacity_1263_);
    v___x_1265_ = crate::leanh::lean_box(1);
    v___x_1266_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1266_, 0, v___x_1264_);
    crate::leanh::lean_ctor_set(v___x_1266_, 1, v___x_1265_);
    return v___x_1266_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty___redArg___boxed(
    mut v_capacity_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1268_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_1267_);
    crate::leanh::lean_dec(v_capacity_1267_);
    return v_res_1268_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty(
    mut v_00_u03b1_1269_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1270_: *mut crate::leanh::LeanObject,
    mut v_cmp_1271_: *mut crate::leanh::LeanObject,
    mut v_capacity_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1273_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Lake_Toml_RBDict_mkEmpty___boxed(
    mut v_00_u03b1_1274_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1275_: *mut crate::leanh::LeanObject,
    mut v_cmp_1276_: *mut crate::leanh::LeanObject,
    mut v_capacity_1277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1278_ = l_Lake_Toml_RBDict_mkEmpty(
        v_00_u03b1_1274_,
        v_00_u03b2_1275_,
        v_cmp_1276_,
        v_capacity_1277_,
    );
    crate::leanh::lean_dec(v_capacity_1277_);
    crate::leanh::lean_dec_ref(v_cmp_1276_);
    return v_res_1278_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(
    mut v_cmp_1279_: *mut crate::leanh::LeanObject,
    mut v_k_1280_: *mut crate::leanh::LeanObject,
    mut v_v_1281_: *mut crate::leanh::LeanObject,
    mut v_t_1282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: u8 = 0;
    let mut v_impl_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: u8 = 0;
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1311_: u8 = 0;
    let mut v_size_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1323_: u8 = 0;
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1349_: u8 = 0;
    let mut v_unused_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1363_: u8 = 0;
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1367_: u8 = 0;
    let mut v_unused_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut v_unused_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1386_: u8 = 0;
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut v_unused_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v_k_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut v_unused_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut v_unused_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v_size_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_unused_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1501_: u8 = 0;
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1505_: u8 = 0;
    let mut v_unused_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_unused_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v_k_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1540_: u8 = 0;
    let mut v_unused_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut v_unused_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1552_: u8 = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_unused_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1282_) == 0 {
                    v_size_1283_ = crate::leanh::lean_ctor_get(v_t_1282_, 0);
                    v_k_1284_ = crate::leanh::lean_ctor_get(v_t_1282_, 1);
                    v_v_1285_ = crate::leanh::lean_ctor_get(v_t_1282_, 2);
                    v_l_1286_ = crate::leanh::lean_ctor_get(v_t_1282_, 3);
                    v_r_1287_ = crate::leanh::lean_ctor_get(v_t_1282_, 4);
                    v_isSharedCheck_1568_ = (!crate::leanh::lean_is_exclusive(v_t_1282_)) as u8;
                    if v_isSharedCheck_1568_ == 0 {
                        v___x_1289_ = v_t_1282_;
                        v_isShared_1290_ = v_isSharedCheck_1568_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1287_);
                        crate::leanh::lean_inc(v_l_1286_);
                        crate::leanh::lean_inc(v_v_1285_);
                        crate::leanh::lean_inc(v_k_1284_);
                        crate::leanh::lean_inc(v_size_1283_);
                        crate::leanh::lean_dec(v_t_1282_);
                        v___x_1289_ = crate::leanh::lean_box(0);
                        v_isShared_1290_ = v_isSharedCheck_1568_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_cmp_1279_);
                    v___x_1569_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1570_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1570_, 0, v___x_1569_);
                    crate::leanh::lean_ctor_set(v___x_1570_, 1, v_k_1280_);
                    crate::leanh::lean_ctor_set(v___x_1570_, 2, v_v_1281_);
                    crate::leanh::lean_ctor_set(v___x_1570_, 3, v_t_1282_);
                    crate::leanh::lean_ctor_set(v___x_1570_, 4, v_t_1282_);
                    return v___x_1570_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_cmp_1279_);
                crate::leanh::lean_inc(v_k_1284_);
                crate::leanh::lean_inc(v_k_1280_);
                v___x_1291_ = crate::leanh::lean_apply_2(v_cmp_1279_, v_k_1280_, v_k_1284_);
                v___x_1292_ = (crate::leanh::lean_unbox(v___x_1291_) as u8);
                match v___x_1292_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_1283_);
                        v_impl_1293_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_1279_, v_k_1280_, v_v_1281_, v_l_1286_);
                        v___x_1294_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_1287_) == 0 {
                            v_size_1295_ = crate::leanh::lean_ctor_get(v_r_1287_, 0);
                            v_size_1296_ = crate::leanh::lean_ctor_get(v_impl_1293_, 0);
                            crate::leanh::lean_inc(v_size_1296_);
                            v_k_1297_ = crate::leanh::lean_ctor_get(v_impl_1293_, 1);
                            crate::leanh::lean_inc(v_k_1297_);
                            v_v_1298_ = crate::leanh::lean_ctor_get(v_impl_1293_, 2);
                            crate::leanh::lean_inc(v_v_1298_);
                            v_l_1299_ = crate::leanh::lean_ctor_get(v_impl_1293_, 3);
                            crate::leanh::lean_inc(v_l_1299_);
                            v_r_1300_ = crate::leanh::lean_ctor_get(v_impl_1293_, 4);
                            crate::leanh::lean_inc(v_r_1300_);
                            v___x_1301_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1302_ = lean_nat_mul(v___x_1301_, v_size_1295_);
                            v___x_1303_ = lean_nat_dec_lt(v___x_1302_, v_size_1296_);
                            crate::leanh::lean_dec(v___x_1302_);
                            if v___x_1303_ == 0 {
                                crate::leanh::lean_dec(v_r_1300_);
                                crate::leanh::lean_dec(v_l_1299_);
                                crate::leanh::lean_dec(v_v_1298_);
                                crate::leanh::lean_dec(v_k_1297_);
                                v___x_1304_ = lean_nat_add(v___x_1294_, v_size_1296_);
                                crate::leanh::lean_dec(v_size_1296_);
                                v___x_1305_ = lean_nat_add(v___x_1304_, v_size_1295_);
                                crate::leanh::lean_dec(v___x_1304_);
                                if v_isShared_1290_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1289_, 3, v_impl_1293_);
                                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1305_);
                                    v___x_1307_ = v___x_1289_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1308_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1308_,
                                        0,
                                        v___x_1305_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1308_,
                                        1,
                                        v_k_1284_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1308_,
                                        2,
                                        v_v_1285_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1308_,
                                        3,
                                        v_impl_1293_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1308_,
                                        4,
                                        v_r_1287_,
                                    );
                                    v___x_1307_ = v_reuseFailAlloc_1308_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1374_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1293_)) as u8;
                                if v_isSharedCheck_1374_ == 0 {
                                    v_unused_1375_ = crate::leanh::lean_ctor_get(v_impl_1293_, 4);
                                    crate::leanh::lean_dec(v_unused_1375_);
                                    v_unused_1376_ = crate::leanh::lean_ctor_get(v_impl_1293_, 3);
                                    crate::leanh::lean_dec(v_unused_1376_);
                                    v_unused_1377_ = crate::leanh::lean_ctor_get(v_impl_1293_, 2);
                                    crate::leanh::lean_dec(v_unused_1377_);
                                    v_unused_1378_ = crate::leanh::lean_ctor_get(v_impl_1293_, 1);
                                    crate::leanh::lean_dec(v_unused_1378_);
                                    v_unused_1379_ = crate::leanh::lean_ctor_get(v_impl_1293_, 0);
                                    crate::leanh::lean_dec(v_unused_1379_);
                                    v___x_1310_ = v_impl_1293_;
                                    v_isShared_1311_ = v_isSharedCheck_1374_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1293_);
                                    v___x_1310_ = crate::leanh::lean_box(0);
                                    v_isShared_1311_ = v_isSharedCheck_1374_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1380_ = crate::leanh::lean_ctor_get(v_impl_1293_, 3);
                            crate::leanh::lean_inc(v_l_1380_);
                            if crate::leanh::lean_obj_tag(v_l_1380_) == 0 {
                                v_r_1381_ = crate::leanh::lean_ctor_get(v_impl_1293_, 4);
                                v_k_1382_ = crate::leanh::lean_ctor_get(v_impl_1293_, 1);
                                v_v_1383_ = crate::leanh::lean_ctor_get(v_impl_1293_, 2);
                                v_isSharedCheck_1394_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1293_)) as u8;
                                if v_isSharedCheck_1394_ == 0 {
                                    v_unused_1395_ = crate::leanh::lean_ctor_get(v_impl_1293_, 3);
                                    crate::leanh::lean_dec(v_unused_1395_);
                                    v_unused_1396_ = crate::leanh::lean_ctor_get(v_impl_1293_, 0);
                                    crate::leanh::lean_dec(v_unused_1396_);
                                    v___x_1385_ = v_impl_1293_;
                                    v_isShared_1386_ = v_isSharedCheck_1394_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_1381_);
                                    crate::leanh::lean_inc(v_v_1383_);
                                    crate::leanh::lean_inc(v_k_1382_);
                                    crate::leanh::lean_dec(v_impl_1293_);
                                    v___x_1385_ = crate::leanh::lean_box(0);
                                    v_isShared_1386_ = v_isSharedCheck_1394_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1397_ = crate::leanh::lean_ctor_get(v_impl_1293_, 4);
                                crate::leanh::lean_inc(v_r_1397_);
                                if crate::leanh::lean_obj_tag(v_r_1397_) == 0 {
                                    v_k_1398_ = crate::leanh::lean_ctor_get(v_impl_1293_, 1);
                                    v_v_1399_ = crate::leanh::lean_ctor_get(v_impl_1293_, 2);
                                    v_isSharedCheck_1422_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1293_)) as u8;
                                    if v_isSharedCheck_1422_ == 0 {
                                        v_unused_1423_ =
                                            crate::leanh::lean_ctor_get(v_impl_1293_, 4);
                                        crate::leanh::lean_dec(v_unused_1423_);
                                        v_unused_1424_ =
                                            crate::leanh::lean_ctor_get(v_impl_1293_, 3);
                                        crate::leanh::lean_dec(v_unused_1424_);
                                        v_unused_1425_ =
                                            crate::leanh::lean_ctor_get(v_impl_1293_, 0);
                                        crate::leanh::lean_dec(v_unused_1425_);
                                        v___x_1401_ = v_impl_1293_;
                                        v_isShared_1402_ = v_isSharedCheck_1422_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_1399_);
                                        crate::leanh::lean_inc(v_k_1398_);
                                        crate::leanh::lean_dec(v_impl_1293_);
                                        v___x_1401_ = crate::leanh::lean_box(0);
                                        v_isShared_1402_ = v_isSharedCheck_1422_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1426_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1290_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1289_, 4, v_r_1397_);
                                        crate::leanh::lean_ctor_set(v___x_1289_, 3, v_impl_1293_);
                                        crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1426_);
                                        v___x_1428_ = v___x_1289_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1429_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1429_,
                                            0,
                                            v___x_1426_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1429_,
                                            1,
                                            v_k_1284_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1429_,
                                            2,
                                            v_v_1285_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1429_,
                                            3,
                                            v_impl_1293_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1429_,
                                            4,
                                            v_r_1397_,
                                        );
                                        v___x_1428_ = v_reuseFailAlloc_1429_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_1285_);
                        crate::leanh::lean_dec(v_k_1284_);
                        crate::leanh::lean_dec_ref(v_cmp_1279_);
                        if v_isShared_1290_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1289_, 2, v_v_1281_);
                            crate::leanh::lean_ctor_set(v___x_1289_, 1, v_k_1280_);
                            v___x_1431_ = v___x_1289_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1432_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_size_1283_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_k_1280_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_v_1281_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 3, v_l_1286_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 4, v_r_1287_);
                            v___x_1431_ = v_reuseFailAlloc_1432_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_1283_);
                        v_impl_1433_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_1279_, v_k_1280_, v_v_1281_, v_r_1287_);
                        v___x_1434_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_1286_) == 0 {
                            v_size_1435_ = crate::leanh::lean_ctor_get(v_l_1286_, 0);
                            v_size_1436_ = crate::leanh::lean_ctor_get(v_impl_1433_, 0);
                            crate::leanh::lean_inc(v_size_1436_);
                            v_k_1437_ = crate::leanh::lean_ctor_get(v_impl_1433_, 1);
                            crate::leanh::lean_inc(v_k_1437_);
                            v_v_1438_ = crate::leanh::lean_ctor_get(v_impl_1433_, 2);
                            crate::leanh::lean_inc(v_v_1438_);
                            v_l_1439_ = crate::leanh::lean_ctor_get(v_impl_1433_, 3);
                            crate::leanh::lean_inc(v_l_1439_);
                            v_r_1440_ = crate::leanh::lean_ctor_get(v_impl_1433_, 4);
                            crate::leanh::lean_inc(v_r_1440_);
                            v___x_1441_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1442_ = lean_nat_mul(v___x_1441_, v_size_1435_);
                            v___x_1443_ = lean_nat_dec_lt(v___x_1442_, v_size_1436_);
                            crate::leanh::lean_dec(v___x_1442_);
                            if v___x_1443_ == 0 {
                                crate::leanh::lean_dec(v_r_1440_);
                                crate::leanh::lean_dec(v_l_1439_);
                                crate::leanh::lean_dec(v_v_1438_);
                                crate::leanh::lean_dec(v_k_1437_);
                                v___x_1444_ = lean_nat_add(v___x_1434_, v_size_1435_);
                                v___x_1445_ = lean_nat_add(v___x_1444_, v_size_1436_);
                                crate::leanh::lean_dec(v_size_1436_);
                                crate::leanh::lean_dec(v___x_1444_);
                                if v_isShared_1290_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1289_, 4, v_impl_1433_);
                                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1445_);
                                    v___x_1447_ = v___x_1289_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1448_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1448_,
                                        0,
                                        v___x_1445_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1448_,
                                        1,
                                        v_k_1284_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1448_,
                                        2,
                                        v_v_1285_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1448_,
                                        3,
                                        v_l_1286_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1448_,
                                        4,
                                        v_impl_1433_,
                                    );
                                    v___x_1447_ = v_reuseFailAlloc_1448_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1512_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1433_)) as u8;
                                if v_isSharedCheck_1512_ == 0 {
                                    v_unused_1513_ = crate::leanh::lean_ctor_get(v_impl_1433_, 4);
                                    crate::leanh::lean_dec(v_unused_1513_);
                                    v_unused_1514_ = crate::leanh::lean_ctor_get(v_impl_1433_, 3);
                                    crate::leanh::lean_dec(v_unused_1514_);
                                    v_unused_1515_ = crate::leanh::lean_ctor_get(v_impl_1433_, 2);
                                    crate::leanh::lean_dec(v_unused_1515_);
                                    v_unused_1516_ = crate::leanh::lean_ctor_get(v_impl_1433_, 1);
                                    crate::leanh::lean_dec(v_unused_1516_);
                                    v_unused_1517_ = crate::leanh::lean_ctor_get(v_impl_1433_, 0);
                                    crate::leanh::lean_dec(v_unused_1517_);
                                    v___x_1450_ = v_impl_1433_;
                                    v_isShared_1451_ = v_isSharedCheck_1512_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1433_);
                                    v___x_1450_ = crate::leanh::lean_box(0);
                                    v_isShared_1451_ = v_isSharedCheck_1512_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1518_ = crate::leanh::lean_ctor_get(v_impl_1433_, 3);
                            crate::leanh::lean_inc(v_l_1518_);
                            if crate::leanh::lean_obj_tag(v_l_1518_) == 0 {
                                v_r_1519_ = crate::leanh::lean_ctor_get(v_impl_1433_, 4);
                                v_k_1520_ = crate::leanh::lean_ctor_get(v_impl_1433_, 1);
                                v_v_1521_ = crate::leanh::lean_ctor_get(v_impl_1433_, 2);
                                v_isSharedCheck_1544_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1433_)) as u8;
                                if v_isSharedCheck_1544_ == 0 {
                                    v_unused_1545_ = crate::leanh::lean_ctor_get(v_impl_1433_, 3);
                                    crate::leanh::lean_dec(v_unused_1545_);
                                    v_unused_1546_ = crate::leanh::lean_ctor_get(v_impl_1433_, 0);
                                    crate::leanh::lean_dec(v_unused_1546_);
                                    v___x_1523_ = v_impl_1433_;
                                    v_isShared_1524_ = v_isSharedCheck_1544_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_1519_);
                                    crate::leanh::lean_inc(v_v_1521_);
                                    crate::leanh::lean_inc(v_k_1520_);
                                    crate::leanh::lean_dec(v_impl_1433_);
                                    v___x_1523_ = crate::leanh::lean_box(0);
                                    v_isShared_1524_ = v_isSharedCheck_1544_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_1547_ = crate::leanh::lean_ctor_get(v_impl_1433_, 4);
                                crate::leanh::lean_inc(v_r_1547_);
                                if crate::leanh::lean_obj_tag(v_r_1547_) == 0 {
                                    v_k_1548_ = crate::leanh::lean_ctor_get(v_impl_1433_, 1);
                                    v_v_1549_ = crate::leanh::lean_ctor_get(v_impl_1433_, 2);
                                    v_isSharedCheck_1560_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1433_)) as u8;
                                    if v_isSharedCheck_1560_ == 0 {
                                        v_unused_1561_ =
                                            crate::leanh::lean_ctor_get(v_impl_1433_, 4);
                                        crate::leanh::lean_dec(v_unused_1561_);
                                        v_unused_1562_ =
                                            crate::leanh::lean_ctor_get(v_impl_1433_, 3);
                                        crate::leanh::lean_dec(v_unused_1562_);
                                        v_unused_1563_ =
                                            crate::leanh::lean_ctor_get(v_impl_1433_, 0);
                                        crate::leanh::lean_dec(v_unused_1563_);
                                        v___x_1551_ = v_impl_1433_;
                                        v_isShared_1552_ = v_isSharedCheck_1560_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_1549_);
                                        crate::leanh::lean_inc(v_k_1548_);
                                        crate::leanh::lean_dec(v_impl_1433_);
                                        v___x_1551_ = crate::leanh::lean_box(0);
                                        v_isShared_1552_ = v_isSharedCheck_1560_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_1564_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1290_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1289_, 4, v_impl_1433_);
                                        crate::leanh::lean_ctor_set(v___x_1289_, 3, v_r_1547_);
                                        crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1564_);
                                        v___x_1566_ = v___x_1289_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1567_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1567_,
                                            0,
                                            v___x_1564_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1567_,
                                            1,
                                            v_k_1284_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1567_,
                                            2,
                                            v_v_1285_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1567_,
                                            3,
                                            v_r_1547_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1567_,
                                            4,
                                            v_impl_1433_,
                                        );
                                        v___x_1566_ = v_reuseFailAlloc_1567_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1307_;
            }
            3 => {
                v_size_1312_ = crate::leanh::lean_ctor_get(v_l_1299_, 0);
                v_size_1313_ = crate::leanh::lean_ctor_get(v_r_1300_, 0);
                v_k_1314_ = crate::leanh::lean_ctor_get(v_r_1300_, 1);
                v_v_1315_ = crate::leanh::lean_ctor_get(v_r_1300_, 2);
                v_l_1316_ = crate::leanh::lean_ctor_get(v_r_1300_, 3);
                v_r_1317_ = crate::leanh::lean_ctor_get(v_r_1300_, 4);
                v___x_1318_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1319_ = lean_nat_mul(v___x_1318_, v_size_1312_);
                v___x_1320_ = lean_nat_dec_lt(v_size_1313_, v___x_1319_);
                crate::leanh::lean_dec(v___x_1319_);
                if v___x_1320_ == 0 {
                    crate::leanh::lean_inc(v_r_1317_);
                    crate::leanh::lean_inc(v_l_1316_);
                    crate::leanh::lean_inc(v_v_1315_);
                    crate::leanh::lean_inc(v_k_1314_);
                    v_isSharedCheck_1349_ = (!crate::leanh::lean_is_exclusive(v_r_1300_)) as u8;
                    if v_isSharedCheck_1349_ == 0 {
                        v_unused_1350_ = crate::leanh::lean_ctor_get(v_r_1300_, 4);
                        crate::leanh::lean_dec(v_unused_1350_);
                        v_unused_1351_ = crate::leanh::lean_ctor_get(v_r_1300_, 3);
                        crate::leanh::lean_dec(v_unused_1351_);
                        v_unused_1352_ = crate::leanh::lean_ctor_get(v_r_1300_, 2);
                        crate::leanh::lean_dec(v_unused_1352_);
                        v_unused_1353_ = crate::leanh::lean_ctor_get(v_r_1300_, 1);
                        crate::leanh::lean_dec(v_unused_1353_);
                        v_unused_1354_ = crate::leanh::lean_ctor_get(v_r_1300_, 0);
                        crate::leanh::lean_dec(v_unused_1354_);
                        v___x_1322_ = v_r_1300_;
                        v_isShared_1323_ = v_isSharedCheck_1349_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_1300_);
                        v___x_1322_ = crate::leanh::lean_box(0);
                        v_isShared_1323_ = v_isSharedCheck_1349_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1289_);
                    v___x_1355_ = lean_nat_add(v___x_1294_, v_size_1296_);
                    crate::leanh::lean_dec(v_size_1296_);
                    v___x_1356_ = lean_nat_add(v___x_1355_, v_size_1295_);
                    crate::leanh::lean_dec(v___x_1355_);
                    v___x_1357_ = lean_nat_add(v___x_1294_, v_size_1295_);
                    v___x_1358_ = lean_nat_add(v___x_1357_, v_size_1313_);
                    crate::leanh::lean_dec(v___x_1357_);
                    crate::leanh::lean_inc_ref(v_r_1287_);
                    if v_isShared_1311_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1310_, 4, v_r_1287_);
                        crate::leanh::lean_ctor_set(v___x_1310_, 3, v_r_1300_);
                        crate::leanh::lean_ctor_set(v___x_1310_, 2, v_v_1285_);
                        crate::leanh::lean_ctor_set(v___x_1310_, 1, v_k_1284_);
                        crate::leanh::lean_ctor_set(v___x_1310_, 0, v___x_1358_);
                        v___x_1360_ = v___x_1310_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1373_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1358_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1284_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1285_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_r_1300_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_r_1287_);
                        v___x_1360_ = v_reuseFailAlloc_1373_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1324_ = lean_nat_add(v___x_1294_, v_size_1296_);
                crate::leanh::lean_dec(v_size_1296_);
                v___x_1325_ = lean_nat_add(v___x_1324_, v_size_1295_);
                crate::leanh::lean_dec(v___x_1324_);
                v___x_1337_ = lean_nat_add(v___x_1294_, v_size_1312_);
                if crate::leanh::lean_obj_tag(v_l_1316_) == 0 {
                    v_size_1347_ = crate::leanh::lean_ctor_get(v_l_1316_, 0);
                    crate::leanh::lean_inc(v_size_1347_);
                    v___y_1339_ = v_size_1347_;
                    state = 8;
                    continue;
                } else {
                    v___x_1348_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1339_ = v___x_1348_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1330_ = lean_nat_add(v___y_1328_, v___y_1329_);
                crate::leanh::lean_dec(v___y_1329_);
                crate::leanh::lean_dec(v___y_1328_);
                if v_isShared_1323_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1322_, 4, v_r_1287_);
                    crate::leanh::lean_ctor_set(v___x_1322_, 3, v_r_1317_);
                    crate::leanh::lean_ctor_set(v___x_1322_, 2, v_v_1285_);
                    crate::leanh::lean_ctor_set(v___x_1322_, 1, v_k_1284_);
                    crate::leanh::lean_ctor_set(v___x_1322_, 0, v___x_1330_);
                    v___x_1332_ = v___x_1322_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_k_1284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_v_1285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 3, v_r_1317_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 4, v_r_1287_);
                    v___x_1332_ = v_reuseFailAlloc_1336_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1310_, 4, v___x_1332_);
                    crate::leanh::lean_ctor_set(v___x_1310_, 3, v___y_1327_);
                    crate::leanh::lean_ctor_set(v___x_1310_, 2, v_v_1315_);
                    crate::leanh::lean_ctor_set(v___x_1310_, 1, v_k_1314_);
                    crate::leanh::lean_ctor_set(v___x_1310_, 0, v___x_1325_);
                    v___x_1334_ = v___x_1310_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1335_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1325_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_k_1314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_v_1315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 3, v___y_1327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 4, v___x_1332_);
                    v___x_1334_ = v_reuseFailAlloc_1335_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1334_;
            }
            8 => {
                v___x_1340_ = lean_nat_add(v___x_1337_, v___y_1339_);
                crate::leanh::lean_dec(v___y_1339_);
                crate::leanh::lean_dec(v___x_1337_);
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1289_, 4, v_l_1316_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 3, v_l_1299_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 2, v_v_1298_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 1, v_k_1297_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1340_);
                    v___x_1342_ = v___x_1289_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1346_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_k_1297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_v_1298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_l_1299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_l_1316_);
                    v___x_1342_ = v_reuseFailAlloc_1346_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1343_ = lean_nat_add(v___x_1294_, v_size_1295_);
                if crate::leanh::lean_obj_tag(v_r_1317_) == 0 {
                    v_size_1344_ = crate::leanh::lean_ctor_get(v_r_1317_, 0);
                    crate::leanh::lean_inc(v_size_1344_);
                    v___y_1327_ = v___x_1342_;
                    v___y_1328_ = v___x_1343_;
                    v___y_1329_ = v_size_1344_;
                    state = 5;
                    continue;
                } else {
                    v___x_1345_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1327_ = v___x_1342_;
                    v___y_1328_ = v___x_1343_;
                    v___y_1329_ = v___x_1345_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1367_ = (!crate::leanh::lean_is_exclusive(v_r_1287_)) as u8;
                if v_isSharedCheck_1367_ == 0 {
                    v_unused_1368_ = crate::leanh::lean_ctor_get(v_r_1287_, 4);
                    crate::leanh::lean_dec(v_unused_1368_);
                    v_unused_1369_ = crate::leanh::lean_ctor_get(v_r_1287_, 3);
                    crate::leanh::lean_dec(v_unused_1369_);
                    v_unused_1370_ = crate::leanh::lean_ctor_get(v_r_1287_, 2);
                    crate::leanh::lean_dec(v_unused_1370_);
                    v_unused_1371_ = crate::leanh::lean_ctor_get(v_r_1287_, 1);
                    crate::leanh::lean_dec(v_unused_1371_);
                    v_unused_1372_ = crate::leanh::lean_ctor_get(v_r_1287_, 0);
                    crate::leanh::lean_dec(v_unused_1372_);
                    v___x_1362_ = v_r_1287_;
                    v_isShared_1363_ = v_isSharedCheck_1367_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_1287_);
                    v___x_1362_ = crate::leanh::lean_box(0);
                    v_isShared_1363_ = v_isSharedCheck_1367_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1363_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1362_, 4, v___x_1360_);
                    crate::leanh::lean_ctor_set(v___x_1362_, 3, v_l_1299_);
                    crate::leanh::lean_ctor_set(v___x_1362_, 2, v_v_1298_);
                    crate::leanh::lean_ctor_set(v___x_1362_, 1, v_k_1297_);
                    crate::leanh::lean_ctor_set(v___x_1362_, 0, v___x_1356_);
                    v___x_1365_ = v___x_1362_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1366_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_l_1299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 4, v___x_1360_);
                    v___x_1365_ = v_reuseFailAlloc_1366_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1365_;
            }
            13 => {
                v___x_1387_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_1381_);
                if v_isShared_1386_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1385_, 3, v_r_1381_);
                    crate::leanh::lean_ctor_set(v___x_1385_, 2, v_v_1285_);
                    crate::leanh::lean_ctor_set(v___x_1385_, 1, v_k_1284_);
                    crate::leanh::lean_ctor_set(v___x_1385_, 0, v___x_1294_);
                    v___x_1389_ = v___x_1385_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_k_1284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_v_1285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_r_1381_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_r_1381_);
                    v___x_1389_ = v_reuseFailAlloc_1393_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1289_, 4, v___x_1389_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 3, v_l_1380_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 2, v_v_1383_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 1, v_k_1382_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1387_);
                    v___x_1391_ = v___x_1289_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1392_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_k_1382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_v_1383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_l_1380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 4, v___x_1389_);
                    v___x_1391_ = v_reuseFailAlloc_1392_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1391_;
            }
            16 => {
                v_k_1403_ = crate::leanh::lean_ctor_get(v_r_1397_, 1);
                v_v_1404_ = crate::leanh::lean_ctor_get(v_r_1397_, 2);
                v_isSharedCheck_1418_ = (!crate::leanh::lean_is_exclusive(v_r_1397_)) as u8;
                if v_isSharedCheck_1418_ == 0 {
                    v_unused_1419_ = crate::leanh::lean_ctor_get(v_r_1397_, 4);
                    crate::leanh::lean_dec(v_unused_1419_);
                    v_unused_1420_ = crate::leanh::lean_ctor_get(v_r_1397_, 3);
                    crate::leanh::lean_dec(v_unused_1420_);
                    v_unused_1421_ = crate::leanh::lean_ctor_get(v_r_1397_, 0);
                    crate::leanh::lean_dec(v_unused_1421_);
                    v___x_1406_ = v_r_1397_;
                    v_isShared_1407_ = v_isSharedCheck_1418_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1404_);
                    crate::leanh::lean_inc(v_k_1403_);
                    crate::leanh::lean_dec(v_r_1397_);
                    v___x_1406_ = crate::leanh::lean_box(0);
                    v_isShared_1407_ = v_isSharedCheck_1418_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1408_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1407_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1406_, 4, v_l_1380_);
                    crate::leanh::lean_ctor_set(v___x_1406_, 3, v_l_1380_);
                    crate::leanh::lean_ctor_set(v___x_1406_, 2, v_v_1399_);
                    crate::leanh::lean_ctor_set(v___x_1406_, 1, v_k_1398_);
                    crate::leanh::lean_ctor_set(v___x_1406_, 0, v___x_1294_);
                    v___x_1410_ = v___x_1406_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1417_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_l_1380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_l_1380_);
                    v___x_1410_ = v_reuseFailAlloc_1417_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1402_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1401_, 4, v_l_1380_);
                    crate::leanh::lean_ctor_set(v___x_1401_, 2, v_v_1285_);
                    crate::leanh::lean_ctor_set(v___x_1401_, 1, v_k_1284_);
                    crate::leanh::lean_ctor_set(v___x_1401_, 0, v___x_1294_);
                    v___x_1412_ = v___x_1401_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1416_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_l_1380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_l_1380_);
                    v___x_1412_ = v_reuseFailAlloc_1416_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1289_, 4, v___x_1412_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 3, v___x_1410_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 2, v_v_1404_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 1, v_k_1403_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1408_);
                    v___x_1414_ = v___x_1289_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1415_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 3, v___x_1410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 4, v___x_1412_);
                    v___x_1414_ = v_reuseFailAlloc_1415_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1414_;
            }
            21 => {
                return v___x_1428_;
            }
            22 => {
                return v___x_1431_;
            }
            23 => {
                return v___x_1447_;
            }
            24 => {
                v_size_1452_ = crate::leanh::lean_ctor_get(v_l_1439_, 0);
                v_k_1453_ = crate::leanh::lean_ctor_get(v_l_1439_, 1);
                v_v_1454_ = crate::leanh::lean_ctor_get(v_l_1439_, 2);
                v_l_1455_ = crate::leanh::lean_ctor_get(v_l_1439_, 3);
                v_r_1456_ = crate::leanh::lean_ctor_get(v_l_1439_, 4);
                v_size_1457_ = crate::leanh::lean_ctor_get(v_r_1440_, 0);
                v___x_1458_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1459_ = lean_nat_mul(v___x_1458_, v_size_1457_);
                v___x_1460_ = lean_nat_dec_lt(v_size_1452_, v___x_1459_);
                crate::leanh::lean_dec(v___x_1459_);
                if v___x_1460_ == 0 {
                    crate::leanh::lean_inc(v_r_1456_);
                    crate::leanh::lean_inc(v_l_1455_);
                    crate::leanh::lean_inc(v_v_1454_);
                    crate::leanh::lean_inc(v_k_1453_);
                    v_isSharedCheck_1488_ = (!crate::leanh::lean_is_exclusive(v_l_1439_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v_unused_1489_ = crate::leanh::lean_ctor_get(v_l_1439_, 4);
                        crate::leanh::lean_dec(v_unused_1489_);
                        v_unused_1490_ = crate::leanh::lean_ctor_get(v_l_1439_, 3);
                        crate::leanh::lean_dec(v_unused_1490_);
                        v_unused_1491_ = crate::leanh::lean_ctor_get(v_l_1439_, 2);
                        crate::leanh::lean_dec(v_unused_1491_);
                        v_unused_1492_ = crate::leanh::lean_ctor_get(v_l_1439_, 1);
                        crate::leanh::lean_dec(v_unused_1492_);
                        v_unused_1493_ = crate::leanh::lean_ctor_get(v_l_1439_, 0);
                        crate::leanh::lean_dec(v_unused_1493_);
                        v___x_1462_ = v_l_1439_;
                        v_isShared_1463_ = v_isSharedCheck_1488_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_1439_);
                        v___x_1462_ = crate::leanh::lean_box(0);
                        v_isShared_1463_ = v_isSharedCheck_1488_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1289_);
                    v___x_1494_ = lean_nat_add(v___x_1434_, v_size_1435_);
                    v___x_1495_ = lean_nat_add(v___x_1494_, v_size_1436_);
                    crate::leanh::lean_dec(v_size_1436_);
                    v___x_1496_ = lean_nat_add(v___x_1494_, v_size_1452_);
                    crate::leanh::lean_dec(v___x_1494_);
                    crate::leanh::lean_inc_ref(v_l_1286_);
                    if v_isShared_1451_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1450_, 4, v_l_1439_);
                        crate::leanh::lean_ctor_set(v___x_1450_, 3, v_l_1286_);
                        crate::leanh::lean_ctor_set(v___x_1450_, 2, v_v_1285_);
                        crate::leanh::lean_ctor_set(v___x_1450_, 1, v_k_1284_);
                        crate::leanh::lean_ctor_set(v___x_1450_, 0, v___x_1496_);
                        v___x_1498_ = v___x_1450_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1511_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1496_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_k_1284_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_v_1285_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_l_1286_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_l_1439_);
                        v___x_1498_ = v_reuseFailAlloc_1511_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1464_ = lean_nat_add(v___x_1434_, v_size_1435_);
                v___x_1465_ = lean_nat_add(v___x_1464_, v_size_1436_);
                crate::leanh::lean_dec(v_size_1436_);
                if crate::leanh::lean_obj_tag(v_l_1455_) == 0 {
                    v_size_1486_ = crate::leanh::lean_ctor_get(v_l_1455_, 0);
                    crate::leanh::lean_inc(v_size_1486_);
                    v___y_1478_ = v_size_1486_;
                    state = 29;
                    continue;
                } else {
                    v___x_1487_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1478_ = v___x_1487_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1470_ = lean_nat_add(v___y_1467_, v___y_1469_);
                crate::leanh::lean_dec(v___y_1469_);
                crate::leanh::lean_dec(v___y_1467_);
                if v_isShared_1463_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1462_, 4, v_r_1440_);
                    crate::leanh::lean_ctor_set(v___x_1462_, 3, v_r_1456_);
                    crate::leanh::lean_ctor_set(v___x_1462_, 2, v_v_1438_);
                    crate::leanh::lean_ctor_set(v___x_1462_, 1, v_k_1437_);
                    crate::leanh::lean_ctor_set(v___x_1462_, 0, v___x_1470_);
                    v___x_1472_ = v___x_1462_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_k_1437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_v_1438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_r_1456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_r_1440_);
                    v___x_1472_ = v_reuseFailAlloc_1476_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1450_, 4, v___x_1472_);
                    crate::leanh::lean_ctor_set(v___x_1450_, 3, v___y_1468_);
                    crate::leanh::lean_ctor_set(v___x_1450_, 2, v_v_1454_);
                    crate::leanh::lean_ctor_set(v___x_1450_, 1, v_k_1453_);
                    crate::leanh::lean_ctor_set(v___x_1450_, 0, v___x_1465_);
                    v___x_1474_ = v___x_1450_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1475_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 3, v___y_1468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 4, v___x_1472_);
                    v___x_1474_ = v_reuseFailAlloc_1475_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1474_;
            }
            29 => {
                v___x_1479_ = lean_nat_add(v___x_1464_, v___y_1478_);
                crate::leanh::lean_dec(v___y_1478_);
                crate::leanh::lean_dec(v___x_1464_);
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1289_, 4, v_l_1455_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1479_);
                    v___x_1481_ = v___x_1289_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1485_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_l_1286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_l_1455_);
                    v___x_1481_ = v_reuseFailAlloc_1485_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1482_ = lean_nat_add(v___x_1434_, v_size_1457_);
                if crate::leanh::lean_obj_tag(v_r_1456_) == 0 {
                    v_size_1483_ = crate::leanh::lean_ctor_get(v_r_1456_, 0);
                    crate::leanh::lean_inc(v_size_1483_);
                    v___y_1467_ = v___x_1482_;
                    v___y_1468_ = v___x_1481_;
                    v___y_1469_ = v_size_1483_;
                    state = 26;
                    continue;
                } else {
                    v___x_1484_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1467_ = v___x_1482_;
                    v___y_1468_ = v___x_1481_;
                    v___y_1469_ = v___x_1484_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1505_ = (!crate::leanh::lean_is_exclusive(v_l_1286_)) as u8;
                if v_isSharedCheck_1505_ == 0 {
                    v_unused_1506_ = crate::leanh::lean_ctor_get(v_l_1286_, 4);
                    crate::leanh::lean_dec(v_unused_1506_);
                    v_unused_1507_ = crate::leanh::lean_ctor_get(v_l_1286_, 3);
                    crate::leanh::lean_dec(v_unused_1507_);
                    v_unused_1508_ = crate::leanh::lean_ctor_get(v_l_1286_, 2);
                    crate::leanh::lean_dec(v_unused_1508_);
                    v_unused_1509_ = crate::leanh::lean_ctor_get(v_l_1286_, 1);
                    crate::leanh::lean_dec(v_unused_1509_);
                    v_unused_1510_ = crate::leanh::lean_ctor_get(v_l_1286_, 0);
                    crate::leanh::lean_dec(v_unused_1510_);
                    v___x_1500_ = v_l_1286_;
                    v_isShared_1501_ = v_isSharedCheck_1505_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_1286_);
                    v___x_1500_ = crate::leanh::lean_box(0);
                    v_isShared_1501_ = v_isSharedCheck_1505_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1501_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1500_, 4, v_r_1440_);
                    crate::leanh::lean_ctor_set(v___x_1500_, 3, v___x_1498_);
                    crate::leanh::lean_ctor_set(v___x_1500_, 2, v_v_1438_);
                    crate::leanh::lean_ctor_set(v___x_1500_, 1, v_k_1437_);
                    crate::leanh::lean_ctor_set(v___x_1500_, 0, v___x_1495_);
                    v___x_1503_ = v___x_1500_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1504_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_k_1437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_v_1438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 3, v___x_1498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 4, v_r_1440_);
                    v___x_1503_ = v_reuseFailAlloc_1504_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1503_;
            }
            34 => {
                v_k_1525_ = crate::leanh::lean_ctor_get(v_l_1518_, 1);
                v_v_1526_ = crate::leanh::lean_ctor_get(v_l_1518_, 2);
                v_isSharedCheck_1540_ = (!crate::leanh::lean_is_exclusive(v_l_1518_)) as u8;
                if v_isSharedCheck_1540_ == 0 {
                    v_unused_1541_ = crate::leanh::lean_ctor_get(v_l_1518_, 4);
                    crate::leanh::lean_dec(v_unused_1541_);
                    v_unused_1542_ = crate::leanh::lean_ctor_get(v_l_1518_, 3);
                    crate::leanh::lean_dec(v_unused_1542_);
                    v_unused_1543_ = crate::leanh::lean_ctor_get(v_l_1518_, 0);
                    crate::leanh::lean_dec(v_unused_1543_);
                    v___x_1528_ = v_l_1518_;
                    v_isShared_1529_ = v_isSharedCheck_1540_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1526_);
                    crate::leanh::lean_inc(v_k_1525_);
                    crate::leanh::lean_dec(v_l_1518_);
                    v___x_1528_ = crate::leanh::lean_box(0);
                    v_isShared_1529_ = v_isSharedCheck_1540_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1530_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_1519_, 2);
                if v_isShared_1529_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1528_, 4, v_r_1519_);
                    crate::leanh::lean_ctor_set(v___x_1528_, 3, v_r_1519_);
                    crate::leanh::lean_ctor_set(v___x_1528_, 2, v_v_1285_);
                    crate::leanh::lean_ctor_set(v___x_1528_, 1, v_k_1284_);
                    crate::leanh::lean_ctor_set(v___x_1528_, 0, v___x_1434_);
                    v___x_1532_ = v___x_1528_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1539_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_r_1519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_r_1519_);
                    v___x_1532_ = v_reuseFailAlloc_1539_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_1519_);
                if v_isShared_1524_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1523_, 3, v_r_1519_);
                    crate::leanh::lean_ctor_set(v___x_1523_, 0, v___x_1434_);
                    v___x_1534_ = v___x_1523_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_k_1520_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_v_1521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_r_1519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_r_1519_);
                    v___x_1534_ = v_reuseFailAlloc_1538_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1289_, 4, v___x_1534_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 3, v___x_1532_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 2, v_v_1526_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 1, v_k_1525_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1530_);
                    v___x_1536_ = v___x_1289_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_k_1525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_v_1526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 3, v___x_1532_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 4, v___x_1534_);
                    v___x_1536_ = v_reuseFailAlloc_1537_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1536_;
            }
            39 => {
                v___x_1553_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1552_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1551_, 4, v_l_1518_);
                    crate::leanh::lean_ctor_set(v___x_1551_, 2, v_v_1285_);
                    crate::leanh::lean_ctor_set(v___x_1551_, 1, v_k_1284_);
                    crate::leanh::lean_ctor_set(v___x_1551_, 0, v___x_1434_);
                    v___x_1555_ = v___x_1551_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_l_1518_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_l_1518_);
                    v___x_1555_ = v_reuseFailAlloc_1559_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1289_, 4, v_r_1547_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 3, v___x_1555_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 2, v_v_1549_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 1, v_k_1548_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1553_);
                    v___x_1557_ = v___x_1289_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1553_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1548_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1549_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 3, v___x_1555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1547_);
                    v___x_1557_ = v_reuseFailAlloc_1558_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1557_;
            }
            42 => {
                return v___x_1566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(
    mut v_items_1571_: *mut crate::leanh::LeanObject,
    mut v_cmp_1572_: *mut crate::leanh::LeanObject,
    mut v_n_1573_: *mut crate::leanh::LeanObject,
    mut v_j_1574_: *mut crate::leanh::LeanObject,
    mut v_a_1575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1577_: u8 = 0;
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1576_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1577_ = lean_nat_dec_eq(v_j_1574_, v_zero_1576_);
                if v_isZero_1577_ == 1 {
                    crate::leanh::lean_dec(v_j_1574_);
                    crate::leanh::lean_dec_ref(v_cmp_1572_);
                    return v_a_1575_;
                } else {
                    v___x_1578_ = lean_nat_sub(v_n_1573_, v_j_1574_);
                    v___x_1579_ = lean_array_fget_borrowed(v_items_1571_, v___x_1578_);
                    v_fst_1580_ = crate::leanh::lean_ctor_get(v___x_1579_, 0);
                    v_one_1581_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1582_ = lean_nat_sub(v_j_1574_, v_one_1581_);
                    crate::leanh::lean_dec(v_j_1574_);
                    crate::leanh::lean_inc(v_fst_1580_);
                    crate::leanh::lean_inc_ref(v_cmp_1572_);
                    v___x_1583_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_1572_, v_fst_1580_, v___x_1578_, v_a_1575_);
                    v_j_1574_ = v_n_1582_;
                    v_a_1575_ = v___x_1583_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg___boxed(
    mut v_items_1585_: *mut crate::leanh::LeanObject,
    mut v_cmp_1586_: *mut crate::leanh::LeanObject,
    mut v_n_1587_: *mut crate::leanh::LeanObject,
    mut v_j_1588_: *mut crate::leanh::LeanObject,
    mut v_a_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_1585_, v_cmp_1586_, v_n_1587_, v_j_1588_, v_a_1589_);
    crate::leanh::lean_dec(v_n_1587_);
    crate::leanh::lean_dec_ref(v_items_1585_);
    return v_res_1590_;
}
pub unsafe fn l_Lake_Toml_RBDict_ofArray___redArg(
    mut v_cmp_1591_: *mut crate::leanh::LeanObject,
    mut v_items_1592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1593_ = lean_array_get_size(v_items_1592_);
    v___x_1594_ = crate::leanh::lean_box(1);
    v_indices_1595_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_1592_, v_cmp_1591_, v___x_1593_, v___x_1593_, v___x_1594_);
    v___x_1596_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1596_, 0, v_items_1592_);
    crate::leanh::lean_ctor_set(v___x_1596_, 1, v_indices_1595_);
    return v___x_1596_;
}
pub unsafe fn l_Lake_Toml_RBDict_ofArray(
    mut v_00_u03b1_1597_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1598_: *mut crate::leanh::LeanObject,
    mut v_cmp_1599_: *mut crate::leanh::LeanObject,
    mut v_items_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1601_ = l_Lake_Toml_RBDict_ofArray___redArg(v_cmp_1599_, v_items_1600_);
    return v___x_1601_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0(
    mut v_00_u03b1_1602_: *mut crate::leanh::LeanObject,
    mut v_cmp_1603_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1604_: *mut crate::leanh::LeanObject,
    mut v_k_1605_: *mut crate::leanh::LeanObject,
    mut v_v_1606_: *mut crate::leanh::LeanObject,
    mut v_t_1607_: *mut crate::leanh::LeanObject,
    mut v_hl_1608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(
            v_cmp_1603_,
            v_k_1605_,
            v_v_1606_,
            v_t_1607_,
        );
    return v___x_1609_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1(
    mut v_00_u03b1_1610_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1611_: *mut crate::leanh::LeanObject,
    mut v_items_1612_: *mut crate::leanh::LeanObject,
    mut v_cmp_1613_: *mut crate::leanh::LeanObject,
    mut v_n_1614_: *mut crate::leanh::LeanObject,
    mut v_j_1615_: *mut crate::leanh::LeanObject,
    mut v_a_1616_: *mut crate::leanh::LeanObject,
    mut v_a_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_1612_, v_cmp_1613_, v_n_1614_, v_j_1615_, v_a_1617_);
    return v___x_1618_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___boxed(
    mut v_00_u03b1_1619_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1620_: *mut crate::leanh::LeanObject,
    mut v_items_1621_: *mut crate::leanh::LeanObject,
    mut v_cmp_1622_: *mut crate::leanh::LeanObject,
    mut v_n_1623_: *mut crate::leanh::LeanObject,
    mut v_j_1624_: *mut crate::leanh::LeanObject,
    mut v_a_1625_: *mut crate::leanh::LeanObject,
    mut v_a_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1627_ =
        l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1(
            v_00_u03b1_1619_,
            v_00_u03b2_1620_,
            v_items_1621_,
            v_cmp_1622_,
            v_n_1623_,
            v_j_1624_,
            v_a_1625_,
            v_a_1626_,
        );
    crate::leanh::lean_dec(v_n_1623_);
    crate::leanh::lean_dec_ref(v_items_1621_);
    return v_res_1627_;
}
pub unsafe fn l_Lake_Toml_RBDict_beq___redArg(
    mut v_inst_1628_: *mut crate::leanh::LeanObject,
    mut v_self_1629_: *mut crate::leanh::LeanObject,
    mut v_other_1630_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_items_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    v_items_1631_ = crate::leanh::lean_ctor_get(v_self_1629_, 0);
    v_items_1632_ = crate::leanh::lean_ctor_get(v_other_1630_, 0);
    v___x_1633_ = lean_array_get_size(v_items_1631_);
    v___x_1634_ = lean_array_get_size(v_items_1632_);
    v___x_1635_ = lean_nat_dec_eq(v___x_1633_, v___x_1634_);
    if v___x_1635_ == 0 {
        crate::leanh::lean_dec_ref(v_inst_1628_);
        return v___x_1635_;
    } else {
        let mut v___x_1636_: u8 = 0;
        v___x_1636_ =
            l_Array_isEqvAux___redArg(v_items_1631_, v_items_1632_, v_inst_1628_, v___x_1633_);
        return v___x_1636_;
    }
}
pub unsafe fn l_Lake_Toml_RBDict_beq___redArg___boxed(
    mut v_inst_1637_: *mut crate::leanh::LeanObject,
    mut v_self_1638_: *mut crate::leanh::LeanObject,
    mut v_other_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1640_: u8 = 0;
    let mut v_r_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1640_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_1637_, v_self_1638_, v_other_1639_);
    crate::leanh::lean_dec_ref(v_other_1639_);
    crate::leanh::lean_dec_ref(v_self_1638_);
    v_r_1641_ = crate::leanh::lean_box((v_res_1640_) as usize);
    return v_r_1641_;
}
pub unsafe fn l_Lake_Toml_RBDict_beq(
    mut v_00_u03b1_1642_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1643_: *mut crate::leanh::LeanObject,
    mut v_cmp_1644_: *mut crate::leanh::LeanObject,
    mut v_inst_1645_: *mut crate::leanh::LeanObject,
    mut v_self_1646_: *mut crate::leanh::LeanObject,
    mut v_other_1647_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1648_: u8 = 0;
    v___x_1648_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_1645_, v_self_1646_, v_other_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Lake_Toml_RBDict_beq___boxed(
    mut v_00_u03b1_1649_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1650_: *mut crate::leanh::LeanObject,
    mut v_cmp_1651_: *mut crate::leanh::LeanObject,
    mut v_inst_1652_: *mut crate::leanh::LeanObject,
    mut v_self_1653_: *mut crate::leanh::LeanObject,
    mut v_other_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1655_: u8 = 0;
    let mut v_r_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ = l_Lake_Toml_RBDict_beq(
        v_00_u03b1_1649_,
        v_00_u03b2_1650_,
        v_cmp_1651_,
        v_inst_1652_,
        v_self_1653_,
        v_other_1654_,
    );
    crate::leanh::lean_dec_ref(v_other_1654_);
    crate::leanh::lean_dec_ref(v_self_1653_);
    crate::leanh::lean_dec_ref(v_cmp_1651_);
    v_r_1656_ = crate::leanh::lean_box((v_res_1655_) as usize);
    return v_r_1656_;
}
pub unsafe fn l_Lake_Toml_RBDict_instBEqOfProd___redArg(
    mut v_cmp_1657_: *mut crate::leanh::LeanObject,
    mut v_inst_1658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1659_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1659_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1659_, 2, v_cmp_1657_);
    crate::leanh::lean_closure_set(v___x_1659_, 3, v_inst_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Lake_Toml_RBDict_instBEqOfProd(
    mut v_00_u03b1_1660_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1661_: *mut crate::leanh::LeanObject,
    mut v_cmp_1662_: *mut crate::leanh::LeanObject,
    mut v_inst_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1664_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1664_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1664_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1664_, 2, v_cmp_1662_);
    crate::leanh::lean_closure_set(v___x_1664_, 3, v_inst_1663_);
    return v___x_1664_;
}
pub unsafe fn l_Lake_Toml_RBDict_size___redArg(
    mut v_t_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_items_1666_ = crate::leanh::lean_ctor_get(v_t_1665_, 0);
    v___x_1667_ = lean_array_get_size(v_items_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Lake_Toml_RBDict_size___redArg___boxed(
    mut v_t_1668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1669_ = l_Lake_Toml_RBDict_size___redArg(v_t_1668_);
    crate::leanh::lean_dec_ref(v_t_1668_);
    return v_res_1669_;
}
pub unsafe fn l_Lake_Toml_RBDict_size(
    mut v_00_u03b1_1670_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1671_: *mut crate::leanh::LeanObject,
    mut v_cmp_1672_: *mut crate::leanh::LeanObject,
    mut v_t_1673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_items_1674_ = crate::leanh::lean_ctor_get(v_t_1673_, 0);
    v___x_1675_ = lean_array_get_size(v_items_1674_);
    return v___x_1675_;
}
pub unsafe fn l_Lake_Toml_RBDict_size___boxed(
    mut v_00_u03b1_1676_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1677_: *mut crate::leanh::LeanObject,
    mut v_cmp_1678_: *mut crate::leanh::LeanObject,
    mut v_t_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1680_ =
        l_Lake_Toml_RBDict_size(v_00_u03b1_1676_, v_00_u03b2_1677_, v_cmp_1678_, v_t_1679_);
    crate::leanh::lean_dec_ref(v_t_1679_);
    crate::leanh::lean_dec_ref(v_cmp_1678_);
    return v_res_1680_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty___redArg(
    mut v_t_1681_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_items_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    v_items_1682_ = crate::leanh::lean_ctor_get(v_t_1681_, 0);
    v___x_1683_ = lean_array_get_size(v_items_1682_);
    v___x_1684_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1685_ = lean_nat_dec_eq(v___x_1683_, v___x_1684_);
    return v___x_1685_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty___redArg___boxed(
    mut v_t_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1687_: u8 = 0;
    let mut v_r_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Lake_Toml_RBDict_isEmpty___redArg(v_t_1686_);
    crate::leanh::lean_dec_ref(v_t_1686_);
    v_r_1688_ = crate::leanh::lean_box((v_res_1687_) as usize);
    return v_r_1688_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty(
    mut v_00_u03b1_1689_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1690_: *mut crate::leanh::LeanObject,
    mut v_cmp_1691_: *mut crate::leanh::LeanObject,
    mut v_t_1692_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_items_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    v_items_1693_ = crate::leanh::lean_ctor_get(v_t_1692_, 0);
    v___x_1694_ = lean_array_get_size(v_items_1693_);
    v___x_1695_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1696_ = lean_nat_dec_eq(v___x_1694_, v___x_1695_);
    return v___x_1696_;
}
pub unsafe fn l_Lake_Toml_RBDict_isEmpty___boxed(
    mut v_00_u03b1_1697_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1698_: *mut crate::leanh::LeanObject,
    mut v_cmp_1699_: *mut crate::leanh::LeanObject,
    mut v_t_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1701_: u8 = 0;
    let mut v_r_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ =
        l_Lake_Toml_RBDict_isEmpty(v_00_u03b1_1697_, v_00_u03b2_1698_, v_cmp_1699_, v_t_1700_);
    crate::leanh::lean_dec_ref(v_t_1700_);
    crate::leanh::lean_dec_ref(v_cmp_1699_);
    v_r_1702_ = crate::leanh::lean_box((v_res_1701_) as usize);
    return v_r_1702_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(
    mut v_sz_1703_: usize,
    mut v_i_1704_: usize,
    mut v_bs_1705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1706_: u8 = 0;
    let mut v_v_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: usize = 0;
    let mut v___x_1712_: usize = 0;
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1706_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
                if v___x_1706_ == 0 {
                    return v_bs_1705_;
                } else {
                    v_v_1707_ = lean_array_uget_borrowed(v_bs_1705_, v_i_1704_);
                    v_fst_1708_ = crate::leanh::lean_ctor_get(v_v_1707_, 0);
                    crate::leanh::lean_inc(v_fst_1708_);
                    v___x_1709_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1710_ = lean_array_uset(v_bs_1705_, v_i_1704_, v___x_1709_);
                    v___x_1711_ = 1usize;
                    v___x_1712_ = lean_usize_add(v_i_1704_, v___x_1711_);
                    v___x_1713_ = lean_array_uset(v_bs_x27_1710_, v_i_1704_, v_fst_1708_);
                    v_i_1704_ = v___x_1712_;
                    v_bs_1705_ = v___x_1713_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg___boxed(
    mut v_sz_1715_: *mut crate::leanh::LeanObject,
    mut v_i_1716_: *mut crate::leanh::LeanObject,
    mut v_bs_1717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1718_: usize = 0;
    let mut v_i_boxed_1719_: usize = 0;
    let mut v_res_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1718_ = crate::leanh::lean_unbox_usize(v_sz_1715_);
    crate::leanh::lean_dec(v_sz_1715_);
    v_i_boxed_1719_ = crate::leanh::lean_unbox_usize(v_i_1716_);
    crate::leanh::lean_dec(v_i_1716_);
    v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1717_);
    return v_res_1720_;
}
pub unsafe fn l_Lake_Toml_RBDict_keys___redArg(
    mut v_t_1721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1723_: usize = 0;
    let mut v___x_1724_: usize = 0;
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_items_1722_ = crate::leanh::lean_ctor_get(v_t_1721_, 0);
    crate::leanh::lean_inc_ref(v_items_1722_);
    crate::leanh::lean_dec_ref(v_t_1721_);
    v_sz_1723_ = lean_array_size(v_items_1722_);
    v___x_1724_ = 0usize;
    v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_1723_, v___x_1724_, v_items_1722_);
    return v___x_1725_;
}
pub unsafe fn l_Lake_Toml_RBDict_keys(
    mut v_00_u03b1_1726_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1727_: *mut crate::leanh::LeanObject,
    mut v_cmp_1728_: *mut crate::leanh::LeanObject,
    mut v_t_1729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = l_Lake_Toml_RBDict_keys___redArg(v_t_1729_);
    return v___x_1730_;
}
pub unsafe fn l_Lake_Toml_RBDict_keys___boxed(
    mut v_00_u03b1_1731_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1732_: *mut crate::leanh::LeanObject,
    mut v_cmp_1733_: *mut crate::leanh::LeanObject,
    mut v_t_1734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1735_ =
        l_Lake_Toml_RBDict_keys(v_00_u03b1_1731_, v_00_u03b2_1732_, v_cmp_1733_, v_t_1734_);
    crate::leanh::lean_dec_ref(v_cmp_1733_);
    return v_res_1735_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(
    mut v_00_u03b1_1736_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1737_: *mut crate::leanh::LeanObject,
    mut v_sz_1738_: usize,
    mut v_i_1739_: usize,
    mut v_bs_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_1738_, v_i_1739_, v_bs_1740_);
    return v___x_1741_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___boxed(
    mut v_00_u03b1_1742_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1743_: *mut crate::leanh::LeanObject,
    mut v_sz_1744_: *mut crate::leanh::LeanObject,
    mut v_i_1745_: *mut crate::leanh::LeanObject,
    mut v_bs_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1747_: usize = 0;
    let mut v_i_boxed_1748_: usize = 0;
    let mut v_res_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1747_ = crate::leanh::lean_unbox_usize(v_sz_1744_);
    crate::leanh::lean_dec(v_sz_1744_);
    v_i_boxed_1748_ = crate::leanh::lean_unbox_usize(v_i_1745_);
    crate::leanh::lean_dec(v_i_1745_);
    v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(v_00_u03b1_1742_, v_00_u03b2_1743_, v_sz_boxed_1747_, v_i_boxed_1748_, v_bs_1746_);
    return v_res_1749_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(
    mut v_sz_1750_: usize,
    mut v_i_1751_: usize,
    mut v_bs_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1753_: u8 = 0;
    let mut v_v_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: usize = 0;
    let mut v___x_1759_: usize = 0;
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1753_ = lean_usize_dec_lt(v_i_1751_, v_sz_1750_);
                if v___x_1753_ == 0 {
                    return v_bs_1752_;
                } else {
                    v_v_1754_ = lean_array_uget_borrowed(v_bs_1752_, v_i_1751_);
                    v_snd_1755_ = crate::leanh::lean_ctor_get(v_v_1754_, 1);
                    crate::leanh::lean_inc(v_snd_1755_);
                    v___x_1756_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1757_ = lean_array_uset(v_bs_1752_, v_i_1751_, v___x_1756_);
                    v___x_1758_ = 1usize;
                    v___x_1759_ = lean_usize_add(v_i_1751_, v___x_1758_);
                    v___x_1760_ = lean_array_uset(v_bs_x27_1757_, v_i_1751_, v_snd_1755_);
                    v_i_1751_ = v___x_1759_;
                    v_bs_1752_ = v___x_1760_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg___boxed(
    mut v_sz_1762_: *mut crate::leanh::LeanObject,
    mut v_i_1763_: *mut crate::leanh::LeanObject,
    mut v_bs_1764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1765_: usize = 0;
    let mut v_i_boxed_1766_: usize = 0;
    let mut v_res_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1765_ = crate::leanh::lean_unbox_usize(v_sz_1762_);
    crate::leanh::lean_dec(v_sz_1762_);
    v_i_boxed_1766_ = crate::leanh::lean_unbox_usize(v_i_1763_);
    crate::leanh::lean_dec(v_i_1763_);
    v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_boxed_1765_, v_i_boxed_1766_, v_bs_1764_);
    return v_res_1767_;
}
pub unsafe fn l_Lake_Toml_RBDict_values___redArg(
    mut v_t_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1770_: usize = 0;
    let mut v___x_1771_: usize = 0;
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_items_1769_ = crate::leanh::lean_ctor_get(v_t_1768_, 0);
    crate::leanh::lean_inc_ref(v_items_1769_);
    crate::leanh::lean_dec_ref(v_t_1768_);
    v_sz_1770_ = lean_array_size(v_items_1769_);
    v___x_1771_ = 0usize;
    v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_1770_, v___x_1771_, v_items_1769_);
    return v___x_1772_;
}
pub unsafe fn l_Lake_Toml_RBDict_values(
    mut v_00_u03b1_1773_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1774_: *mut crate::leanh::LeanObject,
    mut v_cmp_1775_: *mut crate::leanh::LeanObject,
    mut v_t_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lake_Toml_RBDict_values___redArg(v_t_1776_);
    return v___x_1777_;
}
pub unsafe fn l_Lake_Toml_RBDict_values___boxed(
    mut v_00_u03b1_1778_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1779_: *mut crate::leanh::LeanObject,
    mut v_cmp_1780_: *mut crate::leanh::LeanObject,
    mut v_t_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ =
        l_Lake_Toml_RBDict_values(v_00_u03b1_1778_, v_00_u03b2_1779_, v_cmp_1780_, v_t_1781_);
    crate::leanh::lean_dec_ref(v_cmp_1780_);
    return v_res_1782_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(
    mut v_00_u03b1_1783_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1784_: *mut crate::leanh::LeanObject,
    mut v_sz_1785_: usize,
    mut v_i_1786_: usize,
    mut v_bs_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_1785_, v_i_1786_, v_bs_1787_);
    return v___x_1788_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___boxed(
    mut v_00_u03b1_1789_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1790_: *mut crate::leanh::LeanObject,
    mut v_sz_1791_: *mut crate::leanh::LeanObject,
    mut v_i_1792_: *mut crate::leanh::LeanObject,
    mut v_bs_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1794_: usize = 0;
    let mut v_i_boxed_1795_: usize = 0;
    let mut v_res_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1794_ = crate::leanh::lean_unbox_usize(v_sz_1791_);
    crate::leanh::lean_dec(v_sz_1791_);
    v_i_boxed_1795_ = crate::leanh::lean_unbox_usize(v_i_1792_);
    crate::leanh::lean_dec(v_i_1792_);
    v_res_1796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(v_00_u03b1_1789_, v_00_u03b2_1790_, v_sz_boxed_1794_, v_i_boxed_1795_, v_bs_1793_);
    return v_res_1796_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(
    mut v_cmp_1797_: *mut crate::leanh::LeanObject,
    mut v_k_1798_: *mut crate::leanh::LeanObject,
    mut v_t_1799_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1806_: u8 = 0;
    let mut v___x_1808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1799_) == 0 {
                    v_k_1800_ = crate::leanh::lean_ctor_get(v_t_1799_, 1);
                    crate::leanh::lean_inc(v_k_1800_);
                    v_l_1801_ = crate::leanh::lean_ctor_get(v_t_1799_, 3);
                    crate::leanh::lean_inc(v_l_1801_);
                    v_r_1802_ = crate::leanh::lean_ctor_get(v_t_1799_, 4);
                    crate::leanh::lean_inc(v_r_1802_);
                    crate::leanh::lean_dec_ref_known(v_t_1799_, 5);
                    crate::leanh::lean_inc_ref(v_cmp_1797_);
                    crate::leanh::lean_inc(v_k_1798_);
                    v___x_1803_ = crate::leanh::lean_apply_2(v_cmp_1797_, v_k_1798_, v_k_1800_);
                    v___x_1804_ = (crate::leanh::lean_unbox(v___x_1803_) as u8);
                    match v___x_1804_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_1802_);
                            v_t_1799_ = v_l_1801_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_1802_);
                            crate::leanh::lean_dec(v_l_1801_);
                            crate::leanh::lean_dec(v_k_1798_);
                            crate::leanh::lean_dec_ref(v_cmp_1797_);
                            v___x_1806_ = 1;
                            return v___x_1806_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_1801_);
                            v_t_1799_ = v_r_1802_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_1798_);
                    crate::leanh::lean_dec_ref(v_cmp_1797_);
                    v___x_1808_ = 0;
                    return v___x_1808_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg___boxed(
    mut v_cmp_1809_: *mut crate::leanh::LeanObject,
    mut v_k_1810_: *mut crate::leanh::LeanObject,
    mut v_t_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1812_: u8 = 0;
    let mut v_r_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(
            v_cmp_1809_,
            v_k_1810_,
            v_t_1811_,
        );
    v_r_1813_ = crate::leanh::lean_box((v_res_1812_) as usize);
    return v_r_1813_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains___redArg(
    mut v_cmp_1814_: *mut crate::leanh::LeanObject,
    mut v_k_1815_: *mut crate::leanh::LeanObject,
    mut v_t_1816_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_indices_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: u8 = 0;
    v_indices_1817_ = crate::leanh::lean_ctor_get(v_t_1816_, 1);
    crate::leanh::lean_inc(v_indices_1817_);
    crate::leanh::lean_dec_ref(v_t_1816_);
    v___x_1818_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(
            v_cmp_1814_,
            v_k_1815_,
            v_indices_1817_,
        );
    return v___x_1818_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains___redArg___boxed(
    mut v_cmp_1819_: *mut crate::leanh::LeanObject,
    mut v_k_1820_: *mut crate::leanh::LeanObject,
    mut v_t_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1822_: u8 = 0;
    let mut v_r_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1822_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_1819_, v_k_1820_, v_t_1821_);
    v_r_1823_ = crate::leanh::lean_box((v_res_1822_) as usize);
    return v_r_1823_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains(
    mut v_00_u03b1_1824_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1825_: *mut crate::leanh::LeanObject,
    mut v_cmp_1826_: *mut crate::leanh::LeanObject,
    mut v_k_1827_: *mut crate::leanh::LeanObject,
    mut v_t_1828_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1829_: u8 = 0;
    v___x_1829_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_1826_, v_k_1827_, v_t_1828_);
    return v___x_1829_;
}
pub unsafe fn l_Lake_Toml_RBDict_contains___boxed(
    mut v_00_u03b1_1830_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1831_: *mut crate::leanh::LeanObject,
    mut v_cmp_1832_: *mut crate::leanh::LeanObject,
    mut v_k_1833_: *mut crate::leanh::LeanObject,
    mut v_t_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1835_: u8 = 0;
    let mut v_r_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1835_ = l_Lake_Toml_RBDict_contains(
        v_00_u03b1_1830_,
        v_00_u03b2_1831_,
        v_cmp_1832_,
        v_k_1833_,
        v_t_1834_,
    );
    v_r_1836_ = crate::leanh::lean_box((v_res_1835_) as usize);
    return v_r_1836_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(
    mut v_00_u03b1_1837_: *mut crate::leanh::LeanObject,
    mut v_cmp_1838_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1839_: *mut crate::leanh::LeanObject,
    mut v_k_1840_: *mut crate::leanh::LeanObject,
    mut v_t_1841_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1842_: u8 = 0;
    v___x_1842_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(
            v_cmp_1838_,
            v_k_1840_,
            v_t_1841_,
        );
    return v___x_1842_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___boxed(
    mut v_00_u03b1_1843_: *mut crate::leanh::LeanObject,
    mut v_cmp_1844_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1845_: *mut crate::leanh::LeanObject,
    mut v_k_1846_: *mut crate::leanh::LeanObject,
    mut v_t_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1848_: u8 = 0;
    let mut v_r_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(
        v_00_u03b1_1843_,
        v_cmp_1844_,
        v_00_u03b2_1845_,
        v_k_1846_,
        v_t_1847_,
    );
    v_r_1849_ = crate::leanh::lean_box((v_res_1848_) as usize);
    return v_r_1849_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(
    mut v_cmp_1850_: *mut crate::leanh::LeanObject,
    mut v_t_1851_: *mut crate::leanh::LeanObject,
    mut v_k_1852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: u8 = 0;
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1851_) == 0 {
                    v_k_1853_ = crate::leanh::lean_ctor_get(v_t_1851_, 1);
                    crate::leanh::lean_inc(v_k_1853_);
                    v_v_1854_ = crate::leanh::lean_ctor_get(v_t_1851_, 2);
                    crate::leanh::lean_inc(v_v_1854_);
                    v_l_1855_ = crate::leanh::lean_ctor_get(v_t_1851_, 3);
                    crate::leanh::lean_inc(v_l_1855_);
                    v_r_1856_ = crate::leanh::lean_ctor_get(v_t_1851_, 4);
                    crate::leanh::lean_inc(v_r_1856_);
                    crate::leanh::lean_dec_ref_known(v_t_1851_, 5);
                    crate::leanh::lean_inc_ref(v_cmp_1850_);
                    crate::leanh::lean_inc(v_k_1852_);
                    v___x_1857_ = crate::leanh::lean_apply_2(v_cmp_1850_, v_k_1852_, v_k_1853_);
                    v___x_1858_ = (crate::leanh::lean_unbox(v___x_1857_) as u8);
                    match v___x_1858_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_1856_);
                            crate::leanh::lean_dec(v_v_1854_);
                            v_t_1851_ = v_l_1855_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_1856_);
                            crate::leanh::lean_dec(v_l_1855_);
                            crate::leanh::lean_dec(v_k_1852_);
                            crate::leanh::lean_dec_ref(v_cmp_1850_);
                            v___x_1860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1860_, 0, v_v_1854_);
                            return v___x_1860_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_1855_);
                            crate::leanh::lean_dec(v_v_1854_);
                            v_t_1851_ = v_r_1856_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_1852_);
                    crate::leanh::lean_dec_ref(v_cmp_1850_);
                    v___x_1862_ = crate::leanh::lean_box(0);
                    return v___x_1862_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_findIdx_x3f___redArg(
    mut v_cmp_1863_: *mut crate::leanh::LeanObject,
    mut v_k_1864_: *mut crate::leanh::LeanObject,
    mut v_t_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_1866_ = crate::leanh::lean_ctor_get(v_t_1865_, 0);
                crate::leanh::lean_inc_ref(v_items_1866_);
                v_indices_1867_ = crate::leanh::lean_ctor_get(v_t_1865_, 1);
                crate::leanh::lean_inc(v_indices_1867_);
                crate::leanh::lean_dec_ref(v_t_1865_);
                v___x_1868_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_1863_, v_indices_1867_, v_k_1864_);
                if crate::leanh::lean_obj_tag(v___x_1868_) == 0 {
                    crate::leanh::lean_dec_ref(v_items_1866_);
                    v___x_1869_ = crate::leanh::lean_box(0);
                    return v___x_1869_;
                } else {
                    v_val_1870_ = crate::leanh::lean_ctor_get(v___x_1868_, 0);
                    v_isSharedCheck_1880_ = (!crate::leanh::lean_is_exclusive(v___x_1868_)) as u8;
                    if v_isSharedCheck_1880_ == 0 {
                        v___x_1872_ = v___x_1868_;
                        v_isShared_1873_ = v_isSharedCheck_1880_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1870_);
                        crate::leanh::lean_dec(v___x_1868_);
                        v___x_1872_ = crate::leanh::lean_box(0);
                        v_isShared_1873_ = v_isSharedCheck_1880_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1874_ = lean_array_get_size(v_items_1866_);
                crate::leanh::lean_dec_ref(v_items_1866_);
                v___x_1875_ = lean_nat_dec_lt(v_val_1870_, v___x_1874_);
                if v___x_1875_ == 0 {
                    crate::leanh::lean_del_object(v___x_1872_);
                    crate::leanh::lean_dec(v_val_1870_);
                    v___x_1876_ = crate::leanh::lean_box(0);
                    return v___x_1876_;
                } else {
                    if v_isShared_1873_ == 0 {
                        v___x_1878_ = v___x_1872_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_val_1870_);
                        v___x_1878_ = v_reuseFailAlloc_1879_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_findIdx_x3f(
    mut v_00_u03b1_1881_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1882_: *mut crate::leanh::LeanObject,
    mut v_cmp_1883_: *mut crate::leanh::LeanObject,
    mut v_k_1884_: *mut crate::leanh::LeanObject,
    mut v_t_1885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1886_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_1883_, v_k_1884_, v_t_1885_);
    return v___x_1886_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0(
    mut v_00_u03b1_1887_: *mut crate::leanh::LeanObject,
    mut v_cmp_1888_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_1889_: *mut crate::leanh::LeanObject,
    mut v_t_1890_: *mut crate::leanh::LeanObject,
    mut v_k_1891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1892_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_1888_, v_t_1890_, v_k_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lake_Toml_RBDict_findEntry_x3f___redArg(
    mut v_cmp_1893_: *mut crate::leanh::LeanObject,
    mut v_k_1894_: *mut crate::leanh::LeanObject,
    mut v_t_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v_items_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_t_1895_);
                v___x_1896_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_1893_, v_k_1894_, v_t_1895_);
                if crate::leanh::lean_obj_tag(v___x_1896_) == 0 {
                    crate::leanh::lean_dec_ref(v_t_1895_);
                    v___x_1897_ = crate::leanh::lean_box(0);
                    return v___x_1897_;
                } else {
                    v_val_1898_ = crate::leanh::lean_ctor_get(v___x_1896_, 0);
                    v_isSharedCheck_1907_ = (!crate::leanh::lean_is_exclusive(v___x_1896_)) as u8;
                    if v_isSharedCheck_1907_ == 0 {
                        v___x_1900_ = v___x_1896_;
                        v_isShared_1901_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1898_);
                        crate::leanh::lean_dec(v___x_1896_);
                        v___x_1900_ = crate::leanh::lean_box(0);
                        v_isShared_1901_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_items_1902_ = crate::leanh::lean_ctor_get(v_t_1895_, 0);
                crate::leanh::lean_inc_ref(v_items_1902_);
                crate::leanh::lean_dec_ref(v_t_1895_);
                v___x_1903_ = lean_array_fget(v_items_1902_, v_val_1898_);
                crate::leanh::lean_dec(v_val_1898_);
                crate::leanh::lean_dec_ref(v_items_1902_);
                if v_isShared_1901_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1900_, 0, v___x_1903_);
                    v___x_1905_ = v___x_1900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
                    v___x_1905_ = v_reuseFailAlloc_1906_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_findEntry_x3f(
    mut v_00_u03b1_1908_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1909_: *mut crate::leanh::LeanObject,
    mut v_cmp_1910_: *mut crate::leanh::LeanObject,
    mut v_k_1911_: *mut crate::leanh::LeanObject,
    mut v_t_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_1910_, v_k_1911_, v_t_1912_);
    return v___x_1913_;
}
pub unsafe fn l_Lake_Toml_RBDict_find_x3f___redArg(
    mut v_cmp_1914_: *mut crate::leanh::LeanObject,
    mut v_k_1915_: *mut crate::leanh::LeanObject,
    mut v_t_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v_snd_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1917_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_1914_, v_k_1915_, v_t_1916_);
                if crate::leanh::lean_obj_tag(v___x_1917_) == 0 {
                    v___x_1918_ = crate::leanh::lean_box(0);
                    return v___x_1918_;
                } else {
                    v_val_1919_ = crate::leanh::lean_ctor_get(v___x_1917_, 0);
                    v_isSharedCheck_1927_ = (!crate::leanh::lean_is_exclusive(v___x_1917_)) as u8;
                    if v_isSharedCheck_1927_ == 0 {
                        v___x_1921_ = v___x_1917_;
                        v_isShared_1922_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1919_);
                        crate::leanh::lean_dec(v___x_1917_);
                        v___x_1921_ = crate::leanh::lean_box(0);
                        v_isShared_1922_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1923_ = crate::leanh::lean_ctor_get(v_val_1919_, 1);
                crate::leanh::lean_inc(v_snd_1923_);
                crate::leanh::lean_dec(v_val_1919_);
                if v_isShared_1922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1921_, 0, v_snd_1923_);
                    v___x_1925_ = v___x_1921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1926_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_snd_1923_);
                    v___x_1925_ = v_reuseFailAlloc_1926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_find_x3f(
    mut v_00_u03b1_1928_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1929_: *mut crate::leanh::LeanObject,
    mut v_cmp_1930_: *mut crate::leanh::LeanObject,
    mut v_k_1931_: *mut crate::leanh::LeanObject,
    mut v_t_1932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1938_: u8 = 0;
    let mut v_snd_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1933_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_1930_, v_k_1931_, v_t_1932_);
                if crate::leanh::lean_obj_tag(v___x_1933_) == 0 {
                    v___x_1934_ = crate::leanh::lean_box(0);
                    return v___x_1934_;
                } else {
                    v_val_1935_ = crate::leanh::lean_ctor_get(v___x_1933_, 0);
                    v_isSharedCheck_1943_ = (!crate::leanh::lean_is_exclusive(v___x_1933_)) as u8;
                    if v_isSharedCheck_1943_ == 0 {
                        v___x_1937_ = v___x_1933_;
                        v_isShared_1938_ = v_isSharedCheck_1943_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1935_);
                        crate::leanh::lean_dec(v___x_1933_);
                        v___x_1937_ = crate::leanh::lean_box(0);
                        v_isShared_1938_ = v_isSharedCheck_1943_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1939_ = crate::leanh::lean_ctor_get(v_val_1935_, 1);
                crate::leanh::lean_inc(v_snd_1939_);
                crate::leanh::lean_dec(v_val_1935_);
                if v_isShared_1938_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1937_, 0, v_snd_1939_);
                    v___x_1941_ = v___x_1937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_snd_1939_);
                    v___x_1941_ = v_reuseFailAlloc_1942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_push___redArg(
    mut v_cmp_1944_: *mut crate::leanh::LeanObject,
    mut v_k_1945_: *mut crate::leanh::LeanObject,
    mut v_v_1946_: *mut crate::leanh::LeanObject,
    mut v_t_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_1948_ = crate::leanh::lean_ctor_get(v_t_1947_, 0);
                v_indices_1949_ = crate::leanh::lean_ctor_get(v_t_1947_, 1);
                v_isSharedCheck_1960_ = (!crate::leanh::lean_is_exclusive(v_t_1947_)) as u8;
                if v_isSharedCheck_1960_ == 0 {
                    v___x_1951_ = v_t_1947_;
                    v_isShared_1952_ = v_isSharedCheck_1960_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indices_1949_);
                    crate::leanh::lean_inc(v_items_1948_);
                    crate::leanh::lean_dec(v_t_1947_);
                    v___x_1951_ = crate::leanh::lean_box(0);
                    v_isShared_1952_ = v_isSharedCheck_1960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_k_1945_);
                v___x_1953_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1953_, 0, v_k_1945_);
                crate::leanh::lean_ctor_set(v___x_1953_, 1, v_v_1946_);
                crate::leanh::lean_inc_ref(v_items_1948_);
                v___x_1954_ = lean_array_push(v_items_1948_, v___x_1953_);
                v___x_1955_ = lean_array_get_size(v_items_1948_);
                crate::leanh::lean_dec_ref(v_items_1948_);
                v___x_1956_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_1944_, v_k_1945_, v___x_1955_, v_indices_1949_);
                if v_isShared_1952_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1951_, 1, v___x_1956_);
                    crate::leanh::lean_ctor_set(v___x_1951_, 0, v___x_1954_);
                    v___x_1958_ = v___x_1951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___x_1956_);
                    v___x_1958_ = v_reuseFailAlloc_1959_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1958_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_push(
    mut v_00_u03b1_1961_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1962_: *mut crate::leanh::LeanObject,
    mut v_cmp_1963_: *mut crate::leanh::LeanObject,
    mut v_k_1964_: *mut crate::leanh::LeanObject,
    mut v_v_1965_: *mut crate::leanh::LeanObject,
    mut v_t_1966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1967_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_1963_, v_k_1964_, v_v_1965_, v_t_1966_);
    return v___x_1967_;
}
pub unsafe fn l_Lake_Toml_RBDict_alter___redArg(
    mut v_cmp_1968_: *mut crate::leanh::LeanObject,
    mut v_k_1969_: *mut crate::leanh::LeanObject,
    mut v_f_1970_: *mut crate::leanh::LeanObject,
    mut v_t_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v_items_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2006_: u8 = 0;
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_t_1971_);
                crate::leanh::lean_inc(v_k_1969_);
                crate::leanh::lean_inc_ref(v_cmp_1968_);
                v___x_1972_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_1968_, v_k_1969_, v_t_1971_);
                if crate::leanh::lean_obj_tag(v___x_1972_) == 1 {
                    crate::leanh::lean_dec(v_k_1969_);
                    crate::leanh::lean_dec_ref(v_cmp_1968_);
                    v_val_1973_ = crate::leanh::lean_ctor_get(v___x_1972_, 0);
                    v_isSharedCheck_2008_ = (!crate::leanh::lean_is_exclusive(v___x_1972_)) as u8;
                    if v_isSharedCheck_2008_ == 0 {
                        v___x_1975_ = v___x_1972_;
                        v_isShared_1976_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1973_);
                        crate::leanh::lean_dec(v___x_1972_);
                        v___x_1975_ = crate::leanh::lean_box(0);
                        v_isShared_1976_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1972_);
                    v___x_2009_ = crate::leanh::lean_box(0);
                    v___x_2010_ = crate::leanh::lean_apply_1(v_f_1970_, v___x_2009_);
                    v___x_2011_ = l_Lake_Toml_RBDict_push___redArg(
                        v_cmp_1968_,
                        v_k_1969_,
                        v___x_2010_,
                        v_t_1971_,
                    );
                    return v___x_2011_;
                }
            }
            1 => {
                v_items_1977_ = crate::leanh::lean_ctor_get(v_t_1971_, 0);
                v_indices_1978_ = crate::leanh::lean_ctor_get(v_t_1971_, 1);
                v_isSharedCheck_2007_ = (!crate::leanh::lean_is_exclusive(v_t_1971_)) as u8;
                if v_isSharedCheck_2007_ == 0 {
                    v___x_1980_ = v_t_1971_;
                    v_isShared_1981_ = v_isSharedCheck_2007_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indices_1978_);
                    crate::leanh::lean_inc(v_items_1977_);
                    crate::leanh::lean_dec(v_t_1971_);
                    v___x_1980_ = crate::leanh::lean_box(0);
                    v_isShared_1981_ = v_isSharedCheck_2007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1982_ = lean_array_get_size(v_items_1977_);
                v___x_1983_ = lean_nat_dec_lt(v_val_1973_, v___x_1982_);
                if v___x_1983_ == 0 {
                    crate::leanh::lean_del_object(v___x_1975_);
                    crate::leanh::lean_dec(v_val_1973_);
                    crate::leanh::lean_dec(v_f_1970_);
                    if v_isShared_1981_ == 0 {
                        v___x_1985_ = v___x_1980_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1986_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_items_1977_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_indices_1978_);
                        v___x_1985_ = v_reuseFailAlloc_1986_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_v_1987_ = lean_array_fget(v_items_1977_, v_val_1973_);
                    v_fst_1988_ = crate::leanh::lean_ctor_get(v_v_1987_, 0);
                    v_snd_1989_ = crate::leanh::lean_ctor_get(v_v_1987_, 1);
                    v_isSharedCheck_2006_ = (!crate::leanh::lean_is_exclusive(v_v_1987_)) as u8;
                    if v_isSharedCheck_2006_ == 0 {
                        v___x_1991_ = v_v_1987_;
                        v_isShared_1992_ = v_isSharedCheck_2006_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1989_);
                        crate::leanh::lean_inc(v_fst_1988_);
                        crate::leanh::lean_dec(v_v_1987_);
                        v___x_1991_ = crate::leanh::lean_box(0);
                        v_isShared_1992_ = v_isSharedCheck_2006_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1985_;
            }
            4 => {
                v___x_1993_ = crate::leanh::lean_box(0);
                v_xs_x27_1994_ = lean_array_fset(v_items_1977_, v_val_1973_, v___x_1993_);
                if v_isShared_1976_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1975_, 0, v_snd_1989_);
                    v___x_1996_ = v___x_1975_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2005_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_snd_1989_);
                    v___x_1996_ = v_reuseFailAlloc_2005_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1997_ = crate::leanh::lean_apply_1(v_f_1970_, v___x_1996_);
                if v_isShared_1992_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1991_, 1, v___x_1997_);
                    v___x_1999_ = v___x_1991_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_fst_1988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_1997_);
                    v___x_1999_ = v_reuseFailAlloc_2004_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2000_ = lean_array_fset(v_xs_x27_1994_, v_val_1973_, v___x_1999_);
                crate::leanh::lean_dec(v_val_1973_);
                if v_isShared_1981_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1980_, 0, v___x_2000_);
                    v___x_2002_ = v___x_1980_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_indices_1978_);
                    v___x_2002_ = v_reuseFailAlloc_2003_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2002_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_alter(
    mut v_00_u03b1_2012_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2013_: *mut crate::leanh::LeanObject,
    mut v_cmp_2014_: *mut crate::leanh::LeanObject,
    mut v_k_2015_: *mut crate::leanh::LeanObject,
    mut v_f_2016_: *mut crate::leanh::LeanObject,
    mut v_t_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2018_ = l_Lake_Toml_RBDict_alter___redArg(v_cmp_2014_, v_k_2015_, v_f_2016_, v_t_2017_);
    return v___x_2018_;
}
pub unsafe fn l_Lake_Toml_RBDict_insert___redArg(
    mut v_cmp_2019_: *mut crate::leanh::LeanObject,
    mut v_k_2020_: *mut crate::leanh::LeanObject,
    mut v_v_2021_: *mut crate::leanh::LeanObject,
    mut v_t_2022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: u8 = 0;
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_unused_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_t_2022_);
                crate::leanh::lean_inc(v_k_2020_);
                crate::leanh::lean_inc_ref(v_cmp_2019_);
                v___x_2023_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_2019_, v_k_2020_, v_t_2022_);
                if crate::leanh::lean_obj_tag(v___x_2023_) == 1 {
                    v_val_2024_ = crate::leanh::lean_ctor_get(v___x_2023_, 0);
                    crate::leanh::lean_inc(v_val_2024_);
                    crate::leanh::lean_dec_ref_known(v___x_2023_, 1);
                    v_items_2025_ = crate::leanh::lean_ctor_get(v_t_2022_, 0);
                    v_indices_2026_ = crate::leanh::lean_ctor_get(v_t_2022_, 1);
                    v___x_2027_ = lean_array_get_size(v_items_2025_);
                    v___x_2028_ = lean_nat_dec_lt(v_val_2024_, v___x_2027_);
                    if v___x_2028_ == 0 {
                        crate::leanh::lean_dec(v_val_2024_);
                        v___x_2029_ = l_Lake_Toml_RBDict_push___redArg(
                            v_cmp_2019_,
                            v_k_2020_,
                            v_v_2021_,
                            v_t_2022_,
                        );
                        return v___x_2029_;
                    } else {
                        crate::leanh::lean_inc(v_indices_2026_);
                        crate::leanh::lean_inc_ref(v_items_2025_);
                        crate::leanh::lean_dec_ref(v_cmp_2019_);
                        v_isSharedCheck_2038_ = (!crate::leanh::lean_is_exclusive(v_t_2022_)) as u8;
                        if v_isSharedCheck_2038_ == 0 {
                            v_unused_2039_ = crate::leanh::lean_ctor_get(v_t_2022_, 1);
                            crate::leanh::lean_dec(v_unused_2039_);
                            v_unused_2040_ = crate::leanh::lean_ctor_get(v_t_2022_, 0);
                            crate::leanh::lean_dec(v_unused_2040_);
                            v___x_2031_ = v_t_2022_;
                            v_isShared_2032_ = v_isSharedCheck_2038_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_t_2022_);
                            v___x_2031_ = crate::leanh::lean_box(0);
                            v_isShared_2032_ = v_isSharedCheck_2038_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2023_);
                    v___x_2041_ = l_Lake_Toml_RBDict_push___redArg(
                        v_cmp_2019_,
                        v_k_2020_,
                        v_v_2021_,
                        v_t_2022_,
                    );
                    return v___x_2041_;
                }
            }
            1 => {
                v___x_2033_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2033_, 0, v_k_2020_);
                crate::leanh::lean_ctor_set(v___x_2033_, 1, v_v_2021_);
                v___x_2034_ = lean_array_fset(v_items_2025_, v_val_2024_, v___x_2033_);
                crate::leanh::lean_dec(v_val_2024_);
                if v_isShared_2032_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2031_, 0, v___x_2034_);
                    v___x_2036_ = v___x_2031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_indices_2026_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_insert(
    mut v_00_u03b1_2042_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2043_: *mut crate::leanh::LeanObject,
    mut v_cmp_2044_: *mut crate::leanh::LeanObject,
    mut v_k_2045_: *mut crate::leanh::LeanObject,
    mut v_v_2046_: *mut crate::leanh::LeanObject,
    mut v_t_2047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2048_ = l_Lake_Toml_RBDict_insert___redArg(v_cmp_2044_, v_k_2045_, v_v_2046_, v_t_2047_);
    return v___x_2048_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(
    mut v_cmp_2049_: *mut crate::leanh::LeanObject,
    mut v_as_2050_: *mut crate::leanh::LeanObject,
    mut v_i_2051_: usize,
    mut v_stop_2052_: usize,
    mut v_b_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: usize = 0;
    let mut v___x_2060_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2054_ = lean_usize_dec_eq(v_i_2051_, v_stop_2052_);
                if v___x_2054_ == 0 {
                    v___x_2055_ = lean_array_uget_borrowed(v_as_2050_, v_i_2051_);
                    v_fst_2056_ = crate::leanh::lean_ctor_get(v___x_2055_, 0);
                    v_snd_2057_ = crate::leanh::lean_ctor_get(v___x_2055_, 1);
                    crate::leanh::lean_inc(v_snd_2057_);
                    crate::leanh::lean_inc(v_fst_2056_);
                    crate::leanh::lean_inc_ref(v_cmp_2049_);
                    v___x_2058_ = l_Lake_Toml_RBDict_insert___redArg(
                        v_cmp_2049_,
                        v_fst_2056_,
                        v_snd_2057_,
                        v_b_2053_,
                    );
                    v___x_2059_ = 1usize;
                    v___x_2060_ = lean_usize_add(v_i_2051_, v___x_2059_);
                    v_i_2051_ = v___x_2060_;
                    v_b_2053_ = v___x_2058_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_cmp_2049_);
                    return v_b_2053_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg___boxed(
    mut v_cmp_2062_: *mut crate::leanh::LeanObject,
    mut v_as_2063_: *mut crate::leanh::LeanObject,
    mut v_i_2064_: *mut crate::leanh::LeanObject,
    mut v_stop_2065_: *mut crate::leanh::LeanObject,
    mut v_b_2066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2067_: usize = 0;
    let mut v_stop_boxed_2068_: usize = 0;
    let mut v_res_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2067_ = crate::leanh::lean_unbox_usize(v_i_2064_);
    crate::leanh::lean_dec(v_i_2064_);
    v_stop_boxed_2068_ = crate::leanh::lean_unbox_usize(v_stop_2065_);
    crate::leanh::lean_dec(v_stop_2065_);
    v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2062_, v_as_2063_, v_i_boxed_2067_, v_stop_boxed_2068_, v_b_2066_);
    crate::leanh::lean_dec_ref(v_as_2063_);
    return v_res_2069_;
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray___redArg(
    mut v_cmp_2070_: *mut crate::leanh::LeanObject,
    mut v_self_2071_: *mut crate::leanh::LeanObject,
    mut v_other_2072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    v___x_2073_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2074_ = lean_array_get_size(v_other_2072_);
    v___x_2075_ = lean_nat_dec_lt(v___x_2073_, v___x_2074_);
    if v___x_2075_ == 0 {
        crate::leanh::lean_dec_ref(v_cmp_2070_);
        return v_self_2071_;
    } else {
        let mut v___x_2076_: u8 = 0;
        v___x_2076_ = lean_nat_dec_le(v___x_2074_, v___x_2074_);
        if v___x_2076_ == 0 {
            if v___x_2075_ == 0 {
                crate::leanh::lean_dec_ref(v_cmp_2070_);
                return v_self_2071_;
            } else {
                let mut v___x_2077_: usize = 0;
                let mut v___x_2078_: usize = 0;
                let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2077_ = 0usize;
                v___x_2078_ = lean_usize_of_nat(v___x_2074_);
                v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2070_, v_other_2072_, v___x_2077_, v___x_2078_, v_self_2071_);
                return v___x_2079_;
            }
        } else {
            let mut v___x_2080_: usize = 0;
            let mut v___x_2081_: usize = 0;
            let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2080_ = 0usize;
            v___x_2081_ = lean_usize_of_nat(v___x_2074_);
            v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2070_, v_other_2072_, v___x_2080_, v___x_2081_, v_self_2071_);
            return v___x_2082_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray___redArg___boxed(
    mut v_cmp_2083_: *mut crate::leanh::LeanObject,
    mut v_self_2084_: *mut crate::leanh::LeanObject,
    mut v_other_2085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2086_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2083_, v_self_2084_, v_other_2085_);
    crate::leanh::lean_dec_ref(v_other_2085_);
    return v_res_2086_;
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray(
    mut v_00_u03b1_2087_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2088_: *mut crate::leanh::LeanObject,
    mut v_cmp_2089_: *mut crate::leanh::LeanObject,
    mut v_self_2090_: *mut crate::leanh::LeanObject,
    mut v_other_2091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2092_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2089_, v_self_2090_, v_other_2091_);
    return v___x_2092_;
}
pub unsafe fn l_Lake_Toml_RBDict_appendArray___boxed(
    mut v_00_u03b1_2093_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2094_: *mut crate::leanh::LeanObject,
    mut v_cmp_2095_: *mut crate::leanh::LeanObject,
    mut v_self_2096_: *mut crate::leanh::LeanObject,
    mut v_other_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2098_ = l_Lake_Toml_RBDict_appendArray(
        v_00_u03b1_2093_,
        v_00_u03b2_2094_,
        v_cmp_2095_,
        v_self_2096_,
        v_other_2097_,
    );
    crate::leanh::lean_dec_ref(v_other_2097_);
    return v_res_2098_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(
    mut v_00_u03b1_2099_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2100_: *mut crate::leanh::LeanObject,
    mut v_cmp_2101_: *mut crate::leanh::LeanObject,
    mut v_as_2102_: *mut crate::leanh::LeanObject,
    mut v_i_2103_: usize,
    mut v_stop_2104_: usize,
    mut v_b_2105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_2101_, v_as_2102_, v_i_2103_, v_stop_2104_, v_b_2105_);
    return v___x_2106_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___boxed(
    mut v_00_u03b1_2107_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2108_: *mut crate::leanh::LeanObject,
    mut v_cmp_2109_: *mut crate::leanh::LeanObject,
    mut v_as_2110_: *mut crate::leanh::LeanObject,
    mut v_i_2111_: *mut crate::leanh::LeanObject,
    mut v_stop_2112_: *mut crate::leanh::LeanObject,
    mut v_b_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2114_: usize = 0;
    let mut v_stop_boxed_2115_: usize = 0;
    let mut v_res_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2114_ = crate::leanh::lean_unbox_usize(v_i_2111_);
    crate::leanh::lean_dec(v_i_2111_);
    v_stop_boxed_2115_ = crate::leanh::lean_unbox_usize(v_stop_2112_);
    crate::leanh::lean_dec(v_stop_2112_);
    v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(v_00_u03b1_2107_, v_00_u03b2_2108_, v_cmp_2109_, v_as_2110_, v_i_boxed_2114_, v_stop_boxed_2115_, v_b_2113_);
    crate::leanh::lean_dec_ref(v_as_2110_);
    return v_res_2116_;
}
pub unsafe fn l_Lake_Toml_RBDict_instHAppendArrayProd___redArg(
    mut v_cmp_2117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2118_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_appendArray___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2118_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2118_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2118_, 2, v_cmp_2117_);
    return v___x_2118_;
}
pub unsafe fn l_Lake_Toml_RBDict_instHAppendArrayProd(
    mut v_00_u03b1_2119_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2120_: *mut crate::leanh::LeanObject,
    mut v_cmp_2121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2122_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_appendArray___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2122_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2122_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2122_, 2, v_cmp_2121_);
    return v___x_2122_;
}
pub unsafe fn l_Lake_Toml_RBDict_append___redArg(
    mut v_cmp_2123_: *mut crate::leanh::LeanObject,
    mut v_self_2124_: *mut crate::leanh::LeanObject,
    mut v_other_2125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_items_2126_ = crate::leanh::lean_ctor_get(v_other_2125_, 0);
    v___x_2127_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2123_, v_self_2124_, v_items_2126_);
    return v___x_2127_;
}
pub unsafe fn l_Lake_Toml_RBDict_append___redArg___boxed(
    mut v_cmp_2128_: *mut crate::leanh::LeanObject,
    mut v_self_2129_: *mut crate::leanh::LeanObject,
    mut v_other_2130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2131_ = l_Lake_Toml_RBDict_append___redArg(v_cmp_2128_, v_self_2129_, v_other_2130_);
    crate::leanh::lean_dec_ref(v_other_2130_);
    return v_res_2131_;
}
pub unsafe fn l_Lake_Toml_RBDict_append(
    mut v_00_u03b1_2132_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2133_: *mut crate::leanh::LeanObject,
    mut v_cmp_2134_: *mut crate::leanh::LeanObject,
    mut v_self_2135_: *mut crate::leanh::LeanObject,
    mut v_other_2136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_items_2137_ = crate::leanh::lean_ctor_get(v_other_2136_, 0);
    v___x_2138_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_2134_, v_self_2135_, v_items_2137_);
    return v___x_2138_;
}
pub unsafe fn l_Lake_Toml_RBDict_append___boxed(
    mut v_00_u03b1_2139_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2140_: *mut crate::leanh::LeanObject,
    mut v_cmp_2141_: *mut crate::leanh::LeanObject,
    mut v_self_2142_: *mut crate::leanh::LeanObject,
    mut v_other_2143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2144_ = l_Lake_Toml_RBDict_append(
        v_00_u03b1_2139_,
        v_00_u03b2_2140_,
        v_cmp_2141_,
        v_self_2142_,
        v_other_2143_,
    );
    crate::leanh::lean_dec_ref(v_other_2143_);
    return v_res_2144_;
}
pub unsafe fn l_Lake_Toml_RBDict_instAppend___redArg(
    mut v_cmp_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_append___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2146_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2146_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2146_, 2, v_cmp_2145_);
    return v___x_2146_;
}
pub unsafe fn l_Lake_Toml_RBDict_instAppend(
    mut v_00_u03b1_2147_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2148_: *mut crate::leanh::LeanObject,
    mut v_cmp_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2150_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_RBDict_append___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2150_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2150_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2150_, 2, v_cmp_2149_);
    return v___x_2150_;
}
pub unsafe fn l_Lake_Toml_RBDict_map___redArg___lam__0(
    mut v_f_2151_: *mut crate::leanh::LeanObject,
    mut v_x_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2157_: u8 = 0;
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2153_ = crate::leanh::lean_ctor_get(v_x_2152_, 0);
                v_snd_2154_ = crate::leanh::lean_ctor_get(v_x_2152_, 1);
                v_isSharedCheck_2162_ = (!crate::leanh::lean_is_exclusive(v_x_2152_)) as u8;
                if v_isSharedCheck_2162_ == 0 {
                    v___x_2156_ = v_x_2152_;
                    v_isShared_2157_ = v_isSharedCheck_2162_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2154_);
                    crate::leanh::lean_inc(v_fst_2153_);
                    crate::leanh::lean_dec(v_x_2152_);
                    v___x_2156_ = crate::leanh::lean_box(0);
                    v_isShared_2157_ = v_isSharedCheck_2162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_fst_2153_);
                v___x_2158_ = crate::leanh::lean_apply_2(v_f_2151_, v_fst_2153_, v_snd_2154_);
                if v_isShared_2157_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2156_, 1, v___x_2158_);
                    v___x_2160_ = v___x_2156_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2161_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_fst_2153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2158_);
                    v___x_2160_ = v_reuseFailAlloc_2161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_map___redArg(
    mut v_f_2182_: *mut crate::leanh::LeanObject,
    mut v_t_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___f_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2191_: usize = 0;
    let mut v___x_2192_: usize = 0;
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_2184_ = crate::leanh::lean_ctor_get(v_t_2183_, 0);
                v_indices_2185_ = crate::leanh::lean_ctor_get(v_t_2183_, 1);
                v_isSharedCheck_2197_ = (!crate::leanh::lean_is_exclusive(v_t_2183_)) as u8;
                if v_isSharedCheck_2197_ == 0 {
                    v___x_2187_ = v_t_2183_;
                    v_isShared_2188_ = v_isSharedCheck_2197_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indices_2185_);
                    crate::leanh::lean_inc(v_items_2184_);
                    crate::leanh::lean_dec(v_t_2183_);
                    v___x_2187_ = crate::leanh::lean_box(0);
                    v_isShared_2188_ = v_isSharedCheck_2197_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2189_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Toml_RBDict_map___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2189_, 0, v_f_2182_);
                v___x_2190_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
                v_sz_2191_ = lean_array_size(v_items_2184_);
                v___x_2192_ = 0usize;
                v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2190_,
                    v___f_2189_,
                    v_sz_2191_,
                    v___x_2192_,
                    v_items_2184_,
                );
                if v_isShared_2188_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2187_, 0, v___x_2193_);
                    v___x_2195_ = v___x_2187_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2196_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_indices_2185_);
                    v___x_2195_ = v_reuseFailAlloc_2196_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_map(
    mut v_00_u03b1_2198_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2199_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2200_: *mut crate::leanh::LeanObject,
    mut v_cmp_2201_: *mut crate::leanh::LeanObject,
    mut v_f_2202_: *mut crate::leanh::LeanObject,
    mut v_t_2203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2208_: u8 = 0;
    let mut v___f_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2211_: usize = 0;
    let mut v___x_2212_: usize = 0;
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_2204_ = crate::leanh::lean_ctor_get(v_t_2203_, 0);
                v_indices_2205_ = crate::leanh::lean_ctor_get(v_t_2203_, 1);
                v_isSharedCheck_2217_ = (!crate::leanh::lean_is_exclusive(v_t_2203_)) as u8;
                if v_isSharedCheck_2217_ == 0 {
                    v___x_2207_ = v_t_2203_;
                    v_isShared_2208_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indices_2205_);
                    crate::leanh::lean_inc(v_items_2204_);
                    crate::leanh::lean_dec(v_t_2203_);
                    v___x_2207_ = crate::leanh::lean_box(0);
                    v_isShared_2208_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2209_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Toml_RBDict_map___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2209_, 0, v_f_2202_);
                v___x_2210_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
                v_sz_2211_ = lean_array_size(v_items_2204_);
                v___x_2212_ = 0usize;
                v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2210_,
                    v___f_2209_,
                    v_sz_2211_,
                    v___x_2212_,
                    v_items_2204_,
                );
                if v_isShared_2208_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2207_, 0, v___x_2213_);
                    v___x_2215_ = v___x_2207_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_indices_2205_);
                    v___x_2215_ = v_reuseFailAlloc_2216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_map___boxed(
    mut v_00_u03b1_2218_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2219_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2220_: *mut crate::leanh::LeanObject,
    mut v_cmp_2221_: *mut crate::leanh::LeanObject,
    mut v_f_2222_: *mut crate::leanh::LeanObject,
    mut v_t_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_Lake_Toml_RBDict_map(
        v_00_u03b1_2218_,
        v_00_u03b2_2219_,
        v_00_u03b3_2220_,
        v_cmp_2221_,
        v_f_2222_,
        v_t_2223_,
    );
    crate::leanh::lean_dec_ref(v_cmp_2221_);
    return v_res_2224_;
}
pub unsafe fn l_Lake_Toml_RBDict_filter___redArg___lam__0(
    mut v_p_2225_: *mut crate::leanh::LeanObject,
    mut v_cmp_2226_: *mut crate::leanh::LeanObject,
    mut v_x1_2227_: *mut crate::leanh::LeanObject,
    mut v_x2_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    v_fst_2229_ = crate::leanh::lean_ctor_get(v_x2_2228_, 0);
    crate::leanh::lean_inc_n(v_fst_2229_, 2);
    v_snd_2230_ = crate::leanh::lean_ctor_get(v_x2_2228_, 1);
    crate::leanh::lean_inc_n(v_snd_2230_, 2);
    crate::leanh::lean_dec_ref(v_x2_2228_);
    v___x_2231_ = crate::leanh::lean_apply_2(v_p_2225_, v_fst_2229_, v_snd_2230_);
    v___x_2232_ = (crate::leanh::lean_unbox(v___x_2231_) as u8);
    if v___x_2232_ == 0 {
        crate::leanh::lean_dec(v_snd_2230_);
        crate::leanh::lean_dec(v_fst_2229_);
        crate::leanh::lean_dec_ref(v_cmp_2226_);
        return v_x1_2227_;
    } else {
        let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2233_ =
            l_Lake_Toml_RBDict_push___redArg(v_cmp_2226_, v_fst_2229_, v_snd_2230_, v_x1_2227_);
        return v___x_2233_;
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filter___redArg(
    mut v_cmp_2234_: *mut crate::leanh::LeanObject,
    mut v_p_2235_: *mut crate::leanh::LeanObject,
    mut v_t_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    v_items_2237_ = crate::leanh::lean_ctor_get(v_t_2236_, 0);
    crate::leanh::lean_inc_ref(v_items_2237_);
    crate::leanh::lean_dec_ref(v_t_2236_);
    v___x_2238_ = l_Lake_Toml_RBDict_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_cmp_2234_,
    );
    v___x_2239_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2240_ = lean_array_get_size(v_items_2237_);
    v___x_2241_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2242_ = lean_nat_dec_lt(v___x_2239_, v___x_2240_);
    if v___x_2242_ == 0 {
        crate::leanh::lean_dec_ref(v_items_2237_);
        crate::leanh::lean_dec_ref(v_p_2235_);
        crate::leanh::lean_dec_ref(v_cmp_2234_);
        return v___x_2238_;
    } else {
        let mut v___f_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: u8 = 0;
        v___f_2243_ = crate::leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_filter___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2243_, 0, v_p_2235_);
        crate::leanh::lean_closure_set(v___f_2243_, 1, v_cmp_2234_);
        v___x_2244_ = lean_nat_dec_le(v___x_2240_, v___x_2240_);
        if v___x_2244_ == 0 {
            if v___x_2242_ == 0 {
                crate::leanh::lean_dec_ref(v___f_2243_);
                crate::leanh::lean_dec_ref(v_items_2237_);
                return v___x_2238_;
            } else {
                let mut v___x_2245_: usize = 0;
                let mut v___x_2246_: usize = 0;
                let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2245_ = 0usize;
                v___x_2246_ = lean_usize_of_nat(v___x_2240_);
                v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2241_,
                    v___f_2243_,
                    v_items_2237_,
                    v___x_2245_,
                    v___x_2246_,
                    v___x_2238_,
                );
                return v___x_2247_;
            }
        } else {
            let mut v___x_2248_: usize = 0;
            let mut v___x_2249_: usize = 0;
            let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2248_ = 0usize;
            v___x_2249_ = lean_usize_of_nat(v___x_2240_);
            v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2241_,
                v___f_2243_,
                v_items_2237_,
                v___x_2248_,
                v___x_2249_,
                v___x_2238_,
            );
            return v___x_2250_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filter(
    mut v_00_u03b1_2251_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2252_: *mut crate::leanh::LeanObject,
    mut v_cmp_2253_: *mut crate::leanh::LeanObject,
    mut v_p_2254_: *mut crate::leanh::LeanObject,
    mut v_t_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: u8 = 0;
    v_items_2256_ = crate::leanh::lean_ctor_get(v_t_2255_, 0);
    crate::leanh::lean_inc_ref(v_items_2256_);
    crate::leanh::lean_dec_ref(v_t_2255_);
    v___x_2257_ = l_Lake_Toml_RBDict_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_cmp_2253_,
    );
    v___x_2258_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2259_ = lean_array_get_size(v_items_2256_);
    v___x_2260_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2261_ = lean_nat_dec_lt(v___x_2258_, v___x_2259_);
    if v___x_2261_ == 0 {
        crate::leanh::lean_dec_ref(v_items_2256_);
        crate::leanh::lean_dec_ref(v_p_2254_);
        crate::leanh::lean_dec_ref(v_cmp_2253_);
        return v___x_2257_;
    } else {
        let mut v___f_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2263_: u8 = 0;
        v___f_2262_ = crate::leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_filter___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2262_, 0, v_p_2254_);
        crate::leanh::lean_closure_set(v___f_2262_, 1, v_cmp_2253_);
        v___x_2263_ = lean_nat_dec_le(v___x_2259_, v___x_2259_);
        if v___x_2263_ == 0 {
            if v___x_2261_ == 0 {
                crate::leanh::lean_dec_ref(v___f_2262_);
                crate::leanh::lean_dec_ref(v_items_2256_);
                return v___x_2257_;
            } else {
                let mut v___x_2264_: usize = 0;
                let mut v___x_2265_: usize = 0;
                let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2264_ = 0usize;
                v___x_2265_ = lean_usize_of_nat(v___x_2259_);
                v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2260_,
                    v___f_2262_,
                    v_items_2256_,
                    v___x_2264_,
                    v___x_2265_,
                    v___x_2257_,
                );
                return v___x_2266_;
            }
        } else {
            let mut v___x_2267_: usize = 0;
            let mut v___x_2268_: usize = 0;
            let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2267_ = 0usize;
            v___x_2268_ = lean_usize_of_nat(v___x_2259_);
            v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2260_,
                v___f_2262_,
                v_items_2256_,
                v___x_2267_,
                v___x_2268_,
                v___x_2257_,
            );
            return v___x_2269_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filterMap___redArg___lam__0(
    mut v_f_2270_: *mut crate::leanh::LeanObject,
    mut v_cmp_2271_: *mut crate::leanh::LeanObject,
    mut v_x1_2272_: *mut crate::leanh::LeanObject,
    mut v_x2_2273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2274_ = crate::leanh::lean_ctor_get(v_x2_2273_, 0);
    crate::leanh::lean_inc_n(v_fst_2274_, 2);
    v_snd_2275_ = crate::leanh::lean_ctor_get(v_x2_2273_, 1);
    crate::leanh::lean_inc(v_snd_2275_);
    crate::leanh::lean_dec_ref(v_x2_2273_);
    v___x_2276_ = crate::leanh::lean_apply_2(v_f_2270_, v_fst_2274_, v_snd_2275_);
    if crate::leanh::lean_obj_tag(v___x_2276_) == 1 {
        let mut v_val_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2277_ = crate::leanh::lean_ctor_get(v___x_2276_, 0);
        crate::leanh::lean_inc(v_val_2277_);
        crate::leanh::lean_dec_ref_known(v___x_2276_, 1);
        v___x_2278_ =
            l_Lake_Toml_RBDict_push___redArg(v_cmp_2271_, v_fst_2274_, v_val_2277_, v_x1_2272_);
        return v___x_2278_;
    } else {
        crate::leanh::lean_dec(v___x_2276_);
        crate::leanh::lean_dec(v_fst_2274_);
        crate::leanh::lean_dec_ref(v_cmp_2271_);
        return v_x1_2272_;
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filterMap___redArg(
    mut v_cmp_2279_: *mut crate::leanh::LeanObject,
    mut v_f_2280_: *mut crate::leanh::LeanObject,
    mut v_t_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    v_items_2282_ = crate::leanh::lean_ctor_get(v_t_2281_, 0);
    crate::leanh::lean_inc_ref(v_items_2282_);
    crate::leanh::lean_dec_ref(v_t_2281_);
    v___x_2283_ = l_Lake_Toml_RBDict_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_cmp_2279_,
    );
    v___x_2284_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2285_ = lean_array_get_size(v_items_2282_);
    v___x_2286_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2287_ = lean_nat_dec_lt(v___x_2284_, v___x_2285_);
    if v___x_2287_ == 0 {
        crate::leanh::lean_dec_ref(v_items_2282_);
        crate::leanh::lean_dec_ref(v_f_2280_);
        crate::leanh::lean_dec_ref(v_cmp_2279_);
        return v___x_2283_;
    } else {
        let mut v___f_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: u8 = 0;
        v___f_2288_ = crate::leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_filterMap___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2288_, 0, v_f_2280_);
        crate::leanh::lean_closure_set(v___f_2288_, 1, v_cmp_2279_);
        v___x_2289_ = lean_nat_dec_le(v___x_2285_, v___x_2285_);
        if v___x_2289_ == 0 {
            if v___x_2287_ == 0 {
                crate::leanh::lean_dec_ref(v___f_2288_);
                crate::leanh::lean_dec_ref(v_items_2282_);
                return v___x_2283_;
            } else {
                let mut v___x_2290_: usize = 0;
                let mut v___x_2291_: usize = 0;
                let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2290_ = 0usize;
                v___x_2291_ = lean_usize_of_nat(v___x_2285_);
                v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2286_,
                    v___f_2288_,
                    v_items_2282_,
                    v___x_2290_,
                    v___x_2291_,
                    v___x_2283_,
                );
                return v___x_2292_;
            }
        } else {
            let mut v___x_2293_: usize = 0;
            let mut v___x_2294_: usize = 0;
            let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2293_ = 0usize;
            v___x_2294_ = lean_usize_of_nat(v___x_2285_);
            v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2286_,
                v___f_2288_,
                v_items_2282_,
                v___x_2293_,
                v___x_2294_,
                v___x_2283_,
            );
            return v___x_2295_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_filterMap(
    mut v_00_u03b1_2296_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2297_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2298_: *mut crate::leanh::LeanObject,
    mut v_cmp_2299_: *mut crate::leanh::LeanObject,
    mut v_f_2300_: *mut crate::leanh::LeanObject,
    mut v_t_2301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: u8 = 0;
    v_items_2302_ = crate::leanh::lean_ctor_get(v_t_2301_, 0);
    crate::leanh::lean_inc_ref(v_items_2302_);
    crate::leanh::lean_dec_ref(v_t_2301_);
    v___x_2303_ = l_Lake_Toml_RBDict_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_cmp_2299_,
    );
    v___x_2304_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2305_ = lean_array_get_size(v_items_2302_);
    v___x_2306_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v___x_2307_ = lean_nat_dec_lt(v___x_2304_, v___x_2305_);
    if v___x_2307_ == 0 {
        crate::leanh::lean_dec_ref(v_items_2302_);
        crate::leanh::lean_dec_ref(v_f_2300_);
        crate::leanh::lean_dec_ref(v_cmp_2299_);
        return v___x_2303_;
    } else {
        let mut v___f_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2309_: u8 = 0;
        v___f_2308_ = crate::leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_filterMap___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2308_, 0, v_f_2300_);
        crate::leanh::lean_closure_set(v___f_2308_, 1, v_cmp_2299_);
        v___x_2309_ = lean_nat_dec_le(v___x_2305_, v___x_2305_);
        if v___x_2309_ == 0 {
            if v___x_2307_ == 0 {
                crate::leanh::lean_dec_ref(v___f_2308_);
                crate::leanh::lean_dec_ref(v_items_2302_);
                return v___x_2303_;
            } else {
                let mut v___x_2310_: usize = 0;
                let mut v___x_2311_: usize = 0;
                let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2310_ = 0usize;
                v___x_2311_ = lean_usize_of_nat(v___x_2305_);
                v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2306_,
                    v___f_2308_,
                    v_items_2302_,
                    v___x_2310_,
                    v___x_2311_,
                    v___x_2303_,
                );
                return v___x_2312_;
            }
        } else {
            let mut v___x_2313_: usize = 0;
            let mut v___x_2314_: usize = 0;
            let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2313_ = 0usize;
            v___x_2314_ = lean_usize_of_nat(v___x_2305_);
            v___x_2315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2306_,
                v___f_2308_,
                v_items_2302_,
                v___x_2313_,
                v___x_2314_,
                v___x_2303_,
            );
            return v___x_2315_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_foldM___redArg___lam__0(
    mut v_f_2316_: *mut crate::leanh::LeanObject,
    mut v_s_2317_: *mut crate::leanh::LeanObject,
    mut v_x_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2319_ = crate::leanh::lean_ctor_get(v_x_2318_, 0);
    crate::leanh::lean_inc(v_fst_2319_);
    v_snd_2320_ = crate::leanh::lean_ctor_get(v_x_2318_, 1);
    crate::leanh::lean_inc(v_snd_2320_);
    crate::leanh::lean_dec_ref(v_x_2318_);
    v___x_2321_ = crate::leanh::lean_apply_3(v_f_2316_, v_s_2317_, v_fst_2319_, v_snd_2320_);
    return v___x_2321_;
}
pub unsafe fn l_Lake_Toml_RBDict_foldM___redArg(
    mut v_inst_2322_: *mut crate::leanh::LeanObject,
    mut v_f_2323_: *mut crate::leanh::LeanObject,
    mut v_init_2324_: *mut crate::leanh::LeanObject,
    mut v_t_2325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    v_items_2326_ = crate::leanh::lean_ctor_get(v_t_2325_, 0);
    crate::leanh::lean_inc_ref(v_items_2326_);
    crate::leanh::lean_dec_ref(v_t_2325_);
    v___x_2327_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2328_ = lean_array_get_size(v_items_2326_);
    v___x_2329_ = lean_nat_dec_lt(v___x_2327_, v___x_2328_);
    if v___x_2329_ == 0 {
        let mut v_toApplicative_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_items_2326_);
        crate::leanh::lean_dec(v_f_2323_);
        v_toApplicative_2330_ = crate::leanh::lean_ctor_get(v_inst_2322_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_2330_);
        crate::leanh::lean_dec_ref(v_inst_2322_);
        v_toPure_2331_ = crate::leanh::lean_ctor_get(v_toApplicative_2330_, 1);
        crate::leanh::lean_inc(v_toPure_2331_);
        crate::leanh::lean_dec_ref(v_toApplicative_2330_);
        v___x_2332_ =
            crate::leanh::lean_apply_2(v_toPure_2331_, crate::leanh::lean_box(0), v_init_2324_);
        return v___x_2332_;
    } else {
        let mut v___f_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: u8 = 0;
        v___f_2333_ = crate::leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2333_, 0, v_f_2323_);
        v___x_2334_ = lean_nat_dec_le(v___x_2328_, v___x_2328_);
        if v___x_2334_ == 0 {
            if v___x_2329_ == 0 {
                let mut v_toApplicative_2335_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_2333_);
                crate::leanh::lean_dec_ref(v_items_2326_);
                v_toApplicative_2335_ = crate::leanh::lean_ctor_get(v_inst_2322_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_2335_);
                crate::leanh::lean_dec_ref(v_inst_2322_);
                v_toPure_2336_ = crate::leanh::lean_ctor_get(v_toApplicative_2335_, 1);
                crate::leanh::lean_inc(v_toPure_2336_);
                crate::leanh::lean_dec_ref(v_toApplicative_2335_);
                v___x_2337_ = crate::leanh::lean_apply_2(
                    v_toPure_2336_,
                    crate::leanh::lean_box(0),
                    v_init_2324_,
                );
                return v___x_2337_;
            } else {
                let mut v___x_2338_: usize = 0;
                let mut v___x_2339_: usize = 0;
                let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2338_ = 0usize;
                v___x_2339_ = lean_usize_of_nat(v___x_2328_);
                v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_2322_,
                    v___f_2333_,
                    v_items_2326_,
                    v___x_2338_,
                    v___x_2339_,
                    v_init_2324_,
                );
                return v___x_2340_;
            }
        } else {
            let mut v___x_2341_: usize = 0;
            let mut v___x_2342_: usize = 0;
            let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2341_ = 0usize;
            v___x_2342_ = lean_usize_of_nat(v___x_2328_);
            v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_2322_,
                v___f_2333_,
                v_items_2326_,
                v___x_2341_,
                v___x_2342_,
                v_init_2324_,
            );
            return v___x_2343_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_foldM(
    mut v_m_2344_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2345_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2346_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2347_: *mut crate::leanh::LeanObject,
    mut v_cmp_2348_: *mut crate::leanh::LeanObject,
    mut v_inst_2349_: *mut crate::leanh::LeanObject,
    mut v_f_2350_: *mut crate::leanh::LeanObject,
    mut v_init_2351_: *mut crate::leanh::LeanObject,
    mut v_t_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    v_items_2353_ = crate::leanh::lean_ctor_get(v_t_2352_, 0);
    crate::leanh::lean_inc_ref(v_items_2353_);
    crate::leanh::lean_dec_ref(v_t_2352_);
    v___x_2354_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2355_ = lean_array_get_size(v_items_2353_);
    v___x_2356_ = lean_nat_dec_lt(v___x_2354_, v___x_2355_);
    if v___x_2356_ == 0 {
        let mut v_toApplicative_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_items_2353_);
        crate::leanh::lean_dec(v_f_2350_);
        v_toApplicative_2357_ = crate::leanh::lean_ctor_get(v_inst_2349_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_2357_);
        crate::leanh::lean_dec_ref(v_inst_2349_);
        v_toPure_2358_ = crate::leanh::lean_ctor_get(v_toApplicative_2357_, 1);
        crate::leanh::lean_inc(v_toPure_2358_);
        crate::leanh::lean_dec_ref(v_toApplicative_2357_);
        v___x_2359_ =
            crate::leanh::lean_apply_2(v_toPure_2358_, crate::leanh::lean_box(0), v_init_2351_);
        return v___x_2359_;
    } else {
        let mut v___f_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2361_: u8 = 0;
        v___f_2360_ = crate::leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2360_, 0, v_f_2350_);
        v___x_2361_ = lean_nat_dec_le(v___x_2355_, v___x_2355_);
        if v___x_2361_ == 0 {
            if v___x_2356_ == 0 {
                let mut v_toApplicative_2362_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_2360_);
                crate::leanh::lean_dec_ref(v_items_2353_);
                v_toApplicative_2362_ = crate::leanh::lean_ctor_get(v_inst_2349_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_2362_);
                crate::leanh::lean_dec_ref(v_inst_2349_);
                v_toPure_2363_ = crate::leanh::lean_ctor_get(v_toApplicative_2362_, 1);
                crate::leanh::lean_inc(v_toPure_2363_);
                crate::leanh::lean_dec_ref(v_toApplicative_2362_);
                v___x_2364_ = crate::leanh::lean_apply_2(
                    v_toPure_2363_,
                    crate::leanh::lean_box(0),
                    v_init_2351_,
                );
                return v___x_2364_;
            } else {
                let mut v___x_2365_: usize = 0;
                let mut v___x_2366_: usize = 0;
                let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2365_ = 0usize;
                v___x_2366_ = lean_usize_of_nat(v___x_2355_);
                v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_2349_,
                    v___f_2360_,
                    v_items_2353_,
                    v___x_2365_,
                    v___x_2366_,
                    v_init_2351_,
                );
                return v___x_2367_;
            }
        } else {
            let mut v___x_2368_: usize = 0;
            let mut v___x_2369_: usize = 0;
            let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2368_ = 0usize;
            v___x_2369_ = lean_usize_of_nat(v___x_2355_);
            v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_2349_,
                v___f_2360_,
                v_items_2353_,
                v___x_2368_,
                v___x_2369_,
                v_init_2351_,
            );
            return v___x_2370_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_foldM___boxed(
    mut v_m_2371_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2372_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2373_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2374_: *mut crate::leanh::LeanObject,
    mut v_cmp_2375_: *mut crate::leanh::LeanObject,
    mut v_inst_2376_: *mut crate::leanh::LeanObject,
    mut v_f_2377_: *mut crate::leanh::LeanObject,
    mut v_init_2378_: *mut crate::leanh::LeanObject,
    mut v_t_2379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2380_ = l_Lake_Toml_RBDict_foldM(
        v_m_2371_,
        v_00_u03c3_2372_,
        v_00_u03b1_2373_,
        v_00_u03b2_2374_,
        v_cmp_2375_,
        v_inst_2376_,
        v_f_2377_,
        v_init_2378_,
        v_t_2379_,
    );
    crate::leanh::lean_dec_ref(v_cmp_2375_);
    return v_res_2380_;
}
pub unsafe fn l_Lake_Toml_RBDict_fold___redArg(
    mut v_f_2381_: *mut crate::leanh::LeanObject,
    mut v_init_2382_: *mut crate::leanh::LeanObject,
    mut v_t_2383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    v___x_2384_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v_items_2385_ = crate::leanh::lean_ctor_get(v_t_2383_, 0);
    crate::leanh::lean_inc_ref(v_items_2385_);
    crate::leanh::lean_dec_ref(v_t_2383_);
    v___x_2386_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2387_ = lean_array_get_size(v_items_2385_);
    v___x_2388_ = lean_nat_dec_lt(v___x_2386_, v___x_2387_);
    if v___x_2388_ == 0 {
        crate::leanh::lean_dec_ref(v_items_2385_);
        crate::leanh::lean_dec(v_f_2381_);
        return v_init_2382_;
    } else {
        let mut v___f_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2390_: u8 = 0;
        v___f_2389_ = crate::leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2389_, 0, v_f_2381_);
        v___x_2390_ = lean_nat_dec_le(v___x_2387_, v___x_2387_);
        if v___x_2390_ == 0 {
            if v___x_2388_ == 0 {
                crate::leanh::lean_dec_ref(v___f_2389_);
                crate::leanh::lean_dec_ref(v_items_2385_);
                return v_init_2382_;
            } else {
                let mut v___x_2391_: usize = 0;
                let mut v___x_2392_: usize = 0;
                let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2391_ = 0usize;
                v___x_2392_ = lean_usize_of_nat(v___x_2387_);
                v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2384_,
                    v___f_2389_,
                    v_items_2385_,
                    v___x_2391_,
                    v___x_2392_,
                    v_init_2382_,
                );
                return v___x_2393_;
            }
        } else {
            let mut v___x_2394_: usize = 0;
            let mut v___x_2395_: usize = 0;
            let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2394_ = 0usize;
            v___x_2395_ = lean_usize_of_nat(v___x_2387_);
            v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2384_,
                v___f_2389_,
                v_items_2385_,
                v___x_2394_,
                v___x_2395_,
                v_init_2382_,
            );
            return v___x_2396_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_fold(
    mut v_00_u03c3_2397_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2398_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2399_: *mut crate::leanh::LeanObject,
    mut v_cmp_2400_: *mut crate::leanh::LeanObject,
    mut v_f_2401_: *mut crate::leanh::LeanObject,
    mut v_init_2402_: *mut crate::leanh::LeanObject,
    mut v_t_2403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u8 = 0;
    v___x_2404_ = l_Lake_Toml_RBDict_map___redArg___closed__9;
    v_items_2405_ = crate::leanh::lean_ctor_get(v_t_2403_, 0);
    crate::leanh::lean_inc_ref(v_items_2405_);
    crate::leanh::lean_dec_ref(v_t_2403_);
    v___x_2406_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2407_ = lean_array_get_size(v_items_2405_);
    v___x_2408_ = lean_nat_dec_lt(v___x_2406_, v___x_2407_);
    if v___x_2408_ == 0 {
        crate::leanh::lean_dec_ref(v_items_2405_);
        crate::leanh::lean_dec(v_f_2401_);
        return v_init_2402_;
    } else {
        let mut v___f_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2410_: u8 = 0;
        v___f_2409_ = crate::leanh::lean_alloc_closure(
            l_Lake_Toml_RBDict_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2409_, 0, v_f_2401_);
        v___x_2410_ = lean_nat_dec_le(v___x_2407_, v___x_2407_);
        if v___x_2410_ == 0 {
            if v___x_2408_ == 0 {
                crate::leanh::lean_dec_ref(v___f_2409_);
                crate::leanh::lean_dec_ref(v_items_2405_);
                return v_init_2402_;
            } else {
                let mut v___x_2411_: usize = 0;
                let mut v___x_2412_: usize = 0;
                let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2411_ = 0usize;
                v___x_2412_ = lean_usize_of_nat(v___x_2407_);
                v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2404_,
                    v___f_2409_,
                    v_items_2405_,
                    v___x_2411_,
                    v___x_2412_,
                    v_init_2402_,
                );
                return v___x_2413_;
            }
        } else {
            let mut v___x_2414_: usize = 0;
            let mut v___x_2415_: usize = 0;
            let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2414_ = 0usize;
            v___x_2415_ = lean_usize_of_nat(v___x_2407_);
            v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2404_,
                v___f_2409_,
                v_items_2405_,
                v___x_2414_,
                v___x_2415_,
                v_init_2402_,
            );
            return v___x_2416_;
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_fold___boxed(
    mut v_00_u03c3_2417_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2418_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2419_: *mut crate::leanh::LeanObject,
    mut v_cmp_2420_: *mut crate::leanh::LeanObject,
    mut v_f_2421_: *mut crate::leanh::LeanObject,
    mut v_init_2422_: *mut crate::leanh::LeanObject,
    mut v_t_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ = l_Lake_Toml_RBDict_fold(
        v_00_u03c3_2417_,
        v_00_u03b1_2418_,
        v_00_u03b2_2419_,
        v_cmp_2420_,
        v_f_2421_,
        v_init_2422_,
        v_t_2423_,
    );
    crate::leanh::lean_dec_ref(v_cmp_2420_);
    return v_res_2424_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Data_Dict(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Data_Dict(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Data_Dict(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_NameMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Fold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Data_Dict(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Data_Dict(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Toml_Data_Dict(builtin);
}
