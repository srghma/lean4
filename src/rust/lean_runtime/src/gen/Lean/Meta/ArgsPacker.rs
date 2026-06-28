// Lean compiler output
// Module: Lean.Meta.ArgsPacker
// Imports: Lean.Meta.AppBuilder Lean.Meta.PProdN Lean.Meta.ArgsPacker.Basic Init.Omega Init.While
use crate::r#gen::Init::Data::Array::Basic::{l_Array_instInhabited, l_Array_reverse___redArg};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::GetElem::l_List_get_x21Internal___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_str___override, l_List_lengthTR___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::CoreM::{l_Lean_Core_mkFreshUserName, l_Lean_mkArrow};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_appFnCleanup___redArg,
    l_Lean_Expr_beta, l_Lean_Expr_bindingBody_x21, l_Lean_Expr_bindingDomain_x21,
    l_Lean_Expr_bindingName_x21, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_const___override,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_getRevArg_x21, l_Lean_Expr_isApp, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isArrow,
    l_Lean_Expr_isConstOf, l_Lean_Expr_isForall, l_Lean_Expr_isLambda, l_Lean_Expr_sort___override,
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp5, l_Lean_mkApp6,
    l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkLambda, l_Lean_mkProj, l_Lean_mkSort,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_ofNat, l_Lean_Level_succ___override};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkAppM, l_Lean_Meta_mkAppOptM,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::ArgsPacker::Basic::{
    initialize_Lean_Meta_ArgsPacker_Basic, runtime_initialize_Lean_Meta_ArgsPacker_Basic,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instantiateForall,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_whnfD,
    l_Lean_Meta_whnfForall,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::PProdN::{
    initialize_Lean_Meta_PProdN, l_Lean_Meta_PProdN_mk, runtime_initialize_Lean_Meta_PProdN,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate1;
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_apply_7, lean_apply_8, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 83, 105, 103, 109, 97, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0_value) as *mut LeanObject,16079402598994914048 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Unary_packType___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [85, 110, 105, 116, 0],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_packType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_packType___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Unary_packType___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_packType___closed__0_value)
                as *mut LeanObject,
            9833841078580172006 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_packType___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_packType___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ArgsPacker_Unary_packType___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101, 114, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1_value: LeanStringObject<67> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101, 114, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101, 114, 46, 85, 110, 97, 114, 121, 46, 112, 97, 99, 107, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__2_value: LeanStringObject<57> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 56, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 116, 121, 112, 101, 46, 105, 115, 65, 112, 112, 79, 102, 65, 114, 105, 116, 121, 32, 96, 96, 80, 83, 105, 103, 109, 97, 32, 50, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__4_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 38, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 206, 178, 46, 105, 115, 76, 97, 109, 98, 100, 97, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6_value
) as *mut LeanObject;
static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0_value) as *mut LeanObject,16079402598994914048 as *mut LeanObject] };
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6_value) as *mut LeanObject,12627086414142437880 as *mut LeanObject] };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7_value
) as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Unary_pack___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [117, 110, 105, 116, 0],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_pack___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_pack___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_ArgsPacker_Unary_pack___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_packType___closed__0_value)
                as *mut LeanObject,
            9833841078580172006 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_ArgsPacker_Unary_pack___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_pack___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_pack___closed__0_value)
                as *mut LeanObject,
            565778312915565143 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_pack___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_pack___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ArgsPacker_Unary_pack___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__0_value: LeanStringObject<
    39,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101, 114,
        46, 85, 110, 97, 114, 121, 46, 117, 110, 99, 117, 114, 114, 121, 84, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__1_value: LeanStringObject<
    52,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 52,
    m_capacity: 52,
    m_length: 51,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 120, 115, 46, 115, 105, 122, 101, 32, 61, 32, 118, 97, 114, 78, 97, 109, 101, 115,
        46, 115, 105, 122, 101, 10, 32, 32, 32, 32, 32, 32, 0,
    ],
};
static mut l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__3_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 120, 0],
};
static mut l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__3_value)
                as *mut LeanObject,
            7699194985028780469 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [65, 114, 103, 115, 80, 97, 99, 107, 101, 114, 46, 66, 105, 110, 97, 114, 121, 46, 99, 97, 115, 101, 115, 79, 110, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 80, 83, 105, 103, 109, 97, 32, 116, 121, 112, 101, 44, 32, 103, 111, 116, 32, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 97, 115, 101, 115, 79, 110, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2_value
) as *mut LeanObject;
static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0_value) as *mut LeanObject,16079402598994914048 as *mut LeanObject] };
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2_value) as *mut LeanObject,6028345373435855329 as *mut LeanObject] };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101,
            114, 46, 85, 110, 97, 114, 121, 46, 117, 110, 99, 117, 114, 114, 121, 0,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__1_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [120, 0],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__1_value)
                as *mut LeanObject,
            13655884332201764339 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [99, 117, 114, 114, 121, 84, 121, 112, 101, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 80, 83, 105, 103, 109, 97, 32, 116, 121, 112, 101, 44, 32, 103, 111, 116, 32, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [99, 117, 114, 114, 121, 84, 121, 112, 101, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 102, 111, 114, 97, 108, 108, 32, 116, 121, 112, 101, 44, 32, 103, 111, 116, 32, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [99, 117, 114, 114, 121, 80, 83, 105, 103, 109, 97, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 80, 83, 105, 103, 109, 97, 32, 116, 121, 112, 101, 44, 32, 103, 111, 116, 32, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [99, 117, 114, 114, 121, 80, 83, 105, 103, 109, 97, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 111, 114, 97, 108, 108, 32, 116, 121, 112, 101, 44, 32, 103, 111, 116, 32, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 83, 117, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value) as *mut LeanObject,3874814940683362451 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0_value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [77, 117, 116, 117, 97, 108, 46, 117, 110, 112, 97, 99, 107, 84, 121, 112, 101, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 80, 83, 117, 109, 32, 116, 121, 112, 101, 44, 32, 103, 111, 116, 32, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1_value: LeanStringObject<45> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 97, 114, 103, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 50, 10, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101, 114, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101, 114, 46, 77, 117, 116, 117, 97, 108, 46, 112, 97, 99, 107, 46, 103, 111, 0]};
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 110, 114, 0]};
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3_value) as *mut LeanObject;
static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value) as *mut LeanObject,3874814940683362451 as *mut LeanObject] };
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3_value) as *mut LeanObject,5074275697139031241 as *mut LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__5_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 110, 108, 0]};
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__5_value) as *mut LeanObject;
static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value) as *mut LeanObject,3874814940683362451 as *mut LeanObject] };
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__5_value) as *mut LeanObject,9483969946820204814 as *mut LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1_value: LeanStringObject<56> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 120, 84, 121, 112, 101, 46, 105, 115, 65, 112, 112, 79, 102, 65, 114, 105, 116, 121, 32, 96, 96, 80, 83, 117, 109, 32, 50, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0_value: LeanStringObject<74> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101, 114, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101, 114, 46, 77, 117, 116, 117, 97, 108, 46, 109, 107, 67, 111, 100, 111, 109, 97, 105, 110, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value) as *mut LeanObject,3874814940683362451 as *mut LeanObject] };
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2_value) as *mut LeanObject,621621110004085670 as *mut LeanObject] };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0_value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [77, 117, 116, 117, 97, 108, 46, 117, 110, 99, 117, 114, 114, 121, 84, 121, 112, 101, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 102, 111, 114, 97, 108, 108, 32, 116, 121, 112, 101, 44, 32, 103, 111, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0_value: LeanStringObject<57> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 56, m_data: [77, 117, 116, 117, 97, 108, 46, 117, 110, 99, 117, 114, 114, 121, 84, 121, 112, 101, 78, 68, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 101, 113, 117, 97, 108, 32, 99, 111, 100, 111, 109, 97, 105, 110, 115, 44, 32, 98, 117, 116, 32, 103, 111, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [32, 97, 110, 100, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0_value: LeanStringObject<57> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 56, m_data: [77, 117, 116, 117, 97, 108, 46, 117, 110, 99, 117, 114, 114, 121, 84, 121, 112, 101, 78, 68, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 110, 111, 110, 45, 100, 101, 112, 101, 110, 100, 101, 110, 116, 32, 116, 121, 112, 101, 115, 44, 32, 103, 111, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [77, 117, 116, 117, 97, 108, 46, 99, 97, 115, 101, 115, 79, 110, 58, 32, 110, 111, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 115, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2_value: LeanStringObject<41> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [77, 117, 116, 117, 97, 108, 46, 99, 97, 115, 101, 115, 79, 110, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 80, 83, 117, 109, 32, 116, 121, 112, 101, 44, 32, 103, 111, 116, 32, 0]};
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0_value:
    LeanStringObject<44> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101, 114,
        46, 77, 117, 116, 117, 97, 108, 46, 117, 110, 99, 117, 114, 114, 121, 87, 105, 116, 104,
        84, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0_value: LeanStringObject<
    38,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101, 114,
        46, 77, 117, 116, 117, 97, 108, 46, 117, 110, 99, 117, 114, 114, 121, 78, 68, 0,
    ],
};
static mut l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ArgsPacker_pack___closed__0_value: LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101, 114,
        46, 112, 97, 99, 107, 0,
    ],
};
static mut l_Lean_Meta_ArgsPacker_pack___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_pack___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_pack___closed__1_value: LeanStringObject<51> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 102, 105, 100, 120, 32, 60, 32, 97, 114, 103, 115, 80, 97, 99, 107, 101, 114, 46,
        110, 117, 109, 70, 117, 110, 99, 115, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Meta_ArgsPacker_pack___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_pack___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_pack___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ArgsPacker_pack___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ArgsPacker_pack___closed__3_value: LeanStringObject<70> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 70,
    m_capacity: 70,
    m_length: 69,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 97, 114, 103, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 97, 114, 103, 115, 80,
        97, 99, 107, 101, 114, 46, 118, 97, 114, 78, 97, 109, 101, 115, 115, 91, 102, 105, 100,
        120, 93, 33, 46, 115, 105, 122, 101, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Meta_ArgsPacker_pack___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_pack___closed__3_value) as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_pack___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ArgsPacker_pack___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ArgsPacker_curryProj___closed__0_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            99, 117, 114, 114, 121, 80, 114, 111, 106, 58, 32, 105, 110, 100, 101, 120, 32, 111,
            117, 116, 32, 111, 102, 32, 114, 97, 110, 103, 101, 0,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_curryProj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_curryProj___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_curryProj___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ArgsPacker_curryProj___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ArgsPacker_curryProj___closed__2_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 114, 103, 115, 80, 97, 99, 107, 101,
            114, 46, 99, 117, 114, 114, 121, 80, 114, 111, 106, 0,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_curryProj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_curryProj___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_ArgsPacker_curryProj___closed__3_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            99, 117, 114, 114, 121, 80, 114, 111, 106, 58, 32, 101, 120, 112, 101, 99, 116, 101,
            100, 32, 102, 111, 114, 97, 108, 108, 32, 116, 121, 112, 101, 44, 32, 103, 111, 116,
            32, 123, 125, 0,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_curryProj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_curryProj___closed__3_value) as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_curryProj___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ArgsPacker_curryProj___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_ArgsPacker_curry___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ArgsPacker_curry___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0_value: LeanStringObject<51> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 51,
        m_capacity: 51,
        m_length: 50,
        m_data: [
            99, 117, 114, 114, 121, 80, 97, 114, 97, 109, 58, 32, 117, 110, 101, 120, 112, 101, 99,
            116, 101, 100, 32, 112, 97, 99, 107, 101, 100, 32, 109, 111, 116, 105, 118, 101, 44,
            32, 110, 111, 116, 32, 97, 32, 102, 111, 114, 97, 108, 108, 0,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            99, 117, 114, 114, 121, 80, 97, 114, 97, 109, 58, 32, 101, 120, 112, 101, 99, 116, 101,
            100, 32, 102, 111, 114, 97, 108, 108, 44, 32, 103, 111, 116, 32, 0,
        ],
    };
static mut l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0(
    mut v___x_3716_: *mut LeanObject,
    mut v_as_3717_: *mut LeanObject,
    mut v_sz_3718_: usize,
    mut v_i_3719_: usize,
    mut v_b_3720_: *mut LeanObject,
    mut v___y_3721_: *mut LeanObject,
    mut v___y_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3733_: u8 = 0;
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: u8 = 0;
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3744_: u8 = 0;
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: usize = 0;
    let mut v___x_3757_: usize = 0;
    let mut v_reuseFailAlloc_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3761_: u8 = 0;
    let mut v_isSharedCheck_3762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3726_ = lean_usize_dec_lt(v_i_3719_, v_sz_3718_);
                if v___x_3726_ == 0 {
                    v___x_3727_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3727_, 0, v_b_3720_);
                    return v___x_3727_;
                } else {
                    v_a_3728_ = lean_array_uget_borrowed(v_as_3717_, v_i_3719_);
                    lean_inc(v___y_3724_);
                    lean_inc_ref(v___y_3723_);
                    lean_inc(v___y_3722_);
                    lean_inc_ref(v___y_3721_);
                    lean_inc(v_a_3728_);
                    v___x_3729_ = lean_infer_type(
                        v_a_3728_,
                        v___y_3721_,
                        v___y_3722_,
                        v___y_3723_,
                        v___y_3724_,
                    );
                    if lean_obj_tag(v___x_3729_) == 0 {
                        v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
                        v_isSharedCheck_3762_ = (!lean_is_exclusive(v___x_3729_)) as u8;
                        if v_isSharedCheck_3762_ == 0 {
                            v___x_3732_ = v___x_3729_;
                            v_isShared_3733_ = v_isSharedCheck_3762_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3730_);
                            lean_dec(v___x_3729_);
                            v___x_3732_ = lean_box(0);
                            v_isShared_3733_ = v_isSharedCheck_3762_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_3720_);
                        return v___x_3729_;
                    }
                }
            }
            1 => {
                v___x_3734_ = lean_unsigned_to_nat(0);
                v___x_3735_ = lean_nat_dec_eq(v___x_3716_, v___x_3734_);
                v___x_3736_ = lean_unsigned_to_nat(1);
                v___x_3737_ = lean_mk_empty_array_with_capacity(v___x_3736_);
                lean_inc(v_a_3728_);
                v___x_3738_ = lean_array_push(v___x_3737_, v_a_3728_);
                v___x_3739_ = 1;
                v___x_3740_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_3738_,
                    v_b_3720_,
                    v___x_3735_,
                    v___x_3726_,
                    v___x_3735_,
                    v___x_3726_,
                    v___x_3739_,
                    v___y_3721_,
                    v___y_3722_,
                    v___y_3723_,
                    v___y_3724_,
                );
                lean_dec_ref(v___x_3738_);
                if lean_obj_tag(v___x_3740_) == 0 {
                    v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
                    v_isSharedCheck_3761_ = (!lean_is_exclusive(v___x_3740_)) as u8;
                    if v_isSharedCheck_3761_ == 0 {
                        v___x_3743_ = v___x_3740_;
                        v_isShared_3744_ = v_isSharedCheck_3761_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3741_);
                        lean_dec(v___x_3740_);
                        v___x_3743_ = lean_box(0);
                        v_isShared_3744_ = v_isSharedCheck_3761_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3732_);
                    lean_dec(v_a_3730_);
                    return v___x_3740_;
                }
            }
            2 => {
                v___x_3745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1;
                if v_isShared_3744_ == 0 {
                    lean_ctor_set_tag(v___x_3743_, 1);
                    lean_ctor_set(v___x_3743_, 0, v_a_3730_);
                    v___x_3747_ = v___x_3743_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3730_);
                    v___x_3747_ = v_reuseFailAlloc_3760_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3733_ == 0 {
                    lean_ctor_set_tag(v___x_3732_, 1);
                    lean_ctor_set(v___x_3732_, 0, v_a_3741_);
                    v___x_3749_ = v___x_3732_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3741_);
                    v___x_3749_ = v_reuseFailAlloc_3759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3750_ = lean_unsigned_to_nat(2);
                v___x_3751_ = lean_mk_empty_array_with_capacity(v___x_3750_);
                v___x_3752_ = lean_array_push(v___x_3751_, v___x_3747_);
                v___x_3753_ = lean_array_push(v___x_3752_, v___x_3749_);
                v___x_3754_ = l_Lean_Meta_mkAppOptM(
                    v___x_3745_,
                    v___x_3753_,
                    v___y_3721_,
                    v___y_3722_,
                    v___y_3723_,
                    v___y_3724_,
                );
                if lean_obj_tag(v___x_3754_) == 0 {
                    v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
                    lean_inc(v_a_3755_);
                    lean_dec_ref_known(v___x_3754_, 1);
                    v___x_3756_ = 1usize;
                    v___x_3757_ = lean_usize_add(v_i_3719_, v___x_3756_);
                    v_i_3719_ = v___x_3757_;
                    v_b_3720_ = v_a_3755_;
                    state = 0;
                    continue;
                } else {
                    return v___x_3754_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___boxed(
    mut v___x_3763_: *mut LeanObject,
    mut v_as_3764_: *mut LeanObject,
    mut v_sz_3765_: *mut LeanObject,
    mut v_i_3766_: *mut LeanObject,
    mut v_b_3767_: *mut LeanObject,
    mut v___y_3768_: *mut LeanObject,
    mut v___y_3769_: *mut LeanObject,
    mut v___y_3770_: *mut LeanObject,
    mut v___y_3771_: *mut LeanObject,
    mut v___y_3772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3773_: usize = 0;
    let mut v_i_boxed_3774_: usize = 0;
    let mut v_res_3775_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3773_ = lean_unbox_usize(v_sz_3765_);
    lean_dec(v_sz_3765_);
    v_i_boxed_3774_ = lean_unbox_usize(v_i_3766_);
    lean_dec(v_i_3766_);
    v_res_3775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0(v___x_3763_, v_as_3764_, v_sz_boxed_3773_, v_i_boxed_3774_, v_b_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
    lean_dec(v___y_3771_);
    lean_dec_ref(v___y_3770_);
    lean_dec(v___y_3769_);
    lean_dec_ref(v___y_3768_);
    lean_dec_ref(v_as_3764_);
    lean_dec(v___x_3763_);
    return v_res_3775_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2() -> *mut LeanObject {
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    v___x_3779_ = lean_box(0);
    v___x_3780_ = l_Lean_Meta_ArgsPacker_Unary_packType___closed__1;
    v___x_3781_ = l_Lean_mkConst(v___x_3780_, v___x_3779_);
    return v___x_3781_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_packType(
    mut v_xs_3782_: *mut LeanObject,
    mut v_a_3783_: *mut LeanObject,
    mut v_a_3784_: *mut LeanObject,
    mut v_a_3785_: *mut LeanObject,
    mut v_a_3786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: u8 = 0;
    v___x_3788_ = lean_array_get_size(v_xs_3782_);
    v___x_3789_ = lean_unsigned_to_nat(0);
    v___x_3790_ = lean_nat_dec_eq(v___x_3788_, v___x_3789_);
    if v___x_3790_ == 0 {
        let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
        v___x_3791_ = l_Lean_instInhabitedExpr;
        v___x_3792_ = lean_unsigned_to_nat(1);
        v___x_3793_ = lean_nat_sub(v___x_3788_, v___x_3792_);
        v___x_3794_ = lean_array_get_borrowed(v___x_3791_, v_xs_3782_, v___x_3793_);
        lean_dec(v___x_3793_);
        lean_inc(v_a_3786_);
        lean_inc_ref(v_a_3785_);
        lean_inc(v_a_3784_);
        lean_inc_ref(v_a_3783_);
        lean_inc(v___x_3794_);
        v___x_3795_ = lean_infer_type(v___x_3794_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_);
        if lean_obj_tag(v___x_3795_) == 0 {
            let mut v_a_3796_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
            let mut v_sz_3799_: usize = 0;
            let mut v___x_3800_: usize = 0;
            let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
            v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
            lean_inc(v_a_3796_);
            lean_dec_ref_known(v___x_3795_, 1);
            v___x_3797_ = lean_array_pop(v_xs_3782_);
            v___x_3798_ = l_Array_reverse___redArg(v___x_3797_);
            v_sz_3799_ = lean_array_size(v___x_3798_);
            v___x_3800_ = 0usize;
            v___x_3801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0(v___x_3788_, v___x_3798_, v_sz_3799_, v___x_3800_, v_a_3796_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_);
            lean_dec_ref(v___x_3798_);
            return v___x_3801_;
        } else {
            lean_dec_ref(v_xs_3782_);
            return v___x_3795_;
        }
    } else {
        let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_3782_);
        v___x_3802_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Unary_packType___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once),
            _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2,
        );
        v___x_3803_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3803_, 0, v___x_3802_);
        return v___x_3803_;
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_packType___boxed(
    mut v_xs_3804_: *mut LeanObject,
    mut v_a_3805_: *mut LeanObject,
    mut v_a_3806_: *mut LeanObject,
    mut v_a_3807_: *mut LeanObject,
    mut v_a_3808_: *mut LeanObject,
    mut v_a_3809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3810_: *mut LeanObject = core::ptr::null_mut();
    v_res_3810_ = l_Lean_Meta_ArgsPacker_Unary_packType(
        v_xs_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_,
    );
    lean_dec(v_a_3808_);
    lean_dec_ref(v_a_3807_);
    lean_dec(v_a_3806_);
    lean_dec_ref(v_a_3805_);
    return v_res_3810_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go_spec__0(
    mut v_msg_3811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Lean_instInhabitedExpr;
    v___x_3813_ = lean_panic_fn_borrowed(v___x_3812_, v_msg_3811_);
    return v___x_3813_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3()
-> *mut LeanObject {
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    v___x_3817_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__2;
    v___x_3818_ = lean_unsigned_to_nat(6);
    v___x_3819_ = lean_unsigned_to_nat(86);
    v___x_3820_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1;
    v___x_3821_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0;
    v___x_3822_ = l_mkPanicMessageWithDecl(
        v___x_3821_,
        v___x_3820_,
        v___x_3819_,
        v___x_3818_,
        v___x_3817_,
    );
    return v___x_3822_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5()
-> *mut LeanObject {
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    v___x_3824_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__4;
    v___x_3825_ = lean_unsigned_to_nat(6);
    v___x_3826_ = lean_unsigned_to_nat(90);
    v___x_3827_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1;
    v___x_3828_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0;
    v___x_3829_ = l_mkPanicMessageWithDecl(
        v___x_3828_,
        v___x_3827_,
        v___x_3826_,
        v___x_3825_,
        v___x_3824_,
    );
    return v___x_3829_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(
    mut v_args_3834_: *mut LeanObject,
    mut v_i_3835_: *mut LeanObject,
    mut v_type_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: u8 = 0;
    v___x_3837_ = lean_array_get_size(v_args_3834_);
    v___x_3838_ = lean_unsigned_to_nat(1);
    v___x_3839_ = lean_nat_sub(v___x_3837_, v___x_3838_);
    v___x_3840_ = lean_nat_dec_lt(v_i_3835_, v___x_3839_);
    lean_dec(v___x_3839_);
    if v___x_3840_ == 0 {
        let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
        v___x_3841_ = l_Lean_instInhabitedExpr;
        v___x_3842_ = lean_array_get_borrowed(v___x_3841_, v_args_3834_, v_i_3835_);
        lean_inc(v___x_3842_);
        return v___x_3842_;
    } else {
        let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3845_: u8 = 0;
        v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1;
        v___x_3844_ = lean_unsigned_to_nat(2);
        v___x_3845_ = l_Lean_Expr_isAppOfArity(v_type_3836_, v___x_3843_, v___x_3844_);
        if v___x_3845_ == 0 {
            let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
            v___x_3846_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3);
            v___x_3847_ = l_panic___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go_spec__0(v___x_3846_);
            return v___x_3847_;
        } else {
            let mut v_00_u03b2_3848_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3849_: u8 = 0;
            v_00_u03b2_3848_ = l_Lean_Expr_appArg_x21(v_type_3836_);
            v___x_3849_ = l_Lean_Expr_isLambda(v_00_u03b2_3848_);
            if v___x_3849_ == 0 {
                let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_00_u03b2_3848_);
                v___x_3850_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5);
                v___x_3851_ = l_panic___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go_spec__0(v___x_3850_);
                return v___x_3851_;
            } else {
                let mut v_arg_3852_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
                let mut v_us_3854_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
                let mut v_00_u03b1_3856_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
                let mut v_type_3858_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rest_3860_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
                v_arg_3852_ = lean_array_fget_borrowed(v_args_3834_, v_i_3835_);
                v___x_3853_ = l_Lean_Expr_getAppFn(v_type_3836_);
                v_us_3854_ = l_Lean_Expr_constLevels_x21(v___x_3853_);
                lean_dec_ref(v___x_3853_);
                v___x_3855_ = l_Lean_Expr_appFn_x21(v_type_3836_);
                v_00_u03b1_3856_ = l_Lean_Expr_appArg_x21(v___x_3855_);
                lean_dec_ref(v___x_3855_);
                v___x_3857_ = l_Lean_Expr_bindingBody_x21(v_00_u03b2_3848_);
                v_type_3858_ = lean_expr_instantiate1(v___x_3857_, v_arg_3852_);
                lean_dec_ref(v___x_3857_);
                v___x_3859_ = lean_nat_add(v_i_3835_, v___x_3838_);
                v_rest_3860_ =
                    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(
                        v_args_3834_,
                        v___x_3859_,
                        v_type_3858_,
                    );
                lean_dec_ref(v_type_3858_);
                lean_dec(v___x_3859_);
                v___x_3861_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7;
                v___x_3862_ = l_Lean_mkConst(v___x_3861_, v_us_3854_);
                lean_inc(v_arg_3852_);
                v___x_3863_ = l_Lean_mkApp4(
                    v___x_3862_,
                    v_00_u03b1_3856_,
                    v_00_u03b2_3848_,
                    v_arg_3852_,
                    v_rest_3860_,
                );
                return v___x_3863_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___boxed(
    mut v_args_3864_: *mut LeanObject,
    mut v_i_3865_: *mut LeanObject,
    mut v_type_3866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3867_: *mut LeanObject = core::ptr::null_mut();
    v_res_3867_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(
        v_args_3864_,
        v_i_3865_,
        v_type_3866_,
    );
    lean_dec_ref(v_type_3866_);
    lean_dec(v_i_3865_);
    lean_dec_ref(v_args_3864_);
    return v_res_3867_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2() -> *mut LeanObject {
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    v___x_3872_ = lean_box(0);
    v___x_3873_ = l_Lean_Meta_ArgsPacker_Unary_pack___closed__1;
    v___x_3874_ = l_Lean_mkConst(v___x_3873_, v___x_3872_);
    return v___x_3874_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_pack(
    mut v_type_3875_: *mut LeanObject,
    mut v_args_3876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: u8 = 0;
    v___x_3877_ = lean_array_get_size(v_args_3876_);
    v___x_3878_ = lean_unsigned_to_nat(0);
    v___x_3879_ = lean_nat_dec_eq(v___x_3877_, v___x_3878_);
    if v___x_3879_ == 0 {
        let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
        v___x_3880_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(
            v_args_3876_,
            v___x_3878_,
            v_type_3875_,
        );
        return v___x_3880_;
    } else {
        let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
        v___x_3881_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Unary_pack___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once),
            _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2,
        );
        return v___x_3881_;
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_pack___boxed(
    mut v_type_3882_: *mut LeanObject,
    mut v_args_3883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3884_: *mut LeanObject = core::ptr::null_mut();
    v_res_3884_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_type_3882_, v_args_3883_);
    lean_dec_ref(v_args_3883_);
    lean_dec_ref(v_type_3882_);
    return v_res_3884_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(
    mut v_arity_3885_: *mut LeanObject,
    mut v_a_3886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: u8 = 0;
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: u8 = 0;
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3887_ = lean_ctor_get(v_a_3886_, 0);
                v_snd_3888_ = lean_ctor_get(v_a_3886_, 1);
                v_isSharedCheck_3918_ = (!lean_is_exclusive(v_a_3886_)) as u8;
                if v_isSharedCheck_3918_ == 0 {
                    v___x_3890_ = v_a_3886_;
                    v_isShared_3891_ = v_isSharedCheck_3918_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3888_);
                    lean_inc(v_fst_3887_);
                    lean_dec(v_a_3886_);
                    v___x_3890_ = lean_box(0);
                    v_isShared_3891_ = v_isSharedCheck_3918_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3892_ = lean_array_get_size(v_snd_3888_);
                v___x_3893_ = lean_unsigned_to_nat(1);
                v___x_3894_ = lean_nat_add(v___x_3892_, v___x_3893_);
                v___x_3895_ = lean_nat_dec_lt(v___x_3894_, v_arity_3885_);
                lean_dec(v___x_3894_);
                if v___x_3895_ == 0 {
                    if v_isShared_3891_ == 0 {
                        v___x_3897_ = v___x_3890_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_fst_3887_);
                        lean_ctor_set(v_reuseFailAlloc_3899_, 1, v_snd_3888_);
                        v___x_3897_ = v_reuseFailAlloc_3899_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3900_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7;
                    v___x_3901_ = lean_unsigned_to_nat(4);
                    v___x_3902_ = l_Lean_Expr_isAppOfArity(v_fst_3887_, v___x_3900_, v___x_3901_);
                    if v___x_3902_ == 0 {
                        lean_del_object(v___x_3890_);
                        lean_dec(v_snd_3888_);
                        lean_dec(v_fst_3887_);
                        v___x_3903_ = lean_box(0);
                        return v___x_3903_;
                    } else {
                        v___x_3904_ = lean_unsigned_to_nat(2);
                        v___x_3905_ = l_Lean_Expr_getAppNumArgs(v_fst_3887_);
                        v___x_3906_ = lean_nat_sub(v___x_3905_, v___x_3904_);
                        v___x_3907_ = lean_nat_sub(v___x_3906_, v___x_3893_);
                        lean_dec(v___x_3906_);
                        v___x_3908_ = l_Lean_Expr_getRevArg_x21(v_fst_3887_, v___x_3907_);
                        v___x_3909_ = lean_array_push(v_snd_3888_, v___x_3908_);
                        v___x_3910_ = lean_unsigned_to_nat(3);
                        v___x_3911_ = lean_nat_sub(v___x_3905_, v___x_3910_);
                        lean_dec(v___x_3905_);
                        v___x_3912_ = lean_nat_sub(v___x_3911_, v___x_3893_);
                        lean_dec(v___x_3911_);
                        v___x_3913_ = l_Lean_Expr_getRevArg_x21(v_fst_3887_, v___x_3912_);
                        lean_dec(v_fst_3887_);
                        if v_isShared_3891_ == 0 {
                            lean_ctor_set(v___x_3890_, 1, v___x_3909_);
                            lean_ctor_set(v___x_3890_, 0, v___x_3913_);
                            v___x_3915_ = v___x_3890_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3913_);
                            lean_ctor_set(v_reuseFailAlloc_3917_, 1, v___x_3909_);
                            v___x_3915_ = v_reuseFailAlloc_3917_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3898_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3898_, 0, v___x_3897_);
                return v___x_3898_;
            }
            3 => {
                v_a_3886_ = v___x_3915_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg___boxed(
    mut v_arity_3919_: *mut LeanObject,
    mut v_a_3920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3921_: *mut LeanObject = core::ptr::null_mut();
    v_res_3921_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_3919_, v_a_3920_);
    lean_dec(v_arity_3919_);
    return v_res_3921_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_unpack(
    mut v_arity_3926_: *mut LeanObject,
    mut v_e_3927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: u8 = 0;
    let mut v_args_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3937_: u8 = 0;
    let mut v_fst_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3944_: u8 = 0;
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3928_ = lean_unsigned_to_nat(0);
                v___x_3929_ = lean_nat_dec_eq(v_arity_3926_, v___x_3928_);
                if v___x_3929_ == 0 {
                    v_args_3930_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
                    v___x_3931_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3931_, 0, v_e_3927_);
                    lean_ctor_set(v___x_3931_, 1, v_args_3930_);
                    v___x_3932_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_3926_, v___x_3931_);
                    if lean_obj_tag(v___x_3932_) == 0 {
                        v___x_3933_ = lean_box(0);
                        return v___x_3933_;
                    } else {
                        v_val_3934_ = lean_ctor_get(v___x_3932_, 0);
                        v_isSharedCheck_3944_ = (!lean_is_exclusive(v___x_3932_)) as u8;
                        if v_isSharedCheck_3944_ == 0 {
                            v___x_3936_ = v___x_3932_;
                            v_isShared_3937_ = v_isSharedCheck_3944_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_3934_);
                            lean_dec(v___x_3932_);
                            v___x_3936_ = lean_box(0);
                            v_isShared_3937_ = v_isSharedCheck_3944_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_3927_);
                    v___x_3945_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1;
                    return v___x_3945_;
                }
            }
            1 => {
                v_fst_3938_ = lean_ctor_get(v_val_3934_, 0);
                lean_inc(v_fst_3938_);
                v_snd_3939_ = lean_ctor_get(v_val_3934_, 1);
                lean_inc(v_snd_3939_);
                lean_dec(v_val_3934_);
                v___x_3940_ = lean_array_push(v_snd_3939_, v_fst_3938_);
                if v_isShared_3937_ == 0 {
                    lean_ctor_set(v___x_3936_, 0, v___x_3940_);
                    v___x_3942_ = v___x_3936_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
                    v___x_3942_ = v_reuseFailAlloc_3943_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3942_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_unpack___boxed(
    mut v_arity_3946_: *mut LeanObject,
    mut v_e_3947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3948_: *mut LeanObject = core::ptr::null_mut();
    v_res_3948_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v_arity_3946_, v_e_3947_);
    lean_dec(v_arity_3946_);
    return v_res_3948_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(
    mut v_arity_3949_: *mut LeanObject,
    mut v_inst_3950_: *mut LeanObject,
    mut v_a_3951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    v___x_3952_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_3949_, v_a_3951_);
    return v___x_3952_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___boxed(
    mut v_arity_3953_: *mut LeanObject,
    mut v_inst_3954_: *mut LeanObject,
    mut v_a_3955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3956_: *mut LeanObject = core::ptr::null_mut();
    v_res_3956_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(
            v_arity_3953_,
            v_inst_3954_,
            v_a_3955_,
        );
    lean_dec(v_arity_3953_);
    return v_res_3956_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(
    mut v_upperBound_3957_: *mut LeanObject,
    mut v_a_3958_: *mut LeanObject,
    mut v_b_3959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3960_: u8 = 0;
    let mut v_fst_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3965_: u8 = 0;
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3960_ = lean_nat_dec_lt(v_a_3958_, v_upperBound_3957_);
                if v___x_3960_ == 0 {
                    lean_dec(v_a_3958_);
                    return v_b_3959_;
                } else {
                    v_fst_3961_ = lean_ctor_get(v_b_3959_, 0);
                    v_snd_3962_ = lean_ctor_get(v_b_3959_, 1);
                    v_isSharedCheck_3977_ = (!lean_is_exclusive(v_b_3959_)) as u8;
                    if v_isSharedCheck_3977_ == 0 {
                        v___x_3964_ = v_b_3959_;
                        v_isShared_3965_ = v_isSharedCheck_3977_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3962_);
                        lean_inc(v_fst_3961_);
                        lean_dec(v_b_3959_);
                        v___x_3964_ = lean_box(0);
                        v_isShared_3965_ = v_isSharedCheck_3977_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3966_ = lean_unsigned_to_nat(0);
                v___x_3967_ = lean_unsigned_to_nat(1);
                v___x_3968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1;
                lean_inc(v_snd_3962_);
                v___x_3969_ = l_Lean_mkProj(v___x_3968_, v___x_3966_, v_snd_3962_);
                v___x_3970_ = lean_array_push(v_fst_3961_, v___x_3969_);
                v___x_3971_ = l_Lean_mkProj(v___x_3968_, v___x_3967_, v_snd_3962_);
                if v_isShared_3965_ == 0 {
                    lean_ctor_set(v___x_3964_, 1, v___x_3971_);
                    lean_ctor_set(v___x_3964_, 0, v___x_3970_);
                    v___x_3973_ = v___x_3964_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3970_);
                    lean_ctor_set(v_reuseFailAlloc_3976_, 1, v___x_3971_);
                    v___x_3973_ = v_reuseFailAlloc_3976_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3974_ = lean_nat_add(v_a_3958_, v___x_3967_);
                lean_dec(v_a_3958_);
                v_a_3958_ = v___x_3974_;
                v_b_3959_ = v___x_3973_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg___boxed(
    mut v_upperBound_3978_: *mut LeanObject,
    mut v_a_3979_: *mut LeanObject,
    mut v_b_3980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3981_: *mut LeanObject = core::ptr::null_mut();
    v_res_3981_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v_upperBound_3978_, v_a_3979_, v_b_3980_);
    lean_dec(v_upperBound_3978_);
    return v_res_3981_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(
    mut v_t_3982_: *mut LeanObject,
    mut v_arity_3983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: u8 = 0;
    v___x_3984_ = lean_unsigned_to_nat(0);
    v___x_3985_ = lean_nat_dec_eq(v_arity_3983_, v___x_3984_);
    if v___x_3985_ == 0 {
        let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
        let mut v_result_3988_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_3991_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_3992_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
        v___x_3986_ = lean_unsigned_to_nat(1);
        v___x_3987_ = lean_nat_sub(v_arity_3983_, v___x_3986_);
        v_result_3988_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
        v___x_3989_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3989_, 0, v_result_3988_);
        lean_ctor_set(v___x_3989_, 1, v_t_3982_);
        v___x_3990_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v___x_3987_, v___x_3984_, v___x_3989_);
        lean_dec(v___x_3987_);
        v_fst_3991_ = lean_ctor_get(v___x_3990_, 0);
        lean_inc(v_fst_3991_);
        v_snd_3992_ = lean_ctor_get(v___x_3990_, 1);
        lean_inc(v_snd_3992_);
        lean_dec_ref(v___x_3990_);
        v___x_3993_ = lean_array_push(v_fst_3991_, v_snd_3992_);
        return v___x_3993_;
    } else {
        let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_t_3982_);
        v___x_3994_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
        return v___x_3994_;
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___boxed(
    mut v_t_3995_: *mut LeanObject,
    mut v_arity_3996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3997_: *mut LeanObject = core::ptr::null_mut();
    v_res_3997_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(
        v_t_3995_,
        v_arity_3996_,
    );
    lean_dec(v_arity_3996_);
    return v_res_3997_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(
    mut v_upperBound_3998_: *mut LeanObject,
    mut v_inst_3999_: *mut LeanObject,
    mut v_R_4000_: *mut LeanObject,
    mut v_a_4001_: *mut LeanObject,
    mut v_b_4002_: *mut LeanObject,
    mut v_c_4003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    v___x_4004_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v_upperBound_3998_, v_a_4001_, v_b_4002_);
    return v___x_4004_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___boxed(
    mut v_upperBound_4005_: *mut LeanObject,
    mut v_inst_4006_: *mut LeanObject,
    mut v_R_4007_: *mut LeanObject,
    mut v_a_4008_: *mut LeanObject,
    mut v_b_4009_: *mut LeanObject,
    mut v_c_4010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4011_: *mut LeanObject = core::ptr::null_mut();
    v_res_4011_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(v_upperBound_4005_, v_inst_4006_, v_R_4007_, v_a_4008_, v_b_4009_, v_c_4010_);
    lean_dec(v_upperBound_4005_);
    return v_res_4011_;
}
pub unsafe fn l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(
    mut v_msg_4013_: *mut LeanObject,
    mut v___y_4014_: *mut LeanObject,
    mut v___y_4015_: *mut LeanObject,
    mut v___y_4016_: *mut LeanObject,
    mut v___y_4017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665__overap_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    v___f_4019_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0;
    v___x_665__overap_4020_ = lean_panic_fn_borrowed(v___f_4019_, v_msg_4013_);
    lean_inc(v___y_4017_);
    lean_inc_ref(v___y_4016_);
    lean_inc(v___y_4015_);
    lean_inc_ref(v___y_4014_);
    v___x_4021_ = lean_apply_5(
        v___x_665__overap_4020_,
        v___y_4014_,
        v___y_4015_,
        v___y_4016_,
        v___y_4017_,
        lean_box(0),
    );
    return v___x_4021_;
}
pub unsafe fn l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___boxed(
    mut v_msg_4022_: *mut LeanObject,
    mut v___y_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
    mut v___y_4026_: *mut LeanObject,
    mut v___y_4027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4028_: *mut LeanObject = core::ptr::null_mut();
    v_res_4028_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(
        v_msg_4022_,
        v___y_4023_,
        v___y_4024_,
        v___y_4025_,
        v___y_4026_,
    );
    lean_dec(v___y_4026_);
    lean_dec_ref(v___y_4025_);
    lean_dec(v___y_4024_);
    lean_dec_ref(v___y_4023_);
    return v_res_4028_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(
    mut v_k_4029_: *mut LeanObject,
    mut v_b_4030_: *mut LeanObject,
    mut v_c_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
    mut v___y_4033_: *mut LeanObject,
    mut v___y_4034_: *mut LeanObject,
    mut v___y_4035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4035_);
    lean_inc_ref(v___y_4034_);
    lean_inc(v___y_4033_);
    lean_inc_ref(v___y_4032_);
    v___x_4037_ = lean_apply_7(
        v_k_4029_,
        v_b_4030_,
        v_c_4031_,
        v___y_4032_,
        v___y_4033_,
        v___y_4034_,
        v___y_4035_,
        lean_box(0),
    );
    return v___x_4037_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0___boxed(
    mut v_k_4038_: *mut LeanObject,
    mut v_b_4039_: *mut LeanObject,
    mut v_c_4040_: *mut LeanObject,
    mut v___y_4041_: *mut LeanObject,
    mut v___y_4042_: *mut LeanObject,
    mut v___y_4043_: *mut LeanObject,
    mut v___y_4044_: *mut LeanObject,
    mut v___y_4045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4046_: *mut LeanObject = core::ptr::null_mut();
    v_res_4046_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(v_k_4038_, v_b_4039_, v_c_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
    lean_dec(v___y_4044_);
    lean_dec_ref(v___y_4043_);
    lean_dec(v___y_4042_);
    lean_dec_ref(v___y_4041_);
    return v_res_4046_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(
    mut v_type_4047_: *mut LeanObject,
    mut v_maxFVars_x3f_4048_: *mut LeanObject,
    mut v_k_4049_: *mut LeanObject,
    mut v_cleanupAnnotations_4050_: u8,
    mut v_whnfType_4051_: u8,
    mut v___y_4052_: *mut LeanObject,
    mut v___y_4053_: *mut LeanObject,
    mut v___y_4054_: *mut LeanObject,
    mut v___y_4055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut v_a_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4070_: u8 = 0;
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4057_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_4057_, 0, v_k_4049_);
                v___x_4058_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_4047_,
                    v_maxFVars_x3f_4048_,
                    v___f_4057_,
                    v_cleanupAnnotations_4050_,
                    v_whnfType_4051_,
                    v___y_4052_,
                    v___y_4053_,
                    v___y_4054_,
                    v___y_4055_,
                );
                if lean_obj_tag(v___x_4058_) == 0 {
                    v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
                    v_isSharedCheck_4066_ = (!lean_is_exclusive(v___x_4058_)) as u8;
                    if v_isSharedCheck_4066_ == 0 {
                        v___x_4061_ = v___x_4058_;
                        v_isShared_4062_ = v_isSharedCheck_4066_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4059_);
                        lean_dec(v___x_4058_);
                        v___x_4061_ = lean_box(0);
                        v_isShared_4062_ = v_isSharedCheck_4066_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4067_ = lean_ctor_get(v___x_4058_, 0);
                    v_isSharedCheck_4074_ = (!lean_is_exclusive(v___x_4058_)) as u8;
                    if v_isSharedCheck_4074_ == 0 {
                        v___x_4069_ = v___x_4058_;
                        v_isShared_4070_ = v_isSharedCheck_4074_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4067_);
                        lean_dec(v___x_4058_);
                        v___x_4069_ = lean_box(0);
                        v_isShared_4070_ = v_isSharedCheck_4074_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4062_ == 0 {
                    v___x_4064_ = v___x_4061_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
                    v___x_4064_ = v_reuseFailAlloc_4065_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4064_;
            }
            3 => {
                if v_isShared_4070_ == 0 {
                    v___x_4072_ = v___x_4069_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
                    v___x_4072_ = v_reuseFailAlloc_4073_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___boxed(
    mut v_type_4075_: *mut LeanObject,
    mut v_maxFVars_x3f_4076_: *mut LeanObject,
    mut v_k_4077_: *mut LeanObject,
    mut v_cleanupAnnotations_4078_: *mut LeanObject,
    mut v_whnfType_4079_: *mut LeanObject,
    mut v___y_4080_: *mut LeanObject,
    mut v___y_4081_: *mut LeanObject,
    mut v___y_4082_: *mut LeanObject,
    mut v___y_4083_: *mut LeanObject,
    mut v___y_4084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4085_: u8 = 0;
    let mut v_whnfType_boxed_4086_: u8 = 0;
    let mut v_res_4087_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4085_ = (lean_unbox(v_cleanupAnnotations_4078_) as u8);
    v_whnfType_boxed_4086_ = (lean_unbox(v_whnfType_4079_) as u8);
    v_res_4087_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_4075_, v_maxFVars_x3f_4076_, v_k_4077_, v_cleanupAnnotations_boxed_4085_, v_whnfType_boxed_4086_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
    lean_dec(v___y_4083_);
    lean_dec_ref(v___y_4082_);
    lean_dec(v___y_4081_);
    lean_dec_ref(v___y_4080_);
    return v_res_4087_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(
    mut v_00_u03b1_4088_: *mut LeanObject,
    mut v_type_4089_: *mut LeanObject,
    mut v_maxFVars_x3f_4090_: *mut LeanObject,
    mut v_k_4091_: *mut LeanObject,
    mut v_cleanupAnnotations_4092_: u8,
    mut v_whnfType_4093_: u8,
    mut v___y_4094_: *mut LeanObject,
    mut v___y_4095_: *mut LeanObject,
    mut v___y_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    v___x_4099_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_4089_, v_maxFVars_x3f_4090_, v_k_4091_, v_cleanupAnnotations_4092_, v_whnfType_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
    return v___x_4099_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___boxed(
    mut v_00_u03b1_4100_: *mut LeanObject,
    mut v_type_4101_: *mut LeanObject,
    mut v_maxFVars_x3f_4102_: *mut LeanObject,
    mut v_k_4103_: *mut LeanObject,
    mut v_cleanupAnnotations_4104_: *mut LeanObject,
    mut v_whnfType_4105_: *mut LeanObject,
    mut v___y_4106_: *mut LeanObject,
    mut v___y_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
    mut v___y_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4111_: u8 = 0;
    let mut v_whnfType_boxed_4112_: u8 = 0;
    let mut v_res_4113_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4111_ = (lean_unbox(v_cleanupAnnotations_4104_) as u8);
    v_whnfType_boxed_4112_ = (lean_unbox(v_whnfType_4105_) as u8);
    v_res_4113_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(
            v_00_u03b1_4100_,
            v_type_4101_,
            v_maxFVars_x3f_4102_,
            v_k_4103_,
            v_cleanupAnnotations_boxed_4111_,
            v_whnfType_boxed_4112_,
            v___y_4106_,
            v___y_4107_,
            v___y_4108_,
            v___y_4109_,
        );
    lean_dec(v___y_4109_);
    lean_dec_ref(v___y_4108_);
    lean_dec(v___y_4107_);
    lean_dec_ref(v___y_4106_);
    return v_res_4113_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(
    mut v___x_4114_: *mut LeanObject,
    mut v_type_4115_: *mut LeanObject,
    mut v___x_4116_: u8,
    mut v___x_4117_: u8,
    mut v_tuple_4118_: *mut LeanObject,
    mut v___y_4119_: *mut LeanObject,
    mut v___y_4120_: *mut LeanObject,
    mut v___y_4121_: *mut LeanObject,
    mut v___y_4122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_tuple_4118_);
    v___x_4124_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(
        v_tuple_4118_,
        v___x_4114_,
    );
    v___x_4125_ = l_Lean_Meta_instantiateForall(
        v_type_4115_,
        v___x_4124_,
        v___y_4119_,
        v___y_4120_,
        v___y_4121_,
        v___y_4122_,
    );
    lean_dec_ref(v___x_4124_);
    if lean_obj_tag(v___x_4125_) == 0 {
        let mut v_a_4126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4130_: u8 = 0;
        let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
        v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
        lean_inc(v_a_4126_);
        lean_dec_ref_known(v___x_4125_, 1);
        v___x_4127_ = lean_unsigned_to_nat(1);
        v___x_4128_ = lean_mk_empty_array_with_capacity(v___x_4127_);
        v___x_4129_ = lean_array_push(v___x_4128_, v_tuple_4118_);
        v___x_4130_ = 1;
        v___x_4131_ = l_Lean_Meta_mkForallFVars(
            v___x_4129_,
            v_a_4126_,
            v___x_4116_,
            v___x_4117_,
            v___x_4117_,
            v___x_4130_,
            v___y_4119_,
            v___y_4120_,
            v___y_4121_,
            v___y_4122_,
        );
        lean_dec_ref(v___x_4129_);
        return v___x_4131_;
    } else {
        lean_dec_ref(v_tuple_4118_);
        return v___x_4125_;
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed(
    mut v___x_4132_: *mut LeanObject,
    mut v_type_4133_: *mut LeanObject,
    mut v___x_4134_: *mut LeanObject,
    mut v___x_4135_: *mut LeanObject,
    mut v_tuple_4136_: *mut LeanObject,
    mut v___y_4137_: *mut LeanObject,
    mut v___y_4138_: *mut LeanObject,
    mut v___y_4139_: *mut LeanObject,
    mut v___y_4140_: *mut LeanObject,
    mut v___y_4141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1465__boxed_4142_: u8 = 0;
    let mut v___x_1466__boxed_4143_: u8 = 0;
    let mut v_res_4144_: *mut LeanObject = core::ptr::null_mut();
    v___x_1465__boxed_4142_ = (lean_unbox(v___x_4134_) as u8);
    v___x_1466__boxed_4143_ = (lean_unbox(v___x_4135_) as u8);
    v_res_4144_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(
        v___x_4132_,
        v_type_4133_,
        v___x_1465__boxed_4142_,
        v___x_1466__boxed_4143_,
        v_tuple_4136_,
        v___y_4137_,
        v___y_4138_,
        v___y_4139_,
        v___y_4140_,
    );
    lean_dec(v___y_4140_);
    lean_dec_ref(v___y_4139_);
    lean_dec(v___y_4138_);
    lean_dec_ref(v___y_4137_);
    lean_dec(v___x_4132_);
    return v_res_4144_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(
    mut v_k_4145_: *mut LeanObject,
    mut v_b_4146_: *mut LeanObject,
    mut v___y_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4150_);
    lean_inc_ref(v___y_4149_);
    lean_inc(v___y_4148_);
    lean_inc_ref(v___y_4147_);
    v___x_4152_ = lean_apply_6(
        v_k_4145_,
        v_b_4146_,
        v___y_4147_,
        v___y_4148_,
        v___y_4149_,
        v___y_4150_,
        lean_box(0),
    );
    return v___x_4152_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0___boxed(
    mut v_k_4153_: *mut LeanObject,
    mut v_b_4154_: *mut LeanObject,
    mut v___y_4155_: *mut LeanObject,
    mut v___y_4156_: *mut LeanObject,
    mut v___y_4157_: *mut LeanObject,
    mut v___y_4158_: *mut LeanObject,
    mut v___y_4159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4160_: *mut LeanObject = core::ptr::null_mut();
    v_res_4160_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(v_k_4153_, v_b_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
    lean_dec(v___y_4158_);
    lean_dec_ref(v___y_4157_);
    lean_dec(v___y_4156_);
    lean_dec_ref(v___y_4155_);
    return v_res_4160_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(
    mut v_name_4161_: *mut LeanObject,
    mut v_bi_4162_: u8,
    mut v_type_4163_: *mut LeanObject,
    mut v_k_4164_: *mut LeanObject,
    mut v_kind_4165_: u8,
    mut v___y_4166_: *mut LeanObject,
    mut v___y_4167_: *mut LeanObject,
    mut v___y_4168_: *mut LeanObject,
    mut v___y_4169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4180_: u8 = 0;
    let mut v_a_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4184_: u8 = 0;
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4171_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_4171_, 0, v_k_4164_);
                v___x_4172_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_4161_,
                    v_bi_4162_,
                    v_type_4163_,
                    v___f_4171_,
                    v_kind_4165_,
                    v___y_4166_,
                    v___y_4167_,
                    v___y_4168_,
                    v___y_4169_,
                );
                if lean_obj_tag(v___x_4172_) == 0 {
                    v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
                    v_isSharedCheck_4180_ = (!lean_is_exclusive(v___x_4172_)) as u8;
                    if v_isSharedCheck_4180_ == 0 {
                        v___x_4175_ = v___x_4172_;
                        v_isShared_4176_ = v_isSharedCheck_4180_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4173_);
                        lean_dec(v___x_4172_);
                        v___x_4175_ = lean_box(0);
                        v_isShared_4176_ = v_isSharedCheck_4180_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4181_ = lean_ctor_get(v___x_4172_, 0);
                    v_isSharedCheck_4188_ = (!lean_is_exclusive(v___x_4172_)) as u8;
                    if v_isSharedCheck_4188_ == 0 {
                        v___x_4183_ = v___x_4172_;
                        v_isShared_4184_ = v_isSharedCheck_4188_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4181_);
                        lean_dec(v___x_4172_);
                        v___x_4183_ = lean_box(0);
                        v_isShared_4184_ = v_isSharedCheck_4188_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4176_ == 0 {
                    v___x_4178_ = v___x_4175_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
                    v___x_4178_ = v_reuseFailAlloc_4179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4178_;
            }
            3 => {
                if v_isShared_4184_ == 0 {
                    v___x_4186_ = v___x_4183_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
                    v___x_4186_ = v_reuseFailAlloc_4187_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___boxed(
    mut v_name_4189_: *mut LeanObject,
    mut v_bi_4190_: *mut LeanObject,
    mut v_type_4191_: *mut LeanObject,
    mut v_k_4192_: *mut LeanObject,
    mut v_kind_4193_: *mut LeanObject,
    mut v___y_4194_: *mut LeanObject,
    mut v___y_4195_: *mut LeanObject,
    mut v___y_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v___y_4198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_4199_: u8 = 0;
    let mut v_kind_boxed_4200_: u8 = 0;
    let mut v_res_4201_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_4199_ = (lean_unbox(v_bi_4190_) as u8);
    v_kind_boxed_4200_ = (lean_unbox(v_kind_4193_) as u8);
    v_res_4201_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_4189_, v_bi_boxed_4199_, v_type_4191_, v_k_4192_, v_kind_boxed_4200_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
    lean_dec(v___y_4197_);
    lean_dec_ref(v___y_4196_);
    lean_dec(v___y_4195_);
    lean_dec_ref(v___y_4194_);
    return v_res_4201_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(
    mut v_name_4202_: *mut LeanObject,
    mut v_type_4203_: *mut LeanObject,
    mut v_k_4204_: *mut LeanObject,
    mut v___y_4205_: *mut LeanObject,
    mut v___y_4206_: *mut LeanObject,
    mut v___y_4207_: *mut LeanObject,
    mut v___y_4208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4210_: u8 = 0;
    let mut v___x_4211_: u8 = 0;
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    v___x_4210_ = 0;
    v___x_4211_ = 0;
    v___x_4212_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_4202_, v___x_4210_, v_type_4203_, v_k_4204_, v___x_4211_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_);
    return v___x_4212_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg___boxed(
    mut v_name_4213_: *mut LeanObject,
    mut v_type_4214_: *mut LeanObject,
    mut v_k_4215_: *mut LeanObject,
    mut v___y_4216_: *mut LeanObject,
    mut v___y_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
    mut v___y_4220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4221_: *mut LeanObject = core::ptr::null_mut();
    v_res_4221_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(
            v_name_4213_,
            v_type_4214_,
            v_k_4215_,
            v___y_4216_,
            v___y_4217_,
            v___y_4218_,
            v___y_4219_,
        );
    lean_dec(v___y_4219_);
    lean_dec_ref(v___y_4218_);
    lean_dec(v___y_4217_);
    lean_dec_ref(v___y_4216_);
    return v_res_4221_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2()
-> *mut LeanObject {
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    v___x_4224_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__1;
    v___x_4225_ = lean_unsigned_to_nat(6);
    v___x_4226_ = lean_unsigned_to_nat(138);
    v___x_4227_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__0;
    v___x_4228_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0;
    v___x_4229_ = l_mkPanicMessageWithDecl(
        v___x_4228_,
        v___x_4227_,
        v___x_4226_,
        v___x_4225_,
        v___x_4224_,
    );
    return v___x_4229_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(
    mut v___x_4233_: *mut LeanObject,
    mut v_type_4234_: *mut LeanObject,
    mut v___x_4235_: u8,
    mut v___x_4236_: u8,
    mut v_varNames_4237_: *mut LeanObject,
    mut v___x_4238_: *mut LeanObject,
    mut v_xs_4239_: *mut LeanObject,
    mut v_x_4240_: *mut LeanObject,
    mut v___y_4241_: *mut LeanObject,
    mut v___y_4242_: *mut LeanObject,
    mut v___y_4243_: *mut LeanObject,
    mut v___y_4244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: u8 = 0;
    v___x_4246_ = lean_array_get_size(v_xs_4239_);
    v___x_4247_ = lean_nat_dec_eq(v___x_4246_, v___x_4233_);
    if v___x_4247_ == 0 {
        let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_4239_);
        lean_dec_ref(v_type_4234_);
        v___x_4248_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2_once
            ),
            _init_l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2,
        );
        v___x_4249_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(
            v___x_4248_,
            v___y_4241_,
            v___y_4242_,
            v___y_4243_,
            v___y_4244_,
        );
        return v___x_4249_;
    } else {
        let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
        v___x_4250_ = l_Lean_Meta_ArgsPacker_Unary_packType(
            v_xs_4239_,
            v___y_4241_,
            v___y_4242_,
            v___y_4243_,
            v___y_4244_,
        );
        if lean_obj_tag(v___x_4250_) == 0 {
            let mut v_a_4251_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_4254_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4256_: u8 = 0;
            v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
            lean_inc(v_a_4251_);
            lean_dec_ref_known(v___x_4250_, 1);
            v___x_4252_ = lean_box((v___x_4235_) as usize);
            v___x_4253_ = lean_box((v___x_4236_) as usize);
            v___f_4254_ = lean_alloc_closure(
                l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed as *mut core::ffi::c_void,
                10,
                4,
            );
            lean_closure_set(v___f_4254_, 0, v___x_4246_);
            lean_closure_set(v___f_4254_, 1, v_type_4234_);
            lean_closure_set(v___f_4254_, 2, v___x_4252_);
            lean_closure_set(v___f_4254_, 3, v___x_4253_);
            v___x_4255_ = lean_unsigned_to_nat(1);
            v___x_4256_ = lean_nat_dec_eq(v___x_4246_, v___x_4255_);
            if v___x_4256_ == 0 {
                let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
                v___x_4257_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4;
                v___x_4258_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_4257_, v_a_4251_, v___f_4254_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
                return v___x_4258_;
            } else {
                let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
                v___x_4259_ = lean_box(0);
                v___x_4260_ = lean_array_get_borrowed(v___x_4259_, v_varNames_4237_, v___x_4238_);
                lean_inc(v___x_4260_);
                v___x_4261_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_4260_, v_a_4251_, v___f_4254_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
                return v___x_4261_;
            }
        } else {
            lean_dec_ref(v_type_4234_);
            return v___x_4250_;
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed(
    mut v___x_4262_: *mut LeanObject,
    mut v_type_4263_: *mut LeanObject,
    mut v___x_4264_: *mut LeanObject,
    mut v___x_4265_: *mut LeanObject,
    mut v_varNames_4266_: *mut LeanObject,
    mut v___x_4267_: *mut LeanObject,
    mut v_xs_4268_: *mut LeanObject,
    mut v_x_4269_: *mut LeanObject,
    mut v___y_4270_: *mut LeanObject,
    mut v___y_4271_: *mut LeanObject,
    mut v___y_4272_: *mut LeanObject,
    mut v___y_4273_: *mut LeanObject,
    mut v___y_4274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1618__boxed_4275_: u8 = 0;
    let mut v___x_1619__boxed_4276_: u8 = 0;
    let mut v_res_4277_: *mut LeanObject = core::ptr::null_mut();
    v___x_1618__boxed_4275_ = (lean_unbox(v___x_4264_) as u8);
    v___x_1619__boxed_4276_ = (lean_unbox(v___x_4265_) as u8);
    v_res_4277_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(
        v___x_4262_,
        v_type_4263_,
        v___x_1618__boxed_4275_,
        v___x_1619__boxed_4276_,
        v_varNames_4266_,
        v___x_4267_,
        v_xs_4268_,
        v_x_4269_,
        v___y_4270_,
        v___y_4271_,
        v___y_4272_,
        v___y_4273_,
    );
    lean_dec(v___y_4273_);
    lean_dec_ref(v___y_4272_);
    lean_dec(v___y_4271_);
    lean_dec_ref(v___y_4270_);
    lean_dec_ref(v_x_4269_);
    lean_dec(v___x_4267_);
    lean_dec_ref(v_varNames_4266_);
    lean_dec(v___x_4262_);
    return v_res_4277_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_uncurryType(
    mut v_varNames_4278_: *mut LeanObject,
    mut v_type_4279_: *mut LeanObject,
    mut v_a_4280_: *mut LeanObject,
    mut v_a_4281_: *mut LeanObject,
    mut v_a_4282_: *mut LeanObject,
    mut v_a_4283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    v___x_4285_ = lean_array_get_size(v_varNames_4278_);
    v___x_4286_ = lean_unsigned_to_nat(0);
    v___x_4287_ = lean_nat_dec_eq(v___x_4285_, v___x_4286_);
    if v___x_4287_ == 0 {
        let mut v___x_4288_: u8 = 0;
        let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
        v___x_4288_ = 1;
        v___x_4289_ = lean_box((v___x_4287_) as usize);
        v___x_4290_ = lean_box((v___x_4288_) as usize);
        lean_inc_ref(v_type_4279_);
        v___f_4291_ = lean_alloc_closure(
            l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed as *mut core::ffi::c_void,
            13,
            6,
        );
        lean_closure_set(v___f_4291_, 0, v___x_4285_);
        lean_closure_set(v___f_4291_, 1, v_type_4279_);
        lean_closure_set(v___f_4291_, 2, v___x_4289_);
        lean_closure_set(v___f_4291_, 3, v___x_4290_);
        lean_closure_set(v___f_4291_, 4, v_varNames_4278_);
        lean_closure_set(v___f_4291_, 5, v___x_4286_);
        v___x_4292_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4292_, 0, v___x_4285_);
        v___x_4293_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_4279_, v___x_4292_, v___f_4291_, v___x_4287_, v___x_4287_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
        return v___x_4293_;
    } else {
        let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_varNames_4278_);
        v___x_4294_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Unary_packType___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once),
            _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2,
        );
        v___x_4295_ = l_Lean_mkArrow(v___x_4294_, v_type_4279_, v_a_4282_, v_a_4283_);
        return v___x_4295_;
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_uncurryType___boxed(
    mut v_varNames_4296_: *mut LeanObject,
    mut v_type_4297_: *mut LeanObject,
    mut v_a_4298_: *mut LeanObject,
    mut v_a_4299_: *mut LeanObject,
    mut v_a_4300_: *mut LeanObject,
    mut v_a_4301_: *mut LeanObject,
    mut v_a_4302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4303_: *mut LeanObject = core::ptr::null_mut();
    v_res_4303_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(
        v_varNames_4296_,
        v_type_4297_,
        v_a_4298_,
        v_a_4299_,
        v_a_4300_,
        v_a_4301_,
    );
    lean_dec(v_a_4301_);
    lean_dec_ref(v_a_4300_);
    lean_dec(v_a_4299_);
    lean_dec_ref(v_a_4298_);
    return v_res_4303_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(
    mut v_00_u03b1_4304_: *mut LeanObject,
    mut v_name_4305_: *mut LeanObject,
    mut v_bi_4306_: u8,
    mut v_type_4307_: *mut LeanObject,
    mut v_k_4308_: *mut LeanObject,
    mut v_kind_4309_: u8,
    mut v___y_4310_: *mut LeanObject,
    mut v___y_4311_: *mut LeanObject,
    mut v___y_4312_: *mut LeanObject,
    mut v___y_4313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    v___x_4315_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_4305_, v_bi_4306_, v_type_4307_, v_k_4308_, v_kind_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
    return v___x_4315_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___boxed(
    mut v_00_u03b1_4316_: *mut LeanObject,
    mut v_name_4317_: *mut LeanObject,
    mut v_bi_4318_: *mut LeanObject,
    mut v_type_4319_: *mut LeanObject,
    mut v_k_4320_: *mut LeanObject,
    mut v_kind_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_4327_: u8 = 0;
    let mut v_kind_boxed_4328_: u8 = 0;
    let mut v_res_4329_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_4327_ = (lean_unbox(v_bi_4318_) as u8);
    v_kind_boxed_4328_ = (lean_unbox(v_kind_4321_) as u8);
    v_res_4329_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(v_00_u03b1_4316_, v_name_4317_, v_bi_boxed_4327_, v_type_4319_, v_k_4320_, v_kind_boxed_4328_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
    lean_dec(v___y_4325_);
    lean_dec_ref(v___y_4324_);
    lean_dec(v___y_4323_);
    lean_dec_ref(v___y_4322_);
    return v_res_4329_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(
    mut v_00_u03b1_4330_: *mut LeanObject,
    mut v_name_4331_: *mut LeanObject,
    mut v_type_4332_: *mut LeanObject,
    mut v_k_4333_: *mut LeanObject,
    mut v___y_4334_: *mut LeanObject,
    mut v___y_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    v___x_4339_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(
            v_name_4331_,
            v_type_4332_,
            v_k_4333_,
            v___y_4334_,
            v___y_4335_,
            v___y_4336_,
            v___y_4337_,
        );
    return v___x_4339_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___boxed(
    mut v_00_u03b1_4340_: *mut LeanObject,
    mut v_name_4341_: *mut LeanObject,
    mut v_type_4342_: *mut LeanObject,
    mut v_k_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4349_: *mut LeanObject = core::ptr::null_mut();
    v_res_4349_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(
            v_00_u03b1_4340_,
            v_name_4341_,
            v_type_4342_,
            v_k_4343_,
            v___y_4344_,
            v___y_4345_,
            v___y_4346_,
            v___y_4347_,
        );
    lean_dec(v___y_4347_);
    lean_dec_ref(v___y_4346_);
    lean_dec(v___y_4345_);
    lean_dec_ref(v___y_4344_);
    return v_res_4349_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(
    mut v_msgData_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
    mut v___y_4353_: *mut LeanObject,
    mut v___y_4354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    v___x_4356_ = lean_st_ref_get(v___y_4354_);
    v_env_4357_ = lean_ctor_get(v___x_4356_, 0);
    lean_inc_ref(v_env_4357_);
    lean_dec(v___x_4356_);
    v___x_4358_ = lean_st_ref_get(v___y_4352_);
    v_mctx_4359_ = lean_ctor_get(v___x_4358_, 0);
    lean_inc_ref(v_mctx_4359_);
    lean_dec(v___x_4358_);
    v_lctx_4360_ = lean_ctor_get(v___y_4351_, 2);
    v_options_4361_ = lean_ctor_get(v___y_4353_, 2);
    lean_inc_ref(v_options_4361_);
    lean_inc_ref(v_lctx_4360_);
    v___x_4362_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4362_, 0, v_env_4357_);
    lean_ctor_set(v___x_4362_, 1, v_mctx_4359_);
    lean_ctor_set(v___x_4362_, 2, v_lctx_4360_);
    lean_ctor_set(v___x_4362_, 3, v_options_4361_);
    v___x_4363_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4363_, 0, v___x_4362_);
    lean_ctor_set(v___x_4363_, 1, v_msgData_4350_);
    v___x_4364_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4364_, 0, v___x_4363_);
    return v___x_4364_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0___boxed(
    mut v_msgData_4365_: *mut LeanObject,
    mut v___y_4366_: *mut LeanObject,
    mut v___y_4367_: *mut LeanObject,
    mut v___y_4368_: *mut LeanObject,
    mut v___y_4369_: *mut LeanObject,
    mut v___y_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4371_: *mut LeanObject = core::ptr::null_mut();
    v_res_4371_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msgData_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
    lean_dec(v___y_4369_);
    lean_dec_ref(v___y_4368_);
    lean_dec(v___y_4367_);
    lean_dec_ref(v___y_4366_);
    return v_res_4371_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(
    mut v_msg_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
    mut v___y_4375_: *mut LeanObject,
    mut v___y_4376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4383_: u8 = 0;
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4378_ = lean_ctor_get(v___y_4375_, 5);
                v___x_4379_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msg_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
                v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
                v_isSharedCheck_4388_ = (!lean_is_exclusive(v___x_4379_)) as u8;
                if v_isSharedCheck_4388_ == 0 {
                    v___x_4382_ = v___x_4379_;
                    v_isShared_4383_ = v_isSharedCheck_4388_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4380_);
                    lean_dec(v___x_4379_);
                    v___x_4382_ = lean_box(0);
                    v_isShared_4383_ = v_isSharedCheck_4388_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4378_);
                v___x_4384_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4384_, 0, v_ref_4378_);
                lean_ctor_set(v___x_4384_, 1, v_a_4380_);
                if v_isShared_4383_ == 0 {
                    lean_ctor_set_tag(v___x_4382_, 1);
                    lean_ctor_set(v___x_4382_, 0, v___x_4384_);
                    v___x_4386_ = v___x_4382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4384_);
                    v___x_4386_ = v_reuseFailAlloc_4387_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg___boxed(
    mut v_msg_4389_: *mut LeanObject,
    mut v___y_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4395_: *mut LeanObject = core::ptr::null_mut();
    v_res_4395_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
    lean_dec(v___y_4393_);
    lean_dec_ref(v___y_4392_);
    lean_dec(v___y_4391_);
    lean_dec_ref(v___y_4390_);
    return v_res_4395_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1()
-> *mut LeanObject {
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    v___x_4397_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0;
    v___x_4398_ = l_Lean_stringToMessageData(v___x_4397_);
    return v___x_4398_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4399_: *mut LeanObject = *_args.add(0);
    let mut v___x_4400_: *mut LeanObject = *_args.add(1);
    let mut v___x_4401_: *mut LeanObject = *_args.add(2);
    let mut v_arg_4402_: *mut LeanObject = *_args.add(3);
    let mut v_arg_4403_: *mut LeanObject = *_args.add(4);
    let mut v_a_4404_: *mut LeanObject = *_args.add(5);
    let mut v_alt_4405_: *mut LeanObject = *_args.add(6);
    let mut v_tail_4406_: *mut LeanObject = *_args.add(7);
    let mut v_u_4407_: *mut LeanObject = *_args.add(8);
    let mut v___x_4408_: *mut LeanObject = *_args.add(9);
    let mut v___x_4409_: *mut LeanObject = *_args.add(10);
    let mut v___x_4410_: *mut LeanObject = *_args.add(11);
    let mut v_head_4411_: *mut LeanObject = *_args.add(12);
    let mut v_x_4412_: *mut LeanObject = *_args.add(13);
    let mut v___y_4413_: *mut LeanObject = *_args.add(14);
    let mut v___y_4414_: *mut LeanObject = *_args.add(15);
    let mut v___y_4415_: *mut LeanObject = *_args.add(16);
    let mut v___y_4416_: *mut LeanObject = *_args.add(17);
    let mut v___y_4417_: *mut LeanObject = *_args.add(18);
    let mut v___x_3515__boxed_4418_: u8 = 0;
    let mut v___x_3516__boxed_4419_: u8 = 0;
    let mut v___x_3517__boxed_4420_: u8 = 0;
    let mut v_res_4421_: *mut LeanObject = core::ptr::null_mut();
    v___x_3515__boxed_4418_ = (lean_unbox(v___x_4408_) as u8);
    v___x_3516__boxed_4419_ = (lean_unbox(v___x_4409_) as u8);
    v___x_3517__boxed_4420_ = (lean_unbox(v___x_4410_) as u8);
    v_res_4421_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(
        v___x_4399_,
        v___x_4400_,
        v___x_4401_,
        v_arg_4402_,
        v_arg_4403_,
        v_a_4404_,
        v_alt_4405_,
        v_tail_4406_,
        v_u_4407_,
        v___x_3515__boxed_4418_,
        v___x_3516__boxed_4419_,
        v___x_3517__boxed_4420_,
        v_head_4411_,
        v_x_4412_,
        v___y_4413_,
        v___y_4414_,
        v___y_4415_,
        v___y_4416_,
    );
    lean_dec(v___y_4416_);
    lean_dec_ref(v___y_4415_);
    lean_dec(v___y_4414_);
    lean_dec_ref(v___y_4413_);
    return v_res_4421_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(
    mut v_varNames_4426_: *mut LeanObject,
    mut v_e_4427_: *mut LeanObject,
    mut v_u_4428_: *mut LeanObject,
    mut v_codomain_4429_: *mut LeanObject,
    mut v_alt_4430_: *mut LeanObject,
    mut v_a_4431_: *mut LeanObject,
    mut v_a_4432_: *mut LeanObject,
    mut v_a_4433_: *mut LeanObject,
    mut v_a_4434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v_head_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: u8 = 0;
    let mut v_arg_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v_arg_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: u8 = 0;
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: u8 = 0;
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4488_: u8 = 0;
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4498_: u8 = 0;
    let mut v_isSharedCheck_4499_: u8 = 0;
    let mut v_unused_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_varNames_4426_) == 0 {
                    lean_dec_ref(v_codomain_4429_);
                    lean_dec(v_u_4428_);
                    lean_dec_ref(v_e_4427_);
                    v___x_4436_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4436_, 0, v_alt_4430_);
                    return v___x_4436_;
                } else {
                    v_tail_4437_ = lean_ctor_get(v_varNames_4426_, 1);
                    lean_inc(v_tail_4437_);
                    if lean_obj_tag(v_tail_4437_) == 0 {
                        lean_dec_ref_known(v_varNames_4426_, 2);
                        lean_dec_ref(v_codomain_4429_);
                        lean_dec(v_u_4428_);
                        v___x_4438_ = lean_unsigned_to_nat(1);
                        v___x_4439_ = lean_mk_empty_array_with_capacity(v___x_4438_);
                        v___x_4440_ = lean_array_push(v___x_4439_, v_e_4427_);
                        v___x_4441_ = l_Lean_Expr_beta(v_alt_4430_, v___x_4440_);
                        v___x_4442_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4442_, 0, v___x_4441_);
                        return v___x_4442_;
                    } else {
                        v_head_4443_ = lean_ctor_get(v_varNames_4426_, 0);
                        v_isSharedCheck_4499_ = (!lean_is_exclusive(v_varNames_4426_)) as u8;
                        if v_isSharedCheck_4499_ == 0 {
                            v_unused_4500_ = lean_ctor_get(v_varNames_4426_, 1);
                            lean_dec(v_unused_4500_);
                            v___x_4445_ = v_varNames_4426_;
                            v_isShared_4446_ = v_isSharedCheck_4499_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_head_4443_);
                            lean_dec(v_varNames_4426_);
                            v___x_4445_ = lean_box(0);
                            v_isShared_4446_ = v_isSharedCheck_4499_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_head_4447_ = lean_ctor_get(v_tail_4437_, 0);
                lean_inc(v_head_4447_);
                lean_inc(v_a_4434_);
                lean_inc_ref(v_a_4433_);
                lean_inc(v_a_4432_);
                lean_inc_ref(v_a_4431_);
                lean_inc_ref(v_e_4427_);
                v___x_4448_ =
                    lean_infer_type(v_e_4427_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_);
                if lean_obj_tag(v___x_4448_) == 0 {
                    v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
                    lean_inc_n(v_a_4449_, 2);
                    lean_dec_ref_known(v___x_4448_, 1);
                    v___x_4450_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_4449_, v_a_4432_);
                    if lean_obj_tag(v___x_4450_) == 0 {
                        v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
                        lean_inc(v_a_4451_);
                        lean_dec_ref_known(v___x_4450_, 1);
                        v___x_4461_ = l_Lean_Expr_cleanupAnnotations(v_a_4451_);
                        v___x_4462_ = l_Lean_Expr_isApp(v___x_4461_);
                        if v___x_4462_ == 0 {
                            lean_dec_ref(v___x_4461_);
                            lean_dec(v_head_4447_);
                            lean_del_object(v___x_4445_);
                            lean_dec_ref_known(v_tail_4437_, 2);
                            lean_dec(v_head_4443_);
                            lean_dec_ref(v_alt_4430_);
                            lean_dec_ref(v_codomain_4429_);
                            lean_dec(v_u_4428_);
                            lean_dec_ref(v_e_4427_);
                            v___y_4453_ = v_a_4431_;
                            v___y_4454_ = v_a_4432_;
                            v___y_4455_ = v_a_4433_;
                            v___y_4456_ = v_a_4434_;
                            state = 2;
                            continue;
                        } else {
                            v_arg_4463_ = lean_ctor_get(v___x_4461_, 1);
                            lean_inc_ref(v_arg_4463_);
                            v___x_4464_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4461_);
                            v___x_4465_ = l_Lean_Expr_isApp(v___x_4464_);
                            if v___x_4465_ == 0 {
                                lean_dec_ref(v___x_4464_);
                                lean_dec_ref(v_arg_4463_);
                                lean_dec(v_head_4447_);
                                lean_del_object(v___x_4445_);
                                lean_dec_ref_known(v_tail_4437_, 2);
                                lean_dec(v_head_4443_);
                                lean_dec_ref(v_alt_4430_);
                                lean_dec_ref(v_codomain_4429_);
                                lean_dec(v_u_4428_);
                                lean_dec_ref(v_e_4427_);
                                v___y_4453_ = v_a_4431_;
                                v___y_4454_ = v_a_4432_;
                                v___y_4455_ = v_a_4433_;
                                v___y_4456_ = v_a_4434_;
                                state = 2;
                                continue;
                            } else {
                                v_arg_4466_ = lean_ctor_get(v___x_4464_, 1);
                                lean_inc_ref(v_arg_4466_);
                                v___x_4467_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4464_);
                                v___x_4468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0;
                                v___x_4469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1;
                                v___x_4470_ = l_Lean_Expr_isConstOf(v___x_4467_, v___x_4469_);
                                lean_dec_ref(v___x_4467_);
                                if v___x_4470_ == 0 {
                                    lean_dec_ref(v_arg_4466_);
                                    lean_dec_ref(v_arg_4463_);
                                    lean_dec(v_head_4447_);
                                    lean_del_object(v___x_4445_);
                                    lean_dec_ref_known(v_tail_4437_, 2);
                                    lean_dec(v_head_4443_);
                                    lean_dec_ref(v_alt_4430_);
                                    lean_dec_ref(v_codomain_4429_);
                                    lean_dec(v_u_4428_);
                                    lean_dec_ref(v_e_4427_);
                                    v___y_4453_ = v_a_4431_;
                                    v___y_4454_ = v_a_4432_;
                                    v___y_4455_ = v_a_4433_;
                                    v___y_4456_ = v_a_4434_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_4471_ = lean_unsigned_to_nat(1);
                                    v___x_4472_ = lean_mk_empty_array_with_capacity(v___x_4471_);
                                    lean_inc_ref(v_e_4427_);
                                    lean_inc_ref(v___x_4472_);
                                    v___x_4473_ = lean_array_push(v___x_4472_, v_e_4427_);
                                    v___x_4474_ = 0;
                                    v___x_4475_ = 1;
                                    v___x_4476_ = l_Lean_Meta_mkLambdaFVars(
                                        v___x_4473_,
                                        v_codomain_4429_,
                                        v___x_4474_,
                                        v___x_4470_,
                                        v___x_4474_,
                                        v___x_4470_,
                                        v___x_4475_,
                                        v_a_4431_,
                                        v_a_4432_,
                                        v_a_4433_,
                                        v_a_4434_,
                                    );
                                    lean_dec_ref(v___x_4473_);
                                    if lean_obj_tag(v___x_4476_) == 0 {
                                        v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
                                        lean_inc_n(v_a_4477_, 2);
                                        lean_dec_ref_known(v___x_4476_, 1);
                                        v___x_4478_ = l_Lean_Expr_getAppFn(v_a_4449_);
                                        lean_dec(v_a_4449_);
                                        v___x_4479_ = l_Lean_Expr_constLevels_x21(v___x_4478_);
                                        lean_dec_ref(v___x_4478_);
                                        v___x_4480_ = lean_box((v___x_4474_) as usize);
                                        v___x_4481_ = lean_box((v___x_4470_) as usize);
                                        v___x_4482_ = lean_box((v___x_4475_) as usize);
                                        lean_inc(v_u_4428_);
                                        lean_inc_ref(v_arg_4463_);
                                        lean_inc_ref_n(v_arg_4466_, 2);
                                        lean_inc(v___x_4479_);
                                        v___f_4483_ = lean_alloc_closure(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed as *mut core::ffi::c_void, 19, 13);
                                        lean_closure_set(v___f_4483_, 0, v___x_4472_);
                                        lean_closure_set(v___f_4483_, 1, v___x_4468_);
                                        lean_closure_set(v___f_4483_, 2, v___x_4479_);
                                        lean_closure_set(v___f_4483_, 3, v_arg_4466_);
                                        lean_closure_set(v___f_4483_, 4, v_arg_4463_);
                                        lean_closure_set(v___f_4483_, 5, v_a_4477_);
                                        lean_closure_set(v___f_4483_, 6, v_alt_4430_);
                                        lean_closure_set(v___f_4483_, 7, v_tail_4437_);
                                        lean_closure_set(v___f_4483_, 8, v_u_4428_);
                                        lean_closure_set(v___f_4483_, 9, v___x_4480_);
                                        lean_closure_set(v___f_4483_, 10, v___x_4481_);
                                        lean_closure_set(v___f_4483_, 11, v___x_4482_);
                                        lean_closure_set(v___f_4483_, 12, v_head_4447_);
                                        v___x_4484_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_4443_, v_arg_4466_, v___f_4483_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_);
                                        if lean_obj_tag(v___x_4484_) == 0 {
                                            v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
                                            v_isSharedCheck_4498_ =
                                                (!lean_is_exclusive(v___x_4484_)) as u8;
                                            if v_isSharedCheck_4498_ == 0 {
                                                v___x_4487_ = v___x_4484_;
                                                v_isShared_4488_ = v_isSharedCheck_4498_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_a_4485_);
                                                lean_dec(v___x_4484_);
                                                v___x_4487_ = lean_box(0);
                                                v_isShared_4488_ = v_isSharedCheck_4498_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v___x_4479_);
                                            lean_dec(v_a_4477_);
                                            lean_dec_ref(v_arg_4466_);
                                            lean_dec_ref(v_arg_4463_);
                                            lean_del_object(v___x_4445_);
                                            lean_dec(v_u_4428_);
                                            lean_dec_ref(v_e_4427_);
                                            return v___x_4484_;
                                        }
                                    } else {
                                        lean_dec_ref(v___x_4472_);
                                        lean_dec_ref(v_arg_4466_);
                                        lean_dec_ref(v_arg_4463_);
                                        lean_dec(v_a_4449_);
                                        lean_dec(v_head_4447_);
                                        lean_del_object(v___x_4445_);
                                        lean_dec(v_head_4443_);
                                        lean_dec_ref_known(v_tail_4437_, 2);
                                        lean_dec_ref(v_alt_4430_);
                                        lean_dec(v_u_4428_);
                                        lean_dec_ref(v_e_4427_);
                                        return v___x_4476_;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_4449_);
                        lean_dec(v_head_4447_);
                        lean_del_object(v___x_4445_);
                        lean_dec_ref_known(v_tail_4437_, 2);
                        lean_dec(v_head_4443_);
                        lean_dec_ref(v_alt_4430_);
                        lean_dec_ref(v_codomain_4429_);
                        lean_dec(v_u_4428_);
                        lean_dec_ref(v_e_4427_);
                        return v___x_4450_;
                    }
                } else {
                    lean_dec(v_head_4447_);
                    lean_del_object(v___x_4445_);
                    lean_dec(v_head_4443_);
                    lean_dec_ref_known(v_tail_4437_, 2);
                    lean_dec_ref(v_alt_4430_);
                    lean_dec_ref(v_codomain_4429_);
                    lean_dec(v_u_4428_);
                    lean_dec_ref(v_e_4427_);
                    return v___x_4448_;
                }
            }
            2 => {
                v___x_4457_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1);
                v___x_4458_ = l_Lean_MessageData_ofExpr(v_a_4449_);
                v___x_4459_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4459_, 0, v___x_4457_);
                lean_ctor_set(v___x_4459_, 1, v___x_4458_);
                v___x_4460_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_4459_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
                return v___x_4460_;
            }
            3 => {
                v___x_4489_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3;
                if v_isShared_4446_ == 0 {
                    lean_ctor_set(v___x_4445_, 1, v___x_4479_);
                    lean_ctor_set(v___x_4445_, 0, v_u_4428_);
                    v___x_4491_ = v___x_4445_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_u_4428_);
                    lean_ctor_set(v_reuseFailAlloc_4497_, 1, v___x_4479_);
                    v___x_4491_ = v_reuseFailAlloc_4497_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4492_ = l_Lean_Expr_const___override(v___x_4489_, v___x_4491_);
                v___x_4493_ = l_Lean_mkApp5(
                    v___x_4492_,
                    v_arg_4466_,
                    v_arg_4463_,
                    v_a_4477_,
                    v_e_4427_,
                    v_a_4485_,
                );
                if v_isShared_4488_ == 0 {
                    lean_ctor_set(v___x_4487_, 0, v___x_4493_);
                    v___x_4495_ = v___x_4487_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
                    v___x_4495_ = v_reuseFailAlloc_4496_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(
    mut v___x_4501_: *mut LeanObject,
    mut v___x_4502_: *mut LeanObject,
    mut v_arg_4503_: *mut LeanObject,
    mut v_arg_4504_: *mut LeanObject,
    mut v_x_4505_: *mut LeanObject,
    mut v___x_4506_: *mut LeanObject,
    mut v_a_4507_: *mut LeanObject,
    mut v_alt_4508_: *mut LeanObject,
    mut v___x_4509_: *mut LeanObject,
    mut v_tail_4510_: *mut LeanObject,
    mut v_u_4511_: *mut LeanObject,
    mut v___x_4512_: u8,
    mut v___x_4513_: u8,
    mut v___x_4514_: u8,
    mut v_y_4515_: *mut LeanObject,
    mut v___y_4516_: *mut LeanObject,
    mut v___y_4517_: *mut LeanObject,
    mut v___y_4518_: *mut LeanObject,
    mut v___y_4519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    v___x_4521_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6;
    v___x_4522_ = l_Lean_Name_mkStr2(v___x_4501_, v___x_4521_);
    v___x_4523_ = l_Lean_Expr_const___override(v___x_4522_, v___x_4502_);
    lean_inc_ref_n(v_y_4515_, 2);
    lean_inc_ref(v_x_4505_);
    v___x_4524_ = l_Lean_mkApp4(v___x_4523_, v_arg_4503_, v_arg_4504_, v_x_4505_, v_y_4515_);
    v___x_4525_ = lean_array_push(v___x_4506_, v___x_4524_);
    v___x_4526_ = l_Lean_Expr_beta(v_a_4507_, v___x_4525_);
    v___x_4527_ = l_Lean_Expr_beta(v_alt_4508_, v___x_4509_);
    v___x_4528_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(
        v_tail_4510_,
        v_y_4515_,
        v_u_4511_,
        v___x_4526_,
        v___x_4527_,
        v___y_4516_,
        v___y_4517_,
        v___y_4518_,
        v___y_4519_,
    );
    if lean_obj_tag(v___x_4528_) == 0 {
        let mut v_a_4529_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
        v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
        lean_inc(v_a_4529_);
        lean_dec_ref_known(v___x_4528_, 1);
        v___x_4530_ = lean_unsigned_to_nat(2);
        v___x_4531_ = lean_mk_empty_array_with_capacity(v___x_4530_);
        v___x_4532_ = lean_array_push(v___x_4531_, v_x_4505_);
        v___x_4533_ = lean_array_push(v___x_4532_, v_y_4515_);
        v___x_4534_ = l_Lean_Meta_mkLambdaFVars(
            v___x_4533_,
            v_a_4529_,
            v___x_4512_,
            v___x_4513_,
            v___x_4512_,
            v___x_4513_,
            v___x_4514_,
            v___y_4516_,
            v___y_4517_,
            v___y_4518_,
            v___y_4519_,
        );
        lean_dec_ref(v___x_4533_);
        return v___x_4534_;
    } else {
        lean_dec_ref(v_y_4515_);
        lean_dec_ref(v_x_4505_);
        return v___x_4528_;
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4535_: *mut LeanObject = *_args.add(0);
    let mut v___x_4536_: *mut LeanObject = *_args.add(1);
    let mut v_arg_4537_: *mut LeanObject = *_args.add(2);
    let mut v_arg_4538_: *mut LeanObject = *_args.add(3);
    let mut v_x_4539_: *mut LeanObject = *_args.add(4);
    let mut v___x_4540_: *mut LeanObject = *_args.add(5);
    let mut v_a_4541_: *mut LeanObject = *_args.add(6);
    let mut v_alt_4542_: *mut LeanObject = *_args.add(7);
    let mut v___x_4543_: *mut LeanObject = *_args.add(8);
    let mut v_tail_4544_: *mut LeanObject = *_args.add(9);
    let mut v_u_4545_: *mut LeanObject = *_args.add(10);
    let mut v___x_4546_: *mut LeanObject = *_args.add(11);
    let mut v___x_4547_: *mut LeanObject = *_args.add(12);
    let mut v___x_4548_: *mut LeanObject = *_args.add(13);
    let mut v_y_4549_: *mut LeanObject = *_args.add(14);
    let mut v___y_4550_: *mut LeanObject = *_args.add(15);
    let mut v___y_4551_: *mut LeanObject = *_args.add(16);
    let mut v___y_4552_: *mut LeanObject = *_args.add(17);
    let mut v___y_4553_: *mut LeanObject = *_args.add(18);
    let mut v___y_4554_: *mut LeanObject = *_args.add(19);
    let mut v___x_3536__boxed_4555_: u8 = 0;
    let mut v___x_3537__boxed_4556_: u8 = 0;
    let mut v___x_3538__boxed_4557_: u8 = 0;
    let mut v_res_4558_: *mut LeanObject = core::ptr::null_mut();
    v___x_3536__boxed_4555_ = (lean_unbox(v___x_4546_) as u8);
    v___x_3537__boxed_4556_ = (lean_unbox(v___x_4547_) as u8);
    v___x_3538__boxed_4557_ = (lean_unbox(v___x_4548_) as u8);
    v_res_4558_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(
        v___x_4535_,
        v___x_4536_,
        v_arg_4537_,
        v_arg_4538_,
        v_x_4539_,
        v___x_4540_,
        v_a_4541_,
        v_alt_4542_,
        v___x_4543_,
        v_tail_4544_,
        v_u_4545_,
        v___x_3536__boxed_4555_,
        v___x_3537__boxed_4556_,
        v___x_3538__boxed_4557_,
        v_y_4549_,
        v___y_4550_,
        v___y_4551_,
        v___y_4552_,
        v___y_4553_,
    );
    lean_dec(v___y_4553_);
    lean_dec_ref(v___y_4552_);
    lean_dec(v___y_4551_);
    lean_dec_ref(v___y_4550_);
    return v_res_4558_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(
    mut v___x_4559_: *mut LeanObject,
    mut v___x_4560_: *mut LeanObject,
    mut v___x_4561_: *mut LeanObject,
    mut v_arg_4562_: *mut LeanObject,
    mut v_arg_4563_: *mut LeanObject,
    mut v_a_4564_: *mut LeanObject,
    mut v_alt_4565_: *mut LeanObject,
    mut v_tail_4566_: *mut LeanObject,
    mut v_u_4567_: *mut LeanObject,
    mut v___x_4568_: u8,
    mut v___x_4569_: u8,
    mut v___x_4570_: u8,
    mut v_head_4571_: *mut LeanObject,
    mut v_x_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
    mut v___y_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
    mut v___y_4576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_x_4572_);
    lean_inc_ref(v___x_4559_);
    v___x_4578_ = lean_array_push(v___x_4559_, v_x_4572_);
    v___x_4579_ = lean_box((v___x_4568_) as usize);
    v___x_4580_ = lean_box((v___x_4569_) as usize);
    v___x_4581_ = lean_box((v___x_4570_) as usize);
    lean_inc_ref(v___x_4578_);
    lean_inc_ref(v_arg_4563_);
    v___f_4582_ = lean_alloc_closure(
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed
            as *mut core::ffi::c_void,
        20,
        14,
    );
    lean_closure_set(v___f_4582_, 0, v___x_4560_);
    lean_closure_set(v___f_4582_, 1, v___x_4561_);
    lean_closure_set(v___f_4582_, 2, v_arg_4562_);
    lean_closure_set(v___f_4582_, 3, v_arg_4563_);
    lean_closure_set(v___f_4582_, 4, v_x_4572_);
    lean_closure_set(v___f_4582_, 5, v___x_4559_);
    lean_closure_set(v___f_4582_, 6, v_a_4564_);
    lean_closure_set(v___f_4582_, 7, v_alt_4565_);
    lean_closure_set(v___f_4582_, 8, v___x_4578_);
    lean_closure_set(v___f_4582_, 9, v_tail_4566_);
    lean_closure_set(v___f_4582_, 10, v_u_4567_);
    lean_closure_set(v___f_4582_, 11, v___x_4579_);
    lean_closure_set(v___f_4582_, 12, v___x_4580_);
    lean_closure_set(v___f_4582_, 13, v___x_4581_);
    v___x_4583_ = l_Lean_Expr_beta(v_arg_4563_, v___x_4578_);
    v___x_4584_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(
            v_head_4571_,
            v___x_4583_,
            v___f_4582_,
            v___y_4573_,
            v___y_4574_,
            v___y_4575_,
            v___y_4576_,
        );
    return v___x_4584_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___boxed(
    mut v_varNames_4585_: *mut LeanObject,
    mut v_e_4586_: *mut LeanObject,
    mut v_u_4587_: *mut LeanObject,
    mut v_codomain_4588_: *mut LeanObject,
    mut v_alt_4589_: *mut LeanObject,
    mut v_a_4590_: *mut LeanObject,
    mut v_a_4591_: *mut LeanObject,
    mut v_a_4592_: *mut LeanObject,
    mut v_a_4593_: *mut LeanObject,
    mut v_a_4594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4595_: *mut LeanObject = core::ptr::null_mut();
    v_res_4595_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(
        v_varNames_4585_,
        v_e_4586_,
        v_u_4587_,
        v_codomain_4588_,
        v_alt_4589_,
        v_a_4590_,
        v_a_4591_,
        v_a_4592_,
        v_a_4593_,
    );
    lean_dec(v_a_4593_);
    lean_dec_ref(v_a_4592_);
    lean_dec(v_a_4591_);
    lean_dec_ref(v_a_4590_);
    return v_res_4595_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(
    mut v_00_u03b1_4596_: *mut LeanObject,
    mut v_msg_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
    mut v___y_4600_: *mut LeanObject,
    mut v___y_4601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    v___x_4603_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
    return v___x_4603_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___boxed(
    mut v_00_u03b1_4604_: *mut LeanObject,
    mut v_msg_4605_: *mut LeanObject,
    mut v___y_4606_: *mut LeanObject,
    mut v___y_4607_: *mut LeanObject,
    mut v___y_4608_: *mut LeanObject,
    mut v___y_4609_: *mut LeanObject,
    mut v___y_4610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4611_: *mut LeanObject = core::ptr::null_mut();
    v_res_4611_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(v_00_u03b1_4604_, v_msg_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
    lean_dec(v___y_4609_);
    lean_dec_ref(v___y_4608_);
    lean_dec(v___y_4607_);
    lean_dec_ref(v___y_4606_);
    return v_res_4611_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    v___x_4614_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1;
    v___x_4615_ = lean_unsigned_to_nat(23);
    v___x_4616_ = lean_unsigned_to_nat(180);
    v___x_4617_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0;
    v___x_4618_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0;
    v___x_4619_ = l_mkPanicMessageWithDecl(
        v___x_4618_,
        v___x_4617_,
        v___x_4616_,
        v___x_4615_,
        v___x_4614_,
    );
    return v___x_4619_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(
    mut v___x_4620_: *mut LeanObject,
    mut v___x_4621_: *mut LeanObject,
    mut v_varNames_4622_: *mut LeanObject,
    mut v_e_4623_: *mut LeanObject,
    mut v___x_4624_: u8,
    mut v___x_4625_: u8,
    mut v_xs_4626_: *mut LeanObject,
    mut v_codomain_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
    mut v___y_4629_: *mut LeanObject,
    mut v___y_4630_: *mut LeanObject,
    mut v___y_4631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: u8 = 0;
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: u8 = 0;
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4650_: u8 = 0;
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4633_ = lean_array_get_size(v_xs_4626_);
                v___x_4634_ = lean_nat_dec_eq(v___x_4633_, v___x_4620_);
                if v___x_4634_ == 0 {
                    lean_dec_ref(v_codomain_4627_);
                    lean_dec_ref(v_e_4623_);
                    lean_dec_ref(v_varNames_4622_);
                    v___x_4635_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2_once
                        ),
                        _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2,
                    );
                    v___x_4636_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(
                        v___x_4635_,
                        v___y_4628_,
                        v___y_4629_,
                        v___y_4630_,
                        v___y_4631_,
                    );
                    return v___x_4636_;
                } else {
                    lean_inc_ref(v_codomain_4627_);
                    v___x_4637_ = l_Lean_Meta_getLevel(
                        v_codomain_4627_,
                        v___y_4628_,
                        v___y_4629_,
                        v___y_4630_,
                        v___y_4631_,
                    );
                    if lean_obj_tag(v___x_4637_) == 0 {
                        v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
                        lean_inc(v_a_4638_);
                        lean_dec_ref_known(v___x_4637_, 1);
                        v___x_4639_ = lean_array_fget_borrowed(v_xs_4626_, v___x_4621_);
                        v___x_4640_ = lean_array_to_list(v_varNames_4622_);
                        lean_inc(v___x_4639_);
                        v___x_4641_ =
                            l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(
                                v___x_4640_,
                                v___x_4639_,
                                v_a_4638_,
                                v_codomain_4627_,
                                v_e_4623_,
                                v___y_4628_,
                                v___y_4629_,
                                v___y_4630_,
                                v___y_4631_,
                            );
                        if lean_obj_tag(v___x_4641_) == 0 {
                            v_a_4642_ = lean_ctor_get(v___x_4641_, 0);
                            lean_inc(v_a_4642_);
                            lean_dec_ref_known(v___x_4641_, 1);
                            v___x_4643_ = lean_mk_empty_array_with_capacity(v___x_4620_);
                            lean_inc(v___x_4639_);
                            v___x_4644_ = lean_array_push(v___x_4643_, v___x_4639_);
                            v___x_4645_ = 1;
                            v___x_4646_ = l_Lean_Meta_mkLambdaFVars(
                                v___x_4644_,
                                v_a_4642_,
                                v___x_4624_,
                                v___x_4625_,
                                v___x_4624_,
                                v___x_4625_,
                                v___x_4645_,
                                v___y_4628_,
                                v___y_4629_,
                                v___y_4630_,
                                v___y_4631_,
                            );
                            lean_dec_ref(v___x_4644_);
                            return v___x_4646_;
                        } else {
                            return v___x_4641_;
                        }
                    } else {
                        lean_dec_ref(v_codomain_4627_);
                        lean_dec_ref(v_e_4623_);
                        lean_dec_ref(v_varNames_4622_);
                        v_a_4647_ = lean_ctor_get(v___x_4637_, 0);
                        v_isSharedCheck_4654_ = (!lean_is_exclusive(v___x_4637_)) as u8;
                        if v_isSharedCheck_4654_ == 0 {
                            v___x_4649_ = v___x_4637_;
                            v_isShared_4650_ = v_isSharedCheck_4654_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4647_);
                            lean_dec(v___x_4637_);
                            v___x_4649_ = lean_box(0);
                            v_isShared_4650_ = v_isSharedCheck_4654_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4650_ == 0 {
                    v___x_4652_ = v___x_4649_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4653_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
                    v___x_4652_ = v_reuseFailAlloc_4653_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed(
    mut v___x_4655_: *mut LeanObject,
    mut v___x_4656_: *mut LeanObject,
    mut v_varNames_4657_: *mut LeanObject,
    mut v_e_4658_: *mut LeanObject,
    mut v___x_4659_: *mut LeanObject,
    mut v___x_4660_: *mut LeanObject,
    mut v_xs_4661_: *mut LeanObject,
    mut v_codomain_4662_: *mut LeanObject,
    mut v___y_4663_: *mut LeanObject,
    mut v___y_4664_: *mut LeanObject,
    mut v___y_4665_: *mut LeanObject,
    mut v___y_4666_: *mut LeanObject,
    mut v___y_4667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_987__boxed_4668_: u8 = 0;
    let mut v___x_988__boxed_4669_: u8 = 0;
    let mut v_res_4670_: *mut LeanObject = core::ptr::null_mut();
    v___x_987__boxed_4668_ = (lean_unbox(v___x_4659_) as u8);
    v___x_988__boxed_4669_ = (lean_unbox(v___x_4660_) as u8);
    v_res_4670_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(
        v___x_4655_,
        v___x_4656_,
        v_varNames_4657_,
        v_e_4658_,
        v___x_987__boxed_4668_,
        v___x_988__boxed_4669_,
        v_xs_4661_,
        v_codomain_4662_,
        v___y_4663_,
        v___y_4664_,
        v___y_4665_,
        v___y_4666_,
    );
    lean_dec(v___y_4666_);
    lean_dec_ref(v___y_4665_);
    lean_dec(v___y_4664_);
    lean_dec_ref(v___y_4663_);
    lean_dec_ref(v_xs_4661_);
    lean_dec(v___x_4656_);
    lean_dec(v___x_4655_);
    return v_res_4670_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_uncurry(
    mut v_varNames_4676_: *mut LeanObject,
    mut v_e_4677_: *mut LeanObject,
    mut v_a_4678_: *mut LeanObject,
    mut v_a_4679_: *mut LeanObject,
    mut v_a_4680_: *mut LeanObject,
    mut v_a_4681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: u8 = 0;
    v___x_4683_ = lean_array_get_size(v_varNames_4676_);
    v___x_4684_ = lean_unsigned_to_nat(0);
    v___x_4685_ = lean_nat_dec_eq(v___x_4683_, v___x_4684_);
    if v___x_4685_ == 0 {
        let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_a_4681_);
        lean_inc_ref(v_a_4680_);
        lean_inc(v_a_4679_);
        lean_inc_ref(v_a_4678_);
        lean_inc_ref(v_e_4677_);
        v___x_4686_ = lean_infer_type(v_e_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
        if lean_obj_tag(v___x_4686_) == 0 {
            let mut v_a_4687_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
            v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
            lean_inc(v_a_4687_);
            lean_dec_ref_known(v___x_4686_, 1);
            lean_inc_ref(v_varNames_4676_);
            v___x_4688_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(
                v_varNames_4676_,
                v_a_4687_,
                v_a_4678_,
                v_a_4679_,
                v_a_4680_,
                v_a_4681_,
            );
            if lean_obj_tag(v___x_4688_) == 0 {
                let mut v_a_4689_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4690_: u8 = 0;
                let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_4694_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
                v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
                lean_inc(v_a_4689_);
                lean_dec_ref_known(v___x_4688_, 1);
                v___x_4690_ = 1;
                v___x_4691_ = lean_unsigned_to_nat(1);
                v___x_4692_ = lean_box((v___x_4685_) as usize);
                v___x_4693_ = lean_box((v___x_4690_) as usize);
                v___f_4694_ = lean_alloc_closure(
                    l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed as *mut core::ffi::c_void,
                    13,
                    6,
                );
                lean_closure_set(v___f_4694_, 0, v___x_4691_);
                lean_closure_set(v___f_4694_, 1, v___x_4684_);
                lean_closure_set(v___f_4694_, 2, v_varNames_4676_);
                lean_closure_set(v___f_4694_, 3, v_e_4677_);
                lean_closure_set(v___f_4694_, 4, v___x_4692_);
                lean_closure_set(v___f_4694_, 5, v___x_4693_);
                v___x_4695_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0;
                v___x_4696_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_4689_, v___x_4695_, v___f_4694_, v___x_4685_, v___x_4685_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
                return v___x_4696_;
            } else {
                lean_dec_ref(v_e_4677_);
                lean_dec_ref(v_varNames_4676_);
                return v___x_4688_;
            }
        } else {
            lean_dec_ref(v_e_4677_);
            lean_dec_ref(v_varNames_4676_);
            return v___x_4686_;
        }
    } else {
        let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4698_: u8 = 0;
        let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_varNames_4676_);
        v___x_4697_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2;
        v___x_4698_ = 0;
        v___x_4699_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Unary_packType___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once),
            _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2,
        );
        v___x_4700_ = l_Lean_mkLambda(v___x_4697_, v___x_4698_, v___x_4699_, v_e_4677_);
        v___x_4701_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4701_, 0, v___x_4700_);
        return v___x_4701_;
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Unary_uncurry___boxed(
    mut v_varNames_4702_: *mut LeanObject,
    mut v_e_4703_: *mut LeanObject,
    mut v_a_4704_: *mut LeanObject,
    mut v_a_4705_: *mut LeanObject,
    mut v_a_4706_: *mut LeanObject,
    mut v_a_4707_: *mut LeanObject,
    mut v_a_4708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4709_: *mut LeanObject = core::ptr::null_mut();
    v_res_4709_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(
        v_varNames_4702_,
        v_e_4703_,
        v_a_4704_,
        v_a_4705_,
        v_a_4706_,
        v_a_4707_,
    );
    lean_dec(v_a_4707_);
    lean_dec_ref(v_a_4706_);
    lean_dec(v_a_4705_);
    lean_dec_ref(v_a_4704_);
    return v_res_4709_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1()
-> *mut LeanObject {
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    v___x_4711_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0;
    v___x_4712_ = l_Lean_stringToMessageData(v___x_4711_);
    return v___x_4712_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4715_: *mut LeanObject = core::ptr::null_mut();
    v___x_4713_ = lean_box(0);
    v___x_4714_ = l_Lean_Meta_ArgsPacker_Unary_packType___closed__1;
    v_dummy_4715_ = l_Lean_Expr_const___override(v___x_4714_, v___x_4713_);
    return v_dummy_4715_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(
    mut v_args_4716_: *mut LeanObject,
    mut v_type_4717_: *mut LeanObject,
    mut v_packedDomain_4718_: *mut LeanObject,
    mut v_tail_4719_: *mut LeanObject,
    mut v_x_4720_: *mut LeanObject,
    mut v___y_4721_: *mut LeanObject,
    mut v___y_4722_: *mut LeanObject,
    mut v___y_4723_: *mut LeanObject,
    mut v___y_4724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dummy_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    v_dummy_4726_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
    lean_inc_ref(v_x_4720_);
    v___x_4727_ = lean_array_push(v_args_4716_, v_x_4720_);
    v___x_4728_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(
        v_type_4717_,
        v_packedDomain_4718_,
        v_dummy_4726_,
        v___x_4727_,
        v_tail_4719_,
        v___y_4721_,
        v___y_4722_,
        v___y_4723_,
        v___y_4724_,
    );
    if lean_obj_tag(v___x_4728_) == 0 {
        let mut v_a_4729_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4733_: u8 = 0;
        let mut v___x_4734_: u8 = 0;
        let mut v___x_4735_: u8 = 0;
        let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
        v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
        lean_inc(v_a_4729_);
        lean_dec_ref_known(v___x_4728_, 1);
        v___x_4730_ = lean_unsigned_to_nat(1);
        v___x_4731_ = lean_mk_empty_array_with_capacity(v___x_4730_);
        v___x_4732_ = lean_array_push(v___x_4731_, v_x_4720_);
        v___x_4733_ = 0;
        v___x_4734_ = 1;
        v___x_4735_ = 1;
        v___x_4736_ = l_Lean_Meta_mkForallFVars(
            v___x_4732_,
            v_a_4729_,
            v___x_4733_,
            v___x_4734_,
            v___x_4734_,
            v___x_4735_,
            v___y_4721_,
            v___y_4722_,
            v___y_4723_,
            v___y_4724_,
        );
        lean_dec_ref(v___x_4732_);
        return v___x_4736_;
    } else {
        lean_dec_ref(v_x_4720_);
        return v___x_4728_;
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed(
    mut v_args_4737_: *mut LeanObject,
    mut v_type_4738_: *mut LeanObject,
    mut v_packedDomain_4739_: *mut LeanObject,
    mut v_tail_4740_: *mut LeanObject,
    mut v_x_4741_: *mut LeanObject,
    mut v___y_4742_: *mut LeanObject,
    mut v___y_4743_: *mut LeanObject,
    mut v___y_4744_: *mut LeanObject,
    mut v___y_4745_: *mut LeanObject,
    mut v___y_4746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4747_: *mut LeanObject = core::ptr::null_mut();
    v_res_4747_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(
            v_args_4737_,
            v_type_4738_,
            v_packedDomain_4739_,
            v_tail_4740_,
            v_x_4741_,
            v___y_4742_,
            v___y_4743_,
            v___y_4744_,
            v___y_4745_,
        );
    lean_dec(v___y_4745_);
    lean_dec_ref(v___y_4744_);
    lean_dec(v___y_4743_);
    lean_dec_ref(v___y_4742_);
    return v_res_4747_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed(
    mut v_arg_4748_: *mut LeanObject,
    mut v_args_4749_: *mut LeanObject,
    mut v_type_4750_: *mut LeanObject,
    mut v_packedDomain_4751_: *mut LeanObject,
    mut v_tail_4752_: *mut LeanObject,
    mut v___x_4753_: *mut LeanObject,
    mut v_x_4754_: *mut LeanObject,
    mut v___y_4755_: *mut LeanObject,
    mut v___y_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
    mut v___y_4759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_927__boxed_4760_: u8 = 0;
    let mut v_res_4761_: *mut LeanObject = core::ptr::null_mut();
    v___x_927__boxed_4760_ = (lean_unbox(v___x_4753_) as u8);
    v_res_4761_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(
            v_arg_4748_,
            v_args_4749_,
            v_type_4750_,
            v_packedDomain_4751_,
            v_tail_4752_,
            v___x_927__boxed_4760_,
            v_x_4754_,
            v___y_4755_,
            v___y_4756_,
            v___y_4757_,
            v___y_4758_,
        );
    lean_dec(v___y_4758_);
    lean_dec_ref(v___y_4757_);
    lean_dec(v___y_4756_);
    lean_dec_ref(v___y_4755_);
    return v_res_4761_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(
    mut v_type_4762_: *mut LeanObject,
    mut v_packedDomain_4763_: *mut LeanObject,
    mut v_domain_4764_: *mut LeanObject,
    mut v_args_4765_: *mut LeanObject,
    mut v_a_4766_: *mut LeanObject,
    mut v_a_4767_: *mut LeanObject,
    mut v_a_4768_: *mut LeanObject,
    mut v_a_4769_: *mut LeanObject,
    mut v_a_4770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packedArg_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: u8 = 0;
    let mut v_arg_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: u8 = 0;
    let mut v_arg_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: u8 = 0;
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4766_) == 0 {
                    lean_dec_ref(v_domain_4764_);
                    v_packedArg_4781_ =
                        l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_4763_, v_args_4765_);
                    lean_dec_ref(v_args_4765_);
                    lean_dec_ref(v_packedDomain_4763_);
                    v___x_4782_ = lean_unsigned_to_nat(1);
                    v___x_4783_ = lean_mk_empty_array_with_capacity(v___x_4782_);
                    v___x_4784_ = lean_array_push(v___x_4783_, v_packedArg_4781_);
                    v___x_4785_ = l_Lean_Meta_instantiateForall(
                        v_type_4762_,
                        v___x_4784_,
                        v_a_4767_,
                        v_a_4768_,
                        v_a_4769_,
                        v_a_4770_,
                    );
                    lean_dec_ref(v___x_4784_);
                    return v___x_4785_;
                } else {
                    v_tail_4786_ = lean_ctor_get(v_a_4766_, 1);
                    lean_inc(v_tail_4786_);
                    if lean_obj_tag(v_tail_4786_) == 0 {
                        v_head_4787_ = lean_ctor_get(v_a_4766_, 0);
                        lean_inc(v_head_4787_);
                        lean_dec_ref_known(v_a_4766_, 2);
                        v___f_4788_ = lean_alloc_closure(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                        lean_closure_set(v___f_4788_, 0, v_args_4765_);
                        lean_closure_set(v___f_4788_, 1, v_type_4762_);
                        lean_closure_set(v___f_4788_, 2, v_packedDomain_4763_);
                        lean_closure_set(v___f_4788_, 3, v_tail_4786_);
                        v___x_4789_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_4787_, v_domain_4764_, v___f_4788_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
                        return v___x_4789_;
                    } else {
                        v_head_4790_ = lean_ctor_get(v_a_4766_, 0);
                        lean_inc(v_head_4790_);
                        lean_dec_ref_known(v_a_4766_, 2);
                        lean_inc_ref(v_domain_4764_);
                        v___x_4791_ = l_Lean_Expr_cleanupAnnotations(v_domain_4764_);
                        v___x_4792_ = l_Lean_Expr_isApp(v___x_4791_);
                        if v___x_4792_ == 0 {
                            lean_dec_ref(v___x_4791_);
                            lean_dec(v_head_4790_);
                            lean_dec(v_tail_4786_);
                            lean_dec_ref(v_args_4765_);
                            lean_dec_ref(v_packedDomain_4763_);
                            lean_dec_ref(v_type_4762_);
                            v___y_4773_ = v_a_4767_;
                            v___y_4774_ = v_a_4768_;
                            v___y_4775_ = v_a_4769_;
                            v___y_4776_ = v_a_4770_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_4793_ = lean_ctor_get(v___x_4791_, 1);
                            lean_inc_ref(v_arg_4793_);
                            v___x_4794_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4791_);
                            v___x_4795_ = l_Lean_Expr_isApp(v___x_4794_);
                            if v___x_4795_ == 0 {
                                lean_dec_ref(v___x_4794_);
                                lean_dec_ref(v_arg_4793_);
                                lean_dec(v_head_4790_);
                                lean_dec(v_tail_4786_);
                                lean_dec_ref(v_args_4765_);
                                lean_dec_ref(v_packedDomain_4763_);
                                lean_dec_ref(v_type_4762_);
                                v___y_4773_ = v_a_4767_;
                                v___y_4774_ = v_a_4768_;
                                v___y_4775_ = v_a_4769_;
                                v___y_4776_ = v_a_4770_;
                                state = 1;
                                continue;
                            } else {
                                v_arg_4796_ = lean_ctor_get(v___x_4794_, 1);
                                lean_inc_ref(v_arg_4796_);
                                v___x_4797_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4794_);
                                v___x_4798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1;
                                v___x_4799_ = l_Lean_Expr_isConstOf(v___x_4797_, v___x_4798_);
                                lean_dec_ref(v___x_4797_);
                                if v___x_4799_ == 0 {
                                    lean_dec_ref(v_arg_4796_);
                                    lean_dec_ref(v_arg_4793_);
                                    lean_dec(v_head_4790_);
                                    lean_dec(v_tail_4786_);
                                    lean_dec_ref(v_args_4765_);
                                    lean_dec_ref(v_packedDomain_4763_);
                                    lean_dec_ref(v_type_4762_);
                                    v___y_4773_ = v_a_4767_;
                                    v___y_4774_ = v_a_4768_;
                                    v___y_4775_ = v_a_4769_;
                                    v___y_4776_ = v_a_4770_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref(v_domain_4764_);
                                    v___x_4800_ = lean_box((v___x_4799_) as usize);
                                    v___f_4801_ = lean_alloc_closure(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed as *mut core::ffi::c_void, 12, 6);
                                    lean_closure_set(v___f_4801_, 0, v_arg_4793_);
                                    lean_closure_set(v___f_4801_, 1, v_args_4765_);
                                    lean_closure_set(v___f_4801_, 2, v_type_4762_);
                                    lean_closure_set(v___f_4801_, 3, v_packedDomain_4763_);
                                    lean_closure_set(v___f_4801_, 4, v_tail_4786_);
                                    lean_closure_set(v___f_4801_, 5, v___x_4800_);
                                    v___x_4802_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_4790_, v_arg_4796_, v___f_4801_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
                                    return v___x_4802_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4777_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1);
                v___x_4778_ = l_Lean_MessageData_ofExpr(v_domain_4764_);
                v___x_4779_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4779_, 0, v___x_4777_);
                lean_ctor_set(v___x_4779_, 1, v___x_4778_);
                v___x_4780_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_4779_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
                return v___x_4780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(
    mut v_arg_4803_: *mut LeanObject,
    mut v_args_4804_: *mut LeanObject,
    mut v_type_4805_: *mut LeanObject,
    mut v_packedDomain_4806_: *mut LeanObject,
    mut v_tail_4807_: *mut LeanObject,
    mut v___x_4808_: u8,
    mut v_x_4809_: *mut LeanObject,
    mut v___y_4810_: *mut LeanObject,
    mut v___y_4811_: *mut LeanObject,
    mut v___y_4812_: *mut LeanObject,
    mut v___y_4813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    v___x_4815_ = lean_unsigned_to_nat(1);
    v___x_4816_ = lean_mk_empty_array_with_capacity(v___x_4815_);
    lean_inc_ref(v_x_4809_);
    v___x_4817_ = lean_array_push(v___x_4816_, v_x_4809_);
    lean_inc_ref(v___x_4817_);
    v___x_4818_ = l_Lean_Expr_beta(v_arg_4803_, v___x_4817_);
    v___x_4819_ = lean_array_push(v_args_4804_, v_x_4809_);
    v___x_4820_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(
        v_type_4805_,
        v_packedDomain_4806_,
        v___x_4818_,
        v___x_4819_,
        v_tail_4807_,
        v___y_4810_,
        v___y_4811_,
        v___y_4812_,
        v___y_4813_,
    );
    if lean_obj_tag(v___x_4820_) == 0 {
        let mut v_a_4821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4822_: u8 = 0;
        let mut v___x_4823_: u8 = 0;
        let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
        v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
        lean_inc(v_a_4821_);
        lean_dec_ref_known(v___x_4820_, 1);
        v___x_4822_ = 0;
        v___x_4823_ = 1;
        v___x_4824_ = l_Lean_Meta_mkForallFVars(
            v___x_4817_,
            v_a_4821_,
            v___x_4822_,
            v___x_4808_,
            v___x_4808_,
            v___x_4823_,
            v___y_4810_,
            v___y_4811_,
            v___y_4812_,
            v___y_4813_,
        );
        lean_dec_ref(v___x_4817_);
        return v___x_4824_;
    } else {
        lean_dec_ref(v___x_4817_);
        return v___x_4820_;
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___boxed(
    mut v_type_4825_: *mut LeanObject,
    mut v_packedDomain_4826_: *mut LeanObject,
    mut v_domain_4827_: *mut LeanObject,
    mut v_args_4828_: *mut LeanObject,
    mut v_a_4829_: *mut LeanObject,
    mut v_a_4830_: *mut LeanObject,
    mut v_a_4831_: *mut LeanObject,
    mut v_a_4832_: *mut LeanObject,
    mut v_a_4833_: *mut LeanObject,
    mut v_a_4834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4835_: *mut LeanObject = core::ptr::null_mut();
    v_res_4835_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(
        v_type_4825_,
        v_packedDomain_4826_,
        v_domain_4827_,
        v_args_4828_,
        v_a_4829_,
        v_a_4830_,
        v_a_4831_,
        v_a_4832_,
        v_a_4833_,
    );
    lean_dec(v_a_4833_);
    lean_dec_ref(v_a_4832_);
    lean_dec(v_a_4831_);
    lean_dec_ref(v_a_4830_);
    return v_res_4835_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1()
-> *mut LeanObject {
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    v___x_4837_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0;
    v___x_4838_ = l_Lean_stringToMessageData(v___x_4837_);
    return v___x_4838_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(
    mut v_varNames_4839_: *mut LeanObject,
    mut v_type_4840_: *mut LeanObject,
    mut v_a_4841_: *mut LeanObject,
    mut v_a_4842_: *mut LeanObject,
    mut v_a_4843_: *mut LeanObject,
    mut v_a_4844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packedDomain_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: u8 = 0;
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4863_: u8 = 0;
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4855_ = l_Lean_Expr_isForall(v_type_4840_);
                if v___x_4855_ == 0 {
                    lean_dec_ref(v_varNames_4839_);
                    v___x_4856_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
                    v___x_4857_ = l_Lean_MessageData_ofExpr(v_type_4840_);
                    v___x_4858_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4858_, 0, v___x_4856_);
                    lean_ctor_set(v___x_4858_, 1, v___x_4857_);
                    v___x_4859_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_4858_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_);
                    v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
                    v_isSharedCheck_4867_ = (!lean_is_exclusive(v___x_4859_)) as u8;
                    if v_isSharedCheck_4867_ == 0 {
                        v___x_4862_ = v___x_4859_;
                        v_isShared_4863_ = v_isSharedCheck_4867_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4860_);
                        lean_dec(v___x_4859_);
                        v___x_4862_ = lean_box(0);
                        v_isShared_4863_ = v_isSharedCheck_4867_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_4847_ = v_a_4841_;
                    v___y_4848_ = v_a_4842_;
                    v___y_4849_ = v_a_4843_;
                    v___y_4850_ = v_a_4844_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_packedDomain_4851_ = l_Lean_Expr_bindingDomain_x21(v_type_4840_);
                v___x_4852_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
                v___x_4853_ = lean_array_to_list(v_varNames_4839_);
                lean_inc_ref(v_packedDomain_4851_);
                v___x_4854_ =
                    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(
                        v_type_4840_,
                        v_packedDomain_4851_,
                        v_packedDomain_4851_,
                        v___x_4852_,
                        v___x_4853_,
                        v___y_4847_,
                        v___y_4848_,
                        v___y_4849_,
                        v___y_4850_,
                    );
                return v___x_4854_;
            }
            2 => {
                if v_isShared_4863_ == 0 {
                    v___x_4865_ = v___x_4862_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_a_4860_);
                    v___x_4865_ = v_reuseFailAlloc_4866_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___boxed(
    mut v_varNames_4868_: *mut LeanObject,
    mut v_type_4869_: *mut LeanObject,
    mut v_a_4870_: *mut LeanObject,
    mut v_a_4871_: *mut LeanObject,
    mut v_a_4872_: *mut LeanObject,
    mut v_a_4873_: *mut LeanObject,
    mut v_a_4874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4875_: *mut LeanObject = core::ptr::null_mut();
    v_res_4875_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(
        v_varNames_4868_,
        v_type_4869_,
        v_a_4870_,
        v_a_4871_,
        v_a_4872_,
        v_a_4873_,
    );
    lean_dec(v_a_4873_);
    lean_dec_ref(v_a_4872_);
    lean_dec(v_a_4871_);
    lean_dec_ref(v_a_4870_);
    return v_res_4875_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1()
-> *mut LeanObject {
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    v___x_4877_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0;
    v___x_4878_ = l_Lean_stringToMessageData(v___x_4877_);
    return v___x_4878_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(
    mut v_args_4879_: *mut LeanObject,
    mut v_e_4880_: *mut LeanObject,
    mut v_packedDomain_4881_: *mut LeanObject,
    mut v_tail_4882_: *mut LeanObject,
    mut v_x_4883_: *mut LeanObject,
    mut v___y_4884_: *mut LeanObject,
    mut v___y_4885_: *mut LeanObject,
    mut v___y_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dummy_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    v_dummy_4889_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
    lean_inc_ref(v_x_4883_);
    v___x_4890_ = lean_array_push(v_args_4879_, v_x_4883_);
    v___x_4891_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(
        v_e_4880_,
        v_packedDomain_4881_,
        v_dummy_4889_,
        v___x_4890_,
        v_tail_4882_,
        v___y_4884_,
        v___y_4885_,
        v___y_4886_,
        v___y_4887_,
    );
    if lean_obj_tag(v___x_4891_) == 0 {
        let mut v_a_4892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4896_: u8 = 0;
        let mut v___x_4897_: u8 = 0;
        let mut v___x_4898_: u8 = 0;
        let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
        v_a_4892_ = lean_ctor_get(v___x_4891_, 0);
        lean_inc(v_a_4892_);
        lean_dec_ref_known(v___x_4891_, 1);
        v___x_4893_ = lean_unsigned_to_nat(1);
        v___x_4894_ = lean_mk_empty_array_with_capacity(v___x_4893_);
        v___x_4895_ = lean_array_push(v___x_4894_, v_x_4883_);
        v___x_4896_ = 0;
        v___x_4897_ = 1;
        v___x_4898_ = 1;
        v___x_4899_ = l_Lean_Meta_mkLambdaFVars(
            v___x_4895_,
            v_a_4892_,
            v___x_4896_,
            v___x_4897_,
            v___x_4896_,
            v___x_4897_,
            v___x_4898_,
            v___y_4884_,
            v___y_4885_,
            v___y_4886_,
            v___y_4887_,
        );
        lean_dec_ref(v___x_4895_);
        return v___x_4899_;
    } else {
        lean_dec_ref(v_x_4883_);
        return v___x_4891_;
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed(
    mut v_args_4900_: *mut LeanObject,
    mut v_e_4901_: *mut LeanObject,
    mut v_packedDomain_4902_: *mut LeanObject,
    mut v_tail_4903_: *mut LeanObject,
    mut v_x_4904_: *mut LeanObject,
    mut v___y_4905_: *mut LeanObject,
    mut v___y_4906_: *mut LeanObject,
    mut v___y_4907_: *mut LeanObject,
    mut v___y_4908_: *mut LeanObject,
    mut v___y_4909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4910_: *mut LeanObject = core::ptr::null_mut();
    v_res_4910_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(
        v_args_4900_,
        v_e_4901_,
        v_packedDomain_4902_,
        v_tail_4903_,
        v_x_4904_,
        v___y_4905_,
        v___y_4906_,
        v___y_4907_,
        v___y_4908_,
    );
    lean_dec(v___y_4908_);
    lean_dec_ref(v___y_4907_);
    lean_dec(v___y_4906_);
    lean_dec_ref(v___y_4905_);
    return v_res_4910_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed(
    mut v_arg_4911_: *mut LeanObject,
    mut v_args_4912_: *mut LeanObject,
    mut v_e_4913_: *mut LeanObject,
    mut v_packedDomain_4914_: *mut LeanObject,
    mut v_tail_4915_: *mut LeanObject,
    mut v___x_4916_: *mut LeanObject,
    mut v_x_4917_: *mut LeanObject,
    mut v___y_4918_: *mut LeanObject,
    mut v___y_4919_: *mut LeanObject,
    mut v___y_4920_: *mut LeanObject,
    mut v___y_4921_: *mut LeanObject,
    mut v___y_4922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1045__boxed_4923_: u8 = 0;
    let mut v_res_4924_: *mut LeanObject = core::ptr::null_mut();
    v___x_1045__boxed_4923_ = (lean_unbox(v___x_4916_) as u8);
    v_res_4924_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(
        v_arg_4911_,
        v_args_4912_,
        v_e_4913_,
        v_packedDomain_4914_,
        v_tail_4915_,
        v___x_1045__boxed_4923_,
        v_x_4917_,
        v___y_4918_,
        v___y_4919_,
        v___y_4920_,
        v___y_4921_,
    );
    lean_dec(v___y_4921_);
    lean_dec_ref(v___y_4920_);
    lean_dec(v___y_4919_);
    lean_dec_ref(v___y_4918_);
    return v_res_4924_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(
    mut v_e_4925_: *mut LeanObject,
    mut v_packedDomain_4926_: *mut LeanObject,
    mut v_domain_4927_: *mut LeanObject,
    mut v_args_4928_: *mut LeanObject,
    mut v_a_4929_: *mut LeanObject,
    mut v_a_4930_: *mut LeanObject,
    mut v_a_4931_: *mut LeanObject,
    mut v_a_4932_: *mut LeanObject,
    mut v_a_4933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packedArg_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: u8 = 0;
    let mut v_arg_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: u8 = 0;
    let mut v_arg_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: u8 = 0;
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4929_) == 0 {
                    lean_dec_ref(v_domain_4927_);
                    v_packedArg_4944_ =
                        l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_4926_, v_args_4928_);
                    lean_dec_ref(v_args_4928_);
                    lean_dec_ref(v_packedDomain_4926_);
                    v___x_4945_ = lean_unsigned_to_nat(1);
                    v___x_4946_ = lean_mk_empty_array_with_capacity(v___x_4945_);
                    v___x_4947_ = lean_array_push(v___x_4946_, v_packedArg_4944_);
                    v___x_4948_ = l_Lean_Expr_beta(v_e_4925_, v___x_4947_);
                    v___x_4949_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4949_, 0, v___x_4948_);
                    return v___x_4949_;
                } else {
                    v_tail_4950_ = lean_ctor_get(v_a_4929_, 1);
                    lean_inc(v_tail_4950_);
                    if lean_obj_tag(v_tail_4950_) == 0 {
                        v_head_4951_ = lean_ctor_get(v_a_4929_, 0);
                        lean_inc(v_head_4951_);
                        lean_dec_ref_known(v_a_4929_, 2);
                        v___f_4952_ = lean_alloc_closure(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                        lean_closure_set(v___f_4952_, 0, v_args_4928_);
                        lean_closure_set(v___f_4952_, 1, v_e_4925_);
                        lean_closure_set(v___f_4952_, 2, v_packedDomain_4926_);
                        lean_closure_set(v___f_4952_, 3, v_tail_4950_);
                        v___x_4953_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_4951_, v_domain_4927_, v___f_4952_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
                        return v___x_4953_;
                    } else {
                        v_head_4954_ = lean_ctor_get(v_a_4929_, 0);
                        lean_inc(v_head_4954_);
                        lean_dec_ref_known(v_a_4929_, 2);
                        lean_inc_ref(v_domain_4927_);
                        v___x_4955_ = l_Lean_Expr_cleanupAnnotations(v_domain_4927_);
                        v___x_4956_ = l_Lean_Expr_isApp(v___x_4955_);
                        if v___x_4956_ == 0 {
                            lean_dec_ref(v___x_4955_);
                            lean_dec(v_head_4954_);
                            lean_dec(v_tail_4950_);
                            lean_dec_ref(v_args_4928_);
                            lean_dec_ref(v_packedDomain_4926_);
                            lean_dec_ref(v_e_4925_);
                            v___y_4936_ = v_a_4930_;
                            v___y_4937_ = v_a_4931_;
                            v___y_4938_ = v_a_4932_;
                            v___y_4939_ = v_a_4933_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_4957_ = lean_ctor_get(v___x_4955_, 1);
                            lean_inc_ref(v_arg_4957_);
                            v___x_4958_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4955_);
                            v___x_4959_ = l_Lean_Expr_isApp(v___x_4958_);
                            if v___x_4959_ == 0 {
                                lean_dec_ref(v___x_4958_);
                                lean_dec_ref(v_arg_4957_);
                                lean_dec(v_head_4954_);
                                lean_dec(v_tail_4950_);
                                lean_dec_ref(v_args_4928_);
                                lean_dec_ref(v_packedDomain_4926_);
                                lean_dec_ref(v_e_4925_);
                                v___y_4936_ = v_a_4930_;
                                v___y_4937_ = v_a_4931_;
                                v___y_4938_ = v_a_4932_;
                                v___y_4939_ = v_a_4933_;
                                state = 1;
                                continue;
                            } else {
                                v_arg_4960_ = lean_ctor_get(v___x_4958_, 1);
                                lean_inc_ref(v_arg_4960_);
                                v___x_4961_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4958_);
                                v___x_4962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1;
                                v___x_4963_ = l_Lean_Expr_isConstOf(v___x_4961_, v___x_4962_);
                                lean_dec_ref(v___x_4961_);
                                if v___x_4963_ == 0 {
                                    lean_dec_ref(v_arg_4960_);
                                    lean_dec_ref(v_arg_4957_);
                                    lean_dec(v_head_4954_);
                                    lean_dec(v_tail_4950_);
                                    lean_dec_ref(v_args_4928_);
                                    lean_dec_ref(v_packedDomain_4926_);
                                    lean_dec_ref(v_e_4925_);
                                    v___y_4936_ = v_a_4930_;
                                    v___y_4937_ = v_a_4931_;
                                    v___y_4938_ = v_a_4932_;
                                    v___y_4939_ = v_a_4933_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref(v_domain_4927_);
                                    v___x_4964_ = lean_box((v___x_4963_) as usize);
                                    v___f_4965_ = lean_alloc_closure(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed as *mut core::ffi::c_void, 12, 6);
                                    lean_closure_set(v___f_4965_, 0, v_arg_4957_);
                                    lean_closure_set(v___f_4965_, 1, v_args_4928_);
                                    lean_closure_set(v___f_4965_, 2, v_e_4925_);
                                    lean_closure_set(v___f_4965_, 3, v_packedDomain_4926_);
                                    lean_closure_set(v___f_4965_, 4, v_tail_4950_);
                                    lean_closure_set(v___f_4965_, 5, v___x_4964_);
                                    v___x_4966_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_4954_, v_arg_4960_, v___f_4965_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
                                    return v___x_4966_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4940_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1);
                v___x_4941_ = l_Lean_MessageData_ofExpr(v_domain_4927_);
                v___x_4942_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4942_, 0, v___x_4940_);
                lean_ctor_set(v___x_4942_, 1, v___x_4941_);
                v___x_4943_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_4942_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_);
                return v___x_4943_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(
    mut v_arg_4967_: *mut LeanObject,
    mut v_args_4968_: *mut LeanObject,
    mut v_e_4969_: *mut LeanObject,
    mut v_packedDomain_4970_: *mut LeanObject,
    mut v_tail_4971_: *mut LeanObject,
    mut v___x_4972_: u8,
    mut v_x_4973_: *mut LeanObject,
    mut v___y_4974_: *mut LeanObject,
    mut v___y_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
    mut v___y_4977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    v___x_4979_ = lean_unsigned_to_nat(1);
    v___x_4980_ = lean_mk_empty_array_with_capacity(v___x_4979_);
    lean_inc_ref(v_x_4973_);
    v___x_4981_ = lean_array_push(v___x_4980_, v_x_4973_);
    lean_inc_ref(v___x_4981_);
    v___x_4982_ = l_Lean_Expr_beta(v_arg_4967_, v___x_4981_);
    v___x_4983_ = lean_array_push(v_args_4968_, v_x_4973_);
    v___x_4984_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(
        v_e_4969_,
        v_packedDomain_4970_,
        v___x_4982_,
        v___x_4983_,
        v_tail_4971_,
        v___y_4974_,
        v___y_4975_,
        v___y_4976_,
        v___y_4977_,
    );
    if lean_obj_tag(v___x_4984_) == 0 {
        let mut v_a_4985_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4986_: u8 = 0;
        let mut v___x_4987_: u8 = 0;
        let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
        v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
        lean_inc(v_a_4985_);
        lean_dec_ref_known(v___x_4984_, 1);
        v___x_4986_ = 0;
        v___x_4987_ = 1;
        v___x_4988_ = l_Lean_Meta_mkLambdaFVars(
            v___x_4981_,
            v_a_4985_,
            v___x_4986_,
            v___x_4972_,
            v___x_4986_,
            v___x_4972_,
            v___x_4987_,
            v___y_4974_,
            v___y_4975_,
            v___y_4976_,
            v___y_4977_,
        );
        lean_dec_ref(v___x_4981_);
        return v___x_4988_;
    } else {
        lean_dec_ref(v___x_4981_);
        return v___x_4984_;
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___boxed(
    mut v_e_4989_: *mut LeanObject,
    mut v_packedDomain_4990_: *mut LeanObject,
    mut v_domain_4991_: *mut LeanObject,
    mut v_args_4992_: *mut LeanObject,
    mut v_a_4993_: *mut LeanObject,
    mut v_a_4994_: *mut LeanObject,
    mut v_a_4995_: *mut LeanObject,
    mut v_a_4996_: *mut LeanObject,
    mut v_a_4997_: *mut LeanObject,
    mut v_a_4998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4999_: *mut LeanObject = core::ptr::null_mut();
    v_res_4999_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(
        v_e_4989_,
        v_packedDomain_4990_,
        v_domain_4991_,
        v_args_4992_,
        v_a_4993_,
        v_a_4994_,
        v_a_4995_,
        v_a_4996_,
        v_a_4997_,
    );
    lean_dec(v_a_4997_);
    lean_dec_ref(v_a_4996_);
    lean_dec(v_a_4995_);
    lean_dec_ref(v_a_4994_);
    return v_res_4999_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1()
-> *mut LeanObject {
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    v___x_5001_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0;
    v___x_5002_ = l_Lean_stringToMessageData(v___x_5001_);
    return v___x_5002_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2()
-> *mut LeanObject {
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    v___x_5003_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Unary_pack___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once),
        _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2,
    );
    v___x_5004_ = lean_unsigned_to_nat(1);
    v___x_5005_ = lean_mk_empty_array_with_capacity(v___x_5004_);
    v___x_5006_ = lean_array_push(v___x_5005_, v___x_5003_);
    return v___x_5006_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(
    mut v_varNames_5007_: *mut LeanObject,
    mut v_e_5008_: *mut LeanObject,
    mut v_a_5009_: *mut LeanObject,
    mut v_a_5010_: *mut LeanObject,
    mut v_a_5011_: *mut LeanObject,
    mut v_a_5012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: u8 = 0;
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5038_: u8 = 0;
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5042_: u8 = 0;
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5014_ = lean_array_get_size(v_varNames_5007_);
                v___x_5015_ = lean_unsigned_to_nat(0);
                v___x_5016_ = lean_nat_dec_eq(v___x_5014_, v___x_5015_);
                if v___x_5016_ == 0 {
                    lean_inc(v_a_5012_);
                    lean_inc_ref(v_a_5011_);
                    lean_inc(v_a_5010_);
                    lean_inc_ref(v_a_5009_);
                    lean_inc_ref(v_e_5008_);
                    v___x_5017_ =
                        lean_infer_type(v_e_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
                    if lean_obj_tag(v___x_5017_) == 0 {
                        v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
                        lean_inc(v_a_5018_);
                        lean_dec_ref_known(v___x_5017_, 1);
                        v___x_5019_ = l_Lean_Meta_whnfForall(
                            v_a_5018_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_,
                        );
                        if lean_obj_tag(v___x_5019_) == 0 {
                            v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
                            lean_inc(v_a_5020_);
                            lean_dec_ref_known(v___x_5019_, 1);
                            v___x_5030_ = l_Lean_Expr_isForall(v_a_5020_);
                            if v___x_5030_ == 0 {
                                lean_dec_ref(v_e_5008_);
                                lean_dec_ref(v_varNames_5007_);
                                v___x_5031_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1);
                                v___x_5032_ = l_Lean_MessageData_ofExpr(v_a_5020_);
                                v___x_5033_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5033_, 0, v___x_5031_);
                                lean_ctor_set(v___x_5033_, 1, v___x_5032_);
                                v___x_5034_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_5033_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
                                v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
                                v_isSharedCheck_5042_ = (!lean_is_exclusive(v___x_5034_)) as u8;
                                if v_isSharedCheck_5042_ == 0 {
                                    v___x_5037_ = v___x_5034_;
                                    v_isShared_5038_ = v_isSharedCheck_5042_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_5035_);
                                    lean_dec(v___x_5034_);
                                    v___x_5037_ = lean_box(0);
                                    v_isShared_5038_ = v_isSharedCheck_5042_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___y_5022_ = v_a_5009_;
                                v___y_5023_ = v_a_5010_;
                                v___y_5024_ = v_a_5011_;
                                v___y_5025_ = v_a_5012_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_e_5008_);
                            lean_dec_ref(v_varNames_5007_);
                            return v___x_5019_;
                        }
                    } else {
                        lean_dec_ref(v_e_5008_);
                        lean_dec_ref(v_varNames_5007_);
                        return v___x_5017_;
                    }
                } else {
                    lean_dec_ref(v_varNames_5007_);
                    v___x_5043_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2);
                    v___x_5044_ = l_Lean_Expr_beta(v_e_5008_, v___x_5043_);
                    v___x_5045_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5045_, 0, v___x_5044_);
                    return v___x_5045_;
                }
            }
            1 => {
                v___x_5026_ = l_Lean_Expr_bindingDomain_x21(v_a_5020_);
                lean_dec(v_a_5020_);
                v___x_5027_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
                v___x_5028_ = lean_array_to_list(v_varNames_5007_);
                lean_inc_ref(v___x_5026_);
                v___x_5029_ =
                    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(
                        v_e_5008_,
                        v___x_5026_,
                        v___x_5026_,
                        v___x_5027_,
                        v___x_5028_,
                        v___y_5022_,
                        v___y_5023_,
                        v___y_5024_,
                        v___y_5025_,
                    );
                return v___x_5029_;
            }
            2 => {
                if v_isShared_5038_ == 0 {
                    v___x_5040_ = v___x_5037_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5041_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5035_);
                    v___x_5040_ = v_reuseFailAlloc_5041_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___boxed(
    mut v_varNames_5046_: *mut LeanObject,
    mut v_e_5047_: *mut LeanObject,
    mut v_a_5048_: *mut LeanObject,
    mut v_a_5049_: *mut LeanObject,
    mut v_a_5050_: *mut LeanObject,
    mut v_a_5051_: *mut LeanObject,
    mut v_a_5052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5053_: *mut LeanObject = core::ptr::null_mut();
    v_res_5053_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(
        v_varNames_5046_,
        v_e_5047_,
        v_a_5048_,
        v_a_5049_,
        v_a_5050_,
        v_a_5051_,
    );
    lean_dec(v_a_5051_);
    lean_dec_ref(v_a_5050_);
    lean_dec(v_a_5049_);
    lean_dec_ref(v_a_5048_);
    return v_res_5053_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(
    mut v_as_5057_: *mut LeanObject,
    mut v_sz_5058_: usize,
    mut v_i_5059_: usize,
    mut v_b_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
    mut v___y_5062_: *mut LeanObject,
    mut v___y_5063_: *mut LeanObject,
    mut v___y_5064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5066_: u8 = 0;
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: usize = 0;
    let mut v___x_5077_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5066_ = lean_usize_dec_lt(v_i_5059_, v_sz_5058_);
                if v___x_5066_ == 0 {
                    v___x_5067_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5067_, 0, v_b_5060_);
                    return v___x_5067_;
                } else {
                    v_a_5068_ = lean_array_uget_borrowed(v_as_5057_, v_i_5059_);
                    v___x_5069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1;
                    v___x_5070_ = lean_unsigned_to_nat(2);
                    v___x_5071_ = lean_mk_empty_array_with_capacity(v___x_5070_);
                    lean_inc(v_a_5068_);
                    v___x_5072_ = lean_array_push(v___x_5071_, v_a_5068_);
                    v___x_5073_ = lean_array_push(v___x_5072_, v_b_5060_);
                    v___x_5074_ = l_Lean_Meta_mkAppM(
                        v___x_5069_,
                        v___x_5073_,
                        v___y_5061_,
                        v___y_5062_,
                        v___y_5063_,
                        v___y_5064_,
                    );
                    if lean_obj_tag(v___x_5074_) == 0 {
                        v_a_5075_ = lean_ctor_get(v___x_5074_, 0);
                        lean_inc(v_a_5075_);
                        lean_dec_ref_known(v___x_5074_, 1);
                        v___x_5076_ = 1usize;
                        v___x_5077_ = lean_usize_add(v_i_5059_, v___x_5076_);
                        v_i_5059_ = v___x_5077_;
                        v_b_5060_ = v_a_5075_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5074_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___boxed(
    mut v_as_5079_: *mut LeanObject,
    mut v_sz_5080_: *mut LeanObject,
    mut v_i_5081_: *mut LeanObject,
    mut v_b_5082_: *mut LeanObject,
    mut v___y_5083_: *mut LeanObject,
    mut v___y_5084_: *mut LeanObject,
    mut v___y_5085_: *mut LeanObject,
    mut v___y_5086_: *mut LeanObject,
    mut v___y_5087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5088_: usize = 0;
    let mut v_i_boxed_5089_: usize = 0;
    let mut v_res_5090_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5088_ = lean_unbox_usize(v_sz_5080_);
    lean_dec(v_sz_5080_);
    v_i_boxed_5089_ = lean_unbox_usize(v_i_5081_);
    lean_dec(v_i_5081_);
    v_res_5090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v_as_5079_, v_sz_boxed_5088_, v_i_boxed_5089_, v_b_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_);
    lean_dec(v___y_5086_);
    lean_dec_ref(v___y_5085_);
    lean_dec(v___y_5084_);
    lean_dec_ref(v___y_5083_);
    lean_dec_ref(v_as_5079_);
    return v_res_5090_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_packType(
    mut v_ds_5091_: *mut LeanObject,
    mut v_a_5092_: *mut LeanObject,
    mut v_a_5093_: *mut LeanObject,
    mut v_a_5094_: *mut LeanObject,
    mut v_a_5095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5104_: usize = 0;
    let mut v___x_5105_: usize = 0;
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    v___x_5097_ = l_Lean_instInhabitedExpr;
    v___x_5098_ = lean_array_get_size(v_ds_5091_);
    v___x_5099_ = lean_unsigned_to_nat(1);
    v___x_5100_ = lean_nat_sub(v___x_5098_, v___x_5099_);
    v_r_5101_ = lean_array_get(v___x_5097_, v_ds_5091_, v___x_5100_);
    lean_dec(v___x_5100_);
    v___x_5102_ = lean_array_pop(v_ds_5091_);
    v___x_5103_ = l_Array_reverse___redArg(v___x_5102_);
    v_sz_5104_ = lean_array_size(v___x_5103_);
    v___x_5105_ = 0usize;
    v___x_5106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v___x_5103_, v_sz_5104_, v___x_5105_, v_r_5101_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_5095_);
    lean_dec_ref(v___x_5103_);
    return v___x_5106_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_packType___boxed(
    mut v_ds_5107_: *mut LeanObject,
    mut v_a_5108_: *mut LeanObject,
    mut v_a_5109_: *mut LeanObject,
    mut v_a_5110_: *mut LeanObject,
    mut v_a_5111_: *mut LeanObject,
    mut v_a_5112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5113_: *mut LeanObject = core::ptr::null_mut();
    v_res_5113_ = l_Lean_Meta_ArgsPacker_Mutual_packType(
        v_ds_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_,
    );
    lean_dec(v_a_5111_);
    lean_dec_ref(v_a_5110_);
    lean_dec(v_a_5109_);
    lean_dec_ref(v_a_5108_);
    return v_res_5113_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1()
-> *mut LeanObject {
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    v___x_5115_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0;
    v___x_5116_ = l_Lean_stringToMessageData(v___x_5115_);
    return v___x_5116_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(
    mut v_n_5117_: *mut LeanObject,
    mut v_type_5118_: *mut LeanObject,
    mut v_a_5119_: *mut LeanObject,
    mut v_a_5120_: *mut LeanObject,
    mut v_a_5121_: *mut LeanObject,
    mut v_a_5122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5134_: u8 = 0;
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: u8 = 0;
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: u8 = 0;
    let mut v_arg_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: u8 = 0;
    let mut v_arg_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: u8 = 0;
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5153_: u8 = 0;
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5158_: u8 = 0;
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5133_ = lean_unsigned_to_nat(0);
                v_isZero_5134_ = lean_nat_dec_eq(v_n_5117_, v_zero_5133_);
                if v_isZero_5134_ == 1 {
                    lean_dec_ref(v_type_5118_);
                    v___x_5135_ = lean_box(0);
                    v___x_5136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5136_, 0, v___x_5135_);
                    return v___x_5136_;
                } else {
                    v_one_5137_ = lean_unsigned_to_nat(1);
                    v_n_5138_ = lean_nat_sub(v_n_5117_, v_one_5137_);
                    v___x_5139_ = lean_nat_dec_eq(v_n_5138_, v_zero_5133_);
                    if v___x_5139_ == 0 {
                        lean_inc_ref(v_type_5118_);
                        v___x_5140_ = l_Lean_Expr_cleanupAnnotations(v_type_5118_);
                        v___x_5141_ = l_Lean_Expr_isApp(v___x_5140_);
                        if v___x_5141_ == 0 {
                            lean_dec_ref(v___x_5140_);
                            lean_dec(v_n_5138_);
                            v___y_5125_ = v_a_5119_;
                            v___y_5126_ = v_a_5120_;
                            v___y_5127_ = v_a_5121_;
                            v___y_5128_ = v_a_5122_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_5142_ = lean_ctor_get(v___x_5140_, 1);
                            lean_inc_ref(v_arg_5142_);
                            v___x_5143_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5140_);
                            v___x_5144_ = l_Lean_Expr_isApp(v___x_5143_);
                            if v___x_5144_ == 0 {
                                lean_dec_ref(v___x_5143_);
                                lean_dec_ref(v_arg_5142_);
                                lean_dec(v_n_5138_);
                                v___y_5125_ = v_a_5119_;
                                v___y_5126_ = v_a_5120_;
                                v___y_5127_ = v_a_5121_;
                                v___y_5128_ = v_a_5122_;
                                state = 1;
                                continue;
                            } else {
                                v_arg_5145_ = lean_ctor_get(v___x_5143_, 1);
                                lean_inc_ref(v_arg_5145_);
                                v___x_5146_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5143_);
                                v___x_5147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1;
                                v___x_5148_ = l_Lean_Expr_isConstOf(v___x_5146_, v___x_5147_);
                                lean_dec_ref(v___x_5146_);
                                if v___x_5148_ == 0 {
                                    lean_dec_ref(v_arg_5145_);
                                    lean_dec_ref(v_arg_5142_);
                                    lean_dec(v_n_5138_);
                                    v___y_5125_ = v_a_5119_;
                                    v___y_5126_ = v_a_5120_;
                                    v___y_5127_ = v_a_5121_;
                                    v___y_5128_ = v_a_5122_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref(v_type_5118_);
                                    v___x_5149_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_5138_, v_arg_5142_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_);
                                    lean_dec(v_n_5138_);
                                    if lean_obj_tag(v___x_5149_) == 0 {
                                        v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
                                        v_isSharedCheck_5158_ =
                                            (!lean_is_exclusive(v___x_5149_)) as u8;
                                        if v_isSharedCheck_5158_ == 0 {
                                            v___x_5152_ = v___x_5149_;
                                            v_isShared_5153_ = v_isSharedCheck_5158_;
                                            state = 2;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5150_);
                                            lean_dec(v___x_5149_);
                                            v___x_5152_ = lean_box(0);
                                            v_isShared_5153_ = v_isSharedCheck_5158_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_arg_5145_);
                                        return v___x_5149_;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_n_5138_);
                        v___x_5159_ = lean_box(0);
                        v___x_5160_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_5160_, 0, v_type_5118_);
                        lean_ctor_set(v___x_5160_, 1, v___x_5159_);
                        v___x_5161_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5161_, 0, v___x_5160_);
                        return v___x_5161_;
                    }
                }
            }
            1 => {
                v___x_5129_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1);
                v___x_5130_ = l_Lean_MessageData_ofExpr(v_type_5118_);
                v___x_5131_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5131_, 0, v___x_5129_);
                lean_ctor_set(v___x_5131_, 1, v___x_5130_);
                v___x_5132_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_5131_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
                return v___x_5132_;
            }
            2 => {
                v___x_5154_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5154_, 0, v_arg_5145_);
                lean_ctor_set(v___x_5154_, 1, v_a_5150_);
                if v_isShared_5153_ == 0 {
                    lean_ctor_set(v___x_5152_, 0, v___x_5154_);
                    v___x_5156_ = v___x_5152_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5154_);
                    v___x_5156_ = v_reuseFailAlloc_5157_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5156_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___boxed(
    mut v_n_5162_: *mut LeanObject,
    mut v_type_5163_: *mut LeanObject,
    mut v_a_5164_: *mut LeanObject,
    mut v_a_5165_: *mut LeanObject,
    mut v_a_5166_: *mut LeanObject,
    mut v_a_5167_: *mut LeanObject,
    mut v_a_5168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5169_: *mut LeanObject = core::ptr::null_mut();
    v_res_5169_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(
        v_n_5162_,
        v_type_5163_,
        v_a_5164_,
        v_a_5165_,
        v_a_5166_,
        v_a_5167_,
    );
    lean_dec(v_a_5167_);
    lean_dec_ref(v_a_5166_);
    lean_dec(v_a_5165_);
    lean_dec_ref(v_a_5164_);
    lean_dec(v_n_5162_);
    return v_res_5169_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0()
-> *mut LeanObject {
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_5171_: *mut LeanObject = core::ptr::null_mut();
    v___x_5170_ = lean_box(0);
    v_dummy_5171_ = l_Lean_Expr_sort___override(v___x_5170_);
    return v_dummy_5171_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    v___x_5174_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1;
    v___x_5175_ = lean_unsigned_to_nat(8);
    v___x_5176_ = lean_unsigned_to_nat(276);
    v___x_5177_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0;
    v___x_5178_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0;
    v___x_5179_ = l_mkPanicMessageWithDecl(
        v___x_5178_,
        v___x_5177_,
        v___x_5176_,
        v___x_5175_,
        v___x_5174_,
    );
    return v___x_5179_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(
    mut v_i_5188_: *mut LeanObject,
    mut v_fidx_5189_: *mut LeanObject,
    mut v_numFuncs_5190_: *mut LeanObject,
    mut v_arg_5191_: *mut LeanObject,
    mut v_x_5192_: *mut LeanObject,
    mut v_x_5193_: *mut LeanObject,
    mut v_x_5194_: *mut LeanObject,
    mut v___y_5195_: *mut LeanObject,
    mut v___y_5196_: *mut LeanObject,
    mut v___y_5197_: *mut LeanObject,
    mut v___y_5198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: u8 = 0;
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: u8 = 0;
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5219_: u8 = 0;
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5229_: u8 = 0;
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5200_ = lean_unsigned_to_nat(1);
                if lean_obj_tag(v_x_5192_) == 5 {
                    v_fn_5201_ = lean_ctor_get(v_x_5192_, 0);
                    lean_inc_ref(v_fn_5201_);
                    v_arg_5202_ = lean_ctor_get(v_x_5192_, 1);
                    lean_inc_ref(v_arg_5202_);
                    lean_dec_ref_known(v_x_5192_, 2);
                    v___x_5203_ = lean_array_set(v_x_5193_, v_x_5194_, v_arg_5202_);
                    v___x_5204_ = lean_nat_sub(v_x_5194_, v___x_5200_);
                    lean_dec(v_x_5194_);
                    v_x_5192_ = v_fn_5201_;
                    v_x_5193_ = v___x_5203_;
                    v_x_5194_ = v___x_5204_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_5194_);
                    v___x_5206_ = lean_array_get_size(v_x_5193_);
                    v___x_5207_ = lean_unsigned_to_nat(2);
                    v___x_5208_ = lean_nat_dec_eq(v___x_5206_, v___x_5207_);
                    if v___x_5208_ == 0 {
                        lean_dec_ref(v_x_5193_);
                        lean_dec_ref(v_x_5192_);
                        lean_dec_ref(v_arg_5191_);
                        v___x_5209_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2_once), _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2);
                        v___x_5210_ =
                            l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(
                                v___x_5209_,
                                v___y_5195_,
                                v___y_5196_,
                                v___y_5197_,
                                v___y_5198_,
                            );
                        return v___x_5210_;
                    } else {
                        v___x_5211_ = lean_nat_dec_eq(v_i_5188_, v_fidx_5189_);
                        if v___x_5211_ == 0 {
                            v___x_5212_ = lean_nat_add(v_i_5188_, v___x_5200_);
                            v___x_5213_ = l_Lean_instInhabitedExpr;
                            v___x_5214_ = lean_array_get(v___x_5213_, v_x_5193_, v___x_5200_);
                            lean_inc(v___x_5214_);
                            v___x_5215_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_5190_, v_fidx_5189_, v_arg_5191_, v___x_5212_, v___x_5214_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_);
                            lean_dec(v___x_5212_);
                            if lean_obj_tag(v___x_5215_) == 0 {
                                v_a_5216_ = lean_ctor_get(v___x_5215_, 0);
                                v_isSharedCheck_5229_ = (!lean_is_exclusive(v___x_5215_)) as u8;
                                if v_isSharedCheck_5229_ == 0 {
                                    v___x_5218_ = v___x_5215_;
                                    v_isShared_5219_ = v_isSharedCheck_5229_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_5216_);
                                    lean_dec(v___x_5215_);
                                    v___x_5218_ = lean_box(0);
                                    v_isShared_5219_ = v_isSharedCheck_5229_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_5214_);
                                lean_dec_ref(v_x_5193_);
                                lean_dec_ref(v_x_5192_);
                                return v___x_5215_;
                            }
                        } else {
                            v___x_5230_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6;
                            v___x_5231_ = l_Lean_Expr_constLevels_x21(v_x_5192_);
                            lean_dec_ref(v_x_5192_);
                            v___x_5232_ = l_Lean_mkConst(v___x_5230_, v___x_5231_);
                            v___x_5233_ = l_Lean_instInhabitedExpr;
                            v___x_5234_ = lean_unsigned_to_nat(0);
                            v___x_5235_ = lean_array_get(v___x_5233_, v_x_5193_, v___x_5234_);
                            v___x_5236_ = lean_array_get(v___x_5233_, v_x_5193_, v___x_5200_);
                            lean_dec_ref(v_x_5193_);
                            v___x_5237_ =
                                l_Lean_mkApp3(v___x_5232_, v___x_5235_, v___x_5236_, v_arg_5191_);
                            v___x_5238_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5238_, 0, v___x_5237_);
                            return v___x_5238_;
                        }
                    }
                }
            }
            1 => {
                v___x_5220_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4;
                v___x_5221_ = l_Lean_Expr_constLevels_x21(v_x_5192_);
                lean_dec_ref(v_x_5192_);
                v___x_5222_ = l_Lean_mkConst(v___x_5220_, v___x_5221_);
                v___x_5223_ = lean_unsigned_to_nat(0);
                v___x_5224_ = lean_array_get(v___x_5213_, v_x_5193_, v___x_5223_);
                lean_dec_ref(v_x_5193_);
                v___x_5225_ = l_Lean_mkApp3(v___x_5222_, v___x_5224_, v___x_5214_, v_a_5216_);
                if v_isShared_5219_ == 0 {
                    lean_ctor_set(v___x_5218_, 0, v___x_5225_);
                    v___x_5227_ = v___x_5218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5228_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5228_, 0, v___x_5225_);
                    v___x_5227_ = v_reuseFailAlloc_5228_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(
    mut v_numFuncs_5239_: *mut LeanObject,
    mut v_fidx_5240_: *mut LeanObject,
    mut v_arg_5241_: *mut LeanObject,
    mut v_i_5242_: *mut LeanObject,
    mut v_type_5243_: *mut LeanObject,
    mut v_a_5244_: *mut LeanObject,
    mut v_a_5245_: *mut LeanObject,
    mut v_a_5246_: *mut LeanObject,
    mut v_a_5247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: u8 = 0;
    v___x_5249_ = lean_unsigned_to_nat(1);
    v___x_5250_ = lean_nat_sub(v_numFuncs_5239_, v___x_5249_);
    v___x_5251_ = lean_nat_dec_le(v___x_5250_, v_i_5242_);
    lean_dec(v___x_5250_);
    if v___x_5251_ == 0 {
        let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
        v___x_5252_ = l_Lean_Meta_whnfD(v_type_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
        if lean_obj_tag(v___x_5252_) == 0 {
            let mut v_a_5253_: *mut LeanObject = core::ptr::null_mut();
            let mut v_dummy_5254_: *mut LeanObject = core::ptr::null_mut();
            let mut v_nargs_5255_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
            v_a_5253_ = lean_ctor_get(v___x_5252_, 0);
            lean_inc(v_a_5253_);
            lean_dec_ref_known(v___x_5252_, 1);
            v_dummy_5254_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
            v_nargs_5255_ = l_Lean_Expr_getAppNumArgs(v_a_5253_);
            lean_inc(v_nargs_5255_);
            v___x_5256_ = lean_mk_array(v_nargs_5255_, v_dummy_5254_);
            v___x_5257_ = lean_nat_sub(v_nargs_5255_, v___x_5249_);
            lean_dec(v_nargs_5255_);
            v___x_5258_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_5242_, v_fidx_5240_, v_numFuncs_5239_, v_arg_5241_, v_a_5253_, v___x_5256_, v___x_5257_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
            return v___x_5258_;
        } else {
            lean_dec_ref(v_arg_5241_);
            return v___x_5252_;
        }
    } else {
        let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_type_5243_);
        v___x_5259_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5259_, 0, v_arg_5241_);
        return v___x_5259_;
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___boxed(
    mut v_numFuncs_5260_: *mut LeanObject,
    mut v_fidx_5261_: *mut LeanObject,
    mut v_arg_5262_: *mut LeanObject,
    mut v_i_5263_: *mut LeanObject,
    mut v_type_5264_: *mut LeanObject,
    mut v_a_5265_: *mut LeanObject,
    mut v_a_5266_: *mut LeanObject,
    mut v_a_5267_: *mut LeanObject,
    mut v_a_5268_: *mut LeanObject,
    mut v_a_5269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5270_: *mut LeanObject = core::ptr::null_mut();
    v_res_5270_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(
        v_numFuncs_5260_,
        v_fidx_5261_,
        v_arg_5262_,
        v_i_5263_,
        v_type_5264_,
        v_a_5265_,
        v_a_5266_,
        v_a_5267_,
        v_a_5268_,
    );
    lean_dec(v_a_5268_);
    lean_dec_ref(v_a_5267_);
    lean_dec(v_a_5266_);
    lean_dec_ref(v_a_5265_);
    lean_dec(v_i_5263_);
    lean_dec(v_fidx_5261_);
    lean_dec(v_numFuncs_5260_);
    return v_res_5270_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___boxed(
    mut v_i_5271_: *mut LeanObject,
    mut v_fidx_5272_: *mut LeanObject,
    mut v_numFuncs_5273_: *mut LeanObject,
    mut v_arg_5274_: *mut LeanObject,
    mut v_x_5275_: *mut LeanObject,
    mut v_x_5276_: *mut LeanObject,
    mut v_x_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
    mut v___y_5280_: *mut LeanObject,
    mut v___y_5281_: *mut LeanObject,
    mut v___y_5282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5283_: *mut LeanObject = core::ptr::null_mut();
    v_res_5283_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_5271_, v_fidx_5272_, v_numFuncs_5273_, v_arg_5274_, v_x_5275_, v_x_5276_, v_x_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_);
    lean_dec(v___y_5281_);
    lean_dec_ref(v___y_5280_);
    lean_dec(v___y_5279_);
    lean_dec_ref(v___y_5278_);
    lean_dec(v_numFuncs_5273_);
    lean_dec(v_fidx_5272_);
    lean_dec(v_i_5271_);
    return v_res_5283_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_pack(
    mut v_numFuncs_5284_: *mut LeanObject,
    mut v_domain_5285_: *mut LeanObject,
    mut v_fidx_5286_: *mut LeanObject,
    mut v_arg_5287_: *mut LeanObject,
    mut v_a_5288_: *mut LeanObject,
    mut v_a_5289_: *mut LeanObject,
    mut v_a_5290_: *mut LeanObject,
    mut v_a_5291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    v___x_5293_ = lean_unsigned_to_nat(0);
    v___x_5294_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(
        v_numFuncs_5284_,
        v_fidx_5286_,
        v_arg_5287_,
        v___x_5293_,
        v_domain_5285_,
        v_a_5288_,
        v_a_5289_,
        v_a_5290_,
        v_a_5291_,
    );
    return v___x_5294_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_pack___boxed(
    mut v_numFuncs_5295_: *mut LeanObject,
    mut v_domain_5296_: *mut LeanObject,
    mut v_fidx_5297_: *mut LeanObject,
    mut v_arg_5298_: *mut LeanObject,
    mut v_a_5299_: *mut LeanObject,
    mut v_a_5300_: *mut LeanObject,
    mut v_a_5301_: *mut LeanObject,
    mut v_a_5302_: *mut LeanObject,
    mut v_a_5303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5304_: *mut LeanObject = core::ptr::null_mut();
    v_res_5304_ = l_Lean_Meta_ArgsPacker_Mutual_pack(
        v_numFuncs_5295_,
        v_domain_5296_,
        v_fidx_5297_,
        v_arg_5298_,
        v_a_5299_,
        v_a_5300_,
        v_a_5301_,
        v_a_5302_,
    );
    lean_dec(v_a_5302_);
    lean_dec_ref(v_a_5301_);
    lean_dec(v_a_5300_);
    lean_dec_ref(v_a_5299_);
    lean_dec(v_fidx_5297_);
    lean_dec(v_numFuncs_5295_);
    return v_res_5304_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(
    mut v_numFuncs_5305_: *mut LeanObject,
    mut v_a_5306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5311_: u8 = 0;
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: u8 = 0;
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: u8 = 0;
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: u8 = 0;
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5307_ = lean_ctor_get(v_a_5306_, 0);
                v_snd_5308_ = lean_ctor_get(v_a_5306_, 1);
                v_isSharedCheck_5343_ = (!lean_is_exclusive(v_a_5306_)) as u8;
                if v_isSharedCheck_5343_ == 0 {
                    v___x_5310_ = v_a_5306_;
                    v_isShared_5311_ = v_isSharedCheck_5343_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_5308_);
                    lean_inc(v_fst_5307_);
                    lean_dec(v_a_5306_);
                    v___x_5310_ = lean_box(0);
                    v_isShared_5311_ = v_isSharedCheck_5343_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5312_ = lean_unsigned_to_nat(1);
                v___x_5313_ = lean_nat_add(v_fst_5307_, v___x_5312_);
                v___x_5314_ = lean_nat_dec_lt(v___x_5313_, v_numFuncs_5305_);
                if v___x_5314_ == 0 {
                    lean_dec(v___x_5313_);
                    if v_isShared_5311_ == 0 {
                        v___x_5316_ = v___x_5310_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_fst_5307_);
                        lean_ctor_set(v_reuseFailAlloc_5318_, 1, v_snd_5308_);
                        v___x_5316_ = v_reuseFailAlloc_5318_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5319_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4;
                    v___x_5320_ = lean_unsigned_to_nat(3);
                    v___x_5321_ = l_Lean_Expr_isAppOfArity(v_snd_5308_, v___x_5319_, v___x_5320_);
                    if v___x_5321_ == 0 {
                        lean_dec(v___x_5313_);
                        v___x_5322_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6;
                        v___x_5323_ =
                            l_Lean_Expr_isAppOfArity(v_snd_5308_, v___x_5322_, v___x_5320_);
                        if v___x_5323_ == 0 {
                            lean_del_object(v___x_5310_);
                            lean_dec(v_snd_5308_);
                            lean_dec(v_fst_5307_);
                            v___x_5324_ = lean_box(0);
                            return v___x_5324_;
                        } else {
                            v___x_5325_ = lean_unsigned_to_nat(2);
                            v___x_5326_ = l_Lean_Expr_getAppNumArgs(v_snd_5308_);
                            v___x_5327_ = lean_nat_sub(v___x_5326_, v___x_5325_);
                            lean_dec(v___x_5326_);
                            v___x_5328_ = lean_nat_sub(v___x_5327_, v___x_5312_);
                            lean_dec(v___x_5327_);
                            v___x_5329_ = l_Lean_Expr_getRevArg_x21(v_snd_5308_, v___x_5328_);
                            lean_dec(v_snd_5308_);
                            if v_isShared_5311_ == 0 {
                                lean_ctor_set(v___x_5310_, 1, v___x_5329_);
                                v___x_5331_ = v___x_5310_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_fst_5307_);
                                lean_ctor_set(v_reuseFailAlloc_5333_, 1, v___x_5329_);
                                v___x_5331_ = v_reuseFailAlloc_5333_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_fst_5307_);
                        v___x_5334_ = lean_unsigned_to_nat(2);
                        v___x_5335_ = l_Lean_Expr_getAppNumArgs(v_snd_5308_);
                        v___x_5336_ = lean_nat_sub(v___x_5335_, v___x_5334_);
                        lean_dec(v___x_5335_);
                        v___x_5337_ = lean_nat_sub(v___x_5336_, v___x_5312_);
                        lean_dec(v___x_5336_);
                        v___x_5338_ = l_Lean_Expr_getRevArg_x21(v_snd_5308_, v___x_5337_);
                        lean_dec(v_snd_5308_);
                        if v_isShared_5311_ == 0 {
                            lean_ctor_set(v___x_5310_, 1, v___x_5338_);
                            lean_ctor_set(v___x_5310_, 0, v___x_5313_);
                            v___x_5340_ = v___x_5310_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5342_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5342_, 0, v___x_5313_);
                            lean_ctor_set(v_reuseFailAlloc_5342_, 1, v___x_5338_);
                            v___x_5340_ = v_reuseFailAlloc_5342_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_5317_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5317_, 0, v___x_5316_);
                return v___x_5317_;
            }
            3 => {
                v___x_5332_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5332_, 0, v___x_5331_);
                return v___x_5332_;
            }
            4 => {
                v_a_5306_ = v___x_5340_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg___boxed(
    mut v_numFuncs_5344_: *mut LeanObject,
    mut v_a_5345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5346_: *mut LeanObject = core::ptr::null_mut();
    v_res_5346_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_5344_, v_a_5345_);
    lean_dec(v_numFuncs_5344_);
    return v_res_5346_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_unpack(
    mut v_numFuncs_5347_: *mut LeanObject,
    mut v_expr_5348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_funidx_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5355_: u8 = 0;
    let mut v_fst_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5360_: u8 = 0;
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5367_: u8 = 0;
    let mut v_isSharedCheck_5368_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_funidx_5349_ = lean_unsigned_to_nat(0);
                v___x_5350_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5350_, 0, v_funidx_5349_);
                lean_ctor_set(v___x_5350_, 1, v_expr_5348_);
                v___x_5351_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_5347_, v___x_5350_);
                if lean_obj_tag(v___x_5351_) == 0 {
                    return v___x_5351_;
                } else {
                    v_val_5352_ = lean_ctor_get(v___x_5351_, 0);
                    v_isSharedCheck_5368_ = (!lean_is_exclusive(v___x_5351_)) as u8;
                    if v_isSharedCheck_5368_ == 0 {
                        v___x_5354_ = v___x_5351_;
                        v_isShared_5355_ = v_isSharedCheck_5368_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5352_);
                        lean_dec(v___x_5351_);
                        v___x_5354_ = lean_box(0);
                        v_isShared_5355_ = v_isSharedCheck_5368_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5356_ = lean_ctor_get(v_val_5352_, 0);
                v_snd_5357_ = lean_ctor_get(v_val_5352_, 1);
                v_isSharedCheck_5367_ = (!lean_is_exclusive(v_val_5352_)) as u8;
                if v_isSharedCheck_5367_ == 0 {
                    v___x_5359_ = v_val_5352_;
                    v_isShared_5360_ = v_isSharedCheck_5367_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_5357_);
                    lean_inc(v_fst_5356_);
                    lean_dec(v_val_5352_);
                    v___x_5359_ = lean_box(0);
                    v_isShared_5360_ = v_isSharedCheck_5367_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5360_ == 0 {
                    v___x_5362_ = v___x_5359_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_fst_5356_);
                    lean_ctor_set(v_reuseFailAlloc_5366_, 1, v_snd_5357_);
                    v___x_5362_ = v_reuseFailAlloc_5366_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5355_ == 0 {
                    lean_ctor_set(v___x_5354_, 0, v___x_5362_);
                    v___x_5364_ = v___x_5354_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5365_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5365_, 0, v___x_5362_);
                    v___x_5364_ = v_reuseFailAlloc_5365_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_unpack___boxed(
    mut v_numFuncs_5369_: *mut LeanObject,
    mut v_expr_5370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5371_: *mut LeanObject = core::ptr::null_mut();
    v_res_5371_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v_numFuncs_5369_, v_expr_5370_);
    lean_dec(v_numFuncs_5369_);
    return v_res_5371_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(
    mut v_numFuncs_5372_: *mut LeanObject,
    mut v_inst_5373_: *mut LeanObject,
    mut v_a_5374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    v___x_5375_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_5372_, v_a_5374_);
    return v___x_5375_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___boxed(
    mut v_numFuncs_5376_: *mut LeanObject,
    mut v_inst_5377_: *mut LeanObject,
    mut v_a_5378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5379_: *mut LeanObject = core::ptr::null_mut();
    v_res_5379_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(
            v_numFuncs_5376_,
            v_inst_5377_,
            v_a_5378_,
        );
    lean_dec(v_numFuncs_5376_);
    return v_res_5379_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(
    mut v___x_5380_: *mut LeanObject,
    mut v___x_5381_: *mut LeanObject,
    mut v_types_5382_: *mut LeanObject,
    mut v_i_5383_: *mut LeanObject,
    mut v___x_5384_: u8,
    mut v___x_5385_: u8,
    mut v___x_5386_: u8,
    mut v_x_5387_: *mut LeanObject,
    mut v___y_5388_: *mut LeanObject,
    mut v___y_5389_: *mut LeanObject,
    mut v___y_5390_: *mut LeanObject,
    mut v___y_5391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_x_5387_);
    v___x_5393_ = lean_array_push(v___x_5380_, v_x_5387_);
    v___x_5394_ = lean_array_get_borrowed(v___x_5381_, v_types_5382_, v_i_5383_);
    v___x_5395_ = l_Lean_Expr_bindingBody_x21(v___x_5394_);
    v___x_5396_ = lean_expr_instantiate1(v___x_5395_, v_x_5387_);
    lean_dec_ref(v_x_5387_);
    lean_dec_ref(v___x_5395_);
    v___x_5397_ = l_Lean_Meta_mkLambdaFVars(
        v___x_5393_,
        v___x_5396_,
        v___x_5384_,
        v___x_5385_,
        v___x_5384_,
        v___x_5385_,
        v___x_5386_,
        v___y_5388_,
        v___y_5389_,
        v___y_5390_,
        v___y_5391_,
    );
    lean_dec_ref(v___x_5393_);
    return v___x_5397_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(
    mut v___x_5398_: *mut LeanObject,
    mut v___x_5399_: *mut LeanObject,
    mut v_types_5400_: *mut LeanObject,
    mut v_i_5401_: *mut LeanObject,
    mut v___x_5402_: *mut LeanObject,
    mut v___x_5403_: *mut LeanObject,
    mut v___x_5404_: *mut LeanObject,
    mut v_x_5405_: *mut LeanObject,
    mut v___y_5406_: *mut LeanObject,
    mut v___y_5407_: *mut LeanObject,
    mut v___y_5408_: *mut LeanObject,
    mut v___y_5409_: *mut LeanObject,
    mut v___y_5410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1974__boxed_5411_: u8 = 0;
    let mut v___x_1975__boxed_5412_: u8 = 0;
    let mut v___x_1976__boxed_5413_: u8 = 0;
    let mut v_res_5414_: *mut LeanObject = core::ptr::null_mut();
    v___x_1974__boxed_5411_ = (lean_unbox(v___x_5402_) as u8);
    v___x_1975__boxed_5412_ = (lean_unbox(v___x_5403_) as u8);
    v___x_1976__boxed_5413_ = (lean_unbox(v___x_5404_) as u8);
    v_res_5414_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(
            v___x_5398_,
            v___x_5399_,
            v_types_5400_,
            v_i_5401_,
            v___x_1974__boxed_5411_,
            v___x_1975__boxed_5412_,
            v___x_1976__boxed_5413_,
            v_x_5405_,
            v___y_5406_,
            v___y_5407_,
            v___y_5408_,
            v___y_5409_,
        );
    lean_dec(v___y_5409_);
    lean_dec_ref(v___y_5408_);
    lean_dec(v___y_5407_);
    lean_dec_ref(v___y_5406_);
    lean_dec(v_i_5401_);
    lean_dec_ref(v_types_5400_);
    lean_dec_ref(v___x_5399_);
    return v_res_5414_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2()
-> *mut LeanObject {
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    v___x_5417_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1;
    v___x_5418_ = lean_unsigned_to_nat(6);
    v___x_5419_ = lean_unsigned_to_nat(318);
    v___x_5420_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0;
    v___x_5421_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0;
    v___x_5422_ = l_mkPanicMessageWithDecl(
        v___x_5421_,
        v___x_5420_,
        v___x_5419_,
        v___x_5418_,
        v___x_5417_,
    );
    return v___x_5422_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(
    mut v_i_5423_: *mut LeanObject,
    mut v___x_5424_: *mut LeanObject,
    mut v_types_5425_: *mut LeanObject,
    mut v_u_5426_: *mut LeanObject,
    mut v___x_5427_: *mut LeanObject,
    mut v___x_5428_: *mut LeanObject,
    mut v___x_5429_: *mut LeanObject,
    mut v___x_5430_: *mut LeanObject,
    mut v_x_5431_: *mut LeanObject,
    mut v___y_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
    mut v___y_5435_: *mut LeanObject,
    mut v___y_5436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2034__boxed_5437_: u8 = 0;
    let mut v___x_2035__boxed_5438_: u8 = 0;
    let mut v___x_2036__boxed_5439_: u8 = 0;
    let mut v_res_5440_: *mut LeanObject = core::ptr::null_mut();
    v___x_2034__boxed_5437_ = (lean_unbox(v___x_5428_) as u8);
    v___x_2035__boxed_5438_ = (lean_unbox(v___x_5429_) as u8);
    v___x_2036__boxed_5439_ = (lean_unbox(v___x_5430_) as u8);
    v_res_5440_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(
            v_i_5423_,
            v___x_5424_,
            v_types_5425_,
            v_u_5426_,
            v___x_5427_,
            v___x_2034__boxed_5437_,
            v___x_2035__boxed_5438_,
            v___x_2036__boxed_5439_,
            v_x_5431_,
            v___y_5432_,
            v___y_5433_,
            v___y_5434_,
            v___y_5435_,
        );
    lean_dec(v___y_5435_);
    lean_dec_ref(v___y_5434_);
    lean_dec(v___y_5433_);
    lean_dec_ref(v___y_5432_);
    lean_dec(v___x_5424_);
    lean_dec(v_i_5423_);
    return v_res_5440_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(
    mut v_types_5444_: *mut LeanObject,
    mut v_u_5445_: *mut LeanObject,
    mut v_x_5446_: *mut LeanObject,
    mut v_i_5447_: *mut LeanObject,
    mut v_a_5448_: *mut LeanObject,
    mut v_a_5449_: *mut LeanObject,
    mut v_a_5450_: *mut LeanObject,
    mut v_a_5451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: u8 = 0;
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: u8 = 0;
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: u8 = 0;
    let mut v___x_5476_: u8 = 0;
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5507_: u8 = 0;
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5520_: u8 = 0;
    let mut v_a_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5524_: u8 = 0;
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5528_: u8 = 0;
    let mut v_a_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5532_: u8 = 0;
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5453_ = lean_array_get_size(v_types_5444_);
                v___x_5454_ = lean_unsigned_to_nat(1);
                v___x_5455_ = lean_nat_sub(v___x_5453_, v___x_5454_);
                v___x_5456_ = lean_nat_dec_lt(v_i_5447_, v___x_5455_);
                lean_dec(v___x_5455_);
                if v___x_5456_ == 0 {
                    lean_dec(v_u_5445_);
                    v___x_5457_ = l_Lean_instInhabitedExpr;
                    v___x_5458_ = lean_array_get(v___x_5457_, v_types_5444_, v_i_5447_);
                    lean_dec(v_i_5447_);
                    lean_dec_ref(v_types_5444_);
                    v___x_5459_ = l_Lean_Expr_bindingBody_x21(v___x_5458_);
                    lean_dec(v___x_5458_);
                    v___x_5460_ = lean_expr_instantiate1(v___x_5459_, v_x_5446_);
                    lean_dec_ref(v_x_5446_);
                    lean_dec_ref(v___x_5459_);
                    v___x_5461_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5461_, 0, v___x_5460_);
                    return v___x_5461_;
                } else {
                    lean_inc(v_a_5451_);
                    lean_inc_ref(v_a_5450_);
                    lean_inc(v_a_5449_);
                    lean_inc_ref(v_a_5448_);
                    lean_inc_ref(v_x_5446_);
                    v___x_5462_ =
                        lean_infer_type(v_x_5446_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_);
                    if lean_obj_tag(v___x_5462_) == 0 {
                        v_a_5463_ = lean_ctor_get(v___x_5462_, 0);
                        lean_inc(v_a_5463_);
                        lean_dec_ref_known(v___x_5462_, 1);
                        v___x_5464_ = l_Lean_Meta_whnfD(
                            v_a_5463_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_,
                        );
                        if lean_obj_tag(v___x_5464_) == 0 {
                            v_a_5465_ = lean_ctor_get(v___x_5464_, 0);
                            lean_inc(v_a_5465_);
                            lean_dec_ref_known(v___x_5464_, 1);
                            v___x_5466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1;
                            v___x_5467_ = lean_unsigned_to_nat(2);
                            v___x_5468_ =
                                l_Lean_Expr_isAppOfArity(v_a_5465_, v___x_5466_, v___x_5467_);
                            if v___x_5468_ == 0 {
                                lean_dec(v_a_5465_);
                                lean_dec(v_i_5447_);
                                lean_dec_ref(v_x_5446_);
                                lean_dec(v_u_5445_);
                                lean_dec_ref(v_types_5444_);
                                v___x_5469_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2);
                                v___x_5470_ =
                                    l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(
                                        v___x_5469_,
                                        v_a_5448_,
                                        v_a_5449_,
                                        v_a_5450_,
                                        v_a_5451_,
                                    );
                                return v___x_5470_;
                            } else {
                                lean_inc_n(v_u_5445_, 2);
                                v___x_5471_ = l_Lean_Level_succ___override(v_u_5445_);
                                v___x_5472_ = lean_mk_empty_array_with_capacity(v___x_5454_);
                                lean_inc_ref(v_x_5446_);
                                lean_inc_ref(v___x_5472_);
                                v___x_5473_ = lean_array_push(v___x_5472_, v_x_5446_);
                                v___x_5474_ = l_Lean_mkSort(v_u_5445_);
                                v___x_5475_ = 0;
                                v___x_5476_ = 1;
                                v___x_5477_ = l_Lean_Meta_mkLambdaFVars(
                                    v___x_5473_,
                                    v___x_5474_,
                                    v___x_5475_,
                                    v___x_5468_,
                                    v___x_5475_,
                                    v___x_5468_,
                                    v___x_5476_,
                                    v_a_5448_,
                                    v_a_5449_,
                                    v_a_5450_,
                                    v_a_5451_,
                                );
                                lean_dec_ref(v___x_5473_);
                                if lean_obj_tag(v___x_5477_) == 0 {
                                    v_a_5478_ = lean_ctor_get(v___x_5477_, 0);
                                    lean_inc(v_a_5478_);
                                    lean_dec_ref_known(v___x_5477_, 1);
                                    v___x_5479_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4;
                                    v___x_5480_ = l_Lean_Core_mkFreshUserName(
                                        v___x_5479_,
                                        v_a_5450_,
                                        v_a_5451_,
                                    );
                                    if lean_obj_tag(v___x_5480_) == 0 {
                                        v_a_5481_ = lean_ctor_get(v___x_5480_, 0);
                                        lean_inc(v_a_5481_);
                                        lean_dec_ref_known(v___x_5480_, 1);
                                        v_nargs_5482_ = l_Lean_Expr_getAppNumArgs(v_a_5465_);
                                        v_dummy_5483_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
                                        lean_inc(v_nargs_5482_);
                                        v___x_5484_ = lean_mk_array(v_nargs_5482_, v_dummy_5483_);
                                        v___x_5485_ = lean_nat_sub(v_nargs_5482_, v___x_5454_);
                                        lean_dec(v_nargs_5482_);
                                        lean_inc(v_a_5465_);
                                        v___x_5486_ =
                                            l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                                v_a_5465_,
                                                v___x_5484_,
                                                v___x_5485_,
                                            );
                                        v___x_5487_ = l_Lean_instInhabitedExpr;
                                        v___x_5488_ = lean_box((v___x_5475_) as usize);
                                        v___x_5489_ = lean_box((v___x_5468_) as usize);
                                        v___x_5490_ = lean_box((v___x_5476_) as usize);
                                        lean_inc(v_i_5447_);
                                        lean_inc_ref(v_types_5444_);
                                        lean_inc_ref(v___x_5472_);
                                        v___f_5491_ = lean_alloc_closure(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed as *mut core::ffi::c_void, 13, 7);
                                        lean_closure_set(v___f_5491_, 0, v___x_5472_);
                                        lean_closure_set(v___f_5491_, 1, v___x_5487_);
                                        lean_closure_set(v___f_5491_, 2, v_types_5444_);
                                        lean_closure_set(v___f_5491_, 3, v_i_5447_);
                                        lean_closure_set(v___f_5491_, 4, v___x_5488_);
                                        lean_closure_set(v___f_5491_, 5, v___x_5489_);
                                        lean_closure_set(v___f_5491_, 6, v___x_5490_);
                                        v___x_5492_ = lean_unsigned_to_nat(0);
                                        v___x_5493_ = lean_array_get_borrowed(
                                            v___x_5487_,
                                            v___x_5486_,
                                            v___x_5492_,
                                        );
                                        lean_inc(v___x_5493_);
                                        v___x_5494_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_5481_, v___x_5493_, v___f_5491_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_);
                                        if lean_obj_tag(v___x_5494_) == 0 {
                                            v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
                                            lean_inc(v_a_5495_);
                                            lean_dec_ref_known(v___x_5494_, 1);
                                            v___x_5496_ = l_Lean_Core_mkFreshUserName(
                                                v___x_5479_,
                                                v_a_5450_,
                                                v_a_5451_,
                                            );
                                            if lean_obj_tag(v___x_5496_) == 0 {
                                                v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
                                                lean_inc(v_a_5497_);
                                                lean_dec_ref_known(v___x_5496_, 1);
                                                v___x_5498_ = lean_box((v___x_5475_) as usize);
                                                v___x_5499_ = lean_box((v___x_5468_) as usize);
                                                v___x_5500_ = lean_box((v___x_5476_) as usize);
                                                v___f_5501_ = lean_alloc_closure(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed as *mut core::ffi::c_void, 14, 8);
                                                lean_closure_set(v___f_5501_, 0, v_i_5447_);
                                                lean_closure_set(v___f_5501_, 1, v___x_5454_);
                                                lean_closure_set(v___f_5501_, 2, v_types_5444_);
                                                lean_closure_set(v___f_5501_, 3, v_u_5445_);
                                                lean_closure_set(v___f_5501_, 4, v___x_5472_);
                                                lean_closure_set(v___f_5501_, 5, v___x_5498_);
                                                lean_closure_set(v___f_5501_, 6, v___x_5499_);
                                                lean_closure_set(v___f_5501_, 7, v___x_5500_);
                                                v___x_5502_ = lean_array_get(
                                                    v___x_5487_,
                                                    v___x_5486_,
                                                    v___x_5454_,
                                                );
                                                v___x_5503_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_5497_, v___x_5502_, v___f_5501_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_);
                                                if lean_obj_tag(v___x_5503_) == 0 {
                                                    v_a_5504_ = lean_ctor_get(v___x_5503_, 0);
                                                    v_isSharedCheck_5520_ =
                                                        (!lean_is_exclusive(v___x_5503_)) as u8;
                                                    if v_isSharedCheck_5520_ == 0 {
                                                        v___x_5506_ = v___x_5503_;
                                                        v_isShared_5507_ = v_isSharedCheck_5520_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5504_);
                                                        lean_dec(v___x_5503_);
                                                        v___x_5506_ = lean_box(0);
                                                        v_isShared_5507_ = v_isSharedCheck_5520_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec(v_a_5495_);
                                                    lean_dec_ref(v___x_5486_);
                                                    lean_dec(v_a_5478_);
                                                    lean_dec(v___x_5471_);
                                                    lean_dec(v_a_5465_);
                                                    lean_dec_ref(v_x_5446_);
                                                    return v___x_5503_;
                                                }
                                            } else {
                                                lean_dec(v_a_5495_);
                                                lean_dec_ref(v___x_5486_);
                                                lean_dec(v_a_5478_);
                                                lean_dec_ref(v___x_5472_);
                                                lean_dec(v___x_5471_);
                                                lean_dec(v_a_5465_);
                                                lean_dec(v_i_5447_);
                                                lean_dec_ref(v_x_5446_);
                                                lean_dec(v_u_5445_);
                                                lean_dec_ref(v_types_5444_);
                                                v_a_5521_ = lean_ctor_get(v___x_5496_, 0);
                                                v_isSharedCheck_5528_ =
                                                    (!lean_is_exclusive(v___x_5496_)) as u8;
                                                if v_isSharedCheck_5528_ == 0 {
                                                    v___x_5523_ = v___x_5496_;
                                                    v_isShared_5524_ = v_isSharedCheck_5528_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5521_);
                                                    lean_dec(v___x_5496_);
                                                    v___x_5523_ = lean_box(0);
                                                    v_isShared_5524_ = v_isSharedCheck_5528_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_5486_);
                                            lean_dec(v_a_5478_);
                                            lean_dec_ref(v___x_5472_);
                                            lean_dec(v___x_5471_);
                                            lean_dec(v_a_5465_);
                                            lean_dec(v_i_5447_);
                                            lean_dec_ref(v_x_5446_);
                                            lean_dec(v_u_5445_);
                                            lean_dec_ref(v_types_5444_);
                                            return v___x_5494_;
                                        }
                                    } else {
                                        lean_dec(v_a_5478_);
                                        lean_dec_ref(v___x_5472_);
                                        lean_dec(v___x_5471_);
                                        lean_dec(v_a_5465_);
                                        lean_dec(v_i_5447_);
                                        lean_dec_ref(v_x_5446_);
                                        lean_dec(v_u_5445_);
                                        lean_dec_ref(v_types_5444_);
                                        v_a_5529_ = lean_ctor_get(v___x_5480_, 0);
                                        v_isSharedCheck_5536_ =
                                            (!lean_is_exclusive(v___x_5480_)) as u8;
                                        if v_isSharedCheck_5536_ == 0 {
                                            v___x_5531_ = v___x_5480_;
                                            v_isShared_5532_ = v_isSharedCheck_5536_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5529_);
                                            lean_dec(v___x_5480_);
                                            v___x_5531_ = lean_box(0);
                                            v_isShared_5532_ = v_isSharedCheck_5536_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_5472_);
                                    lean_dec(v___x_5471_);
                                    lean_dec(v_a_5465_);
                                    lean_dec(v_i_5447_);
                                    lean_dec_ref(v_x_5446_);
                                    lean_dec(v_u_5445_);
                                    lean_dec_ref(v_types_5444_);
                                    return v___x_5477_;
                                }
                            }
                        } else {
                            lean_dec(v_i_5447_);
                            lean_dec_ref(v_x_5446_);
                            lean_dec(v_u_5445_);
                            lean_dec_ref(v_types_5444_);
                            return v___x_5464_;
                        }
                    } else {
                        lean_dec(v_i_5447_);
                        lean_dec_ref(v_x_5446_);
                        lean_dec(v_u_5445_);
                        lean_dec_ref(v_types_5444_);
                        return v___x_5462_;
                    }
                }
            }
            1 => {
                v___x_5508_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3;
                v___x_5509_ = l_Lean_Expr_getAppFn(v_a_5465_);
                lean_dec(v_a_5465_);
                v___x_5510_ = l_Lean_Expr_constLevels_x21(v___x_5509_);
                lean_dec_ref(v___x_5509_);
                v___x_5511_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5511_, 0, v___x_5471_);
                lean_ctor_set(v___x_5511_, 1, v___x_5510_);
                v___x_5512_ = l_Lean_mkConst(v___x_5508_, v___x_5511_);
                v___x_5513_ = l_Lean_mkAppN(v___x_5512_, v___x_5486_);
                lean_dec_ref(v___x_5486_);
                v___x_5514_ = l_Lean_Expr_app___override(v___x_5513_, v_a_5478_);
                v___x_5515_ = l_Lean_Expr_app___override(v___x_5514_, v_x_5446_);
                v___x_5516_ = l_Lean_mkAppB(v___x_5515_, v_a_5495_, v_a_5504_);
                if v_isShared_5507_ == 0 {
                    lean_ctor_set(v___x_5506_, 0, v___x_5516_);
                    v___x_5518_ = v___x_5506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5519_, 0, v___x_5516_);
                    v___x_5518_ = v_reuseFailAlloc_5519_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5518_;
            }
            3 => {
                if v_isShared_5524_ == 0 {
                    v___x_5526_ = v___x_5523_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5527_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_a_5521_);
                    v___x_5526_ = v_reuseFailAlloc_5527_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5526_;
            }
            5 => {
                if v_isShared_5532_ == 0 {
                    v___x_5534_ = v___x_5531_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5529_);
                    v___x_5534_ = v_reuseFailAlloc_5535_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(
    mut v_i_5537_: *mut LeanObject,
    mut v___x_5538_: *mut LeanObject,
    mut v_types_5539_: *mut LeanObject,
    mut v_u_5540_: *mut LeanObject,
    mut v___x_5541_: *mut LeanObject,
    mut v___x_5542_: u8,
    mut v___x_5543_: u8,
    mut v___x_5544_: u8,
    mut v_x_5545_: *mut LeanObject,
    mut v___y_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
    mut v___y_5548_: *mut LeanObject,
    mut v___y_5549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    v___x_5551_ = lean_nat_add(v_i_5537_, v___x_5538_);
    lean_inc_ref(v_x_5545_);
    v___x_5552_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(
        v_types_5539_,
        v_u_5540_,
        v_x_5545_,
        v___x_5551_,
        v___y_5546_,
        v___y_5547_,
        v___y_5548_,
        v___y_5549_,
    );
    if lean_obj_tag(v___x_5552_) == 0 {
        let mut v_a_5553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
        v_a_5553_ = lean_ctor_get(v___x_5552_, 0);
        lean_inc(v_a_5553_);
        lean_dec_ref_known(v___x_5552_, 1);
        v___x_5554_ = lean_array_push(v___x_5541_, v_x_5545_);
        v___x_5555_ = l_Lean_Meta_mkLambdaFVars(
            v___x_5554_,
            v_a_5553_,
            v___x_5542_,
            v___x_5543_,
            v___x_5542_,
            v___x_5543_,
            v___x_5544_,
            v___y_5546_,
            v___y_5547_,
            v___y_5548_,
            v___y_5549_,
        );
        lean_dec_ref(v___x_5554_);
        return v___x_5555_;
    } else {
        lean_dec_ref(v_x_5545_);
        lean_dec_ref(v___x_5541_);
        return v___x_5552_;
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___boxed(
    mut v_types_5556_: *mut LeanObject,
    mut v_u_5557_: *mut LeanObject,
    mut v_x_5558_: *mut LeanObject,
    mut v_i_5559_: *mut LeanObject,
    mut v_a_5560_: *mut LeanObject,
    mut v_a_5561_: *mut LeanObject,
    mut v_a_5562_: *mut LeanObject,
    mut v_a_5563_: *mut LeanObject,
    mut v_a_5564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5565_: *mut LeanObject = core::ptr::null_mut();
    v_res_5565_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(
        v_types_5556_,
        v_u_5557_,
        v_x_5558_,
        v_i_5559_,
        v_a_5560_,
        v_a_5561_,
        v_a_5562_,
        v_a_5563_,
    );
    lean_dec(v_a_5563_);
    lean_dec_ref(v_a_5562_);
    lean_dec(v_a_5561_);
    lean_dec_ref(v_a_5560_);
    return v_res_5565_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(
    mut v_x_5566_: *mut LeanObject,
    mut v_body_5567_: *mut LeanObject,
    mut v___y_5568_: *mut LeanObject,
    mut v___y_5569_: *mut LeanObject,
    mut v___y_5570_: *mut LeanObject,
    mut v___y_5571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    v___x_5573_ = l_Lean_Meta_getLevel(
        v_body_5567_,
        v___y_5568_,
        v___y_5569_,
        v___y_5570_,
        v___y_5571_,
    );
    return v___x_5573_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed(
    mut v_x_5574_: *mut LeanObject,
    mut v_body_5575_: *mut LeanObject,
    mut v___y_5576_: *mut LeanObject,
    mut v___y_5577_: *mut LeanObject,
    mut v___y_5578_: *mut LeanObject,
    mut v___y_5579_: *mut LeanObject,
    mut v___y_5580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5581_: *mut LeanObject = core::ptr::null_mut();
    v_res_5581_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(
        v_x_5574_,
        v_body_5575_,
        v___y_5576_,
        v___y_5577_,
        v___y_5578_,
        v___y_5579_,
    );
    lean_dec(v___y_5579_);
    lean_dec_ref(v___y_5578_);
    lean_dec(v___y_5577_);
    lean_dec_ref(v___y_5576_);
    lean_dec_ref(v_x_5574_);
    return v_res_5581_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(
    mut v_types_5583_: *mut LeanObject,
    mut v_x_5584_: *mut LeanObject,
    mut v_a_5585_: *mut LeanObject,
    mut v_a_5586_: *mut LeanObject,
    mut v_a_5587_: *mut LeanObject,
    mut v_a_5588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: u8 = 0;
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5602_: u8 = 0;
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5590_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0;
                v___x_5591_ = l_Lean_instInhabitedExpr;
                v___x_5592_ = lean_unsigned_to_nat(0);
                v___x_5593_ = lean_array_get_borrowed(v___x_5591_, v_types_5583_, v___x_5592_);
                v___x_5594_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0;
                v___x_5595_ = 0;
                lean_inc(v___x_5593_);
                v___x_5596_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v___x_5593_, v___x_5594_, v___f_5590_, v___x_5595_, v___x_5595_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_);
                if lean_obj_tag(v___x_5596_) == 0 {
                    v_a_5597_ = lean_ctor_get(v___x_5596_, 0);
                    lean_inc(v_a_5597_);
                    lean_dec_ref_known(v___x_5596_, 1);
                    v___x_5598_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_5583_, v_a_5597_, v_x_5584_, v___x_5592_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_);
                    return v___x_5598_;
                } else {
                    lean_dec_ref(v_x_5584_);
                    lean_dec_ref(v_types_5583_);
                    v_a_5599_ = lean_ctor_get(v___x_5596_, 0);
                    v_isSharedCheck_5606_ = (!lean_is_exclusive(v___x_5596_)) as u8;
                    if v_isSharedCheck_5606_ == 0 {
                        v___x_5601_ = v___x_5596_;
                        v_isShared_5602_ = v_isSharedCheck_5606_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5599_);
                        lean_dec(v___x_5596_);
                        v___x_5601_ = lean_box(0);
                        v_isShared_5602_ = v_isSharedCheck_5606_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5602_ == 0 {
                    v___x_5604_ = v___x_5601_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5605_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_a_5599_);
                    v___x_5604_ = v_reuseFailAlloc_5605_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___boxed(
    mut v_types_5607_: *mut LeanObject,
    mut v_x_5608_: *mut LeanObject,
    mut v_a_5609_: *mut LeanObject,
    mut v_a_5610_: *mut LeanObject,
    mut v_a_5611_: *mut LeanObject,
    mut v_a_5612_: *mut LeanObject,
    mut v_a_5613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5614_: *mut LeanObject = core::ptr::null_mut();
    v_res_5614_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(
        v_types_5607_,
        v_x_5608_,
        v_a_5609_,
        v_a_5610_,
        v_a_5611_,
        v_a_5612_,
    );
    lean_dec(v_a_5612_);
    lean_dec_ref(v_a_5611_);
    lean_dec(v_a_5610_);
    lean_dec_ref(v_a_5609_);
    return v_res_5614_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(
    mut v_a_5615_: *mut LeanObject,
    mut v___x_5616_: *mut LeanObject,
    mut v___x_5617_: u8,
    mut v_x_5618_: *mut LeanObject,
    mut v___y_5619_: *mut LeanObject,
    mut v___y_5620_: *mut LeanObject,
    mut v___y_5621_: *mut LeanObject,
    mut v___y_5622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_x_5618_);
    v___x_5624_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(
        v_a_5615_,
        v_x_5618_,
        v___y_5619_,
        v___y_5620_,
        v___y_5621_,
        v___y_5622_,
    );
    if lean_obj_tag(v___x_5624_) == 0 {
        let mut v_a_5625_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5628_: u8 = 0;
        let mut v___x_5629_: u8 = 0;
        let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
        v_a_5625_ = lean_ctor_get(v___x_5624_, 0);
        lean_inc(v_a_5625_);
        lean_dec_ref_known(v___x_5624_, 1);
        v___x_5626_ = lean_mk_empty_array_with_capacity(v___x_5616_);
        v___x_5627_ = lean_array_push(v___x_5626_, v_x_5618_);
        v___x_5628_ = 1;
        v___x_5629_ = 1;
        v___x_5630_ = l_Lean_Meta_mkForallFVars(
            v___x_5627_,
            v_a_5625_,
            v___x_5617_,
            v___x_5628_,
            v___x_5628_,
            v___x_5629_,
            v___y_5619_,
            v___y_5620_,
            v___y_5621_,
            v___y_5622_,
        );
        lean_dec_ref(v___x_5627_);
        return v___x_5630_;
    } else {
        lean_dec_ref(v_x_5618_);
        return v___x_5624_;
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed(
    mut v_a_5631_: *mut LeanObject,
    mut v___x_5632_: *mut LeanObject,
    mut v___x_5633_: *mut LeanObject,
    mut v_x_5634_: *mut LeanObject,
    mut v___y_5635_: *mut LeanObject,
    mut v___y_5636_: *mut LeanObject,
    mut v___y_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
    mut v___y_5639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2053__boxed_5640_: u8 = 0;
    let mut v_res_5641_: *mut LeanObject = core::ptr::null_mut();
    v___x_2053__boxed_5640_ = (lean_unbox(v___x_5633_) as u8);
    v_res_5641_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(
        v_a_5631_,
        v___x_5632_,
        v___x_2053__boxed_5640_,
        v_x_5634_,
        v___y_5635_,
        v___y_5636_,
        v___y_5637_,
        v___y_5638_,
    );
    lean_dec(v___y_5638_);
    lean_dec_ref(v___y_5637_);
    lean_dec(v___y_5636_);
    lean_dec_ref(v___y_5635_);
    lean_dec(v___x_5632_);
    return v_res_5641_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(
    mut v_sz_5642_: usize,
    mut v_i_5643_: usize,
    mut v_bs_5644_: *mut LeanObject,
    mut v___y_5645_: *mut LeanObject,
    mut v___y_5646_: *mut LeanObject,
    mut v___y_5647_: *mut LeanObject,
    mut v___y_5648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5650_: u8 = 0;
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: usize = 0;
    let mut v___x_5658_: usize = 0;
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5664_: u8 = 0;
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5650_ = lean_usize_dec_lt(v_i_5643_, v_sz_5642_);
                if v___x_5650_ == 0 {
                    v___x_5651_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5651_, 0, v_bs_5644_);
                    return v___x_5651_;
                } else {
                    v_v_5652_ = lean_array_uget_borrowed(v_bs_5644_, v_i_5643_);
                    lean_inc(v_v_5652_);
                    v___x_5653_ = l_Lean_Meta_whnfForall(
                        v_v_5652_,
                        v___y_5645_,
                        v___y_5646_,
                        v___y_5647_,
                        v___y_5648_,
                    );
                    if lean_obj_tag(v___x_5653_) == 0 {
                        v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
                        lean_inc(v_a_5654_);
                        lean_dec_ref_known(v___x_5653_, 1);
                        v___x_5655_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5656_ = lean_array_uset(v_bs_5644_, v_i_5643_, v___x_5655_);
                        v___x_5657_ = 1usize;
                        v___x_5658_ = lean_usize_add(v_i_5643_, v___x_5657_);
                        v___x_5659_ = lean_array_uset(v_bs_x27_5656_, v_i_5643_, v_a_5654_);
                        v_i_5643_ = v___x_5658_;
                        v_bs_5644_ = v___x_5659_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5644_);
                        v_a_5661_ = lean_ctor_get(v___x_5653_, 0);
                        v_isSharedCheck_5668_ = (!lean_is_exclusive(v___x_5653_)) as u8;
                        if v_isSharedCheck_5668_ == 0 {
                            v___x_5663_ = v___x_5653_;
                            v_isShared_5664_ = v_isSharedCheck_5668_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5661_);
                            lean_dec(v___x_5653_);
                            v___x_5663_ = lean_box(0);
                            v_isShared_5664_ = v_isSharedCheck_5668_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5664_ == 0 {
                    v___x_5666_ = v___x_5663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5667_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_a_5661_);
                    v___x_5666_ = v_reuseFailAlloc_5667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0___boxed(
    mut v_sz_5669_: *mut LeanObject,
    mut v_i_5670_: *mut LeanObject,
    mut v_bs_5671_: *mut LeanObject,
    mut v___y_5672_: *mut LeanObject,
    mut v___y_5673_: *mut LeanObject,
    mut v___y_5674_: *mut LeanObject,
    mut v___y_5675_: *mut LeanObject,
    mut v___y_5676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5677_: usize = 0;
    let mut v_i_boxed_5678_: usize = 0;
    let mut v_res_5679_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5677_ = lean_unbox_usize(v_sz_5669_);
    lean_dec(v_sz_5669_);
    v_i_boxed_5678_ = lean_unbox_usize(v_i_5670_);
    lean_dec(v_i_5670_);
    v_res_5679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_boxed_5677_, v_i_boxed_5678_, v_bs_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_);
    lean_dec(v___y_5675_);
    lean_dec_ref(v___y_5674_);
    lean_dec(v___y_5673_);
    lean_dec_ref(v___y_5672_);
    return v_res_5679_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    v___x_5681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0;
    v___x_5682_ = l_Lean_stringToMessageData(v___x_5681_);
    return v___x_5682_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(
    mut v_as_5683_: *mut LeanObject,
    mut v_i_5684_: usize,
    mut v_stop_5685_: usize,
    mut v_b_5686_: *mut LeanObject,
    mut v___y_5687_: *mut LeanObject,
    mut v___y_5688_: *mut LeanObject,
    mut v___y_5689_: *mut LeanObject,
    mut v___y_5690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: usize = 0;
    let mut v___x_5695_: usize = 0;
    let mut v___x_5697_: u8 = 0;
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: u8 = 0;
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5697_ = lean_usize_dec_eq(v_i_5684_, v_stop_5685_);
                if v___x_5697_ == 0 {
                    v___x_5698_ = lean_array_uget_borrowed(v_as_5683_, v_i_5684_);
                    v___x_5699_ = l_Lean_Expr_isForall(v___x_5698_);
                    if v___x_5699_ == 0 {
                        v___x_5700_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1);
                        lean_inc(v___x_5698_);
                        v___x_5701_ = l_Lean_MessageData_ofExpr(v___x_5698_);
                        v___x_5702_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5702_, 0, v___x_5700_);
                        lean_ctor_set(v___x_5702_, 1, v___x_5701_);
                        v___x_5703_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_5702_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
                        if lean_obj_tag(v___x_5703_) == 0 {
                            v_a_5704_ = lean_ctor_get(v___x_5703_, 0);
                            lean_inc(v_a_5704_);
                            lean_dec_ref_known(v___x_5703_, 1);
                            v_a_5693_ = v_a_5704_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_5703_;
                        }
                    } else {
                        v___x_5705_ = lean_box(0);
                        v_a_5693_ = v___x_5705_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_5706_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5706_, 0, v_b_5686_);
                    return v___x_5706_;
                }
            }
            1 => {
                v___x_5694_ = 1usize;
                v___x_5695_ = lean_usize_add(v_i_5684_, v___x_5694_);
                v_i_5684_ = v___x_5695_;
                v_b_5686_ = v_a_5693_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___boxed(
    mut v_as_5707_: *mut LeanObject,
    mut v_i_5708_: *mut LeanObject,
    mut v_stop_5709_: *mut LeanObject,
    mut v_b_5710_: *mut LeanObject,
    mut v___y_5711_: *mut LeanObject,
    mut v___y_5712_: *mut LeanObject,
    mut v___y_5713_: *mut LeanObject,
    mut v___y_5714_: *mut LeanObject,
    mut v___y_5715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5716_: usize = 0;
    let mut v_stop_boxed_5717_: usize = 0;
    let mut v_res_5718_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5716_ = lean_unbox_usize(v_i_5708_);
    lean_dec(v_i_5708_);
    v_stop_boxed_5717_ = lean_unbox_usize(v_stop_5709_);
    lean_dec(v_stop_5709_);
    v_res_5718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_as_5707_, v_i_boxed_5716_, v_stop_boxed_5717_, v_b_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
    lean_dec(v___y_5714_);
    lean_dec_ref(v___y_5713_);
    lean_dec(v___y_5712_);
    lean_dec_ref(v___y_5711_);
    lean_dec_ref(v_as_5707_);
    return v_res_5718_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(
    mut v_sz_5719_: usize,
    mut v_i_5720_: usize,
    mut v_bs_5721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5722_: u8 = 0;
    let mut v_v_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: usize = 0;
    let mut v___x_5728_: usize = 0;
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5722_ = lean_usize_dec_lt(v_i_5720_, v_sz_5719_);
                if v___x_5722_ == 0 {
                    return v_bs_5721_;
                } else {
                    v_v_5723_ = lean_array_uget(v_bs_5721_, v_i_5720_);
                    v___x_5724_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5725_ = lean_array_uset(v_bs_5721_, v_i_5720_, v___x_5724_);
                    v___x_5726_ = l_Lean_Expr_bindingDomain_x21(v_v_5723_);
                    lean_dec(v_v_5723_);
                    v___x_5727_ = 1usize;
                    v___x_5728_ = lean_usize_add(v_i_5720_, v___x_5727_);
                    v___x_5729_ = lean_array_uset(v_bs_x27_5725_, v_i_5720_, v___x_5726_);
                    v_i_5720_ = v___x_5728_;
                    v_bs_5721_ = v___x_5729_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1___boxed(
    mut v_sz_5731_: *mut LeanObject,
    mut v_i_5732_: *mut LeanObject,
    mut v_bs_5733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5734_: usize = 0;
    let mut v_i_boxed_5735_: usize = 0;
    let mut v_res_5736_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5734_ = lean_unbox_usize(v_sz_5731_);
    lean_dec(v_sz_5731_);
    v_i_boxed_5735_ = lean_unbox_usize(v_i_5732_);
    lean_dec(v_i_5732_);
    v_res_5736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_boxed_5734_, v_i_boxed_5735_, v_bs_5733_);
    return v_res_5736_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryType(
    mut v_types_5737_: *mut LeanObject,
    mut v_a_5738_: *mut LeanObject,
    mut v_a_5739_: *mut LeanObject,
    mut v_a_5740_: *mut LeanObject,
    mut v_a_5741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: u8 = 0;
    let mut v_sz_5746_: usize = 0;
    let mut v___x_5747_: usize = 0;
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5753_: usize = 0;
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5764_: u8 = 0;
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5768_: u8 = 0;
    let mut v___y_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5774_: u8 = 0;
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5778_: u8 = 0;
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: u8 = 0;
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: u8 = 0;
    let mut v___x_5784_: usize = 0;
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: usize = 0;
    let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5791_: u8 = 0;
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5795_: u8 = 0;
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5743_ = lean_array_get_size(v_types_5737_);
                v___x_5744_ = lean_unsigned_to_nat(1);
                v___x_5745_ = lean_nat_dec_eq(v___x_5743_, v___x_5744_);
                if v___x_5745_ == 0 {
                    v_sz_5746_ = lean_array_size(v_types_5737_);
                    v___x_5747_ = 0usize;
                    v___x_5748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_5746_, v___x_5747_, v_types_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_);
                    if lean_obj_tag(v___x_5748_) == 0 {
                        v_a_5749_ = lean_ctor_get(v___x_5748_, 0);
                        lean_inc_n(v_a_5749_, 2);
                        lean_dec_ref_known(v___x_5748_, 1);
                        v___x_5750_ = lean_box((v___x_5745_) as usize);
                        v___f_5751_ = lean_alloc_closure(
                            l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed
                                as *mut core::ffi::c_void,
                            9,
                            3,
                        );
                        lean_closure_set(v___f_5751_, 0, v_a_5749_);
                        lean_closure_set(v___f_5751_, 1, v___x_5744_);
                        lean_closure_set(v___f_5751_, 2, v___x_5750_);
                        v___x_5779_ = lean_unsigned_to_nat(0);
                        v___x_5780_ = lean_array_get_size(v_a_5749_);
                        v___x_5781_ = lean_nat_dec_lt(v___x_5779_, v___x_5780_);
                        if v___x_5781_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_5782_ = lean_box(0);
                            v___x_5783_ = lean_nat_dec_le(v___x_5780_, v___x_5780_);
                            if v___x_5783_ == 0 {
                                if v___x_5781_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_5784_ = lean_usize_of_nat(v___x_5780_);
                                    v___x_5785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_5749_, v___x_5747_, v___x_5784_, v___x_5782_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_);
                                    v___y_5770_ = v___x_5785_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v___x_5786_ = lean_usize_of_nat(v___x_5780_);
                                v___x_5787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_5749_, v___x_5747_, v___x_5786_, v___x_5782_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_);
                                v___y_5770_ = v___x_5787_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_5788_ = lean_ctor_get(v___x_5748_, 0);
                        v_isSharedCheck_5795_ = (!lean_is_exclusive(v___x_5748_)) as u8;
                        if v_isSharedCheck_5795_ == 0 {
                            v___x_5790_ = v___x_5748_;
                            v_isShared_5791_ = v_isSharedCheck_5795_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5788_);
                            lean_dec(v___x_5748_);
                            v___x_5790_ = lean_box(0);
                            v_isShared_5791_ = v_isSharedCheck_5795_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_5796_ = l_Lean_instInhabitedExpr;
                    v___x_5797_ = lean_unsigned_to_nat(0);
                    v___x_5798_ = lean_array_get(v___x_5796_, v_types_5737_, v___x_5797_);
                    lean_dec_ref(v_types_5737_);
                    v___x_5799_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5799_, 0, v___x_5798_);
                    return v___x_5799_;
                }
            }
            1 => {
                v_sz_5753_ = lean_array_size(v_a_5749_);
                v___x_5754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_5753_, v___x_5747_, v_a_5749_);
                v___x_5755_ = l_Lean_Meta_ArgsPacker_Mutual_packType(
                    v___x_5754_,
                    v_a_5738_,
                    v_a_5739_,
                    v_a_5740_,
                    v_a_5741_,
                );
                if lean_obj_tag(v___x_5755_) == 0 {
                    v_a_5756_ = lean_ctor_get(v___x_5755_, 0);
                    lean_inc(v_a_5756_);
                    lean_dec_ref_known(v___x_5755_, 1);
                    v___x_5757_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2;
                    v___x_5758_ = l_Lean_Core_mkFreshUserName(v___x_5757_, v_a_5740_, v_a_5741_);
                    if lean_obj_tag(v___x_5758_) == 0 {
                        v_a_5759_ = lean_ctor_get(v___x_5758_, 0);
                        lean_inc(v_a_5759_);
                        lean_dec_ref_known(v___x_5758_, 1);
                        v___x_5760_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_5759_, v_a_5756_, v___f_5751_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_);
                        return v___x_5760_;
                    } else {
                        lean_dec(v_a_5756_);
                        lean_dec_ref(v___f_5751_);
                        v_a_5761_ = lean_ctor_get(v___x_5758_, 0);
                        v_isSharedCheck_5768_ = (!lean_is_exclusive(v___x_5758_)) as u8;
                        if v_isSharedCheck_5768_ == 0 {
                            v___x_5763_ = v___x_5758_;
                            v_isShared_5764_ = v_isSharedCheck_5768_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5761_);
                            lean_dec(v___x_5758_);
                            v___x_5763_ = lean_box(0);
                            v_isShared_5764_ = v_isSharedCheck_5768_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___f_5751_);
                    return v___x_5755_;
                }
            }
            2 => {
                if v_isShared_5764_ == 0 {
                    v___x_5766_ = v___x_5763_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5767_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5767_, 0, v_a_5761_);
                    v___x_5766_ = v_reuseFailAlloc_5767_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5766_;
            }
            4 => {
                if lean_obj_tag(v___y_5770_) == 0 {
                    lean_dec_ref_known(v___y_5770_, 1);
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___f_5751_);
                    lean_dec(v_a_5749_);
                    v_a_5771_ = lean_ctor_get(v___y_5770_, 0);
                    v_isSharedCheck_5778_ = (!lean_is_exclusive(v___y_5770_)) as u8;
                    if v_isSharedCheck_5778_ == 0 {
                        v___x_5773_ = v___y_5770_;
                        v_isShared_5774_ = v_isSharedCheck_5778_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5771_);
                        lean_dec(v___y_5770_);
                        v___x_5773_ = lean_box(0);
                        v_isShared_5774_ = v_isSharedCheck_5778_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_5774_ == 0 {
                    v___x_5776_ = v___x_5773_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5777_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_a_5771_);
                    v___x_5776_ = v_reuseFailAlloc_5777_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5776_;
            }
            7 => {
                if v_isShared_5791_ == 0 {
                    v___x_5793_ = v___x_5790_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5794_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_a_5788_);
                    v___x_5793_ = v_reuseFailAlloc_5794_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryType___boxed(
    mut v_types_5800_: *mut LeanObject,
    mut v_a_5801_: *mut LeanObject,
    mut v_a_5802_: *mut LeanObject,
    mut v_a_5803_: *mut LeanObject,
    mut v_a_5804_: *mut LeanObject,
    mut v_a_5805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5806_: *mut LeanObject = core::ptr::null_mut();
    v_res_5806_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(
        v_types_5800_,
        v_a_5801_,
        v_a_5802_,
        v_a_5803_,
        v_a_5804_,
    );
    lean_dec(v_a_5804_);
    lean_dec_ref(v_a_5803_);
    lean_dec(v_a_5802_);
    lean_dec_ref(v_a_5801_);
    return v_res_5806_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    v___x_5808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0;
    v___x_5809_ = l_Lean_stringToMessageData(v___x_5808_);
    return v___x_5809_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    v___x_5811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2;
    v___x_5812_ = l_Lean_stringToMessageData(v___x_5811_);
    return v___x_5812_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(
    mut v___x_5813_: *mut LeanObject,
    mut v_as_5814_: *mut LeanObject,
    mut v_i_5815_: usize,
    mut v_stop_5816_: usize,
    mut v_b_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
    mut v___y_5819_: *mut LeanObject,
    mut v___y_5820_: *mut LeanObject,
    mut v___y_5821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: usize = 0;
    let mut v___x_5826_: usize = 0;
    let mut v___x_5828_: u8 = 0;
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: u8 = 0;
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5846_: u8 = 0;
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5850_: u8 = 0;
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5828_ = lean_usize_dec_eq(v_i_5815_, v_stop_5816_);
                if v___x_5828_ == 0 {
                    v___x_5829_ = lean_array_uget_borrowed(v_as_5814_, v_i_5815_);
                    lean_inc_ref(v___x_5813_);
                    lean_inc(v___x_5829_);
                    v___x_5830_ = l_Lean_Meta_isExprDefEq(
                        v___x_5829_,
                        v___x_5813_,
                        v___y_5818_,
                        v___y_5819_,
                        v___y_5820_,
                        v___y_5821_,
                    );
                    if lean_obj_tag(v___x_5830_) == 0 {
                        v_a_5831_ = lean_ctor_get(v___x_5830_, 0);
                        lean_inc(v_a_5831_);
                        lean_dec_ref_known(v___x_5830_, 1);
                        v___x_5832_ = (lean_unbox(v_a_5831_) as u8);
                        lean_dec(v_a_5831_);
                        if v___x_5832_ == 0 {
                            v___x_5833_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1);
                            lean_inc(v___x_5829_);
                            v___x_5834_ = l_Lean_MessageData_ofExpr(v___x_5829_);
                            v___x_5835_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5835_, 0, v___x_5833_);
                            lean_ctor_set(v___x_5835_, 1, v___x_5834_);
                            v___x_5836_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3);
                            v___x_5837_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5837_, 0, v___x_5835_);
                            lean_ctor_set(v___x_5837_, 1, v___x_5836_);
                            lean_inc_ref(v___x_5813_);
                            v___x_5838_ = l_Lean_MessageData_ofExpr(v___x_5813_);
                            v___x_5839_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5839_, 0, v___x_5837_);
                            lean_ctor_set(v___x_5839_, 1, v___x_5838_);
                            v___x_5840_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_5839_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_);
                            if lean_obj_tag(v___x_5840_) == 0 {
                                v_a_5841_ = lean_ctor_get(v___x_5840_, 0);
                                lean_inc(v_a_5841_);
                                lean_dec_ref_known(v___x_5840_, 1);
                                v_a_5824_ = v_a_5841_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v___x_5813_);
                                return v___x_5840_;
                            }
                        } else {
                            v___x_5842_ = lean_box(0);
                            v_a_5824_ = v___x_5842_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_5813_);
                        v_a_5843_ = lean_ctor_get(v___x_5830_, 0);
                        v_isSharedCheck_5850_ = (!lean_is_exclusive(v___x_5830_)) as u8;
                        if v_isSharedCheck_5850_ == 0 {
                            v___x_5845_ = v___x_5830_;
                            v_isShared_5846_ = v_isSharedCheck_5850_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5843_);
                            lean_dec(v___x_5830_);
                            v___x_5845_ = lean_box(0);
                            v_isShared_5846_ = v_isSharedCheck_5850_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_5813_);
                    v___x_5851_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5851_, 0, v_b_5817_);
                    return v___x_5851_;
                }
            }
            1 => {
                v___x_5825_ = 1usize;
                v___x_5826_ = lean_usize_add(v_i_5815_, v___x_5825_);
                v_i_5815_ = v___x_5826_;
                v_b_5817_ = v_a_5824_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5846_ == 0 {
                    v___x_5848_ = v___x_5845_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5849_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5849_, 0, v_a_5843_);
                    v___x_5848_ = v_reuseFailAlloc_5849_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___boxed(
    mut v___x_5852_: *mut LeanObject,
    mut v_as_5853_: *mut LeanObject,
    mut v_i_5854_: *mut LeanObject,
    mut v_stop_5855_: *mut LeanObject,
    mut v_b_5856_: *mut LeanObject,
    mut v___y_5857_: *mut LeanObject,
    mut v___y_5858_: *mut LeanObject,
    mut v___y_5859_: *mut LeanObject,
    mut v___y_5860_: *mut LeanObject,
    mut v___y_5861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5862_: usize = 0;
    let mut v_stop_boxed_5863_: usize = 0;
    let mut v_res_5864_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5862_ = lean_unbox_usize(v_i_5854_);
    lean_dec(v_i_5854_);
    v_stop_boxed_5863_ = lean_unbox_usize(v_stop_5855_);
    lean_dec(v_stop_5855_);
    v_res_5864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_5852_, v_as_5853_, v_i_boxed_5862_, v_stop_boxed_5863_, v_b_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_);
    lean_dec(v___y_5860_);
    lean_dec_ref(v___y_5859_);
    lean_dec(v___y_5858_);
    lean_dec_ref(v___y_5857_);
    lean_dec_ref(v_as_5853_);
    return v_res_5864_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(
    mut v_sz_5865_: usize,
    mut v_i_5866_: usize,
    mut v_bs_5867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5868_: u8 = 0;
    let mut v_v_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: usize = 0;
    let mut v___x_5874_: usize = 0;
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5868_ = lean_usize_dec_lt(v_i_5866_, v_sz_5865_);
                if v___x_5868_ == 0 {
                    return v_bs_5867_;
                } else {
                    v_v_5869_ = lean_array_uget(v_bs_5867_, v_i_5866_);
                    v___x_5870_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5871_ = lean_array_uset(v_bs_5867_, v_i_5866_, v___x_5870_);
                    v___x_5872_ = l_Lean_Expr_bindingBody_x21(v_v_5869_);
                    lean_dec(v_v_5869_);
                    v___x_5873_ = 1usize;
                    v___x_5874_ = lean_usize_add(v_i_5866_, v___x_5873_);
                    v___x_5875_ = lean_array_uset(v_bs_x27_5871_, v_i_5866_, v___x_5872_);
                    v_i_5866_ = v___x_5874_;
                    v_bs_5867_ = v___x_5875_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0___boxed(
    mut v_sz_5877_: *mut LeanObject,
    mut v_i_5878_: *mut LeanObject,
    mut v_bs_5879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5880_: usize = 0;
    let mut v_i_boxed_5881_: usize = 0;
    let mut v_res_5882_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5880_ = lean_unbox_usize(v_sz_5877_);
    lean_dec(v_sz_5877_);
    v_i_boxed_5881_ = lean_unbox_usize(v_i_5878_);
    lean_dec(v_i_5878_);
    v_res_5882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_boxed_5880_, v_i_boxed_5881_, v_bs_5879_);
    return v_res_5882_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    v___x_5884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0;
    v___x_5885_ = l_Lean_stringToMessageData(v___x_5884_);
    return v___x_5885_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(
    mut v_as_5886_: *mut LeanObject,
    mut v_i_5887_: usize,
    mut v_stop_5888_: usize,
    mut v_b_5889_: *mut LeanObject,
    mut v___y_5890_: *mut LeanObject,
    mut v___y_5891_: *mut LeanObject,
    mut v___y_5892_: *mut LeanObject,
    mut v___y_5893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: usize = 0;
    let mut v___x_5898_: usize = 0;
    let mut v___x_5900_: u8 = 0;
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: u8 = 0;
    let mut v___x_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5900_ = lean_usize_dec_eq(v_i_5887_, v_stop_5888_);
                if v___x_5900_ == 0 {
                    v___x_5901_ = lean_array_uget_borrowed(v_as_5886_, v_i_5887_);
                    v___x_5902_ = l_Lean_Expr_isArrow(v___x_5901_);
                    if v___x_5902_ == 0 {
                        v___x_5903_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1);
                        lean_inc(v___x_5901_);
                        v___x_5904_ = l_Lean_MessageData_ofExpr(v___x_5901_);
                        v___x_5905_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5905_, 0, v___x_5903_);
                        lean_ctor_set(v___x_5905_, 1, v___x_5904_);
                        v___x_5906_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_5905_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_);
                        if lean_obj_tag(v___x_5906_) == 0 {
                            v_a_5907_ = lean_ctor_get(v___x_5906_, 0);
                            lean_inc(v_a_5907_);
                            lean_dec_ref_known(v___x_5906_, 1);
                            v_a_5896_ = v_a_5907_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_5906_;
                        }
                    } else {
                        v___x_5908_ = lean_box(0);
                        v_a_5896_ = v___x_5908_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_5909_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5909_, 0, v_b_5889_);
                    return v___x_5909_;
                }
            }
            1 => {
                v___x_5897_ = 1usize;
                v___x_5898_ = lean_usize_add(v_i_5887_, v___x_5897_);
                v_i_5887_ = v___x_5898_;
                v_b_5889_ = v_a_5896_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___boxed(
    mut v_as_5910_: *mut LeanObject,
    mut v_i_5911_: *mut LeanObject,
    mut v_stop_5912_: *mut LeanObject,
    mut v_b_5913_: *mut LeanObject,
    mut v___y_5914_: *mut LeanObject,
    mut v___y_5915_: *mut LeanObject,
    mut v___y_5916_: *mut LeanObject,
    mut v___y_5917_: *mut LeanObject,
    mut v___y_5918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5919_: usize = 0;
    let mut v_stop_boxed_5920_: usize = 0;
    let mut v_res_5921_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5919_ = lean_unbox_usize(v_i_5911_);
    lean_dec(v_i_5911_);
    v_stop_boxed_5920_ = lean_unbox_usize(v_stop_5912_);
    lean_dec(v_stop_5912_);
    v_res_5921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_as_5910_, v_i_boxed_5919_, v_stop_boxed_5920_, v_b_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_);
    lean_dec(v___y_5917_);
    lean_dec_ref(v___y_5916_);
    lean_dec(v___y_5915_);
    lean_dec_ref(v___y_5914_);
    lean_dec_ref(v_as_5910_);
    return v_res_5921_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(
    mut v_types_5922_: *mut LeanObject,
    mut v_a_5923_: *mut LeanObject,
    mut v_a_5924_: *mut LeanObject,
    mut v_a_5925_: *mut LeanObject,
    mut v_a_5926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_5928_: usize = 0;
    let mut v___x_5929_: usize = 0;
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5935_: usize = 0;
    let mut v___y_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5943_: usize = 0;
    let mut v___y_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5949_: u8 = 0;
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5953_: u8 = 0;
    let mut v_sz_5955_: usize = 0;
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: u8 = 0;
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: u8 = 0;
    let mut v___x_5966_: usize = 0;
    let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: usize = 0;
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5975_: u8 = 0;
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5979_: u8 = 0;
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: u8 = 0;
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: u8 = 0;
    let mut v___x_5984_: usize = 0;
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: usize = 0;
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5991_: u8 = 0;
    let mut v___x_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_5928_ = lean_array_size(v_types_5922_);
                v___x_5929_ = 0usize;
                v___x_5930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_5928_, v___x_5929_, v_types_5922_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_);
                if lean_obj_tag(v___x_5930_) == 0 {
                    v_a_5931_ = lean_ctor_get(v___x_5930_, 0);
                    lean_inc(v_a_5931_);
                    lean_dec_ref_known(v___x_5930_, 1);
                    v___x_5932_ = l_Lean_instInhabitedExpr;
                    v___x_5933_ = lean_unsigned_to_nat(0);
                    v___x_5980_ = lean_array_get_size(v_a_5931_);
                    v___x_5981_ = lean_nat_dec_lt(v___x_5933_, v___x_5980_);
                    if v___x_5981_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        v___x_5982_ = lean_box(0);
                        v___x_5983_ = lean_nat_dec_le(v___x_5980_, v___x_5980_);
                        if v___x_5983_ == 0 {
                            if v___x_5981_ == 0 {
                                state = 5;
                                continue;
                            } else {
                                v___x_5984_ = lean_usize_of_nat(v___x_5980_);
                                v___x_5985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_5931_, v___x_5929_, v___x_5984_, v___x_5982_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_);
                                v___y_5971_ = v___x_5985_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v___x_5986_ = lean_usize_of_nat(v___x_5980_);
                            v___x_5987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_5931_, v___x_5929_, v___x_5986_, v___x_5982_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_);
                            v___y_5971_ = v___x_5987_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_5988_ = lean_ctor_get(v___x_5930_, 0);
                    v_isSharedCheck_5995_ = (!lean_is_exclusive(v___x_5930_)) as u8;
                    if v_isSharedCheck_5995_ == 0 {
                        v___x_5990_ = v___x_5930_;
                        v_isShared_5991_ = v_isSharedCheck_5995_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5988_);
                        lean_dec(v___x_5930_);
                        v___x_5990_ = lean_box(0);
                        v_isShared_5991_ = v_isSharedCheck_5995_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v___y_5935_, v___x_5929_, v_a_5931_);
                v___x_5938_ = l_Lean_Meta_ArgsPacker_Mutual_packType(
                    v___x_5937_,
                    v_a_5923_,
                    v_a_5924_,
                    v_a_5925_,
                    v_a_5926_,
                );
                if lean_obj_tag(v___x_5938_) == 0 {
                    v_a_5939_ = lean_ctor_get(v___x_5938_, 0);
                    lean_inc(v_a_5939_);
                    lean_dec_ref_known(v___x_5938_, 1);
                    v___x_5940_ = lean_array_get(v___x_5932_, v___y_5936_, v___x_5933_);
                    lean_dec_ref(v___y_5936_);
                    v___x_5941_ = l_Lean_mkArrow(v_a_5939_, v___x_5940_, v_a_5925_, v_a_5926_);
                    return v___x_5941_;
                } else {
                    lean_dec_ref(v___y_5936_);
                    return v___x_5938_;
                }
            }
            2 => {
                if lean_obj_tag(v___y_5945_) == 0 {
                    lean_dec_ref_known(v___y_5945_, 1);
                    v___y_5935_ = v___y_5943_;
                    v___y_5936_ = v___y_5944_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___y_5944_);
                    lean_dec(v_a_5931_);
                    v_a_5946_ = lean_ctor_get(v___y_5945_, 0);
                    v_isSharedCheck_5953_ = (!lean_is_exclusive(v___y_5945_)) as u8;
                    if v_isSharedCheck_5953_ == 0 {
                        v___x_5948_ = v___y_5945_;
                        v_isShared_5949_ = v_isSharedCheck_5953_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5946_);
                        lean_dec(v___y_5945_);
                        v___x_5948_ = lean_box(0);
                        v_isShared_5949_ = v_isSharedCheck_5953_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5949_ == 0 {
                    v___x_5951_ = v___x_5948_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5952_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_a_5946_);
                    v___x_5951_ = v_reuseFailAlloc_5952_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5951_;
            }
            5 => {
                v_sz_5955_ = lean_array_size(v_a_5931_);
                lean_inc(v_a_5931_);
                v___x_5956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_5955_, v___x_5929_, v_a_5931_);
                v___x_5957_ = lean_array_get_size(v___x_5956_);
                v___x_5958_ = lean_unsigned_to_nat(1);
                v___x_5959_ = lean_nat_sub(v___x_5957_, v___x_5958_);
                v___x_5960_ = lean_array_get(v___x_5932_, v___x_5956_, v___x_5959_);
                lean_dec(v___x_5959_);
                lean_inc_ref(v___x_5956_);
                v___x_5961_ = lean_array_pop(v___x_5956_);
                v___x_5962_ = lean_array_get_size(v___x_5961_);
                v___x_5963_ = lean_nat_dec_lt(v___x_5933_, v___x_5962_);
                if v___x_5963_ == 0 {
                    lean_dec_ref(v___x_5961_);
                    lean_dec(v___x_5960_);
                    v___y_5935_ = v_sz_5955_;
                    v___y_5936_ = v___x_5956_;
                    state = 1;
                    continue;
                } else {
                    v___x_5964_ = lean_box(0);
                    v___x_5965_ = lean_nat_dec_le(v___x_5962_, v___x_5962_);
                    if v___x_5965_ == 0 {
                        if v___x_5963_ == 0 {
                            lean_dec_ref(v___x_5961_);
                            lean_dec(v___x_5960_);
                            v___y_5935_ = v_sz_5955_;
                            v___y_5936_ = v___x_5956_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5966_ = lean_usize_of_nat(v___x_5962_);
                            v___x_5967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_5960_, v___x_5961_, v___x_5929_, v___x_5966_, v___x_5964_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_);
                            lean_dec_ref(v___x_5961_);
                            v___y_5943_ = v_sz_5955_;
                            v___y_5944_ = v___x_5956_;
                            v___y_5945_ = v___x_5967_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_5968_ = lean_usize_of_nat(v___x_5962_);
                        v___x_5969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_5960_, v___x_5961_, v___x_5929_, v___x_5968_, v___x_5964_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_);
                        lean_dec_ref(v___x_5961_);
                        v___y_5943_ = v_sz_5955_;
                        v___y_5944_ = v___x_5956_;
                        v___y_5945_ = v___x_5969_;
                        state = 2;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v___y_5971_) == 0 {
                    lean_dec_ref_known(v___y_5971_, 1);
                    state = 5;
                    continue;
                } else {
                    lean_dec(v_a_5931_);
                    v_a_5972_ = lean_ctor_get(v___y_5971_, 0);
                    v_isSharedCheck_5979_ = (!lean_is_exclusive(v___y_5971_)) as u8;
                    if v_isSharedCheck_5979_ == 0 {
                        v___x_5974_ = v___y_5971_;
                        v_isShared_5975_ = v_isSharedCheck_5979_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5972_);
                        lean_dec(v___y_5971_);
                        v___x_5974_ = lean_box(0);
                        v_isShared_5975_ = v_isSharedCheck_5979_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_5975_ == 0 {
                    v___x_5977_ = v___x_5974_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5978_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5978_, 0, v_a_5972_);
                    v___x_5977_ = v_reuseFailAlloc_5978_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5977_;
            }
            9 => {
                if v_isShared_5991_ == 0 {
                    v___x_5993_ = v___x_5990_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5994_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5994_, 0, v_a_5988_);
                    v___x_5993_ = v_reuseFailAlloc_5994_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND___boxed(
    mut v_types_5996_: *mut LeanObject,
    mut v_a_5997_: *mut LeanObject,
    mut v_a_5998_: *mut LeanObject,
    mut v_a_5999_: *mut LeanObject,
    mut v_a_6000_: *mut LeanObject,
    mut v_a_6001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6002_: *mut LeanObject = core::ptr::null_mut();
    v_res_6002_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(
        v_types_5996_,
        v_a_5997_,
        v_a_5998_,
        v_a_5999_,
        v_a_6000_,
    );
    lean_dec(v_a_6000_);
    lean_dec_ref(v_a_5999_);
    lean_dec(v_a_5998_);
    lean_dec_ref(v_a_5997_);
    return v_res_6002_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1()
-> *mut LeanObject {
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    v___x_6004_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0;
    v___x_6005_ = l_Lean_stringToMessageData(v___x_6004_);
    return v___x_6005_;
}
pub unsafe fn _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3()
-> *mut LeanObject {
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    v___x_6007_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2;
    v___x_6008_ = l_Lean_stringToMessageData(v___x_6007_);
    return v___x_6008_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed(
    mut v___x_6009_: *mut LeanObject,
    mut v___x_6010_: *mut LeanObject,
    mut v_arg_6011_: *mut LeanObject,
    mut v_arg_6012_: *mut LeanObject,
    mut v___x_6013_: *mut LeanObject,
    mut v_a_6014_: *mut LeanObject,
    mut v_tail_6015_: *mut LeanObject,
    mut v___x_6016_: *mut LeanObject,
    mut v___x_6017_: *mut LeanObject,
    mut v___x_6018_: *mut LeanObject,
    mut v_y_6019_: *mut LeanObject,
    mut v___y_6020_: *mut LeanObject,
    mut v___y_6021_: *mut LeanObject,
    mut v___y_6022_: *mut LeanObject,
    mut v___y_6023_: *mut LeanObject,
    mut v___y_6024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3071__boxed_6025_: u8 = 0;
    let mut v___x_3072__boxed_6026_: u8 = 0;
    let mut v___x_3073__boxed_6027_: u8 = 0;
    let mut v_res_6028_: *mut LeanObject = core::ptr::null_mut();
    v___x_3071__boxed_6025_ = (lean_unbox(v___x_6016_) as u8);
    v___x_3072__boxed_6026_ = (lean_unbox(v___x_6017_) as u8);
    v___x_3073__boxed_6027_ = (lean_unbox(v___x_6018_) as u8);
    v_res_6028_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(
        v___x_6009_,
        v___x_6010_,
        v_arg_6011_,
        v_arg_6012_,
        v___x_6013_,
        v_a_6014_,
        v_tail_6015_,
        v___x_3071__boxed_6025_,
        v___x_3072__boxed_6026_,
        v___x_3073__boxed_6027_,
        v_y_6019_,
        v___y_6020_,
        v___y_6021_,
        v___y_6022_,
        v___y_6023_,
    );
    lean_dec(v___y_6023_);
    lean_dec_ref(v___y_6022_);
    lean_dec(v___y_6021_);
    lean_dec_ref(v___y_6020_);
    return v_res_6028_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(
    mut v_x_6029_: *mut LeanObject,
    mut v_codomain_6030_: *mut LeanObject,
    mut v_alts_6031_: *mut LeanObject,
    mut v_a_6032_: *mut LeanObject,
    mut v_a_6033_: *mut LeanObject,
    mut v_a_6034_: *mut LeanObject,
    mut v_a_6035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6049_: u8 = 0;
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: u8 = 0;
    let mut v_arg_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: u8 = 0;
    let mut v_arg_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: u8 = 0;
    let mut v___x_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: u8 = 0;
    let mut v___x_6079_: u8 = 0;
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6084_: u8 = 0;
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alt_u2082_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6115_: u8 = 0;
    let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6119_: u8 = 0;
    let mut v_tail_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6122_: u8 = 0;
    let mut v_a_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6126_: u8 = 0;
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6130_: u8 = 0;
    let mut v_isSharedCheck_6131_: u8 = 0;
    let mut v_unused_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_alts_6031_) == 0 {
                    lean_dec_ref(v_codomain_6030_);
                    lean_dec_ref(v_x_6029_);
                    v___x_6037_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1);
                    v___x_6038_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_6037_, v_a_6032_, v_a_6033_, v_a_6034_, v_a_6035_);
                    return v___x_6038_;
                } else {
                    v_tail_6039_ = lean_ctor_get(v_alts_6031_, 1);
                    if lean_obj_tag(v_tail_6039_) == 0 {
                        lean_dec_ref(v_codomain_6030_);
                        v_head_6040_ = lean_ctor_get(v_alts_6031_, 0);
                        lean_inc(v_head_6040_);
                        lean_dec_ref_known(v_alts_6031_, 2);
                        v___x_6041_ = lean_unsigned_to_nat(1);
                        v___x_6042_ = lean_mk_empty_array_with_capacity(v___x_6041_);
                        v___x_6043_ = lean_array_push(v___x_6042_, v_x_6029_);
                        v___x_6044_ = l_Lean_Expr_beta(v_head_6040_, v___x_6043_);
                        v___x_6045_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6045_, 0, v___x_6044_);
                        return v___x_6045_;
                    } else {
                        lean_inc(v_tail_6039_);
                        v_head_6046_ = lean_ctor_get(v_alts_6031_, 0);
                        v_isSharedCheck_6131_ = (!lean_is_exclusive(v_alts_6031_)) as u8;
                        if v_isSharedCheck_6131_ == 0 {
                            v_unused_6132_ = lean_ctor_get(v_alts_6031_, 1);
                            lean_dec(v_unused_6132_);
                            v___x_6048_ = v_alts_6031_;
                            v_isShared_6049_ = v_isSharedCheck_6131_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_head_6046_);
                            lean_dec(v_alts_6031_);
                            v___x_6048_ = lean_box(0);
                            v_isShared_6049_ = v_isSharedCheck_6131_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_6035_);
                lean_inc_ref(v_a_6034_);
                lean_inc(v_a_6033_);
                lean_inc_ref(v_a_6032_);
                lean_inc_ref(v_x_6029_);
                v___x_6050_ =
                    lean_infer_type(v_x_6029_, v_a_6032_, v_a_6033_, v_a_6034_, v_a_6035_);
                if lean_obj_tag(v___x_6050_) == 0 {
                    v_a_6051_ = lean_ctor_get(v___x_6050_, 0);
                    lean_inc_n(v_a_6051_, 2);
                    lean_dec_ref_known(v___x_6050_, 1);
                    v___x_6052_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_6051_, v_a_6033_);
                    if lean_obj_tag(v___x_6052_) == 0 {
                        v_a_6053_ = lean_ctor_get(v___x_6052_, 0);
                        lean_inc(v_a_6053_);
                        lean_dec_ref_known(v___x_6052_, 1);
                        v___x_6063_ = l_Lean_Expr_cleanupAnnotations(v_a_6053_);
                        v___x_6064_ = l_Lean_Expr_isApp(v___x_6063_);
                        if v___x_6064_ == 0 {
                            lean_dec_ref(v___x_6063_);
                            lean_del_object(v___x_6048_);
                            lean_dec(v_head_6046_);
                            lean_dec(v_tail_6039_);
                            lean_dec_ref(v_codomain_6030_);
                            lean_dec_ref(v_x_6029_);
                            v___y_6055_ = v_a_6032_;
                            v___y_6056_ = v_a_6033_;
                            v___y_6057_ = v_a_6034_;
                            v___y_6058_ = v_a_6035_;
                            state = 2;
                            continue;
                        } else {
                            v_arg_6065_ = lean_ctor_get(v___x_6063_, 1);
                            lean_inc_ref(v_arg_6065_);
                            v___x_6066_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6063_);
                            v___x_6067_ = l_Lean_Expr_isApp(v___x_6066_);
                            if v___x_6067_ == 0 {
                                lean_dec_ref(v___x_6066_);
                                lean_dec_ref(v_arg_6065_);
                                lean_del_object(v___x_6048_);
                                lean_dec(v_head_6046_);
                                lean_dec(v_tail_6039_);
                                lean_dec_ref(v_codomain_6030_);
                                lean_dec_ref(v_x_6029_);
                                v___y_6055_ = v_a_6032_;
                                v___y_6056_ = v_a_6033_;
                                v___y_6057_ = v_a_6034_;
                                v___y_6058_ = v_a_6035_;
                                state = 2;
                                continue;
                            } else {
                                v_arg_6068_ = lean_ctor_get(v___x_6066_, 1);
                                lean_inc_ref(v_arg_6068_);
                                v___x_6069_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6066_);
                                v___x_6070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0;
                                v___x_6071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1;
                                v___x_6072_ = l_Lean_Expr_isConstOf(v___x_6069_, v___x_6071_);
                                lean_dec_ref(v___x_6069_);
                                if v___x_6072_ == 0 {
                                    lean_dec_ref(v_arg_6068_);
                                    lean_dec_ref(v_arg_6065_);
                                    lean_del_object(v___x_6048_);
                                    lean_dec(v_head_6046_);
                                    lean_dec(v_tail_6039_);
                                    lean_dec_ref(v_codomain_6030_);
                                    lean_dec_ref(v_x_6029_);
                                    v___y_6055_ = v_a_6032_;
                                    v___y_6056_ = v_a_6033_;
                                    v___y_6057_ = v_a_6034_;
                                    v___y_6058_ = v_a_6035_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc_ref(v_codomain_6030_);
                                    v___x_6073_ = l_Lean_Meta_getLevel(
                                        v_codomain_6030_,
                                        v_a_6032_,
                                        v_a_6033_,
                                        v_a_6034_,
                                        v_a_6035_,
                                    );
                                    if lean_obj_tag(v___x_6073_) == 0 {
                                        v_a_6074_ = lean_ctor_get(v___x_6073_, 0);
                                        lean_inc(v_a_6074_);
                                        lean_dec_ref_known(v___x_6073_, 1);
                                        v___x_6075_ = lean_unsigned_to_nat(1);
                                        v___x_6076_ =
                                            lean_mk_empty_array_with_capacity(v___x_6075_);
                                        lean_inc_ref(v_x_6029_);
                                        lean_inc_ref(v___x_6076_);
                                        v___x_6077_ = lean_array_push(v___x_6076_, v_x_6029_);
                                        v___x_6078_ = 0;
                                        v___x_6079_ = 1;
                                        v___x_6080_ = l_Lean_Meta_mkLambdaFVars(
                                            v___x_6077_,
                                            v_codomain_6030_,
                                            v___x_6078_,
                                            v___x_6072_,
                                            v___x_6078_,
                                            v___x_6072_,
                                            v___x_6079_,
                                            v_a_6032_,
                                            v_a_6033_,
                                            v_a_6034_,
                                            v_a_6035_,
                                        );
                                        lean_dec_ref(v___x_6077_);
                                        if lean_obj_tag(v___x_6080_) == 0 {
                                            v_a_6081_ = lean_ctor_get(v___x_6080_, 0);
                                            v_isSharedCheck_6122_ =
                                                (!lean_is_exclusive(v___x_6080_)) as u8;
                                            if v_isSharedCheck_6122_ == 0 {
                                                v___x_6083_ = v___x_6080_;
                                                v_isShared_6084_ = v_isSharedCheck_6122_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_a_6081_);
                                                lean_dec(v___x_6080_);
                                                v___x_6083_ = lean_box(0);
                                                v_isShared_6084_ = v_isSharedCheck_6122_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v___x_6076_);
                                            lean_dec(v_a_6074_);
                                            lean_dec_ref(v_arg_6068_);
                                            lean_dec_ref(v_arg_6065_);
                                            lean_dec(v_a_6051_);
                                            lean_del_object(v___x_6048_);
                                            lean_dec(v_head_6046_);
                                            lean_dec(v_tail_6039_);
                                            lean_dec_ref(v_x_6029_);
                                            return v___x_6080_;
                                        }
                                    } else {
                                        lean_dec_ref(v_arg_6068_);
                                        lean_dec_ref(v_arg_6065_);
                                        lean_dec(v_a_6051_);
                                        lean_del_object(v___x_6048_);
                                        lean_dec(v_head_6046_);
                                        lean_dec(v_tail_6039_);
                                        lean_dec_ref(v_codomain_6030_);
                                        lean_dec_ref(v_x_6029_);
                                        v_a_6123_ = lean_ctor_get(v___x_6073_, 0);
                                        v_isSharedCheck_6130_ =
                                            (!lean_is_exclusive(v___x_6073_)) as u8;
                                        if v_isSharedCheck_6130_ == 0 {
                                            v___x_6125_ = v___x_6073_;
                                            v_isShared_6126_ = v_isSharedCheck_6130_;
                                            state = 10;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6123_);
                                            lean_dec(v___x_6073_);
                                            v___x_6125_ = lean_box(0);
                                            v_isShared_6126_ = v_isSharedCheck_6130_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_6051_);
                        lean_del_object(v___x_6048_);
                        lean_dec(v_head_6046_);
                        lean_dec(v_tail_6039_);
                        lean_dec_ref(v_codomain_6030_);
                        lean_dec_ref(v_x_6029_);
                        return v___x_6052_;
                    }
                } else {
                    lean_del_object(v___x_6048_);
                    lean_dec(v_head_6046_);
                    lean_dec(v_tail_6039_);
                    lean_dec_ref(v_codomain_6030_);
                    lean_dec_ref(v_x_6029_);
                    return v___x_6050_;
                }
            }
            2 => {
                v___x_6059_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3);
                v___x_6060_ = l_Lean_MessageData_ofExpr(v_a_6051_);
                v___x_6061_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6061_, 0, v___x_6059_);
                lean_ctor_set(v___x_6061_, 1, v___x_6060_);
                v___x_6062_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_6061_, v___y_6055_, v___y_6056_, v___y_6057_, v___y_6058_);
                return v___x_6062_;
            }
            3 => {
                v___x_6085_ = l_Lean_Expr_getAppFn(v_a_6051_);
                lean_dec(v_a_6051_);
                v___x_6086_ = l_Lean_Expr_constLevels_x21(v___x_6085_);
                lean_dec_ref(v___x_6085_);
                v___x_6098_ = lean_box((v___x_6078_) as usize);
                v___x_6099_ = lean_box((v___x_6072_) as usize);
                v___x_6100_ = lean_box((v___x_6079_) as usize);
                lean_inc(v_tail_6039_);
                lean_inc(v_a_6081_);
                lean_inc_ref(v_arg_6065_);
                lean_inc_ref(v_arg_6068_);
                lean_inc(v___x_6086_);
                v___f_6101_ = lean_alloc_closure(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed as *mut core::ffi::c_void, 16, 10);
                lean_closure_set(v___f_6101_, 0, v___x_6070_);
                lean_closure_set(v___f_6101_, 1, v___x_6086_);
                lean_closure_set(v___f_6101_, 2, v_arg_6068_);
                lean_closure_set(v___f_6101_, 3, v_arg_6065_);
                lean_closure_set(v___f_6101_, 4, v___x_6076_);
                lean_closure_set(v___f_6101_, 5, v_a_6081_);
                lean_closure_set(v___f_6101_, 6, v_tail_6039_);
                lean_closure_set(v___f_6101_, 7, v___x_6098_);
                lean_closure_set(v___f_6101_, 8, v___x_6099_);
                lean_closure_set(v___f_6101_, 9, v___x_6100_);
                if lean_obj_tag(v_tail_6039_) == 1 {
                    v_tail_6120_ = lean_ctor_get(v_tail_6039_, 1);
                    if lean_obj_tag(v_tail_6120_) == 0 {
                        lean_dec_ref(v___f_6101_);
                        v_head_6121_ = lean_ctor_get(v_tail_6039_, 0);
                        lean_inc(v_head_6121_);
                        lean_dec_ref_known(v_tail_6039_, 2);
                        v_alt_u2082_6088_ = v_head_6121_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec_ref_known(v_tail_6039_, 2);
                        v___y_6103_ = v_a_6032_;
                        v___y_6104_ = v_a_6033_;
                        v___y_6105_ = v_a_6034_;
                        v___y_6106_ = v_a_6035_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v_tail_6039_);
                    v___y_6103_ = v_a_6032_;
                    v___y_6104_ = v_a_6033_;
                    v___y_6105_ = v_a_6034_;
                    v___y_6106_ = v_a_6035_;
                    state = 7;
                    continue;
                }
            }
            4 => {
                v___x_6089_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3;
                if v_isShared_6049_ == 0 {
                    lean_ctor_set(v___x_6048_, 1, v___x_6086_);
                    lean_ctor_set(v___x_6048_, 0, v_a_6074_);
                    v___x_6091_ = v___x_6048_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6097_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6097_, 0, v_a_6074_);
                    lean_ctor_set(v_reuseFailAlloc_6097_, 1, v___x_6086_);
                    v___x_6091_ = v_reuseFailAlloc_6097_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6092_ = l_Lean_Expr_const___override(v___x_6089_, v___x_6091_);
                v___x_6093_ = l_Lean_mkApp6(
                    v___x_6092_,
                    v_arg_6068_,
                    v_arg_6065_,
                    v_a_6081_,
                    v_x_6029_,
                    v_head_6046_,
                    v_alt_u2082_6088_,
                );
                if v_isShared_6084_ == 0 {
                    lean_ctor_set(v___x_6083_, 0, v___x_6093_);
                    v___x_6095_ = v___x_6083_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6096_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6096_, 0, v___x_6093_);
                    v___x_6095_ = v_reuseFailAlloc_6096_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6095_;
            }
            7 => {
                v___x_6107_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4;
                v___x_6108_ = l_Lean_Core_mkFreshUserName(v___x_6107_, v___y_6105_, v___y_6106_);
                if lean_obj_tag(v___x_6108_) == 0 {
                    v_a_6109_ = lean_ctor_get(v___x_6108_, 0);
                    lean_inc(v_a_6109_);
                    lean_dec_ref_known(v___x_6108_, 1);
                    lean_inc_ref(v_arg_6065_);
                    v___x_6110_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_6109_, v_arg_6065_, v___f_6101_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_);
                    if lean_obj_tag(v___x_6110_) == 0 {
                        v_a_6111_ = lean_ctor_get(v___x_6110_, 0);
                        lean_inc(v_a_6111_);
                        lean_dec_ref_known(v___x_6110_, 1);
                        v_alt_u2082_6088_ = v_a_6111_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_6086_);
                        lean_del_object(v___x_6083_);
                        lean_dec(v_a_6081_);
                        lean_dec(v_a_6074_);
                        lean_dec_ref(v_arg_6068_);
                        lean_dec_ref(v_arg_6065_);
                        lean_del_object(v___x_6048_);
                        lean_dec(v_head_6046_);
                        lean_dec_ref(v_x_6029_);
                        return v___x_6110_;
                    }
                } else {
                    lean_dec_ref(v___f_6101_);
                    lean_dec(v___x_6086_);
                    lean_del_object(v___x_6083_);
                    lean_dec(v_a_6081_);
                    lean_dec(v_a_6074_);
                    lean_dec_ref(v_arg_6068_);
                    lean_dec_ref(v_arg_6065_);
                    lean_del_object(v___x_6048_);
                    lean_dec(v_head_6046_);
                    lean_dec_ref(v_x_6029_);
                    v_a_6112_ = lean_ctor_get(v___x_6108_, 0);
                    v_isSharedCheck_6119_ = (!lean_is_exclusive(v___x_6108_)) as u8;
                    if v_isSharedCheck_6119_ == 0 {
                        v___x_6114_ = v___x_6108_;
                        v_isShared_6115_ = v_isSharedCheck_6119_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6112_);
                        lean_dec(v___x_6108_);
                        v___x_6114_ = lean_box(0);
                        v_isShared_6115_ = v_isSharedCheck_6119_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_6115_ == 0 {
                    v___x_6117_ = v___x_6114_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6118_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6118_, 0, v_a_6112_);
                    v___x_6117_ = v_reuseFailAlloc_6118_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6117_;
            }
            10 => {
                if v_isShared_6126_ == 0 {
                    v___x_6128_ = v___x_6125_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6129_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6129_, 0, v_a_6123_);
                    v___x_6128_ = v_reuseFailAlloc_6129_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(
    mut v___x_6133_: *mut LeanObject,
    mut v___x_6134_: *mut LeanObject,
    mut v_arg_6135_: *mut LeanObject,
    mut v_arg_6136_: *mut LeanObject,
    mut v___x_6137_: *mut LeanObject,
    mut v_a_6138_: *mut LeanObject,
    mut v_tail_6139_: *mut LeanObject,
    mut v___x_6140_: u8,
    mut v___x_6141_: u8,
    mut v___x_6142_: u8,
    mut v_y_6143_: *mut LeanObject,
    mut v___y_6144_: *mut LeanObject,
    mut v___y_6145_: *mut LeanObject,
    mut v___y_6146_: *mut LeanObject,
    mut v___y_6147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    v___x_6149_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3;
    v___x_6150_ = l_Lean_Name_mkStr2(v___x_6133_, v___x_6149_);
    v___x_6151_ = l_Lean_Expr_const___override(v___x_6150_, v___x_6134_);
    lean_inc_ref_n(v_y_6143_, 2);
    v___x_6152_ = l_Lean_mkApp3(v___x_6151_, v_arg_6135_, v_arg_6136_, v_y_6143_);
    lean_inc_ref(v___x_6137_);
    v___x_6153_ = lean_array_push(v___x_6137_, v___x_6152_);
    v___x_6154_ = l_Lean_Expr_beta(v_a_6138_, v___x_6153_);
    v___x_6155_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(
        v_y_6143_,
        v___x_6154_,
        v_tail_6139_,
        v___y_6144_,
        v___y_6145_,
        v___y_6146_,
        v___y_6147_,
    );
    if lean_obj_tag(v___x_6155_) == 0 {
        let mut v_a_6156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
        v_a_6156_ = lean_ctor_get(v___x_6155_, 0);
        lean_inc(v_a_6156_);
        lean_dec_ref_known(v___x_6155_, 1);
        v___x_6157_ = lean_array_push(v___x_6137_, v_y_6143_);
        v___x_6158_ = l_Lean_Meta_mkLambdaFVars(
            v___x_6157_,
            v_a_6156_,
            v___x_6140_,
            v___x_6141_,
            v___x_6140_,
            v___x_6141_,
            v___x_6142_,
            v___y_6144_,
            v___y_6145_,
            v___y_6146_,
            v___y_6147_,
        );
        lean_dec_ref(v___x_6157_);
        return v___x_6158_;
    } else {
        lean_dec_ref(v_y_6143_);
        lean_dec_ref(v___x_6137_);
        return v___x_6155_;
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___boxed(
    mut v_x_6159_: *mut LeanObject,
    mut v_codomain_6160_: *mut LeanObject,
    mut v_alts_6161_: *mut LeanObject,
    mut v_a_6162_: *mut LeanObject,
    mut v_a_6163_: *mut LeanObject,
    mut v_a_6164_: *mut LeanObject,
    mut v_a_6165_: *mut LeanObject,
    mut v_a_6166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6167_: *mut LeanObject = core::ptr::null_mut();
    v_res_6167_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(
        v_x_6159_,
        v_codomain_6160_,
        v_alts_6161_,
        v_a_6162_,
        v_a_6163_,
        v_a_6164_,
        v_a_6165_,
    );
    lean_dec(v_a_6165_);
    lean_dec_ref(v_a_6164_);
    lean_dec(v_a_6163_);
    lean_dec_ref(v_a_6162_);
    return v_res_6167_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    v___x_6169_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1;
    v___x_6170_ = lean_unsigned_to_nat(21);
    v___x_6171_ = lean_unsigned_to_nat(414);
    v___x_6172_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0;
    v___x_6173_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0;
    v___x_6174_ = l_mkPanicMessageWithDecl(
        v___x_6173_,
        v___x_6172_,
        v___x_6171_,
        v___x_6170_,
        v___x_6169_,
    );
    return v___x_6174_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(
    mut v___x_6175_: *mut LeanObject,
    mut v_es_6176_: *mut LeanObject,
    mut v_xs_6177_: *mut LeanObject,
    mut v_codomain_6178_: *mut LeanObject,
    mut v___y_6179_: *mut LeanObject,
    mut v___y_6180_: *mut LeanObject,
    mut v___y_6181_: *mut LeanObject,
    mut v___y_6182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: u8 = 0;
    v___x_6184_ = lean_array_get_size(v_xs_6177_);
    v___x_6185_ = lean_nat_dec_eq(v___x_6184_, v___x_6175_);
    if v___x_6185_ == 0 {
        let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_codomain_6178_);
        lean_dec_ref(v_es_6176_);
        v___x_6186_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1_once
            ),
            _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1,
        );
        v___x_6187_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(
            v___x_6186_,
            v___y_6179_,
            v___y_6180_,
            v___y_6181_,
            v___y_6182_,
        );
        return v___x_6187_;
    } else {
        let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
        v___x_6188_ = lean_unsigned_to_nat(0);
        v___x_6189_ = lean_array_fget_borrowed(v_xs_6177_, v___x_6188_);
        v___x_6190_ = lean_array_to_list(v_es_6176_);
        lean_inc(v___x_6189_);
        v___x_6191_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(
            v___x_6189_,
            v_codomain_6178_,
            v___x_6190_,
            v___y_6179_,
            v___y_6180_,
            v___y_6181_,
            v___y_6182_,
        );
        if lean_obj_tag(v___x_6191_) == 0 {
            let mut v_a_6192_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6195_: u8 = 0;
            let mut v___x_6196_: u8 = 0;
            let mut v___x_6197_: *mut LeanObject = core::ptr::null_mut();
            v_a_6192_ = lean_ctor_get(v___x_6191_, 0);
            lean_inc(v_a_6192_);
            lean_dec_ref_known(v___x_6191_, 1);
            v___x_6193_ = lean_mk_empty_array_with_capacity(v___x_6175_);
            lean_inc(v___x_6189_);
            v___x_6194_ = lean_array_push(v___x_6193_, v___x_6189_);
            v___x_6195_ = 0;
            v___x_6196_ = 1;
            v___x_6197_ = l_Lean_Meta_mkLambdaFVars(
                v___x_6194_,
                v_a_6192_,
                v___x_6195_,
                v___x_6185_,
                v___x_6195_,
                v___x_6185_,
                v___x_6196_,
                v___y_6179_,
                v___y_6180_,
                v___y_6181_,
                v___y_6182_,
            );
            lean_dec_ref(v___x_6194_);
            return v___x_6197_;
        } else {
            return v___x_6191_;
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed(
    mut v___x_6198_: *mut LeanObject,
    mut v_es_6199_: *mut LeanObject,
    mut v_xs_6200_: *mut LeanObject,
    mut v_codomain_6201_: *mut LeanObject,
    mut v___y_6202_: *mut LeanObject,
    mut v___y_6203_: *mut LeanObject,
    mut v___y_6204_: *mut LeanObject,
    mut v___y_6205_: *mut LeanObject,
    mut v___y_6206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6207_: *mut LeanObject = core::ptr::null_mut();
    v_res_6207_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(
        v___x_6198_,
        v_es_6199_,
        v_xs_6200_,
        v_codomain_6201_,
        v___y_6202_,
        v___y_6203_,
        v___y_6204_,
        v___y_6205_,
    );
    lean_dec(v___y_6205_);
    lean_dec_ref(v___y_6204_);
    lean_dec(v___y_6203_);
    lean_dec_ref(v___y_6202_);
    lean_dec_ref(v_xs_6200_);
    lean_dec(v___x_6198_);
    return v_res_6207_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(
    mut v_resultType_6208_: *mut LeanObject,
    mut v_es_6209_: *mut LeanObject,
    mut v_a_6210_: *mut LeanObject,
    mut v_a_6211_: *mut LeanObject,
    mut v_a_6212_: *mut LeanObject,
    mut v_a_6213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: u8 = 0;
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    v___x_6215_ = lean_unsigned_to_nat(1);
    v___f_6216_ = lean_alloc_closure(
        l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    lean_closure_set(v___f_6216_, 0, v___x_6215_);
    lean_closure_set(v___f_6216_, 1, v_es_6209_);
    v___x_6217_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0;
    v___x_6218_ = 0;
    v___x_6219_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_resultType_6208_, v___x_6217_, v___f_6216_, v___x_6218_, v___x_6218_, v_a_6210_, v_a_6211_, v_a_6212_, v_a_6213_);
    return v___x_6219_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___boxed(
    mut v_resultType_6220_: *mut LeanObject,
    mut v_es_6221_: *mut LeanObject,
    mut v_a_6222_: *mut LeanObject,
    mut v_a_6223_: *mut LeanObject,
    mut v_a_6224_: *mut LeanObject,
    mut v_a_6225_: *mut LeanObject,
    mut v_a_6226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6227_: *mut LeanObject = core::ptr::null_mut();
    v_res_6227_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(
        v_resultType_6220_,
        v_es_6221_,
        v_a_6222_,
        v_a_6223_,
        v_a_6224_,
        v_a_6225_,
    );
    lean_dec(v_a_6225_);
    lean_dec_ref(v_a_6224_);
    lean_dec(v_a_6223_);
    lean_dec_ref(v_a_6222_);
    return v_res_6227_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(
    mut v_sz_6228_: usize,
    mut v_i_6229_: usize,
    mut v_bs_6230_: *mut LeanObject,
    mut v___y_6231_: *mut LeanObject,
    mut v___y_6232_: *mut LeanObject,
    mut v___y_6233_: *mut LeanObject,
    mut v___y_6234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6236_: u8 = 0;
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: usize = 0;
    let mut v___x_6244_: usize = 0;
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6250_: u8 = 0;
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6236_ = lean_usize_dec_lt(v_i_6229_, v_sz_6228_);
                if v___x_6236_ == 0 {
                    v___x_6237_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6237_, 0, v_bs_6230_);
                    return v___x_6237_;
                } else {
                    v_v_6238_ = lean_array_uget_borrowed(v_bs_6230_, v_i_6229_);
                    lean_inc(v___y_6234_);
                    lean_inc_ref(v___y_6233_);
                    lean_inc(v___y_6232_);
                    lean_inc_ref(v___y_6231_);
                    lean_inc(v_v_6238_);
                    v___x_6239_ = lean_infer_type(
                        v_v_6238_,
                        v___y_6231_,
                        v___y_6232_,
                        v___y_6233_,
                        v___y_6234_,
                    );
                    if lean_obj_tag(v___x_6239_) == 0 {
                        v_a_6240_ = lean_ctor_get(v___x_6239_, 0);
                        lean_inc(v_a_6240_);
                        lean_dec_ref_known(v___x_6239_, 1);
                        v___x_6241_ = lean_unsigned_to_nat(0);
                        v_bs_x27_6242_ = lean_array_uset(v_bs_6230_, v_i_6229_, v___x_6241_);
                        v___x_6243_ = 1usize;
                        v___x_6244_ = lean_usize_add(v_i_6229_, v___x_6243_);
                        v___x_6245_ = lean_array_uset(v_bs_x27_6242_, v_i_6229_, v_a_6240_);
                        v_i_6229_ = v___x_6244_;
                        v_bs_6230_ = v___x_6245_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_6230_);
                        v_a_6247_ = lean_ctor_get(v___x_6239_, 0);
                        v_isSharedCheck_6254_ = (!lean_is_exclusive(v___x_6239_)) as u8;
                        if v_isSharedCheck_6254_ == 0 {
                            v___x_6249_ = v___x_6239_;
                            v_isShared_6250_ = v_isSharedCheck_6254_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6247_);
                            lean_dec(v___x_6239_);
                            v___x_6249_ = lean_box(0);
                            v_isShared_6250_ = v_isSharedCheck_6254_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6250_ == 0 {
                    v___x_6252_ = v___x_6249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6253_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6253_, 0, v_a_6247_);
                    v___x_6252_ = v_reuseFailAlloc_6253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0___boxed(
    mut v_sz_6255_: *mut LeanObject,
    mut v_i_6256_: *mut LeanObject,
    mut v_bs_6257_: *mut LeanObject,
    mut v___y_6258_: *mut LeanObject,
    mut v___y_6259_: *mut LeanObject,
    mut v___y_6260_: *mut LeanObject,
    mut v___y_6261_: *mut LeanObject,
    mut v___y_6262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6263_: usize = 0;
    let mut v_i_boxed_6264_: usize = 0;
    let mut v_res_6265_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6263_ = lean_unbox_usize(v_sz_6255_);
    lean_dec(v_sz_6255_);
    v_i_boxed_6264_ = lean_unbox_usize(v_i_6256_);
    lean_dec(v_i_6256_);
    v_res_6265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_boxed_6263_, v_i_boxed_6264_, v_bs_6257_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_);
    lean_dec(v___y_6261_);
    lean_dec_ref(v___y_6260_);
    lean_dec(v___y_6259_);
    lean_dec_ref(v___y_6258_);
    return v_res_6265_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurry(
    mut v_es_6266_: *mut LeanObject,
    mut v_a_6267_: *mut LeanObject,
    mut v_a_6268_: *mut LeanObject,
    mut v_a_6269_: *mut LeanObject,
    mut v_a_6270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_6272_: usize = 0;
    let mut v___x_6273_: usize = 0;
    let mut v___x_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6282_: u8 = 0;
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_6272_ = lean_array_size(v_es_6266_);
                v___x_6273_ = 0usize;
                lean_inc_ref(v_es_6266_);
                v___x_6274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_6272_, v___x_6273_, v_es_6266_, v_a_6267_, v_a_6268_, v_a_6269_, v_a_6270_);
                if lean_obj_tag(v___x_6274_) == 0 {
                    v_a_6275_ = lean_ctor_get(v___x_6274_, 0);
                    lean_inc(v_a_6275_);
                    lean_dec_ref_known(v___x_6274_, 1);
                    v___x_6276_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(
                        v_a_6275_, v_a_6267_, v_a_6268_, v_a_6269_, v_a_6270_,
                    );
                    if lean_obj_tag(v___x_6276_) == 0 {
                        v_a_6277_ = lean_ctor_get(v___x_6276_, 0);
                        lean_inc(v_a_6277_);
                        lean_dec_ref_known(v___x_6276_, 1);
                        v___x_6278_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(
                            v_a_6277_, v_es_6266_, v_a_6267_, v_a_6268_, v_a_6269_, v_a_6270_,
                        );
                        return v___x_6278_;
                    } else {
                        lean_dec_ref(v_es_6266_);
                        return v___x_6276_;
                    }
                } else {
                    lean_dec_ref(v_es_6266_);
                    v_a_6279_ = lean_ctor_get(v___x_6274_, 0);
                    v_isSharedCheck_6286_ = (!lean_is_exclusive(v___x_6274_)) as u8;
                    if v_isSharedCheck_6286_ == 0 {
                        v___x_6281_ = v___x_6274_;
                        v_isShared_6282_ = v_isSharedCheck_6286_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6279_);
                        lean_dec(v___x_6274_);
                        v___x_6281_ = lean_box(0);
                        v_isShared_6282_ = v_isSharedCheck_6286_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6282_ == 0 {
                    v___x_6284_ = v___x_6281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6285_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6285_, 0, v_a_6279_);
                    v___x_6284_ = v_reuseFailAlloc_6285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurry___boxed(
    mut v_es_6287_: *mut LeanObject,
    mut v_a_6288_: *mut LeanObject,
    mut v_a_6289_: *mut LeanObject,
    mut v_a_6290_: *mut LeanObject,
    mut v_a_6291_: *mut LeanObject,
    mut v_a_6292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6293_: *mut LeanObject = core::ptr::null_mut();
    v_res_6293_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(
        v_es_6287_, v_a_6288_, v_a_6289_, v_a_6290_, v_a_6291_,
    );
    lean_dec(v_a_6291_);
    lean_dec_ref(v_a_6290_);
    lean_dec(v_a_6289_);
    lean_dec_ref(v_a_6288_);
    return v_res_6293_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1() -> *mut LeanObject
{
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    v___x_6295_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1;
    v___x_6296_ = lean_unsigned_to_nat(21);
    v___x_6297_ = lean_unsigned_to_nat(434);
    v___x_6298_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0;
    v___x_6299_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0;
    v___x_6300_ = l_mkPanicMessageWithDecl(
        v___x_6299_,
        v___x_6298_,
        v___x_6297_,
        v___x_6296_,
        v___x_6295_,
    );
    return v___x_6300_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(
    mut v___x_6301_: *mut LeanObject,
    mut v_es_6302_: *mut LeanObject,
    mut v_xs_6303_: *mut LeanObject,
    mut v_codomain_6304_: *mut LeanObject,
    mut v___y_6305_: *mut LeanObject,
    mut v___y_6306_: *mut LeanObject,
    mut v___y_6307_: *mut LeanObject,
    mut v___y_6308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: u8 = 0;
    v___x_6310_ = lean_array_get_size(v_xs_6303_);
    v___x_6311_ = lean_nat_dec_eq(v___x_6310_, v___x_6301_);
    if v___x_6311_ == 0 {
        let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_codomain_6304_);
        lean_dec_ref(v_es_6302_);
        v___x_6312_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1_once
            ),
            _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1,
        );
        v___x_6313_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(
            v___x_6312_,
            v___y_6305_,
            v___y_6306_,
            v___y_6307_,
            v___y_6308_,
        );
        return v___x_6313_;
    } else {
        let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
        v___x_6314_ = lean_unsigned_to_nat(0);
        v___x_6315_ = lean_array_fget_borrowed(v_xs_6303_, v___x_6314_);
        v___x_6316_ = lean_array_to_list(v_es_6302_);
        lean_inc(v___x_6315_);
        v___x_6317_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(
            v___x_6315_,
            v_codomain_6304_,
            v___x_6316_,
            v___y_6305_,
            v___y_6306_,
            v___y_6307_,
            v___y_6308_,
        );
        if lean_obj_tag(v___x_6317_) == 0 {
            let mut v_a_6318_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6321_: u8 = 0;
            let mut v___x_6322_: u8 = 0;
            let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
            v_a_6318_ = lean_ctor_get(v___x_6317_, 0);
            lean_inc(v_a_6318_);
            lean_dec_ref_known(v___x_6317_, 1);
            v___x_6319_ = lean_mk_empty_array_with_capacity(v___x_6301_);
            lean_inc(v___x_6315_);
            v___x_6320_ = lean_array_push(v___x_6319_, v___x_6315_);
            v___x_6321_ = 0;
            v___x_6322_ = 1;
            v___x_6323_ = l_Lean_Meta_mkLambdaFVars(
                v___x_6320_,
                v_a_6318_,
                v___x_6321_,
                v___x_6311_,
                v___x_6321_,
                v___x_6311_,
                v___x_6322_,
                v___y_6305_,
                v___y_6306_,
                v___y_6307_,
                v___y_6308_,
            );
            lean_dec_ref(v___x_6320_);
            return v___x_6323_;
        } else {
            return v___x_6317_;
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed(
    mut v___x_6324_: *mut LeanObject,
    mut v_es_6325_: *mut LeanObject,
    mut v_xs_6326_: *mut LeanObject,
    mut v_codomain_6327_: *mut LeanObject,
    mut v___y_6328_: *mut LeanObject,
    mut v___y_6329_: *mut LeanObject,
    mut v___y_6330_: *mut LeanObject,
    mut v___y_6331_: *mut LeanObject,
    mut v___y_6332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6333_: *mut LeanObject = core::ptr::null_mut();
    v_res_6333_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(
        v___x_6324_,
        v_es_6325_,
        v_xs_6326_,
        v_codomain_6327_,
        v___y_6328_,
        v___y_6329_,
        v___y_6330_,
        v___y_6331_,
    );
    lean_dec(v___y_6331_);
    lean_dec_ref(v___y_6330_);
    lean_dec(v___y_6329_);
    lean_dec_ref(v___y_6328_);
    lean_dec_ref(v_xs_6326_);
    lean_dec(v___x_6324_);
    return v_res_6333_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryND(
    mut v_es_6334_: *mut LeanObject,
    mut v_a_6335_: *mut LeanObject,
    mut v_a_6336_: *mut LeanObject,
    mut v_a_6337_: *mut LeanObject,
    mut v_a_6338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_6340_: usize = 0;
    let mut v___x_6341_: usize = 0;
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: u8 = 0;
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6354_: u8 = 0;
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_6340_ = lean_array_size(v_es_6334_);
                v___x_6341_ = 0usize;
                lean_inc_ref(v_es_6334_);
                v___x_6342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_6340_, v___x_6341_, v_es_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_);
                if lean_obj_tag(v___x_6342_) == 0 {
                    v_a_6343_ = lean_ctor_get(v___x_6342_, 0);
                    lean_inc(v_a_6343_);
                    lean_dec_ref_known(v___x_6342_, 1);
                    v___x_6344_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(
                        v_a_6343_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_,
                    );
                    if lean_obj_tag(v___x_6344_) == 0 {
                        v_a_6345_ = lean_ctor_get(v___x_6344_, 0);
                        lean_inc(v_a_6345_);
                        lean_dec_ref_known(v___x_6344_, 1);
                        v___x_6346_ = lean_unsigned_to_nat(1);
                        v___f_6347_ = lean_alloc_closure(
                            l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed
                                as *mut core::ffi::c_void,
                            9,
                            2,
                        );
                        lean_closure_set(v___f_6347_, 0, v___x_6346_);
                        lean_closure_set(v___f_6347_, 1, v_es_6334_);
                        v___x_6348_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0;
                        v___x_6349_ = 0;
                        v___x_6350_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_6345_, v___x_6348_, v___f_6347_, v___x_6349_, v___x_6349_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_);
                        return v___x_6350_;
                    } else {
                        lean_dec_ref(v_es_6334_);
                        return v___x_6344_;
                    }
                } else {
                    lean_dec_ref(v_es_6334_);
                    v_a_6351_ = lean_ctor_get(v___x_6342_, 0);
                    v_isSharedCheck_6358_ = (!lean_is_exclusive(v___x_6342_)) as u8;
                    if v_isSharedCheck_6358_ == 0 {
                        v___x_6353_ = v___x_6342_;
                        v_isShared_6354_ = v_isSharedCheck_6358_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6351_);
                        lean_dec(v___x_6342_);
                        v___x_6353_ = lean_box(0);
                        v_isShared_6354_ = v_isSharedCheck_6358_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6354_ == 0 {
                    v___x_6356_ = v___x_6353_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6357_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6357_, 0, v_a_6351_);
                    v___x_6356_ = v_reuseFailAlloc_6357_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_uncurryND___boxed(
    mut v_es_6359_: *mut LeanObject,
    mut v_a_6360_: *mut LeanObject,
    mut v_a_6361_: *mut LeanObject,
    mut v_a_6362_: *mut LeanObject,
    mut v_a_6363_: *mut LeanObject,
    mut v_a_6364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6365_: *mut LeanObject = core::ptr::null_mut();
    v_res_6365_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(
        v_es_6359_, v_a_6360_, v_a_6361_, v_a_6362_, v_a_6363_,
    );
    lean_dec(v_a_6363_);
    lean_dec_ref(v_a_6362_);
    lean_dec(v_a_6361_);
    lean_dec_ref(v_a_6360_);
    return v_res_6365_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(
    mut v_a_6366_: *mut LeanObject,
    mut v_domain_6367_: *mut LeanObject,
    mut v_j_6368_: *mut LeanObject,
    mut v_type_6369_: *mut LeanObject,
    mut v_isZero_6370_: u8,
    mut v_x_6371_: *mut LeanObject,
    mut v___y_6372_: *mut LeanObject,
    mut v___y_6373_: *mut LeanObject,
    mut v___y_6374_: *mut LeanObject,
    mut v___y_6375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    v___x_6377_ = l_List_lengthTR___redArg(v_a_6366_);
    lean_inc_ref(v_x_6371_);
    v___x_6378_ = l_Lean_Meta_ArgsPacker_Mutual_pack(
        v___x_6377_,
        v_domain_6367_,
        v_j_6368_,
        v_x_6371_,
        v___y_6372_,
        v___y_6373_,
        v___y_6374_,
        v___y_6375_,
    );
    lean_dec(v___x_6377_);
    if lean_obj_tag(v___x_6378_) == 0 {
        let mut v_a_6379_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
        v_a_6379_ = lean_ctor_get(v___x_6378_, 0);
        lean_inc(v_a_6379_);
        lean_dec_ref_known(v___x_6378_, 1);
        v___x_6380_ = lean_unsigned_to_nat(1);
        v___x_6381_ = lean_mk_empty_array_with_capacity(v___x_6380_);
        lean_inc_ref(v___x_6381_);
        v___x_6382_ = lean_array_push(v___x_6381_, v_a_6379_);
        v___x_6383_ = l_Lean_Meta_instantiateForall(
            v_type_6369_,
            v___x_6382_,
            v___y_6372_,
            v___y_6373_,
            v___y_6374_,
            v___y_6375_,
        );
        lean_dec_ref(v___x_6382_);
        if lean_obj_tag(v___x_6383_) == 0 {
            let mut v_a_6384_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6386_: u8 = 0;
            let mut v___x_6387_: u8 = 0;
            let mut v___x_6388_: *mut LeanObject = core::ptr::null_mut();
            v_a_6384_ = lean_ctor_get(v___x_6383_, 0);
            lean_inc(v_a_6384_);
            lean_dec_ref_known(v___x_6383_, 1);
            v___x_6385_ = lean_array_push(v___x_6381_, v_x_6371_);
            v___x_6386_ = 1;
            v___x_6387_ = 1;
            v___x_6388_ = l_Lean_Meta_mkForallFVars(
                v___x_6385_,
                v_a_6384_,
                v_isZero_6370_,
                v___x_6386_,
                v___x_6386_,
                v___x_6387_,
                v___y_6372_,
                v___y_6373_,
                v___y_6374_,
                v___y_6375_,
            );
            lean_dec_ref(v___x_6385_);
            return v___x_6388_;
        } else {
            lean_dec_ref(v___x_6381_);
            lean_dec_ref(v_x_6371_);
            return v___x_6383_;
        }
    } else {
        lean_dec_ref(v_x_6371_);
        lean_dec_ref(v_type_6369_);
        return v___x_6378_;
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed(
    mut v_a_6389_: *mut LeanObject,
    mut v_domain_6390_: *mut LeanObject,
    mut v_j_6391_: *mut LeanObject,
    mut v_type_6392_: *mut LeanObject,
    mut v_isZero_6393_: *mut LeanObject,
    mut v_x_6394_: *mut LeanObject,
    mut v___y_6395_: *mut LeanObject,
    mut v___y_6396_: *mut LeanObject,
    mut v___y_6397_: *mut LeanObject,
    mut v___y_6398_: *mut LeanObject,
    mut v___y_6399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isZero_boxed_6400_: u8 = 0;
    let mut v_res_6401_: *mut LeanObject = core::ptr::null_mut();
    v_isZero_boxed_6400_ = (lean_unbox(v_isZero_6393_) as u8);
    v_res_6401_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(v_a_6389_, v_domain_6390_, v_j_6391_, v_type_6392_, v_isZero_boxed_6400_, v_x_6394_, v___y_6395_, v___y_6396_, v___y_6397_, v___y_6398_);
    lean_dec(v___y_6398_);
    lean_dec_ref(v___y_6397_);
    lean_dec(v___y_6396_);
    lean_dec_ref(v___y_6395_);
    lean_dec(v_j_6391_);
    lean_dec(v_a_6389_);
    return v_res_6401_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(
    mut v_a_6402_: *mut LeanObject,
    mut v_domain_6403_: *mut LeanObject,
    mut v_type_6404_: *mut LeanObject,
    mut v_as_6405_: *mut LeanObject,
    mut v_i_6406_: *mut LeanObject,
    mut v_j_6407_: *mut LeanObject,
    mut v_bs_6408_: *mut LeanObject,
    mut v___y_6409_: *mut LeanObject,
    mut v___y_6410_: *mut LeanObject,
    mut v___y_6411_: *mut LeanObject,
    mut v___y_6412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6415_: u8 = 0;
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6431_: u8 = 0;
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6414_ = lean_unsigned_to_nat(0);
                v_isZero_6415_ = lean_nat_dec_eq(v_i_6406_, v_zero_6414_);
                if v_isZero_6415_ == 1 {
                    lean_dec(v_j_6407_);
                    lean_dec(v_i_6406_);
                    lean_dec_ref(v_type_6404_);
                    lean_dec_ref(v_domain_6403_);
                    lean_dec(v_a_6402_);
                    v___x_6416_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6416_, 0, v_bs_6408_);
                    return v___x_6416_;
                } else {
                    v___x_6417_ = lean_box((v_isZero_6415_) as usize);
                    lean_inc_ref(v_type_6404_);
                    lean_inc(v_j_6407_);
                    lean_inc_ref(v_domain_6403_);
                    lean_inc(v_a_6402_);
                    v___f_6418_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                    lean_closure_set(v___f_6418_, 0, v_a_6402_);
                    lean_closure_set(v___f_6418_, 1, v_domain_6403_);
                    lean_closure_set(v___f_6418_, 2, v_j_6407_);
                    lean_closure_set(v___f_6418_, 3, v_type_6404_);
                    lean_closure_set(v___f_6418_, 4, v___x_6417_);
                    v___x_6419_ = lean_array_fget_borrowed(v_as_6405_, v_j_6407_);
                    v___x_6420_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2;
                    lean_inc(v___x_6419_);
                    v___x_6421_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_6420_, v___x_6419_, v___f_6418_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_);
                    if lean_obj_tag(v___x_6421_) == 0 {
                        v_a_6422_ = lean_ctor_get(v___x_6421_, 0);
                        lean_inc(v_a_6422_);
                        lean_dec_ref_known(v___x_6421_, 1);
                        v_one_6423_ = lean_unsigned_to_nat(1);
                        v_n_6424_ = lean_nat_sub(v_i_6406_, v_one_6423_);
                        lean_dec(v_i_6406_);
                        v___x_6425_ = lean_nat_add(v_j_6407_, v_one_6423_);
                        lean_dec(v_j_6407_);
                        v___x_6426_ = lean_array_push(v_bs_6408_, v_a_6422_);
                        v_i_6406_ = v_n_6424_;
                        v_j_6407_ = v___x_6425_;
                        v_bs_6408_ = v___x_6426_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_6408_);
                        lean_dec(v_j_6407_);
                        lean_dec(v_i_6406_);
                        lean_dec_ref(v_type_6404_);
                        lean_dec_ref(v_domain_6403_);
                        lean_dec(v_a_6402_);
                        v_a_6428_ = lean_ctor_get(v___x_6421_, 0);
                        v_isSharedCheck_6435_ = (!lean_is_exclusive(v___x_6421_)) as u8;
                        if v_isSharedCheck_6435_ == 0 {
                            v___x_6430_ = v___x_6421_;
                            v_isShared_6431_ = v_isSharedCheck_6435_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6428_);
                            lean_dec(v___x_6421_);
                            v___x_6430_ = lean_box(0);
                            v_isShared_6431_ = v_isSharedCheck_6435_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6431_ == 0 {
                    v___x_6433_ = v___x_6430_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6434_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6434_, 0, v_a_6428_);
                    v___x_6433_ = v_reuseFailAlloc_6434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___boxed(
    mut v_a_6436_: *mut LeanObject,
    mut v_domain_6437_: *mut LeanObject,
    mut v_type_6438_: *mut LeanObject,
    mut v_as_6439_: *mut LeanObject,
    mut v_i_6440_: *mut LeanObject,
    mut v_j_6441_: *mut LeanObject,
    mut v_bs_6442_: *mut LeanObject,
    mut v___y_6443_: *mut LeanObject,
    mut v___y_6444_: *mut LeanObject,
    mut v___y_6445_: *mut LeanObject,
    mut v___y_6446_: *mut LeanObject,
    mut v___y_6447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6448_: *mut LeanObject = core::ptr::null_mut();
    v_res_6448_ =
        l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(
            v_a_6436_,
            v_domain_6437_,
            v_type_6438_,
            v_as_6439_,
            v_i_6440_,
            v_j_6441_,
            v_bs_6442_,
            v___y_6443_,
            v___y_6444_,
            v___y_6445_,
            v___y_6446_,
        );
    lean_dec(v___y_6446_);
    lean_dec_ref(v___y_6445_);
    lean_dec(v___y_6444_);
    lean_dec_ref(v___y_6443_);
    lean_dec_ref(v_as_6439_);
    return v_res_6448_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_curryType(
    mut v_n_6449_: *mut LeanObject,
    mut v_type_6450_: *mut LeanObject,
    mut v_a_6451_: *mut LeanObject,
    mut v_a_6452_: *mut LeanObject,
    mut v_a_6453_: *mut LeanObject,
    mut v_a_6454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_domain_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6472_: u8 = 0;
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6476_: u8 = 0;
    let mut v___x_6477_: u8 = 0;
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v___x_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6477_ = l_Lean_Expr_isForall(v_type_6450_);
                if v___x_6477_ == 0 {
                    v___x_6478_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once), _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
                    v___x_6479_ = l_Lean_MessageData_ofExpr(v_type_6450_);
                    v___x_6480_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6480_, 0, v___x_6478_);
                    lean_ctor_set(v___x_6480_, 1, v___x_6479_);
                    v___x_6481_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_6480_, v_a_6451_, v_a_6452_, v_a_6453_, v_a_6454_);
                    v_a_6482_ = lean_ctor_get(v___x_6481_, 0);
                    v_isSharedCheck_6489_ = (!lean_is_exclusive(v___x_6481_)) as u8;
                    if v_isSharedCheck_6489_ == 0 {
                        v___x_6484_ = v___x_6481_;
                        v_isShared_6485_ = v_isSharedCheck_6489_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6482_);
                        lean_dec(v___x_6481_);
                        v___x_6484_ = lean_box(0);
                        v_isShared_6485_ = v_isSharedCheck_6489_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___y_6457_ = v_a_6451_;
                    v___y_6458_ = v_a_6452_;
                    v___y_6459_ = v_a_6453_;
                    v___y_6460_ = v_a_6454_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_domain_6461_ = l_Lean_Expr_bindingDomain_x21(v_type_6450_);
                lean_inc_ref(v_domain_6461_);
                v___x_6462_ =
                    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(
                        v_n_6449_,
                        v_domain_6461_,
                        v___y_6457_,
                        v___y_6458_,
                        v___y_6459_,
                        v___y_6460_,
                    );
                if lean_obj_tag(v___x_6462_) == 0 {
                    v_a_6463_ = lean_ctor_get(v___x_6462_, 0);
                    lean_inc_n(v_a_6463_, 2);
                    lean_dec_ref_known(v___x_6462_, 1);
                    v___x_6464_ = lean_array_mk(v_a_6463_);
                    v___x_6465_ = lean_array_get_size(v___x_6464_);
                    v___x_6466_ = lean_unsigned_to_nat(0);
                    v___x_6467_ = lean_mk_empty_array_with_capacity(v___x_6465_);
                    v___x_6468_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_6463_, v_domain_6461_, v_type_6450_, v___x_6464_, v___x_6465_, v___x_6466_, v___x_6467_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_);
                    lean_dec_ref(v___x_6464_);
                    return v___x_6468_;
                } else {
                    lean_dec_ref(v_domain_6461_);
                    lean_dec_ref(v_type_6450_);
                    v_a_6469_ = lean_ctor_get(v___x_6462_, 0);
                    v_isSharedCheck_6476_ = (!lean_is_exclusive(v___x_6462_)) as u8;
                    if v_isSharedCheck_6476_ == 0 {
                        v___x_6471_ = v___x_6462_;
                        v_isShared_6472_ = v_isSharedCheck_6476_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6469_);
                        lean_dec(v___x_6462_);
                        v___x_6471_ = lean_box(0);
                        v_isShared_6472_ = v_isSharedCheck_6476_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6472_ == 0 {
                    v___x_6474_ = v___x_6471_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6475_, 0, v_a_6469_);
                    v___x_6474_ = v_reuseFailAlloc_6475_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6474_;
            }
            4 => {
                if v_isShared_6485_ == 0 {
                    v___x_6487_ = v___x_6484_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6488_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6488_, 0, v_a_6482_);
                    v___x_6487_ = v_reuseFailAlloc_6488_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_Mutual_curryType___boxed(
    mut v_n_6490_: *mut LeanObject,
    mut v_type_6491_: *mut LeanObject,
    mut v_a_6492_: *mut LeanObject,
    mut v_a_6493_: *mut LeanObject,
    mut v_a_6494_: *mut LeanObject,
    mut v_a_6495_: *mut LeanObject,
    mut v_a_6496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6497_: *mut LeanObject = core::ptr::null_mut();
    v_res_6497_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(
        v_n_6490_,
        v_type_6491_,
        v_a_6492_,
        v_a_6493_,
        v_a_6494_,
        v_a_6495_,
    );
    lean_dec(v_a_6495_);
    lean_dec_ref(v_a_6494_);
    lean_dec(v_a_6493_);
    lean_dec_ref(v_a_6492_);
    lean_dec(v_n_6490_);
    return v_res_6497_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(
    mut v_a_6498_: *mut LeanObject,
    mut v_domain_6499_: *mut LeanObject,
    mut v_type_6500_: *mut LeanObject,
    mut v_as_6501_: *mut LeanObject,
    mut v_i_6502_: *mut LeanObject,
    mut v_j_6503_: *mut LeanObject,
    mut v_inv_6504_: *mut LeanObject,
    mut v_bs_6505_: *mut LeanObject,
    mut v___y_6506_: *mut LeanObject,
    mut v___y_6507_: *mut LeanObject,
    mut v___y_6508_: *mut LeanObject,
    mut v___y_6509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    v___x_6511_ =
        l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(
            v_a_6498_,
            v_domain_6499_,
            v_type_6500_,
            v_as_6501_,
            v_i_6502_,
            v_j_6503_,
            v_bs_6505_,
            v___y_6506_,
            v___y_6507_,
            v___y_6508_,
            v___y_6509_,
        );
    return v___x_6511_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___boxed(
    mut v_a_6512_: *mut LeanObject,
    mut v_domain_6513_: *mut LeanObject,
    mut v_type_6514_: *mut LeanObject,
    mut v_as_6515_: *mut LeanObject,
    mut v_i_6516_: *mut LeanObject,
    mut v_j_6517_: *mut LeanObject,
    mut v_inv_6518_: *mut LeanObject,
    mut v_bs_6519_: *mut LeanObject,
    mut v___y_6520_: *mut LeanObject,
    mut v___y_6521_: *mut LeanObject,
    mut v___y_6522_: *mut LeanObject,
    mut v___y_6523_: *mut LeanObject,
    mut v___y_6524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6525_: *mut LeanObject = core::ptr::null_mut();
    v_res_6525_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(
        v_a_6512_,
        v_domain_6513_,
        v_type_6514_,
        v_as_6515_,
        v_i_6516_,
        v_j_6517_,
        v_inv_6518_,
        v_bs_6519_,
        v___y_6520_,
        v___y_6521_,
        v___y_6522_,
        v___y_6523_,
    );
    lean_dec(v___y_6523_);
    lean_dec_ref(v___y_6522_);
    lean_dec(v___y_6521_);
    lean_dec_ref(v___y_6520_);
    lean_dec_ref(v_as_6515_);
    return v_res_6525_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_numFuncs(
    mut v_argsPacker_6526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
    v___x_6527_ = lean_array_get_size(v_argsPacker_6526_);
    return v___x_6527_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_numFuncs___boxed(
    mut v_argsPacker_6528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6529_: *mut LeanObject = core::ptr::null_mut();
    v_res_6529_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_6528_);
    lean_dec_ref(v_argsPacker_6528_);
    return v_res_6529_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(
    mut v_sz_6530_: usize,
    mut v_i_6531_: usize,
    mut v_bs_6532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6533_: u8 = 0;
    let mut v_v_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: usize = 0;
    let mut v___x_6539_: usize = 0;
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6533_ = lean_usize_dec_lt(v_i_6531_, v_sz_6530_);
                if v___x_6533_ == 0 {
                    return v_bs_6532_;
                } else {
                    v_v_6534_ = lean_array_uget(v_bs_6532_, v_i_6531_);
                    v___x_6535_ = lean_unsigned_to_nat(0);
                    v_bs_x27_6536_ = lean_array_uset(v_bs_6532_, v_i_6531_, v___x_6535_);
                    v___x_6537_ = lean_array_get_size(v_v_6534_);
                    lean_dec(v_v_6534_);
                    v___x_6538_ = 1usize;
                    v___x_6539_ = lean_usize_add(v_i_6531_, v___x_6538_);
                    v___x_6540_ = lean_array_uset(v_bs_x27_6536_, v_i_6531_, v___x_6537_);
                    v_i_6531_ = v___x_6539_;
                    v_bs_6532_ = v___x_6540_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0___boxed(
    mut v_sz_6542_: *mut LeanObject,
    mut v_i_6543_: *mut LeanObject,
    mut v_bs_6544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6545_: usize = 0;
    let mut v_i_boxed_6546_: usize = 0;
    let mut v_res_6547_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6545_ = lean_unbox_usize(v_sz_6542_);
    lean_dec(v_sz_6542_);
    v_i_boxed_6546_ = lean_unbox_usize(v_i_6543_);
    lean_dec(v_i_6543_);
    v_res_6547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_boxed_6545_, v_i_boxed_6546_, v_bs_6544_);
    return v_res_6547_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_arities(
    mut v_argsPacker_6548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_6549_: usize = 0;
    let mut v___x_6550_: usize = 0;
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    v_sz_6549_ = lean_array_size(v_argsPacker_6548_);
    v___x_6550_ = 0usize;
    v___x_6551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_6549_, v___x_6550_, v_argsPacker_6548_);
    return v___x_6551_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0() -> *mut LeanObject {
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    v___x_6552_ = l_Array_instInhabited(lean_box(0));
    return v___x_6552_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_onlyOneUnary(mut v_argsPacker_6553_: *mut LeanObject) -> u8 {
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: u8 = 0;
    v___x_6554_ = lean_array_get_size(v_argsPacker_6553_);
    v___x_6555_ = lean_unsigned_to_nat(1);
    v___x_6556_ = lean_nat_dec_eq(v___x_6554_, v___x_6555_);
    if v___x_6556_ == 0 {
        return v___x_6556_;
    } else {
        let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6561_: u8 = 0;
        v___x_6557_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once),
            _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0,
        );
        v___x_6558_ = lean_unsigned_to_nat(0);
        v___x_6559_ = lean_array_get_borrowed(v___x_6557_, v_argsPacker_6553_, v___x_6558_);
        v___x_6560_ = lean_array_get_size(v___x_6559_);
        v___x_6561_ = lean_nat_dec_eq(v___x_6560_, v___x_6555_);
        return v___x_6561_;
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_onlyOneUnary___boxed(
    mut v_argsPacker_6562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6563_: u8 = 0;
    let mut v_r_6564_: *mut LeanObject = core::ptr::null_mut();
    v_res_6563_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_6562_);
    lean_dec_ref(v_argsPacker_6562_);
    v_r_6564_ = lean_box((v_res_6563_) as usize);
    return v_r_6564_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_pack___closed__2() -> *mut LeanObject {
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    v___x_6567_ = l_Lean_Meta_ArgsPacker_pack___closed__1;
    v___x_6568_ = lean_unsigned_to_nat(2);
    v___x_6569_ = lean_unsigned_to_nat(469);
    v___x_6570_ = l_Lean_Meta_ArgsPacker_pack___closed__0;
    v___x_6571_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0;
    v___x_6572_ = l_mkPanicMessageWithDecl(
        v___x_6571_,
        v___x_6570_,
        v___x_6569_,
        v___x_6568_,
        v___x_6567_,
    );
    return v___x_6572_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_pack___closed__4() -> *mut LeanObject {
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    v___x_6574_ = l_Lean_Meta_ArgsPacker_pack___closed__3;
    v___x_6575_ = lean_unsigned_to_nat(2);
    v___x_6576_ = lean_unsigned_to_nat(470);
    v___x_6577_ = l_Lean_Meta_ArgsPacker_pack___closed__0;
    v___x_6578_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0;
    v___x_6579_ = l_mkPanicMessageWithDecl(
        v___x_6578_,
        v___x_6577_,
        v___x_6576_,
        v___x_6575_,
        v___x_6574_,
    );
    return v___x_6579_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_pack(
    mut v_argsPacker_6580_: *mut LeanObject,
    mut v_domain_6581_: *mut LeanObject,
    mut v_fidx_6582_: *mut LeanObject,
    mut v_args_6583_: *mut LeanObject,
    mut v_a_6584_: *mut LeanObject,
    mut v_a_6585_: *mut LeanObject,
    mut v_a_6586_: *mut LeanObject,
    mut v_a_6587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: u8 = 0;
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: u8 = 0;
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6609_: u8 = 0;
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6589_ = lean_array_get_size(v_argsPacker_6580_);
                v___x_6590_ = lean_nat_dec_lt(v_fidx_6582_, v___x_6589_);
                if v___x_6590_ == 0 {
                    lean_dec(v_fidx_6582_);
                    lean_dec_ref(v_domain_6581_);
                    v___x_6591_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_pack___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_pack___closed__2_once),
                        _init_l_Lean_Meta_ArgsPacker_pack___closed__2,
                    );
                    v___x_6592_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(
                        v___x_6591_,
                        v_a_6584_,
                        v_a_6585_,
                        v_a_6586_,
                        v_a_6587_,
                    );
                    return v___x_6592_;
                } else {
                    v___x_6593_ = lean_array_get_size(v_args_6583_);
                    v___x_6594_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once
                        ),
                        _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0,
                    );
                    v___x_6595_ =
                        lean_array_get_borrowed(v___x_6594_, v_argsPacker_6580_, v_fidx_6582_);
                    v___x_6596_ = lean_array_get_size(v___x_6595_);
                    v___x_6597_ = lean_nat_dec_eq(v___x_6593_, v___x_6596_);
                    if v___x_6597_ == 0 {
                        lean_dec(v_fidx_6582_);
                        lean_dec_ref(v_domain_6581_);
                        v___x_6598_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_pack___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_pack___closed__4_once),
                            _init_l_Lean_Meta_ArgsPacker_pack___closed__4,
                        );
                        v___x_6599_ =
                            l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(
                                v___x_6598_,
                                v_a_6584_,
                                v_a_6585_,
                                v_a_6586_,
                                v_a_6587_,
                            );
                        return v___x_6599_;
                    } else {
                        lean_inc_ref(v_domain_6581_);
                        v___x_6600_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v___x_6589_, v_domain_6581_, v_a_6584_, v_a_6585_, v_a_6586_, v_a_6587_);
                        if lean_obj_tag(v___x_6600_) == 0 {
                            v_a_6601_ = lean_ctor_get(v___x_6600_, 0);
                            lean_inc(v_a_6601_);
                            lean_dec_ref_known(v___x_6600_, 1);
                            v___x_6602_ = l_Lean_instInhabitedExpr;
                            lean_inc(v_fidx_6582_);
                            v___x_6603_ = l_List_get_x21Internal___redArg(
                                v___x_6602_,
                                v_a_6601_,
                                v_fidx_6582_,
                            );
                            lean_dec(v_a_6601_);
                            v___x_6604_ =
                                l_Lean_Meta_ArgsPacker_Unary_pack(v___x_6603_, v_args_6583_);
                            lean_dec(v___x_6603_);
                            v___x_6605_ = l_Lean_Meta_ArgsPacker_Mutual_pack(
                                v___x_6589_,
                                v_domain_6581_,
                                v_fidx_6582_,
                                v___x_6604_,
                                v_a_6584_,
                                v_a_6585_,
                                v_a_6586_,
                                v_a_6587_,
                            );
                            lean_dec(v_fidx_6582_);
                            return v___x_6605_;
                        } else {
                            lean_dec(v_fidx_6582_);
                            lean_dec_ref(v_domain_6581_);
                            v_a_6606_ = lean_ctor_get(v___x_6600_, 0);
                            v_isSharedCheck_6613_ = (!lean_is_exclusive(v___x_6600_)) as u8;
                            if v_isSharedCheck_6613_ == 0 {
                                v___x_6608_ = v___x_6600_;
                                v_isShared_6609_ = v_isSharedCheck_6613_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_6606_);
                                lean_dec(v___x_6600_);
                                v___x_6608_ = lean_box(0);
                                v_isShared_6609_ = v_isSharedCheck_6613_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6609_ == 0 {
                    v___x_6611_ = v___x_6608_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6612_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6612_, 0, v_a_6606_);
                    v___x_6611_ = v_reuseFailAlloc_6612_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_pack___boxed(
    mut v_argsPacker_6614_: *mut LeanObject,
    mut v_domain_6615_: *mut LeanObject,
    mut v_fidx_6616_: *mut LeanObject,
    mut v_args_6617_: *mut LeanObject,
    mut v_a_6618_: *mut LeanObject,
    mut v_a_6619_: *mut LeanObject,
    mut v_a_6620_: *mut LeanObject,
    mut v_a_6621_: *mut LeanObject,
    mut v_a_6622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6623_: *mut LeanObject = core::ptr::null_mut();
    v_res_6623_ = l_Lean_Meta_ArgsPacker_pack(
        v_argsPacker_6614_,
        v_domain_6615_,
        v_fidx_6616_,
        v_args_6617_,
        v_a_6618_,
        v_a_6619_,
        v_a_6620_,
        v_a_6621_,
    );
    lean_dec(v_a_6621_);
    lean_dec_ref(v_a_6620_);
    lean_dec(v_a_6619_);
    lean_dec_ref(v_a_6618_);
    lean_dec_ref(v_args_6617_);
    lean_dec_ref(v_argsPacker_6614_);
    return v_res_6623_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_unpack(
    mut v_argsPacker_6624_: *mut LeanObject,
    mut v_e_6625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6634_: u8 = 0;
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6643_: u8 = 0;
    let mut v___x_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6650_: u8 = 0;
    let mut v_isSharedCheck_6651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6626_ = lean_array_get_size(v_argsPacker_6624_);
                v___x_6627_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v___x_6626_, v_e_6625_);
                if lean_obj_tag(v___x_6627_) == 0 {
                    v___x_6628_ = lean_box(0);
                    return v___x_6628_;
                } else {
                    v_val_6629_ = lean_ctor_get(v___x_6627_, 0);
                    lean_inc(v_val_6629_);
                    lean_dec_ref_known(v___x_6627_, 1);
                    v_fst_6630_ = lean_ctor_get(v_val_6629_, 0);
                    v_snd_6631_ = lean_ctor_get(v_val_6629_, 1);
                    v_isSharedCheck_6651_ = (!lean_is_exclusive(v_val_6629_)) as u8;
                    if v_isSharedCheck_6651_ == 0 {
                        v___x_6633_ = v_val_6629_;
                        v_isShared_6634_ = v_isSharedCheck_6651_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6631_);
                        lean_inc(v_fst_6630_);
                        lean_dec(v_val_6629_);
                        v___x_6633_ = lean_box(0);
                        v_isShared_6634_ = v_isSharedCheck_6651_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6635_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once),
                    _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0,
                );
                v___x_6636_ = lean_array_get_borrowed(v___x_6635_, v_argsPacker_6624_, v_fst_6630_);
                v___x_6637_ = lean_array_get_size(v___x_6636_);
                v___x_6638_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v___x_6637_, v_snd_6631_);
                if lean_obj_tag(v___x_6638_) == 0 {
                    lean_del_object(v___x_6633_);
                    lean_dec(v_fst_6630_);
                    v___x_6639_ = lean_box(0);
                    return v___x_6639_;
                } else {
                    v_val_6640_ = lean_ctor_get(v___x_6638_, 0);
                    v_isSharedCheck_6650_ = (!lean_is_exclusive(v___x_6638_)) as u8;
                    if v_isSharedCheck_6650_ == 0 {
                        v___x_6642_ = v___x_6638_;
                        v_isShared_6643_ = v_isSharedCheck_6650_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_6640_);
                        lean_dec(v___x_6638_);
                        v___x_6642_ = lean_box(0);
                        v_isShared_6643_ = v_isSharedCheck_6650_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6634_ == 0 {
                    lean_ctor_set(v___x_6633_, 1, v_val_6640_);
                    v___x_6645_ = v___x_6633_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6649_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6649_, 0, v_fst_6630_);
                    lean_ctor_set(v_reuseFailAlloc_6649_, 1, v_val_6640_);
                    v___x_6645_ = v_reuseFailAlloc_6649_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6643_ == 0 {
                    lean_ctor_set(v___x_6642_, 0, v___x_6645_);
                    v___x_6647_ = v___x_6642_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6648_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6648_, 0, v___x_6645_);
                    v___x_6647_ = v_reuseFailAlloc_6648_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_unpack___boxed(
    mut v_argsPacker_6652_: *mut LeanObject,
    mut v_e_6653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6654_: *mut LeanObject = core::ptr::null_mut();
    v_res_6654_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_6652_, v_e_6653_);
    lean_dec_ref(v_argsPacker_6652_);
    return v_res_6654_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(
    mut v_as_6655_: *mut LeanObject,
    mut v_bs_6656_: *mut LeanObject,
    mut v_i_6657_: *mut LeanObject,
    mut v_cs_6658_: *mut LeanObject,
    mut v___y_6659_: *mut LeanObject,
    mut v___y_6660_: *mut LeanObject,
    mut v___y_6661_: *mut LeanObject,
    mut v___y_6662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: u8 = 0;
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: u8 = 0;
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6681_: u8 = 0;
    let mut v___x_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6685_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6664_ = lean_array_get_size(v_as_6655_);
                v___x_6665_ = lean_nat_dec_lt(v_i_6657_, v___x_6664_);
                if v___x_6665_ == 0 {
                    lean_dec(v_i_6657_);
                    v___x_6666_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6666_, 0, v_cs_6658_);
                    return v___x_6666_;
                } else {
                    v___x_6667_ = lean_array_get_size(v_bs_6656_);
                    v___x_6668_ = lean_nat_dec_lt(v_i_6657_, v___x_6667_);
                    if v___x_6668_ == 0 {
                        lean_dec(v_i_6657_);
                        v___x_6669_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6669_, 0, v_cs_6658_);
                        return v___x_6669_;
                    } else {
                        v_a_6670_ = lean_array_fget_borrowed(v_as_6655_, v_i_6657_);
                        v_b_6671_ = lean_array_fget_borrowed(v_bs_6656_, v_i_6657_);
                        lean_inc(v_b_6671_);
                        lean_inc(v_a_6670_);
                        v___x_6672_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(
                            v_a_6670_,
                            v_b_6671_,
                            v___y_6659_,
                            v___y_6660_,
                            v___y_6661_,
                            v___y_6662_,
                        );
                        if lean_obj_tag(v___x_6672_) == 0 {
                            v_a_6673_ = lean_ctor_get(v___x_6672_, 0);
                            lean_inc(v_a_6673_);
                            lean_dec_ref_known(v___x_6672_, 1);
                            v___x_6674_ = lean_unsigned_to_nat(1);
                            v___x_6675_ = lean_nat_add(v_i_6657_, v___x_6674_);
                            lean_dec(v_i_6657_);
                            v___x_6676_ = lean_array_push(v_cs_6658_, v_a_6673_);
                            v_i_6657_ = v___x_6675_;
                            v_cs_6658_ = v___x_6676_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_cs_6658_);
                            lean_dec(v_i_6657_);
                            v_a_6678_ = lean_ctor_get(v___x_6672_, 0);
                            v_isSharedCheck_6685_ = (!lean_is_exclusive(v___x_6672_)) as u8;
                            if v_isSharedCheck_6685_ == 0 {
                                v___x_6680_ = v___x_6672_;
                                v_isShared_6681_ = v_isSharedCheck_6685_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_6678_);
                                lean_dec(v___x_6672_);
                                v___x_6680_ = lean_box(0);
                                v_isShared_6681_ = v_isSharedCheck_6685_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6681_ == 0 {
                    v___x_6683_ = v___x_6680_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6684_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6684_, 0, v_a_6678_);
                    v___x_6683_ = v_reuseFailAlloc_6684_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0___boxed(
    mut v_as_6686_: *mut LeanObject,
    mut v_bs_6687_: *mut LeanObject,
    mut v_i_6688_: *mut LeanObject,
    mut v_cs_6689_: *mut LeanObject,
    mut v___y_6690_: *mut LeanObject,
    mut v___y_6691_: *mut LeanObject,
    mut v___y_6692_: *mut LeanObject,
    mut v___y_6693_: *mut LeanObject,
    mut v___y_6694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6695_: *mut LeanObject = core::ptr::null_mut();
    v_res_6695_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(
        v_as_6686_,
        v_bs_6687_,
        v_i_6688_,
        v_cs_6689_,
        v___y_6690_,
        v___y_6691_,
        v___y_6692_,
        v___y_6693_,
    );
    lean_dec(v___y_6693_);
    lean_dec_ref(v___y_6692_);
    lean_dec(v___y_6691_);
    lean_dec_ref(v___y_6690_);
    lean_dec_ref(v_bs_6687_);
    lean_dec_ref(v_as_6686_);
    return v_res_6695_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_uncurryType(
    mut v_argsPacker_6696_: *mut LeanObject,
    mut v_types_6697_: *mut LeanObject,
    mut v_a_6698_: *mut LeanObject,
    mut v_a_6699_: *mut LeanObject,
    mut v_a_6700_: *mut LeanObject,
    mut v_a_6701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6711_: u8 = 0;
    let mut v___x_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6715_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6703_ = lean_unsigned_to_nat(0);
                v___x_6704_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
                v___x_6705_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(
                    v_argsPacker_6696_,
                    v_types_6697_,
                    v___x_6703_,
                    v___x_6704_,
                    v_a_6698_,
                    v_a_6699_,
                    v_a_6700_,
                    v_a_6701_,
                );
                if lean_obj_tag(v___x_6705_) == 0 {
                    v_a_6706_ = lean_ctor_get(v___x_6705_, 0);
                    lean_inc(v_a_6706_);
                    lean_dec_ref_known(v___x_6705_, 1);
                    v___x_6707_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(
                        v_a_6706_, v_a_6698_, v_a_6699_, v_a_6700_, v_a_6701_,
                    );
                    return v___x_6707_;
                } else {
                    v_a_6708_ = lean_ctor_get(v___x_6705_, 0);
                    v_isSharedCheck_6715_ = (!lean_is_exclusive(v___x_6705_)) as u8;
                    if v_isSharedCheck_6715_ == 0 {
                        v___x_6710_ = v___x_6705_;
                        v_isShared_6711_ = v_isSharedCheck_6715_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6708_);
                        lean_dec(v___x_6705_);
                        v___x_6710_ = lean_box(0);
                        v_isShared_6711_ = v_isSharedCheck_6715_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6711_ == 0 {
                    v___x_6713_ = v___x_6710_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6714_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6714_, 0, v_a_6708_);
                    v___x_6713_ = v_reuseFailAlloc_6714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6713_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_uncurryType___boxed(
    mut v_argsPacker_6716_: *mut LeanObject,
    mut v_types_6717_: *mut LeanObject,
    mut v_a_6718_: *mut LeanObject,
    mut v_a_6719_: *mut LeanObject,
    mut v_a_6720_: *mut LeanObject,
    mut v_a_6721_: *mut LeanObject,
    mut v_a_6722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6723_: *mut LeanObject = core::ptr::null_mut();
    v_res_6723_ = l_Lean_Meta_ArgsPacker_uncurryType(
        v_argsPacker_6716_,
        v_types_6717_,
        v_a_6718_,
        v_a_6719_,
        v_a_6720_,
        v_a_6721_,
    );
    lean_dec(v_a_6721_);
    lean_dec_ref(v_a_6720_);
    lean_dec(v_a_6719_);
    lean_dec_ref(v_a_6718_);
    lean_dec_ref(v_types_6717_);
    lean_dec_ref(v_argsPacker_6716_);
    return v_res_6723_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(
    mut v_as_6724_: *mut LeanObject,
    mut v_bs_6725_: *mut LeanObject,
    mut v_i_6726_: *mut LeanObject,
    mut v_cs_6727_: *mut LeanObject,
    mut v___y_6728_: *mut LeanObject,
    mut v___y_6729_: *mut LeanObject,
    mut v___y_6730_: *mut LeanObject,
    mut v___y_6731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: u8 = 0;
    let mut v___x_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: u8 = 0;
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6750_: u8 = 0;
    let mut v___x_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6733_ = lean_array_get_size(v_as_6724_);
                v___x_6734_ = lean_nat_dec_lt(v_i_6726_, v___x_6733_);
                if v___x_6734_ == 0 {
                    lean_dec(v_i_6726_);
                    v___x_6735_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6735_, 0, v_cs_6727_);
                    return v___x_6735_;
                } else {
                    v___x_6736_ = lean_array_get_size(v_bs_6725_);
                    v___x_6737_ = lean_nat_dec_lt(v_i_6726_, v___x_6736_);
                    if v___x_6737_ == 0 {
                        lean_dec(v_i_6726_);
                        v___x_6738_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6738_, 0, v_cs_6727_);
                        return v___x_6738_;
                    } else {
                        v_a_6739_ = lean_array_fget_borrowed(v_as_6724_, v_i_6726_);
                        v_b_6740_ = lean_array_fget_borrowed(v_bs_6725_, v_i_6726_);
                        lean_inc(v_b_6740_);
                        lean_inc(v_a_6739_);
                        v___x_6741_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(
                            v_a_6739_,
                            v_b_6740_,
                            v___y_6728_,
                            v___y_6729_,
                            v___y_6730_,
                            v___y_6731_,
                        );
                        if lean_obj_tag(v___x_6741_) == 0 {
                            v_a_6742_ = lean_ctor_get(v___x_6741_, 0);
                            lean_inc(v_a_6742_);
                            lean_dec_ref_known(v___x_6741_, 1);
                            v___x_6743_ = lean_unsigned_to_nat(1);
                            v___x_6744_ = lean_nat_add(v_i_6726_, v___x_6743_);
                            lean_dec(v_i_6726_);
                            v___x_6745_ = lean_array_push(v_cs_6727_, v_a_6742_);
                            v_i_6726_ = v___x_6744_;
                            v_cs_6727_ = v___x_6745_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_cs_6727_);
                            lean_dec(v_i_6726_);
                            v_a_6747_ = lean_ctor_get(v___x_6741_, 0);
                            v_isSharedCheck_6754_ = (!lean_is_exclusive(v___x_6741_)) as u8;
                            if v_isSharedCheck_6754_ == 0 {
                                v___x_6749_ = v___x_6741_;
                                v_isShared_6750_ = v_isSharedCheck_6754_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_6747_);
                                lean_dec(v___x_6741_);
                                v___x_6749_ = lean_box(0);
                                v_isShared_6750_ = v_isSharedCheck_6754_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6750_ == 0 {
                    v___x_6752_ = v___x_6749_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6753_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6753_, 0, v_a_6747_);
                    v___x_6752_ = v_reuseFailAlloc_6753_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0___boxed(
    mut v_as_6755_: *mut LeanObject,
    mut v_bs_6756_: *mut LeanObject,
    mut v_i_6757_: *mut LeanObject,
    mut v_cs_6758_: *mut LeanObject,
    mut v___y_6759_: *mut LeanObject,
    mut v___y_6760_: *mut LeanObject,
    mut v___y_6761_: *mut LeanObject,
    mut v___y_6762_: *mut LeanObject,
    mut v___y_6763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6764_: *mut LeanObject = core::ptr::null_mut();
    v_res_6764_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(
        v_as_6755_,
        v_bs_6756_,
        v_i_6757_,
        v_cs_6758_,
        v___y_6759_,
        v___y_6760_,
        v___y_6761_,
        v___y_6762_,
    );
    lean_dec(v___y_6762_);
    lean_dec_ref(v___y_6761_);
    lean_dec(v___y_6760_);
    lean_dec_ref(v___y_6759_);
    lean_dec_ref(v_bs_6756_);
    lean_dec_ref(v_as_6755_);
    return v_res_6764_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_uncurry(
    mut v_argsPacker_6765_: *mut LeanObject,
    mut v_es_6766_: *mut LeanObject,
    mut v_a_6767_: *mut LeanObject,
    mut v_a_6768_: *mut LeanObject,
    mut v_a_6769_: *mut LeanObject,
    mut v_a_6770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6780_: u8 = 0;
    let mut v___x_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6772_ = lean_unsigned_to_nat(0);
                v___x_6773_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
                v___x_6774_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(
                    v_argsPacker_6765_,
                    v_es_6766_,
                    v___x_6772_,
                    v___x_6773_,
                    v_a_6767_,
                    v_a_6768_,
                    v_a_6769_,
                    v_a_6770_,
                );
                if lean_obj_tag(v___x_6774_) == 0 {
                    v_a_6775_ = lean_ctor_get(v___x_6774_, 0);
                    lean_inc(v_a_6775_);
                    lean_dec_ref_known(v___x_6774_, 1);
                    v___x_6776_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(
                        v_a_6775_, v_a_6767_, v_a_6768_, v_a_6769_, v_a_6770_,
                    );
                    return v___x_6776_;
                } else {
                    v_a_6777_ = lean_ctor_get(v___x_6774_, 0);
                    v_isSharedCheck_6784_ = (!lean_is_exclusive(v___x_6774_)) as u8;
                    if v_isSharedCheck_6784_ == 0 {
                        v___x_6779_ = v___x_6774_;
                        v_isShared_6780_ = v_isSharedCheck_6784_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6777_);
                        lean_dec(v___x_6774_);
                        v___x_6779_ = lean_box(0);
                        v_isShared_6780_ = v_isSharedCheck_6784_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6780_ == 0 {
                    v___x_6782_ = v___x_6779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6783_, 0, v_a_6777_);
                    v___x_6782_ = v_reuseFailAlloc_6783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_uncurry___boxed(
    mut v_argsPacker_6785_: *mut LeanObject,
    mut v_es_6786_: *mut LeanObject,
    mut v_a_6787_: *mut LeanObject,
    mut v_a_6788_: *mut LeanObject,
    mut v_a_6789_: *mut LeanObject,
    mut v_a_6790_: *mut LeanObject,
    mut v_a_6791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6792_: *mut LeanObject = core::ptr::null_mut();
    v_res_6792_ = l_Lean_Meta_ArgsPacker_uncurry(
        v_argsPacker_6785_,
        v_es_6786_,
        v_a_6787_,
        v_a_6788_,
        v_a_6789_,
        v_a_6790_,
    );
    lean_dec(v_a_6790_);
    lean_dec_ref(v_a_6789_);
    lean_dec(v_a_6788_);
    lean_dec_ref(v_a_6787_);
    lean_dec_ref(v_es_6786_);
    lean_dec_ref(v_argsPacker_6785_);
    return v_res_6792_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_uncurryWithType(
    mut v_argsPacker_6793_: *mut LeanObject,
    mut v_resultType_6794_: *mut LeanObject,
    mut v_es_6795_: *mut LeanObject,
    mut v_a_6796_: *mut LeanObject,
    mut v_a_6797_: *mut LeanObject,
    mut v_a_6798_: *mut LeanObject,
    mut v_a_6799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6809_: u8 = 0;
    let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6801_ = lean_unsigned_to_nat(0);
                v___x_6802_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
                v___x_6803_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(
                    v_argsPacker_6793_,
                    v_es_6795_,
                    v___x_6801_,
                    v___x_6802_,
                    v_a_6796_,
                    v_a_6797_,
                    v_a_6798_,
                    v_a_6799_,
                );
                if lean_obj_tag(v___x_6803_) == 0 {
                    v_a_6804_ = lean_ctor_get(v___x_6803_, 0);
                    lean_inc(v_a_6804_);
                    lean_dec_ref_known(v___x_6803_, 1);
                    v___x_6805_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(
                        v_resultType_6794_,
                        v_a_6804_,
                        v_a_6796_,
                        v_a_6797_,
                        v_a_6798_,
                        v_a_6799_,
                    );
                    return v___x_6805_;
                } else {
                    lean_dec_ref(v_resultType_6794_);
                    v_a_6806_ = lean_ctor_get(v___x_6803_, 0);
                    v_isSharedCheck_6813_ = (!lean_is_exclusive(v___x_6803_)) as u8;
                    if v_isSharedCheck_6813_ == 0 {
                        v___x_6808_ = v___x_6803_;
                        v_isShared_6809_ = v_isSharedCheck_6813_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6806_);
                        lean_dec(v___x_6803_);
                        v___x_6808_ = lean_box(0);
                        v_isShared_6809_ = v_isSharedCheck_6813_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6809_ == 0 {
                    v___x_6811_ = v___x_6808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6812_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6812_, 0, v_a_6806_);
                    v___x_6811_ = v_reuseFailAlloc_6812_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_uncurryWithType___boxed(
    mut v_argsPacker_6814_: *mut LeanObject,
    mut v_resultType_6815_: *mut LeanObject,
    mut v_es_6816_: *mut LeanObject,
    mut v_a_6817_: *mut LeanObject,
    mut v_a_6818_: *mut LeanObject,
    mut v_a_6819_: *mut LeanObject,
    mut v_a_6820_: *mut LeanObject,
    mut v_a_6821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6822_: *mut LeanObject = core::ptr::null_mut();
    v_res_6822_ = l_Lean_Meta_ArgsPacker_uncurryWithType(
        v_argsPacker_6814_,
        v_resultType_6815_,
        v_es_6816_,
        v_a_6817_,
        v_a_6818_,
        v_a_6819_,
        v_a_6820_,
    );
    lean_dec(v_a_6820_);
    lean_dec_ref(v_a_6819_);
    lean_dec(v_a_6818_);
    lean_dec_ref(v_a_6817_);
    lean_dec_ref(v_es_6816_);
    lean_dec_ref(v_argsPacker_6814_);
    return v_res_6822_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_uncurryND(
    mut v_argsPacker_6823_: *mut LeanObject,
    mut v_es_6824_: *mut LeanObject,
    mut v_a_6825_: *mut LeanObject,
    mut v_a_6826_: *mut LeanObject,
    mut v_a_6827_: *mut LeanObject,
    mut v_a_6828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6838_: u8 = 0;
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6830_ = lean_unsigned_to_nat(0);
                v___x_6831_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
                v___x_6832_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(
                    v_argsPacker_6823_,
                    v_es_6824_,
                    v___x_6830_,
                    v___x_6831_,
                    v_a_6825_,
                    v_a_6826_,
                    v_a_6827_,
                    v_a_6828_,
                );
                if lean_obj_tag(v___x_6832_) == 0 {
                    v_a_6833_ = lean_ctor_get(v___x_6832_, 0);
                    lean_inc(v_a_6833_);
                    lean_dec_ref_known(v___x_6832_, 1);
                    v___x_6834_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(
                        v_a_6833_, v_a_6825_, v_a_6826_, v_a_6827_, v_a_6828_,
                    );
                    return v___x_6834_;
                } else {
                    v_a_6835_ = lean_ctor_get(v___x_6832_, 0);
                    v_isSharedCheck_6842_ = (!lean_is_exclusive(v___x_6832_)) as u8;
                    if v_isSharedCheck_6842_ == 0 {
                        v___x_6837_ = v___x_6832_;
                        v_isShared_6838_ = v_isSharedCheck_6842_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6835_);
                        lean_dec(v___x_6832_);
                        v___x_6837_ = lean_box(0);
                        v_isShared_6838_ = v_isSharedCheck_6842_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6838_ == 0 {
                    v___x_6840_ = v___x_6837_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6841_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6841_, 0, v_a_6835_);
                    v___x_6840_ = v_reuseFailAlloc_6841_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_uncurryND___boxed(
    mut v_argsPacker_6843_: *mut LeanObject,
    mut v_es_6844_: *mut LeanObject,
    mut v_a_6845_: *mut LeanObject,
    mut v_a_6846_: *mut LeanObject,
    mut v_a_6847_: *mut LeanObject,
    mut v_a_6848_: *mut LeanObject,
    mut v_a_6849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6850_: *mut LeanObject = core::ptr::null_mut();
    v_res_6850_ = l_Lean_Meta_ArgsPacker_uncurryND(
        v_argsPacker_6843_,
        v_es_6844_,
        v_a_6845_,
        v_a_6846_,
        v_a_6847_,
        v_a_6848_,
    );
    lean_dec(v_a_6848_);
    lean_dec_ref(v_a_6847_);
    lean_dec(v_a_6846_);
    lean_dec_ref(v_a_6845_);
    lean_dec_ref(v_es_6844_);
    lean_dec_ref(v_argsPacker_6843_);
    return v_res_6850_;
}
pub unsafe fn l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(
    mut v_msg_6851_: *mut LeanObject,
    mut v___y_6852_: *mut LeanObject,
    mut v___y_6853_: *mut LeanObject,
    mut v___y_6854_: *mut LeanObject,
    mut v___y_6855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078__overap_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    v___f_6857_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0;
    v___x_1078__overap_6858_ = lean_panic_fn_borrowed(v___f_6857_, v_msg_6851_);
    lean_inc(v___y_6855_);
    lean_inc_ref(v___y_6854_);
    lean_inc(v___y_6853_);
    lean_inc_ref(v___y_6852_);
    v___x_6859_ = lean_apply_5(
        v___x_1078__overap_6858_,
        v___y_6852_,
        v___y_6853_,
        v___y_6854_,
        v___y_6855_,
        lean_box(0),
    );
    return v___x_6859_;
}
pub unsafe fn l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0___boxed(
    mut v_msg_6860_: *mut LeanObject,
    mut v___y_6861_: *mut LeanObject,
    mut v___y_6862_: *mut LeanObject,
    mut v___y_6863_: *mut LeanObject,
    mut v___y_6864_: *mut LeanObject,
    mut v___y_6865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6866_: *mut LeanObject = core::ptr::null_mut();
    v_res_6866_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(
        v_msg_6860_,
        v___y_6861_,
        v___y_6862_,
        v___y_6863_,
        v___y_6864_,
    );
    lean_dec(v___y_6864_);
    lean_dec_ref(v___y_6863_);
    lean_dec(v___y_6862_);
    lean_dec_ref(v___y_6861_);
    return v_res_6866_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryProj___lam__0(
    mut v_a_6867_: *mut LeanObject,
    mut v___x_6868_: *mut LeanObject,
    mut v_i_6869_: *mut LeanObject,
    mut v_e_6870_: *mut LeanObject,
    mut v_x_6871_: *mut LeanObject,
    mut v___y_6872_: *mut LeanObject,
    mut v___y_6873_: *mut LeanObject,
    mut v___y_6874_: *mut LeanObject,
    mut v___y_6875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
    v___x_6877_ = l_List_lengthTR___redArg(v_a_6867_);
    lean_inc_ref(v_x_6871_);
    v___x_6878_ = l_Lean_Meta_ArgsPacker_Mutual_pack(
        v___x_6877_,
        v___x_6868_,
        v_i_6869_,
        v_x_6871_,
        v___y_6872_,
        v___y_6873_,
        v___y_6874_,
        v___y_6875_,
    );
    lean_dec(v___x_6877_);
    if lean_obj_tag(v___x_6878_) == 0 {
        let mut v_a_6879_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6881_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6885_: u8 = 0;
        let mut v___x_6886_: u8 = 0;
        let mut v___x_6887_: u8 = 0;
        let mut v___x_6888_: *mut LeanObject = core::ptr::null_mut();
        v_a_6879_ = lean_ctor_get(v___x_6878_, 0);
        lean_inc(v_a_6879_);
        lean_dec_ref_known(v___x_6878_, 1);
        v___x_6880_ = lean_unsigned_to_nat(1);
        v___x_6881_ = lean_mk_empty_array_with_capacity(v___x_6880_);
        lean_inc_ref(v___x_6881_);
        v___x_6882_ = lean_array_push(v___x_6881_, v_x_6871_);
        v___x_6883_ = lean_array_push(v___x_6881_, v_a_6879_);
        v___x_6884_ = l_Lean_Expr_beta(v_e_6870_, v___x_6883_);
        v___x_6885_ = 0;
        v___x_6886_ = 1;
        v___x_6887_ = 1;
        v___x_6888_ = l_Lean_Meta_mkLambdaFVars(
            v___x_6882_,
            v___x_6884_,
            v___x_6885_,
            v___x_6886_,
            v___x_6885_,
            v___x_6886_,
            v___x_6887_,
            v___y_6872_,
            v___y_6873_,
            v___y_6874_,
            v___y_6875_,
        );
        lean_dec_ref(v___x_6882_);
        return v___x_6888_;
    } else {
        lean_dec_ref(v_x_6871_);
        lean_dec_ref(v_e_6870_);
        return v___x_6878_;
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed(
    mut v_a_6889_: *mut LeanObject,
    mut v___x_6890_: *mut LeanObject,
    mut v_i_6891_: *mut LeanObject,
    mut v_e_6892_: *mut LeanObject,
    mut v_x_6893_: *mut LeanObject,
    mut v___y_6894_: *mut LeanObject,
    mut v___y_6895_: *mut LeanObject,
    mut v___y_6896_: *mut LeanObject,
    mut v___y_6897_: *mut LeanObject,
    mut v___y_6898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6899_: *mut LeanObject = core::ptr::null_mut();
    v_res_6899_ = l_Lean_Meta_ArgsPacker_curryProj___lam__0(
        v_a_6889_,
        v___x_6890_,
        v_i_6891_,
        v_e_6892_,
        v_x_6893_,
        v___y_6894_,
        v___y_6895_,
        v___y_6896_,
        v___y_6897_,
    );
    lean_dec(v___y_6897_);
    lean_dec_ref(v___y_6896_);
    lean_dec(v___y_6895_);
    lean_dec_ref(v___y_6894_);
    lean_dec(v_i_6891_);
    lean_dec(v_a_6889_);
    return v_res_6899_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1() -> *mut LeanObject {
    let mut v___x_6901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    v___x_6901_ = l_Lean_Meta_ArgsPacker_curryProj___closed__0;
    v___x_6902_ = l_Lean_stringToMessageData(v___x_6901_);
    return v___x_6902_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4() -> *mut LeanObject {
    let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut LeanObject = core::ptr::null_mut();
    v___x_6905_ = l_Lean_Meta_ArgsPacker_curryProj___closed__3;
    v___x_6906_ = lean_unsigned_to_nat(4);
    v___x_6907_ = lean_unsigned_to_nat(535);
    v___x_6908_ = l_Lean_Meta_ArgsPacker_curryProj___closed__2;
    v___x_6909_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0;
    v___x_6910_ = l_mkPanicMessageWithDecl(
        v___x_6909_,
        v___x_6908_,
        v___x_6907_,
        v___x_6906_,
        v___x_6905_,
    );
    return v___x_6910_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryProj(
    mut v_argsPacker_6911_: *mut LeanObject,
    mut v_e_6912_: *mut LeanObject,
    mut v_i_6913_: *mut LeanObject,
    mut v_a_6914_: *mut LeanObject,
    mut v_a_6915_: *mut LeanObject,
    mut v_a_6916_: *mut LeanObject,
    mut v_a_6917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: u8 = 0;
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6955_: u8 = 0;
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6959_: u8 = 0;
    let mut v_a_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6963_: u8 = 0;
    let mut v___x_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6967_: u8 = 0;
    let mut v___x_6968_: u8 = 0;
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6974_: u8 = 0;
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_6917_);
                lean_inc_ref(v_a_6916_);
                lean_inc(v_a_6915_);
                lean_inc_ref(v_a_6914_);
                lean_inc_ref(v_e_6912_);
                v___x_6919_ =
                    lean_infer_type(v_e_6912_, v_a_6914_, v_a_6915_, v_a_6916_, v_a_6917_);
                if lean_obj_tag(v___x_6919_) == 0 {
                    v_a_6920_ = lean_ctor_get(v___x_6919_, 0);
                    lean_inc(v_a_6920_);
                    lean_dec_ref_known(v___x_6919_, 1);
                    lean_inc(v_a_6917_);
                    lean_inc_ref(v_a_6916_);
                    lean_inc(v_a_6915_);
                    lean_inc_ref(v_a_6914_);
                    v___x_6921_ = lean_whnf(v_a_6920_, v_a_6914_, v_a_6915_, v_a_6916_, v_a_6917_);
                    if lean_obj_tag(v___x_6921_) == 0 {
                        v_a_6922_ = lean_ctor_get(v___x_6921_, 0);
                        lean_inc(v_a_6922_);
                        lean_dec_ref_known(v___x_6921_, 1);
                        v___x_6923_ = l_Lean_instInhabitedExpr;
                        v___x_6924_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once
                            ),
                            _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0,
                        );
                        v_n_6938_ = lean_array_get_size(v_argsPacker_6911_);
                        v___x_6968_ = l_Lean_Expr_isForall(v_a_6922_);
                        if v___x_6968_ == 0 {
                            v___x_6969_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_ArgsPacker_curryProj___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_ArgsPacker_curryProj___closed__4_once
                                ),
                                _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4,
                            );
                            v___x_6970_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(
                                v___x_6969_,
                                v_a_6914_,
                                v_a_6915_,
                                v_a_6916_,
                                v_a_6917_,
                            );
                            if lean_obj_tag(v___x_6970_) == 0 {
                                lean_dec_ref_known(v___x_6970_, 1);
                                v___y_6940_ = v_a_6914_;
                                v___y_6941_ = v_a_6915_;
                                v___y_6942_ = v_a_6916_;
                                v___y_6943_ = v_a_6917_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_6922_);
                                lean_dec(v_i_6913_);
                                lean_dec_ref(v_e_6912_);
                                v_a_6971_ = lean_ctor_get(v___x_6970_, 0);
                                v_isSharedCheck_6978_ = (!lean_is_exclusive(v___x_6970_)) as u8;
                                if v_isSharedCheck_6978_ == 0 {
                                    v___x_6973_ = v___x_6970_;
                                    v_isShared_6974_ = v_isSharedCheck_6978_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_6971_);
                                    lean_dec(v___x_6970_);
                                    v___x_6973_ = lean_box(0);
                                    v_isShared_6974_ = v_isSharedCheck_6978_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            v___y_6940_ = v_a_6914_;
                            v___y_6941_ = v_a_6915_;
                            v___y_6942_ = v_a_6916_;
                            v___y_6943_ = v_a_6917_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_i_6913_);
                        lean_dec_ref(v_e_6912_);
                        return v___x_6921_;
                    }
                } else {
                    lean_dec(v_i_6913_);
                    lean_dec_ref(v_e_6912_);
                    return v___x_6919_;
                }
            }
            1 => {
                lean_inc(v_i_6913_);
                v___x_6932_ = l_List_get_x21Internal___redArg(v___x_6923_, v___y_6927_, v_i_6913_);
                lean_dec(v___y_6927_);
                v___x_6933_ = l_Lean_Expr_bindingName_x21(v_a_6922_);
                lean_dec(v_a_6922_);
                v___x_6934_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_6933_, v___x_6932_, v___y_6926_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_);
                if lean_obj_tag(v___x_6934_) == 0 {
                    v_a_6935_ = lean_ctor_get(v___x_6934_, 0);
                    lean_inc(v_a_6935_);
                    lean_dec_ref_known(v___x_6934_, 1);
                    v___x_6936_ =
                        lean_array_get_borrowed(v___x_6924_, v_argsPacker_6911_, v_i_6913_);
                    lean_dec(v_i_6913_);
                    lean_inc(v___x_6936_);
                    v___x_6937_ =
                        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(
                            v___x_6936_,
                            v_a_6935_,
                            v___y_6928_,
                            v___y_6929_,
                            v___y_6930_,
                            v___y_6931_,
                        );
                    return v___x_6937_;
                } else {
                    lean_dec(v_i_6913_);
                    return v___x_6934_;
                }
            }
            2 => {
                v___x_6944_ = l_Lean_Expr_bindingDomain_x21(v_a_6922_);
                lean_inc_ref(v___x_6944_);
                v___x_6945_ =
                    l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(
                        v_n_6938_,
                        v___x_6944_,
                        v___y_6940_,
                        v___y_6941_,
                        v___y_6942_,
                        v___y_6943_,
                    );
                if lean_obj_tag(v___x_6945_) == 0 {
                    v_a_6946_ = lean_ctor_get(v___x_6945_, 0);
                    lean_inc_n(v_a_6946_, 2);
                    lean_dec_ref_known(v___x_6945_, 1);
                    lean_inc(v_i_6913_);
                    v___f_6947_ = lean_alloc_closure(
                        l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed as *mut core::ffi::c_void,
                        10,
                        4,
                    );
                    lean_closure_set(v___f_6947_, 0, v_a_6946_);
                    lean_closure_set(v___f_6947_, 1, v___x_6944_);
                    lean_closure_set(v___f_6947_, 2, v_i_6913_);
                    lean_closure_set(v___f_6947_, 3, v_e_6912_);
                    v___x_6948_ = l_List_lengthTR___redArg(v_a_6946_);
                    v___x_6949_ = lean_nat_dec_lt(v_i_6913_, v___x_6948_);
                    lean_dec(v___x_6948_);
                    if v___x_6949_ == 0 {
                        lean_dec_ref(v___f_6947_);
                        lean_dec(v_a_6946_);
                        lean_dec(v_a_6922_);
                        lean_dec(v_i_6913_);
                        v___x_6950_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_curryProj___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_ArgsPacker_curryProj___closed__1_once
                            ),
                            _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1,
                        );
                        v___x_6951_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_6950_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_);
                        v_a_6952_ = lean_ctor_get(v___x_6951_, 0);
                        v_isSharedCheck_6959_ = (!lean_is_exclusive(v___x_6951_)) as u8;
                        if v_isSharedCheck_6959_ == 0 {
                            v___x_6954_ = v___x_6951_;
                            v_isShared_6955_ = v_isSharedCheck_6959_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6952_);
                            lean_dec(v___x_6951_);
                            v___x_6954_ = lean_box(0);
                            v_isShared_6955_ = v_isSharedCheck_6959_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___y_6926_ = v___f_6947_;
                        v___y_6927_ = v_a_6946_;
                        v___y_6928_ = v___y_6940_;
                        v___y_6929_ = v___y_6941_;
                        v___y_6930_ = v___y_6942_;
                        v___y_6931_ = v___y_6943_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_6944_);
                    lean_dec(v_a_6922_);
                    lean_dec(v_i_6913_);
                    lean_dec_ref(v_e_6912_);
                    v_a_6960_ = lean_ctor_get(v___x_6945_, 0);
                    v_isSharedCheck_6967_ = (!lean_is_exclusive(v___x_6945_)) as u8;
                    if v_isSharedCheck_6967_ == 0 {
                        v___x_6962_ = v___x_6945_;
                        v_isShared_6963_ = v_isSharedCheck_6967_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6960_);
                        lean_dec(v___x_6945_);
                        v___x_6962_ = lean_box(0);
                        v_isShared_6963_ = v_isSharedCheck_6967_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6955_ == 0 {
                    v___x_6957_ = v___x_6954_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6958_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6958_, 0, v_a_6952_);
                    v___x_6957_ = v_reuseFailAlloc_6958_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6957_;
            }
            5 => {
                if v_isShared_6963_ == 0 {
                    v___x_6965_ = v___x_6962_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6966_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 0, v_a_6960_);
                    v___x_6965_ = v_reuseFailAlloc_6966_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6965_;
            }
            7 => {
                if v_isShared_6974_ == 0 {
                    v___x_6976_ = v___x_6973_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6977_, 0, v_a_6971_);
                    v___x_6976_ = v_reuseFailAlloc_6977_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryProj___boxed(
    mut v_argsPacker_6979_: *mut LeanObject,
    mut v_e_6980_: *mut LeanObject,
    mut v_i_6981_: *mut LeanObject,
    mut v_a_6982_: *mut LeanObject,
    mut v_a_6983_: *mut LeanObject,
    mut v_a_6984_: *mut LeanObject,
    mut v_a_6985_: *mut LeanObject,
    mut v_a_6986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6987_: *mut LeanObject = core::ptr::null_mut();
    v_res_6987_ = l_Lean_Meta_ArgsPacker_curryProj(
        v_argsPacker_6979_,
        v_e_6980_,
        v_i_6981_,
        v_a_6982_,
        v_a_6983_,
        v_a_6984_,
        v_a_6985_,
    );
    lean_dec(v_a_6985_);
    lean_dec_ref(v_a_6984_);
    lean_dec(v_a_6983_);
    lean_dec_ref(v_a_6982_);
    lean_dec_ref(v_argsPacker_6979_);
    return v_res_6987_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(
    mut v_as_6988_: *mut LeanObject,
    mut v_bs_6989_: *mut LeanObject,
    mut v_i_6990_: *mut LeanObject,
    mut v_cs_6991_: *mut LeanObject,
    mut v___y_6992_: *mut LeanObject,
    mut v___y_6993_: *mut LeanObject,
    mut v___y_6994_: *mut LeanObject,
    mut v___y_6995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: u8 = 0;
    let mut v___x_6999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: u8 = 0;
    let mut v___x_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7014_: u8 = 0;
    let mut v___x_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6997_ = lean_array_get_size(v_as_6988_);
                v___x_6998_ = lean_nat_dec_lt(v_i_6990_, v___x_6997_);
                if v___x_6998_ == 0 {
                    lean_dec(v_i_6990_);
                    v___x_6999_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6999_, 0, v_cs_6991_);
                    return v___x_6999_;
                } else {
                    v___x_7000_ = lean_array_get_size(v_bs_6989_);
                    v___x_7001_ = lean_nat_dec_lt(v_i_6990_, v___x_7000_);
                    if v___x_7001_ == 0 {
                        lean_dec(v_i_6990_);
                        v___x_7002_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7002_, 0, v_cs_6991_);
                        return v___x_7002_;
                    } else {
                        v_a_7003_ = lean_array_fget_borrowed(v_as_6988_, v_i_6990_);
                        v_b_7004_ = lean_array_fget_borrowed(v_bs_6989_, v_i_6990_);
                        lean_inc(v_b_7004_);
                        lean_inc(v_a_7003_);
                        v___x_7005_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_a_7003_, v_b_7004_, v___y_6992_, v___y_6993_, v___y_6994_, v___y_6995_);
                        if lean_obj_tag(v___x_7005_) == 0 {
                            v_a_7006_ = lean_ctor_get(v___x_7005_, 0);
                            lean_inc(v_a_7006_);
                            lean_dec_ref_known(v___x_7005_, 1);
                            v___x_7007_ = lean_unsigned_to_nat(1);
                            v___x_7008_ = lean_nat_add(v_i_6990_, v___x_7007_);
                            lean_dec(v_i_6990_);
                            v___x_7009_ = lean_array_push(v_cs_6991_, v_a_7006_);
                            v_i_6990_ = v___x_7008_;
                            v_cs_6991_ = v___x_7009_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_cs_6991_);
                            lean_dec(v_i_6990_);
                            v_a_7011_ = lean_ctor_get(v___x_7005_, 0);
                            v_isSharedCheck_7018_ = (!lean_is_exclusive(v___x_7005_)) as u8;
                            if v_isSharedCheck_7018_ == 0 {
                                v___x_7013_ = v___x_7005_;
                                v_isShared_7014_ = v_isSharedCheck_7018_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_7011_);
                                lean_dec(v___x_7005_);
                                v___x_7013_ = lean_box(0);
                                v_isShared_7014_ = v_isSharedCheck_7018_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7014_ == 0 {
                    v___x_7016_ = v___x_7013_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7017_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7017_, 0, v_a_7011_);
                    v___x_7016_ = v_reuseFailAlloc_7017_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0___boxed(
    mut v_as_7019_: *mut LeanObject,
    mut v_bs_7020_: *mut LeanObject,
    mut v_i_7021_: *mut LeanObject,
    mut v_cs_7022_: *mut LeanObject,
    mut v___y_7023_: *mut LeanObject,
    mut v___y_7024_: *mut LeanObject,
    mut v___y_7025_: *mut LeanObject,
    mut v___y_7026_: *mut LeanObject,
    mut v___y_7027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7028_: *mut LeanObject = core::ptr::null_mut();
    v_res_7028_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(
        v_as_7019_,
        v_bs_7020_,
        v_i_7021_,
        v_cs_7022_,
        v___y_7023_,
        v___y_7024_,
        v___y_7025_,
        v___y_7026_,
    );
    lean_dec(v___y_7026_);
    lean_dec_ref(v___y_7025_);
    lean_dec(v___y_7024_);
    lean_dec_ref(v___y_7023_);
    lean_dec_ref(v_bs_7020_);
    lean_dec_ref(v_as_7019_);
    return v_res_7028_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryType(
    mut v_argsPacker_7029_: *mut LeanObject,
    mut v_t_7030_: *mut LeanObject,
    mut v_a_7031_: *mut LeanObject,
    mut v_a_7032_: *mut LeanObject,
    mut v_a_7033_: *mut LeanObject,
    mut v_a_7034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut LeanObject = core::ptr::null_mut();
    v___x_7036_ = lean_array_get_size(v_argsPacker_7029_);
    v___x_7037_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(
        v___x_7036_,
        v_t_7030_,
        v_a_7031_,
        v_a_7032_,
        v_a_7033_,
        v_a_7034_,
    );
    if lean_obj_tag(v___x_7037_) == 0 {
        let mut v_a_7038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7039_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7040_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7041_: *mut LeanObject = core::ptr::null_mut();
        v_a_7038_ = lean_ctor_get(v___x_7037_, 0);
        lean_inc(v_a_7038_);
        lean_dec_ref_known(v___x_7037_, 1);
        v___x_7039_ = lean_unsigned_to_nat(0);
        v___x_7040_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
        v___x_7041_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(
            v_argsPacker_7029_,
            v_a_7038_,
            v___x_7039_,
            v___x_7040_,
            v_a_7031_,
            v_a_7032_,
            v_a_7033_,
            v_a_7034_,
        );
        lean_dec(v_a_7038_);
        return v___x_7041_;
    } else {
        return v___x_7037_;
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryType___boxed(
    mut v_argsPacker_7042_: *mut LeanObject,
    mut v_t_7043_: *mut LeanObject,
    mut v_a_7044_: *mut LeanObject,
    mut v_a_7045_: *mut LeanObject,
    mut v_a_7046_: *mut LeanObject,
    mut v_a_7047_: *mut LeanObject,
    mut v_a_7048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7049_: *mut LeanObject = core::ptr::null_mut();
    v_res_7049_ = l_Lean_Meta_ArgsPacker_curryType(
        v_argsPacker_7042_,
        v_t_7043_,
        v_a_7044_,
        v_a_7045_,
        v_a_7046_,
        v_a_7047_,
    );
    lean_dec(v_a_7047_);
    lean_dec_ref(v_a_7046_);
    lean_dec(v_a_7045_);
    lean_dec_ref(v_a_7044_);
    lean_dec_ref(v_argsPacker_7042_);
    return v_res_7049_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(
    mut v_upperBound_7050_: *mut LeanObject,
    mut v_argsPacker_7051_: *mut LeanObject,
    mut v_e_7052_: *mut LeanObject,
    mut v_a_7053_: *mut LeanObject,
    mut v_b_7054_: *mut LeanObject,
    mut v___y_7055_: *mut LeanObject,
    mut v___y_7056_: *mut LeanObject,
    mut v___y_7057_: *mut LeanObject,
    mut v___y_7058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7060_: u8 = 0;
    let mut v___x_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7071_: u8 = 0;
    let mut v___x_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7060_ = lean_nat_dec_lt(v_a_7053_, v_upperBound_7050_);
                if v___x_7060_ == 0 {
                    lean_dec(v_a_7053_);
                    lean_dec_ref(v_e_7052_);
                    v___x_7061_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7061_, 0, v_b_7054_);
                    return v___x_7061_;
                } else {
                    lean_inc(v_a_7053_);
                    lean_inc_ref(v_e_7052_);
                    v___x_7062_ = l_Lean_Meta_ArgsPacker_curryProj(
                        v_argsPacker_7051_,
                        v_e_7052_,
                        v_a_7053_,
                        v___y_7055_,
                        v___y_7056_,
                        v___y_7057_,
                        v___y_7058_,
                    );
                    if lean_obj_tag(v___x_7062_) == 0 {
                        v_a_7063_ = lean_ctor_get(v___x_7062_, 0);
                        lean_inc(v_a_7063_);
                        lean_dec_ref_known(v___x_7062_, 1);
                        v___x_7064_ = lean_array_push(v_b_7054_, v_a_7063_);
                        v___x_7065_ = lean_unsigned_to_nat(1);
                        v___x_7066_ = lean_nat_add(v_a_7053_, v___x_7065_);
                        lean_dec(v_a_7053_);
                        v_a_7053_ = v___x_7066_;
                        v_b_7054_ = v___x_7064_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_b_7054_);
                        lean_dec(v_a_7053_);
                        lean_dec_ref(v_e_7052_);
                        v_a_7068_ = lean_ctor_get(v___x_7062_, 0);
                        v_isSharedCheck_7075_ = (!lean_is_exclusive(v___x_7062_)) as u8;
                        if v_isSharedCheck_7075_ == 0 {
                            v___x_7070_ = v___x_7062_;
                            v_isShared_7071_ = v_isSharedCheck_7075_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7068_);
                            lean_dec(v___x_7062_);
                            v___x_7070_ = lean_box(0);
                            v_isShared_7071_ = v_isSharedCheck_7075_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7071_ == 0 {
                    v___x_7073_ = v___x_7070_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7074_, 0, v_a_7068_);
                    v___x_7073_ = v_reuseFailAlloc_7074_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg___boxed(
    mut v_upperBound_7076_: *mut LeanObject,
    mut v_argsPacker_7077_: *mut LeanObject,
    mut v_e_7078_: *mut LeanObject,
    mut v_a_7079_: *mut LeanObject,
    mut v_b_7080_: *mut LeanObject,
    mut v___y_7081_: *mut LeanObject,
    mut v___y_7082_: *mut LeanObject,
    mut v___y_7083_: *mut LeanObject,
    mut v___y_7084_: *mut LeanObject,
    mut v___y_7085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7086_: *mut LeanObject = core::ptr::null_mut();
    v_res_7086_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(
            v_upperBound_7076_,
            v_argsPacker_7077_,
            v_e_7078_,
            v_a_7079_,
            v_b_7080_,
            v___y_7081_,
            v___y_7082_,
            v___y_7083_,
            v___y_7084_,
        );
    lean_dec(v___y_7084_);
    lean_dec_ref(v___y_7083_);
    lean_dec(v___y_7082_);
    lean_dec_ref(v___y_7081_);
    lean_dec_ref(v_argsPacker_7077_);
    lean_dec(v_upperBound_7076_);
    return v_res_7086_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_curry___closed__0() -> *mut LeanObject {
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut LeanObject = core::ptr::null_mut();
    v___x_7087_ = lean_unsigned_to_nat(0);
    v___x_7088_ = l_Lean_Level_ofNat(v___x_7087_);
    return v___x_7088_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curry(
    mut v_argsPacker_7089_: *mut LeanObject,
    mut v_e_7090_: *mut LeanObject,
    mut v_a_7091_: *mut LeanObject,
    mut v_a_7092_: *mut LeanObject,
    mut v_a_7093_: *mut LeanObject,
    mut v_a_7094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_es_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7106_: u8 = 0;
    let mut v___x_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7096_ = lean_array_get_size(v_argsPacker_7089_);
                v___x_7097_ = lean_unsigned_to_nat(0);
                v_es_7098_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
                v___x_7099_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v___x_7096_, v_argsPacker_7089_, v_e_7090_, v___x_7097_, v_es_7098_, v_a_7091_, v_a_7092_, v_a_7093_, v_a_7094_);
                if lean_obj_tag(v___x_7099_) == 0 {
                    v_a_7100_ = lean_ctor_get(v___x_7099_, 0);
                    lean_inc(v_a_7100_);
                    lean_dec_ref_known(v___x_7099_, 1);
                    v___x_7101_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_curry___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Meta_ArgsPacker_curry___closed__0_once),
                        _init_l_Lean_Meta_ArgsPacker_curry___closed__0,
                    );
                    v___x_7102_ = l_Lean_Meta_PProdN_mk(
                        v___x_7101_,
                        v_a_7100_,
                        v_a_7091_,
                        v_a_7092_,
                        v_a_7093_,
                        v_a_7094_,
                    );
                    return v___x_7102_;
                } else {
                    v_a_7103_ = lean_ctor_get(v___x_7099_, 0);
                    v_isSharedCheck_7110_ = (!lean_is_exclusive(v___x_7099_)) as u8;
                    if v_isSharedCheck_7110_ == 0 {
                        v___x_7105_ = v___x_7099_;
                        v_isShared_7106_ = v_isSharedCheck_7110_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7103_);
                        lean_dec(v___x_7099_);
                        v___x_7105_ = lean_box(0);
                        v_isShared_7106_ = v_isSharedCheck_7110_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7106_ == 0 {
                    v___x_7108_ = v___x_7105_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7109_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7109_, 0, v_a_7103_);
                    v___x_7108_ = v_reuseFailAlloc_7109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curry___boxed(
    mut v_argsPacker_7111_: *mut LeanObject,
    mut v_e_7112_: *mut LeanObject,
    mut v_a_7113_: *mut LeanObject,
    mut v_a_7114_: *mut LeanObject,
    mut v_a_7115_: *mut LeanObject,
    mut v_a_7116_: *mut LeanObject,
    mut v_a_7117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7118_: *mut LeanObject = core::ptr::null_mut();
    v_res_7118_ = l_Lean_Meta_ArgsPacker_curry(
        v_argsPacker_7111_,
        v_e_7112_,
        v_a_7113_,
        v_a_7114_,
        v_a_7115_,
        v_a_7116_,
    );
    lean_dec(v_a_7116_);
    lean_dec_ref(v_a_7115_);
    lean_dec(v_a_7114_);
    lean_dec_ref(v_a_7113_);
    lean_dec_ref(v_argsPacker_7111_);
    return v_res_7118_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(
    mut v_upperBound_7119_: *mut LeanObject,
    mut v_argsPacker_7120_: *mut LeanObject,
    mut v_e_7121_: *mut LeanObject,
    mut v_inst_7122_: *mut LeanObject,
    mut v_R_7123_: *mut LeanObject,
    mut v_a_7124_: *mut LeanObject,
    mut v_b_7125_: *mut LeanObject,
    mut v_c_7126_: *mut LeanObject,
    mut v___y_7127_: *mut LeanObject,
    mut v___y_7128_: *mut LeanObject,
    mut v___y_7129_: *mut LeanObject,
    mut v___y_7130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    v___x_7132_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(
            v_upperBound_7119_,
            v_argsPacker_7120_,
            v_e_7121_,
            v_a_7124_,
            v_b_7125_,
            v___y_7127_,
            v___y_7128_,
            v___y_7129_,
            v___y_7130_,
        );
    return v___x_7132_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___boxed(
    mut v_upperBound_7133_: *mut LeanObject,
    mut v_argsPacker_7134_: *mut LeanObject,
    mut v_e_7135_: *mut LeanObject,
    mut v_inst_7136_: *mut LeanObject,
    mut v_R_7137_: *mut LeanObject,
    mut v_a_7138_: *mut LeanObject,
    mut v_b_7139_: *mut LeanObject,
    mut v_c_7140_: *mut LeanObject,
    mut v___y_7141_: *mut LeanObject,
    mut v___y_7142_: *mut LeanObject,
    mut v___y_7143_: *mut LeanObject,
    mut v___y_7144_: *mut LeanObject,
    mut v___y_7145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7146_: *mut LeanObject = core::ptr::null_mut();
    v_res_7146_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(
        v_upperBound_7133_,
        v_argsPacker_7134_,
        v_e_7135_,
        v_inst_7136_,
        v_R_7137_,
        v_a_7138_,
        v_b_7139_,
        v_c_7140_,
        v___y_7141_,
        v___y_7142_,
        v___y_7143_,
        v___y_7144_,
    );
    lean_dec(v___y_7144_);
    lean_dec_ref(v___y_7143_);
    lean_dec(v___y_7142_);
    lean_dec_ref(v___y_7141_);
    lean_dec_ref(v_argsPacker_7134_);
    lean_dec(v_upperBound_7133_);
    return v_res_7146_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed(
    mut v_a_7147_: *mut LeanObject,
    mut v_argsPacker_7148_: *mut LeanObject,
    mut v_name_7149_: *mut LeanObject,
    mut v_k_7150_: *mut LeanObject,
    mut v_tail_7151_: *mut LeanObject,
    mut v_x_7152_: *mut LeanObject,
    mut v___y_7153_: *mut LeanObject,
    mut v___y_7154_: *mut LeanObject,
    mut v___y_7155_: *mut LeanObject,
    mut v___y_7156_: *mut LeanObject,
    mut v___y_7157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7158_: *mut LeanObject = core::ptr::null_mut();
    v_res_7158_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(v_a_7147_, v_argsPacker_7148_, v_name_7149_, v_k_7150_, v_tail_7151_, v_x_7152_, v___y_7153_, v___y_7154_, v___y_7155_, v___y_7156_);
    lean_dec(v___y_7156_);
    lean_dec_ref(v___y_7155_);
    lean_dec(v___y_7154_);
    lean_dec_ref(v___y_7153_);
    return v_res_7158_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(
    mut v_argsPacker_7159_: *mut LeanObject,
    mut v_name_7160_: *mut LeanObject,
    mut v_k_7161_: *mut LeanObject,
    mut v_a_7162_: *mut LeanObject,
    mut v_a_7163_: *mut LeanObject,
    mut v_a_7164_: *mut LeanObject,
    mut v_a_7165_: *mut LeanObject,
    mut v_a_7166_: *mut LeanObject,
    mut v_a_7167_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_7162_) == 0 {
        let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_name_7160_);
        lean_dec_ref(v_argsPacker_7159_);
        lean_inc(v_a_7167_);
        lean_inc_ref(v_a_7166_);
        lean_inc(v_a_7165_);
        lean_inc_ref(v_a_7164_);
        v___x_7169_ = lean_apply_6(
            v_k_7161_,
            v_a_7163_,
            v_a_7164_,
            v_a_7165_,
            v_a_7166_,
            v_a_7167_,
            lean_box(0),
        );
        return v___x_7169_;
    } else {
        let mut v_head_7170_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_7171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_7172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7175_: u8 = 0;
        v_head_7170_ = lean_ctor_get(v_a_7162_, 0);
        lean_inc(v_head_7170_);
        v_tail_7171_ = lean_ctor_get(v_a_7162_, 1);
        lean_inc(v_tail_7171_);
        lean_dec_ref_known(v_a_7162_, 2);
        lean_inc(v_name_7160_);
        lean_inc_ref(v_argsPacker_7159_);
        lean_inc_ref(v_a_7163_);
        v___f_7172_ = lean_alloc_closure(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
        lean_closure_set(v___f_7172_, 0, v_a_7163_);
        lean_closure_set(v___f_7172_, 1, v_argsPacker_7159_);
        lean_closure_set(v___f_7172_, 2, v_name_7160_);
        lean_closure_set(v___f_7172_, 3, v_k_7161_);
        lean_closure_set(v___f_7172_, 4, v_tail_7171_);
        v___x_7173_ = lean_array_get_size(v_argsPacker_7159_);
        lean_dec_ref(v_argsPacker_7159_);
        v___x_7174_ = lean_unsigned_to_nat(1);
        v___x_7175_ = lean_nat_dec_eq(v___x_7173_, v___x_7174_);
        if v___x_7175_ == 0 {
            let mut v___x_7176_: u8 = 0;
            let mut v___x_7177_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7179_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7180_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7181_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7182_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7184_: *mut LeanObject = core::ptr::null_mut();
            v___x_7176_ = 1;
            v___x_7177_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v_name_7160_,
                v___x_7176_,
            );
            v___x_7178_ = lean_array_get_size(v_a_7163_);
            lean_dec_ref(v_a_7163_);
            v___x_7179_ = lean_nat_add(v___x_7178_, v___x_7174_);
            v___x_7180_ = l_Nat_reprFast(v___x_7179_);
            v___x_7181_ = lean_string_append(v___x_7177_, v___x_7180_);
            lean_dec_ref(v___x_7180_);
            v___x_7182_ = lean_box(0);
            v___x_7183_ = l_Lean_Name_str___override(v___x_7182_, v___x_7181_);
            v___x_7184_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_7183_, v_head_7170_, v___f_7172_, v_a_7164_, v_a_7165_, v_a_7166_, v_a_7167_);
            return v___x_7184_;
        } else {
            let mut v___x_7185_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_a_7163_);
            v___x_7185_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_7160_, v_head_7170_, v___f_7172_, v_a_7164_, v_a_7165_, v_a_7166_, v_a_7167_);
            return v___x_7185_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(
    mut v_a_7186_: *mut LeanObject,
    mut v_argsPacker_7187_: *mut LeanObject,
    mut v_name_7188_: *mut LeanObject,
    mut v_k_7189_: *mut LeanObject,
    mut v_tail_7190_: *mut LeanObject,
    mut v_x_7191_: *mut LeanObject,
    mut v___y_7192_: *mut LeanObject,
    mut v___y_7193_: *mut LeanObject,
    mut v___y_7194_: *mut LeanObject,
    mut v___y_7195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7198_: *mut LeanObject = core::ptr::null_mut();
    v___x_7197_ = lean_array_push(v_a_7186_, v_x_7191_);
    v___x_7198_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(
            v_argsPacker_7187_,
            v_name_7188_,
            v_k_7189_,
            v_tail_7190_,
            v___x_7197_,
            v___y_7192_,
            v___y_7193_,
            v___y_7194_,
            v___y_7195_,
        );
    return v___x_7198_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___boxed(
    mut v_argsPacker_7199_: *mut LeanObject,
    mut v_name_7200_: *mut LeanObject,
    mut v_k_7201_: *mut LeanObject,
    mut v_a_7202_: *mut LeanObject,
    mut v_a_7203_: *mut LeanObject,
    mut v_a_7204_: *mut LeanObject,
    mut v_a_7205_: *mut LeanObject,
    mut v_a_7206_: *mut LeanObject,
    mut v_a_7207_: *mut LeanObject,
    mut v_a_7208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7209_: *mut LeanObject = core::ptr::null_mut();
    v_res_7209_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(
            v_argsPacker_7199_,
            v_name_7200_,
            v_k_7201_,
            v_a_7202_,
            v_a_7203_,
            v_a_7204_,
            v_a_7205_,
            v_a_7206_,
            v_a_7207_,
        );
    lean_dec(v_a_7207_);
    lean_dec_ref(v_a_7206_);
    lean_dec(v_a_7205_);
    lean_dec_ref(v_a_7204_);
    return v_res_7209_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(
    mut v_00_u03b1_7210_: *mut LeanObject,
    mut v_argsPacker_7211_: *mut LeanObject,
    mut v_name_7212_: *mut LeanObject,
    mut v_k_7213_: *mut LeanObject,
    mut v_a_7214_: *mut LeanObject,
    mut v_a_7215_: *mut LeanObject,
    mut v_a_7216_: *mut LeanObject,
    mut v_a_7217_: *mut LeanObject,
    mut v_a_7218_: *mut LeanObject,
    mut v_a_7219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7221_: *mut LeanObject = core::ptr::null_mut();
    v___x_7221_ =
        l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(
            v_argsPacker_7211_,
            v_name_7212_,
            v_k_7213_,
            v_a_7214_,
            v_a_7215_,
            v_a_7216_,
            v_a_7217_,
            v_a_7218_,
            v_a_7219_,
        );
    return v___x_7221_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___boxed(
    mut v_00_u03b1_7222_: *mut LeanObject,
    mut v_argsPacker_7223_: *mut LeanObject,
    mut v_name_7224_: *mut LeanObject,
    mut v_k_7225_: *mut LeanObject,
    mut v_a_7226_: *mut LeanObject,
    mut v_a_7227_: *mut LeanObject,
    mut v_a_7228_: *mut LeanObject,
    mut v_a_7229_: *mut LeanObject,
    mut v_a_7230_: *mut LeanObject,
    mut v_a_7231_: *mut LeanObject,
    mut v_a_7232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7233_: *mut LeanObject = core::ptr::null_mut();
    v_res_7233_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(
        v_00_u03b1_7222_,
        v_argsPacker_7223_,
        v_name_7224_,
        v_k_7225_,
        v_a_7226_,
        v_a_7227_,
        v_a_7228_,
        v_a_7229_,
        v_a_7230_,
        v_a_7231_,
    );
    lean_dec(v_a_7231_);
    lean_dec_ref(v_a_7230_);
    lean_dec(v_a_7229_);
    lean_dec_ref(v_a_7228_);
    return v_res_7233_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(
    mut v_argsPacker_7234_: *mut LeanObject,
    mut v_name_7235_: *mut LeanObject,
    mut v_type_7236_: *mut LeanObject,
    mut v_k_7237_: *mut LeanObject,
    mut v_a_7238_: *mut LeanObject,
    mut v_a_7239_: *mut LeanObject,
    mut v_a_7240_: *mut LeanObject,
    mut v_a_7241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7251_: u8 = 0;
    let mut v___x_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7243_ = l_Lean_Meta_ArgsPacker_curryType(
                    v_argsPacker_7234_,
                    v_type_7236_,
                    v_a_7238_,
                    v_a_7239_,
                    v_a_7240_,
                    v_a_7241_,
                );
                if lean_obj_tag(v___x_7243_) == 0 {
                    v_a_7244_ = lean_ctor_get(v___x_7243_, 0);
                    lean_inc(v_a_7244_);
                    lean_dec_ref_known(v___x_7243_, 1);
                    v___x_7245_ = lean_array_to_list(v_a_7244_);
                    v___x_7246_ = l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0;
                    v___x_7247_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_7234_, v_name_7235_, v_k_7237_, v___x_7245_, v___x_7246_, v_a_7238_, v_a_7239_, v_a_7240_, v_a_7241_);
                    return v___x_7247_;
                } else {
                    lean_dec_ref(v_k_7237_);
                    lean_dec(v_name_7235_);
                    lean_dec_ref(v_argsPacker_7234_);
                    v_a_7248_ = lean_ctor_get(v___x_7243_, 0);
                    v_isSharedCheck_7255_ = (!lean_is_exclusive(v___x_7243_)) as u8;
                    if v_isSharedCheck_7255_ == 0 {
                        v___x_7250_ = v___x_7243_;
                        v_isShared_7251_ = v_isSharedCheck_7255_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7248_);
                        lean_dec(v___x_7243_);
                        v___x_7250_ = lean_box(0);
                        v_isShared_7251_ = v_isSharedCheck_7255_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7251_ == 0 {
                    v___x_7253_ = v___x_7250_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7254_, 0, v_a_7248_);
                    v___x_7253_ = v_reuseFailAlloc_7254_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg___boxed(
    mut v_argsPacker_7256_: *mut LeanObject,
    mut v_name_7257_: *mut LeanObject,
    mut v_type_7258_: *mut LeanObject,
    mut v_k_7259_: *mut LeanObject,
    mut v_a_7260_: *mut LeanObject,
    mut v_a_7261_: *mut LeanObject,
    mut v_a_7262_: *mut LeanObject,
    mut v_a_7263_: *mut LeanObject,
    mut v_a_7264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7265_: *mut LeanObject = core::ptr::null_mut();
    v_res_7265_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(
        v_argsPacker_7256_,
        v_name_7257_,
        v_type_7258_,
        v_k_7259_,
        v_a_7260_,
        v_a_7261_,
        v_a_7262_,
        v_a_7263_,
    );
    lean_dec(v_a_7263_);
    lean_dec_ref(v_a_7262_);
    lean_dec(v_a_7261_);
    lean_dec_ref(v_a_7260_);
    return v_res_7265_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(
    mut v_00_u03b1_7266_: *mut LeanObject,
    mut v_argsPacker_7267_: *mut LeanObject,
    mut v_name_7268_: *mut LeanObject,
    mut v_type_7269_: *mut LeanObject,
    mut v_k_7270_: *mut LeanObject,
    mut v_a_7271_: *mut LeanObject,
    mut v_a_7272_: *mut LeanObject,
    mut v_a_7273_: *mut LeanObject,
    mut v_a_7274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7276_: *mut LeanObject = core::ptr::null_mut();
    v___x_7276_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(
        v_argsPacker_7267_,
        v_name_7268_,
        v_type_7269_,
        v_k_7270_,
        v_a_7271_,
        v_a_7272_,
        v_a_7273_,
        v_a_7274_,
    );
    return v___x_7276_;
}
pub unsafe fn l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___boxed(
    mut v_00_u03b1_7277_: *mut LeanObject,
    mut v_argsPacker_7278_: *mut LeanObject,
    mut v_name_7279_: *mut LeanObject,
    mut v_type_7280_: *mut LeanObject,
    mut v_k_7281_: *mut LeanObject,
    mut v_a_7282_: *mut LeanObject,
    mut v_a_7283_: *mut LeanObject,
    mut v_a_7284_: *mut LeanObject,
    mut v_a_7285_: *mut LeanObject,
    mut v_a_7286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7287_: *mut LeanObject = core::ptr::null_mut();
    v_res_7287_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(
        v_00_u03b1_7277_,
        v_argsPacker_7278_,
        v_name_7279_,
        v_type_7280_,
        v_k_7281_,
        v_a_7282_,
        v_a_7283_,
        v_a_7284_,
        v_a_7285_,
    );
    lean_dec(v_a_7285_);
    lean_dec_ref(v_a_7284_);
    lean_dec(v_a_7283_);
    lean_dec_ref(v_a_7282_);
    return v_res_7287_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(
    mut v_argsPacker_7288_: *mut LeanObject,
    mut v_packedMotiveType_7289_: *mut LeanObject,
    mut v_type_7290_: *mut LeanObject,
    mut v_value_7291_: *mut LeanObject,
    mut v_k_7292_: *mut LeanObject,
    mut v_motives_7293_: *mut LeanObject,
    mut v___y_7294_: *mut LeanObject,
    mut v___y_7295_: *mut LeanObject,
    mut v___y_7296_: *mut LeanObject,
    mut v___y_7297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7311_: u8 = 0;
    let mut v___x_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7315_: u8 = 0;
    let mut v_a_7316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7319_: u8 = 0;
    let mut v___x_7321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7299_ = l_Lean_Meta_ArgsPacker_uncurryWithType(
                    v_argsPacker_7288_,
                    v_packedMotiveType_7289_,
                    v_motives_7293_,
                    v___y_7294_,
                    v___y_7295_,
                    v___y_7296_,
                    v___y_7297_,
                );
                if lean_obj_tag(v___x_7299_) == 0 {
                    v_a_7300_ = lean_ctor_get(v___x_7299_, 0);
                    lean_inc_n(v_a_7300_, 2);
                    lean_dec_ref_known(v___x_7299_, 1);
                    v___x_7301_ = lean_unsigned_to_nat(1);
                    v___x_7302_ = lean_mk_empty_array_with_capacity(v___x_7301_);
                    v___x_7303_ = lean_array_push(v___x_7302_, v_a_7300_);
                    v___x_7304_ = l_Lean_Meta_instantiateForall(
                        v_type_7290_,
                        v___x_7303_,
                        v___y_7294_,
                        v___y_7295_,
                        v___y_7296_,
                        v___y_7297_,
                    );
                    lean_dec_ref(v___x_7303_);
                    if lean_obj_tag(v___x_7304_) == 0 {
                        v_a_7305_ = lean_ctor_get(v___x_7304_, 0);
                        lean_inc(v_a_7305_);
                        lean_dec_ref_known(v___x_7304_, 1);
                        v___x_7306_ = l_Lean_Expr_app___override(v_value_7291_, v_a_7300_);
                        lean_inc(v___y_7297_);
                        lean_inc_ref(v___y_7296_);
                        lean_inc(v___y_7295_);
                        lean_inc_ref(v___y_7294_);
                        v___x_7307_ = lean_apply_8(
                            v_k_7292_,
                            v_motives_7293_,
                            v___x_7306_,
                            v_a_7305_,
                            v___y_7294_,
                            v___y_7295_,
                            v___y_7296_,
                            v___y_7297_,
                            lean_box(0),
                        );
                        return v___x_7307_;
                    } else {
                        lean_dec(v_a_7300_);
                        lean_dec_ref(v_motives_7293_);
                        lean_dec_ref(v_k_7292_);
                        lean_dec_ref(v_value_7291_);
                        v_a_7308_ = lean_ctor_get(v___x_7304_, 0);
                        v_isSharedCheck_7315_ = (!lean_is_exclusive(v___x_7304_)) as u8;
                        if v_isSharedCheck_7315_ == 0 {
                            v___x_7310_ = v___x_7304_;
                            v_isShared_7311_ = v_isSharedCheck_7315_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7308_);
                            lean_dec(v___x_7304_);
                            v___x_7310_ = lean_box(0);
                            v_isShared_7311_ = v_isSharedCheck_7315_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_motives_7293_);
                    lean_dec_ref(v_k_7292_);
                    lean_dec_ref(v_value_7291_);
                    lean_dec_ref(v_type_7290_);
                    v_a_7316_ = lean_ctor_get(v___x_7299_, 0);
                    v_isSharedCheck_7323_ = (!lean_is_exclusive(v___x_7299_)) as u8;
                    if v_isSharedCheck_7323_ == 0 {
                        v___x_7318_ = v___x_7299_;
                        v_isShared_7319_ = v_isSharedCheck_7323_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7316_);
                        lean_dec(v___x_7299_);
                        v___x_7318_ = lean_box(0);
                        v_isShared_7319_ = v_isSharedCheck_7323_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7311_ == 0 {
                    v___x_7313_ = v___x_7310_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7314_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7314_, 0, v_a_7308_);
                    v___x_7313_ = v_reuseFailAlloc_7314_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7313_;
            }
            3 => {
                if v_isShared_7319_ == 0 {
                    v___x_7321_ = v___x_7318_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7322_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7322_, 0, v_a_7316_);
                    v___x_7321_ = v_reuseFailAlloc_7322_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed(
    mut v_argsPacker_7324_: *mut LeanObject,
    mut v_packedMotiveType_7325_: *mut LeanObject,
    mut v_type_7326_: *mut LeanObject,
    mut v_value_7327_: *mut LeanObject,
    mut v_k_7328_: *mut LeanObject,
    mut v_motives_7329_: *mut LeanObject,
    mut v___y_7330_: *mut LeanObject,
    mut v___y_7331_: *mut LeanObject,
    mut v___y_7332_: *mut LeanObject,
    mut v___y_7333_: *mut LeanObject,
    mut v___y_7334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7335_: *mut LeanObject = core::ptr::null_mut();
    v_res_7335_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(
        v_argsPacker_7324_,
        v_packedMotiveType_7325_,
        v_type_7326_,
        v_value_7327_,
        v_k_7328_,
        v_motives_7329_,
        v___y_7330_,
        v___y_7331_,
        v___y_7332_,
        v___y_7333_,
    );
    lean_dec(v___y_7333_);
    lean_dec_ref(v___y_7332_);
    lean_dec(v___y_7331_);
    lean_dec_ref(v___y_7330_);
    lean_dec_ref(v_argsPacker_7324_);
    return v_res_7335_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut LeanObject = core::ptr::null_mut();
    v___x_7337_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0;
    v___x_7338_ = l_Lean_stringToMessageData(v___x_7337_);
    return v___x_7338_;
}
pub unsafe fn _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_7340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut LeanObject = core::ptr::null_mut();
    v___x_7340_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2;
    v___x_7341_ = l_Lean_stringToMessageData(v___x_7340_);
    return v___x_7341_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryParam___redArg(
    mut v_argsPacker_7342_: *mut LeanObject,
    mut v_value_7343_: *mut LeanObject,
    mut v_type_7344_: *mut LeanObject,
    mut v_k_7345_: *mut LeanObject,
    mut v_a_7346_: *mut LeanObject,
    mut v_a_7347_: *mut LeanObject,
    mut v_a_7348_: *mut LeanObject,
    mut v_a_7349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packedMotiveType_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: u8 = 0;
    let mut v___x_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7375_: u8 = 0;
    let mut v___x_7377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7379_: u8 = 0;
    let mut v___x_7380_: u8 = 0;
    let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7388_: u8 = 0;
    let mut v___x_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7380_ = l_Lean_Expr_isForall(v_type_7344_);
                if v___x_7380_ == 0 {
                    lean_dec_ref(v_k_7345_);
                    lean_dec_ref(v_value_7343_);
                    lean_dec_ref(v_argsPacker_7342_);
                    v___x_7381_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3_once
                        ),
                        _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3,
                    );
                    v___x_7382_ = l_Lean_MessageData_ofExpr(v_type_7344_);
                    v___x_7383_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7383_, 0, v___x_7381_);
                    lean_ctor_set(v___x_7383_, 1, v___x_7382_);
                    v___x_7384_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_7383_, v_a_7346_, v_a_7347_, v_a_7348_, v_a_7349_);
                    v_a_7385_ = lean_ctor_get(v___x_7384_, 0);
                    v_isSharedCheck_7392_ = (!lean_is_exclusive(v___x_7384_)) as u8;
                    if v_isSharedCheck_7392_ == 0 {
                        v___x_7387_ = v___x_7384_;
                        v_isShared_7388_ = v_isSharedCheck_7392_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7385_);
                        lean_dec(v___x_7384_);
                        v___x_7387_ = lean_box(0);
                        v_isShared_7388_ = v_isSharedCheck_7392_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___y_7361_ = v_a_7346_;
                    v___y_7362_ = v_a_7347_;
                    v___y_7363_ = v_a_7348_;
                    v___y_7364_ = v_a_7349_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_7358_ = l_Lean_Expr_bindingName_x21(v_type_7344_);
                lean_dec_ref(v_type_7344_);
                v___x_7359_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_7342_, v___x_7358_, v___y_7352_, v___y_7353_, v___y_7354_, v___y_7355_, v___y_7356_, v___y_7357_);
                return v___x_7359_;
            }
            2 => {
                v_packedMotiveType_7365_ = l_Lean_Expr_bindingDomain_x21(v_type_7344_);
                lean_inc_ref(v_type_7344_);
                lean_inc_ref(v_packedMotiveType_7365_);
                lean_inc_ref(v_argsPacker_7342_);
                v___f_7366_ = lean_alloc_closure(
                    l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    11,
                    5,
                );
                lean_closure_set(v___f_7366_, 0, v_argsPacker_7342_);
                lean_closure_set(v___f_7366_, 1, v_packedMotiveType_7365_);
                lean_closure_set(v___f_7366_, 2, v_type_7344_);
                lean_closure_set(v___f_7366_, 3, v_value_7343_);
                lean_closure_set(v___f_7366_, 4, v_k_7345_);
                v___x_7367_ = l_Lean_Expr_isForall(v_packedMotiveType_7365_);
                if v___x_7367_ == 0 {
                    lean_dec_ref(v___f_7366_);
                    lean_dec_ref(v_type_7344_);
                    lean_dec_ref(v_argsPacker_7342_);
                    v___x_7368_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1_once
                        ),
                        _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1,
                    );
                    v___x_7369_ = l_Lean_indentExpr(v_packedMotiveType_7365_);
                    v___x_7370_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7370_, 0, v___x_7368_);
                    lean_ctor_set(v___x_7370_, 1, v___x_7369_);
                    v___x_7371_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_7370_, v___y_7361_, v___y_7362_, v___y_7363_, v___y_7364_);
                    v_a_7372_ = lean_ctor_get(v___x_7371_, 0);
                    v_isSharedCheck_7379_ = (!lean_is_exclusive(v___x_7371_)) as u8;
                    if v_isSharedCheck_7379_ == 0 {
                        v___x_7374_ = v___x_7371_;
                        v_isShared_7375_ = v_isSharedCheck_7379_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7372_);
                        lean_dec(v___x_7371_);
                        v___x_7374_ = lean_box(0);
                        v_isShared_7375_ = v_isSharedCheck_7379_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_7352_ = v_packedMotiveType_7365_;
                    v___y_7353_ = v___f_7366_;
                    v___y_7354_ = v___y_7361_;
                    v___y_7355_ = v___y_7362_;
                    v___y_7356_ = v___y_7363_;
                    v___y_7357_ = v___y_7364_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_7375_ == 0 {
                    v___x_7377_ = v___x_7374_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7378_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7378_, 0, v_a_7372_);
                    v___x_7377_ = v_reuseFailAlloc_7378_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7377_;
            }
            5 => {
                if v_isShared_7388_ == 0 {
                    v___x_7390_ = v___x_7387_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7391_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7391_, 0, v_a_7385_);
                    v___x_7390_ = v_reuseFailAlloc_7391_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryParam___redArg___boxed(
    mut v_argsPacker_7393_: *mut LeanObject,
    mut v_value_7394_: *mut LeanObject,
    mut v_type_7395_: *mut LeanObject,
    mut v_k_7396_: *mut LeanObject,
    mut v_a_7397_: *mut LeanObject,
    mut v_a_7398_: *mut LeanObject,
    mut v_a_7399_: *mut LeanObject,
    mut v_a_7400_: *mut LeanObject,
    mut v_a_7401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7402_: *mut LeanObject = core::ptr::null_mut();
    v_res_7402_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(
        v_argsPacker_7393_,
        v_value_7394_,
        v_type_7395_,
        v_k_7396_,
        v_a_7397_,
        v_a_7398_,
        v_a_7399_,
        v_a_7400_,
    );
    lean_dec(v_a_7400_);
    lean_dec_ref(v_a_7399_);
    lean_dec(v_a_7398_);
    lean_dec_ref(v_a_7397_);
    return v_res_7402_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryParam(
    mut v_00_u03b1_7403_: *mut LeanObject,
    mut v_argsPacker_7404_: *mut LeanObject,
    mut v_value_7405_: *mut LeanObject,
    mut v_type_7406_: *mut LeanObject,
    mut v_k_7407_: *mut LeanObject,
    mut v_a_7408_: *mut LeanObject,
    mut v_a_7409_: *mut LeanObject,
    mut v_a_7410_: *mut LeanObject,
    mut v_a_7411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7413_: *mut LeanObject = core::ptr::null_mut();
    v___x_7413_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(
        v_argsPacker_7404_,
        v_value_7405_,
        v_type_7406_,
        v_k_7407_,
        v_a_7408_,
        v_a_7409_,
        v_a_7410_,
        v_a_7411_,
    );
    return v___x_7413_;
}
pub unsafe fn l_Lean_Meta_ArgsPacker_curryParam___boxed(
    mut v_00_u03b1_7414_: *mut LeanObject,
    mut v_argsPacker_7415_: *mut LeanObject,
    mut v_value_7416_: *mut LeanObject,
    mut v_type_7417_: *mut LeanObject,
    mut v_k_7418_: *mut LeanObject,
    mut v_a_7419_: *mut LeanObject,
    mut v_a_7420_: *mut LeanObject,
    mut v_a_7421_: *mut LeanObject,
    mut v_a_7422_: *mut LeanObject,
    mut v_a_7423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7424_: *mut LeanObject = core::ptr::null_mut();
    v_res_7424_ = l_Lean_Meta_ArgsPacker_curryParam(
        v_00_u03b1_7414_,
        v_argsPacker_7415_,
        v_value_7416_,
        v_type_7417_,
        v_k_7418_,
        v_a_7419_,
        v_a_7420_,
        v_a_7421_,
        v_a_7422_,
    );
    lean_dec(v_a_7422_);
    lean_dec_ref(v_a_7421_);
    lean_dec(v_a_7420_);
    lean_dec_ref(v_a_7419_);
    return v_res_7424_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_ArgsPacker(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_PProdN(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ArgsPacker_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ArgsPacker(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ArgsPacker(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_PProdN(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_ArgsPacker_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ArgsPacker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ArgsPacker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_ArgsPacker(builtin);
}
