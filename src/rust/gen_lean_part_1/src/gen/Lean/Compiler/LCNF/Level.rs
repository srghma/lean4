// Lean compiler output
// Module: Lean.Compiler.LCNF.Level
// Imports: Lean.Util.CollectLevelParams Lean.Compiler.LCNF.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_name_eq, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_panic_fn_borrowed,
    lean_ptr_addr, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat,
    lean_usize_sub,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::l_instInhabitedOfMonad___redArg;
use crate::r#gen::Init::Util::{l_mkPanicMessageWithDecl, l_ptrEqList___redArg};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    initialize_Lean_Compiler_LCNF_Basic, runtime_initialize_Lean_Compiler_LCNF_Basic,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_forallE___override,
    l_Lean_Expr_hasLevelParam, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_instBEqBinderInfo_beq, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_hasParam, l_Lean_Level_param___override, l_Lean_Level_succ___override,
    l_Lean_mkLevelIMax_x27, l_Lean_mkLevelMax_x27, l_Lean_simpLevelIMax_x27,
    l_Lean_simpLevelMax_x27,
};
use crate::r#gen::Lean::Util::CollectLevelParams::{
    initialize_Lean_Util_CollectLevelParams, l_Lean_CollectLevelParams_visitExpr,
    l_Lean_CollectLevelParams_visitLevels, runtime_initialize_Lean_Util_CollectLevelParams,
};
pub static l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0: u64 = 0;
pub static l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [117, 0],
};
static mut l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__0_value)
            as *mut leanh::LeanObject,
        12562556307207860968 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 76,
        101, 118, 101, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__3_value:
    leanh::LeanStringObject<44> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 78,
        111, 114, 109, 76, 101, 118, 101, 108, 80, 97, 114, 97, 109, 46, 110, 111, 114, 109, 76,
        101, 118, 101, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 78,
        111, 114, 109, 76, 101, 118, 101, 108, 80, 97, 114, 97, 109, 46, 110, 111, 114, 109, 69,
        120, 112, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_normLevelParams___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_normLevelParams___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_normLevelParams___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_normLevelParams___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_normLevelParams___closed__2_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_normLevelParams___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_normLevelParams___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_normLevelParams___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_normLevelParams___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(
    mut v_msg_862_: *mut leanh::LeanObject,
    mut v___y_863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193__overap_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_864_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0;
    v___f_865_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1;
    v___f_866_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2;
    v___f_867_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3;
    v___f_868_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4;
    v___f_869_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5;
    v___f_870_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6;
    v___x_871_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_871_, 0, v___f_864_);
    leanh::lean_ctor_set(v___x_871_, 1, v___f_865_);
    v___x_872_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_872_, 0, v___x_871_);
    leanh::lean_ctor_set(v___x_872_, 1, v___f_866_);
    leanh::lean_ctor_set(v___x_872_, 2, v___f_867_);
    leanh::lean_ctor_set(v___x_872_, 3, v___f_868_);
    leanh::lean_ctor_set(v___x_872_, 4, v___f_869_);
    v___x_873_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_873_, 0, v___x_872_);
    leanh::lean_ctor_set(v___x_873_, 1, v___f_870_);
    leanh::lean_inc_ref_n(v___x_873_, 6);
    v___f_874_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_874_, 0, v___x_873_);
    v___f_875_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_875_, 0, v___x_873_);
    v___f_876_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_876_, 0, v___x_873_);
    v___f_877_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_877_, 0, v___x_873_);
    v___x_878_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_878_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_878_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_878_, 2, v___x_873_);
    v___x_879_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_879_, 0, v___x_878_);
    leanh::lean_ctor_set(v___x_879_, 1, v___f_874_);
    v___x_880_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_880_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_880_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_880_, 2, v___x_873_);
    v___x_881_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_881_, 0, v___x_879_);
    leanh::lean_ctor_set(v___x_881_, 1, v___x_880_);
    leanh::lean_ctor_set(v___x_881_, 2, v___f_875_);
    leanh::lean_ctor_set(v___x_881_, 3, v___f_876_);
    leanh::lean_ctor_set(v___x_881_, 4, v___f_877_);
    v___x_882_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_882_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_882_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_882_, 2, v___x_873_);
    v___x_883_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_883_, 0, v___x_881_);
    leanh::lean_ctor_set(v___x_883_, 1, v___x_882_);
    v___x_884_ = leanh::lean_box(0);
    v___x_885_ = l_instInhabitedOfMonad___redArg(v___x_883_, v___x_884_);
    v___x_3193__overap_886_ = lean_panic_fn_borrowed(v___x_885_, v_msg_862_);
    leanh::lean_dec(v___x_885_);
    v___x_887_ = leanh::lean_apply_1(v___x_3193__overap_886_, v___y_863_);
    return v___x_887_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(
    mut v_a_888_: *mut leanh::LeanObject,
    mut v_b_889_: *mut leanh::LeanObject,
    mut v_x_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_896_: u8 = 0;
    let mut v___x_897_: u8 = 0;
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_890_) == 0 {
                    leanh::lean_dec(v_b_889_);
                    leanh::lean_dec(v_a_888_);
                    return v_x_890_;
                } else {
                    v_key_891_ = leanh::lean_ctor_get(v_x_890_, 0);
                    v_value_892_ = leanh::lean_ctor_get(v_x_890_, 1);
                    v_tail_893_ = leanh::lean_ctor_get(v_x_890_, 2);
                    v_isSharedCheck_905_ = (!leanh::lean_is_exclusive(v_x_890_)) as u8;
                    if v_isSharedCheck_905_ == 0 {
                        v___x_895_ = v_x_890_;
                        v_isShared_896_ = v_isSharedCheck_905_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_893_);
                        leanh::lean_inc(v_value_892_);
                        leanh::lean_inc(v_key_891_);
                        leanh::lean_dec(v_x_890_);
                        v___x_895_ = leanh::lean_box(0);
                        v_isShared_896_ = v_isSharedCheck_905_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_897_ = lean_name_eq(v_key_891_, v_a_888_);
                if v___x_897_ == 0 {
                    v___x_898_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_888_, v_b_889_, v_tail_893_);
                    if v_isShared_896_ == 0 {
                        leanh::lean_ctor_set(v___x_895_, 2, v___x_898_);
                        v___x_900_ = v___x_895_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_901_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_901_, 0, v_key_891_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_901_, 1, v_value_892_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_901_, 2, v___x_898_);
                        v___x_900_ = v_reuseFailAlloc_901_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_892_);
                    leanh::lean_dec(v_key_891_);
                    if v_isShared_896_ == 0 {
                        leanh::lean_ctor_set(v___x_895_, 1, v_b_889_);
                        leanh::lean_ctor_set(v___x_895_, 0, v_a_888_);
                        v___x_903_ = v___x_895_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_904_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_888_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_904_, 1, v_b_889_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_904_, 2, v_tail_893_);
                        v___x_903_ = v_reuseFailAlloc_904_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_900_;
            }
            3 => {
                return v___x_903_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0()
-> u64 {
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: u64 = 0;
    v___x_906_ = leanh::lean_unsigned_to_nat(1723);
    v___x_907_ = lean_uint64_of_nat(v___x_906_);
    return v___x_907_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(
    mut v_x_908_: *mut leanh::LeanObject,
    mut v_x_909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_915_: u8 = 0;
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_918_: u64 = 0;
    let mut v___x_919_: u64 = 0;
    let mut v___x_920_: u64 = 0;
    let mut v_fold_921_: u64 = 0;
    let mut v___x_922_: u64 = 0;
    let mut v___x_923_: u64 = 0;
    let mut v___x_924_: u64 = 0;
    let mut v___x_925_: usize = 0;
    let mut v___x_926_: usize = 0;
    let mut v___x_927_: usize = 0;
    let mut v___x_928_: usize = 0;
    let mut v___x_929_: usize = 0;
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: u64 = 0;
    let mut v_hash_937_: u64 = 0;
    let mut v_isSharedCheck_938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_909_) == 0 {
                    return v_x_908_;
                } else {
                    v_key_910_ = leanh::lean_ctor_get(v_x_909_, 0);
                    v_value_911_ = leanh::lean_ctor_get(v_x_909_, 1);
                    v_tail_912_ = leanh::lean_ctor_get(v_x_909_, 2);
                    v_isSharedCheck_938_ = (!leanh::lean_is_exclusive(v_x_909_)) as u8;
                    if v_isSharedCheck_938_ == 0 {
                        v___x_914_ = v_x_909_;
                        v_isShared_915_ = v_isSharedCheck_938_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_912_);
                        leanh::lean_inc(v_value_911_);
                        leanh::lean_inc(v_key_910_);
                        leanh::lean_dec(v_x_909_);
                        v___x_914_ = leanh::lean_box(0);
                        v_isShared_915_ = v_isSharedCheck_938_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_916_ = lean_array_get_size(v_x_908_);
                if leanh::lean_obj_tag(v_key_910_) == 0 {
                    v___x_936_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0);
                    v___y_918_ = v___x_936_;
                    state = 2;
                    continue;
                } else {
                    v_hash_937_ = leanh::lean_ctor_get_uint64(
                        v_key_910_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_918_ = v_hash_937_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_919_ = 32u64;
                v___x_920_ = lean_uint64_shift_right(v___y_918_, v___x_919_);
                v_fold_921_ = lean_uint64_xor(v___y_918_, v___x_920_);
                v___x_922_ = 16u64;
                v___x_923_ = lean_uint64_shift_right(v_fold_921_, v___x_922_);
                v___x_924_ = lean_uint64_xor(v_fold_921_, v___x_923_);
                v___x_925_ = lean_uint64_to_usize(v___x_924_);
                v___x_926_ = lean_usize_of_nat(v___x_916_);
                v___x_927_ = 1usize;
                v___x_928_ = lean_usize_sub(v___x_926_, v___x_927_);
                v___x_929_ = lean_usize_land(v___x_925_, v___x_928_);
                v___x_930_ = lean_array_uget_borrowed(v_x_908_, v___x_929_);
                leanh::lean_inc(v___x_930_);
                if v_isShared_915_ == 0 {
                    leanh::lean_ctor_set(v___x_914_, 2, v___x_930_);
                    v___x_932_ = v___x_914_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_935_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_935_, 0, v_key_910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_935_, 1, v_value_911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_935_, 2, v___x_930_);
                    v___x_932_ = v_reuseFailAlloc_935_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_933_ = lean_array_uset(v_x_908_, v___x_929_, v___x_932_);
                v_x_908_ = v___x_933_;
                v_x_909_ = v_tail_912_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(
    mut v_i_939_: *mut leanh::LeanObject,
    mut v_source_940_: *mut leanh::LeanObject,
    mut v_target_941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: u8 = 0;
    let mut v_es_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_942_ = lean_array_get_size(v_source_940_);
                v___x_943_ = lean_nat_dec_lt(v_i_939_, v___x_942_);
                if v___x_943_ == 0 {
                    leanh::lean_dec_ref(v_source_940_);
                    leanh::lean_dec(v_i_939_);
                    return v_target_941_;
                } else {
                    v_es_944_ = lean_array_fget(v_source_940_, v_i_939_);
                    v___x_945_ = leanh::lean_box(0);
                    v_source_946_ = lean_array_fset(v_source_940_, v_i_939_, v___x_945_);
                    v_target_947_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(v_target_941_, v_es_944_);
                    v___x_948_ = leanh::lean_unsigned_to_nat(1);
                    v___x_949_ = lean_nat_add(v_i_939_, v___x_948_);
                    leanh::lean_dec(v_i_939_);
                    v_i_939_ = v___x_949_;
                    v_source_940_ = v_source_946_;
                    v_target_941_ = v_target_947_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(
    mut v_data_951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = lean_array_get_size(v_data_951_);
    v___x_953_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_954_ = lean_nat_mul(v___x_952_, v___x_953_);
    v___x_955_ = leanh::lean_unsigned_to_nat(0);
    v___x_956_ = leanh::lean_box(0);
    v___x_957_ = lean_mk_array(v_nbuckets_954_, v___x_956_);
    v___x_958_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(v___x_955_, v_data_951_, v___x_957_);
    return v___x_958_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(
    mut v_a_959_: *mut leanh::LeanObject,
    mut v_x_960_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_961_: u8 = 0;
    let mut v_key_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_960_) == 0 {
                    v___x_961_ = 0;
                    return v___x_961_;
                } else {
                    v_key_962_ = leanh::lean_ctor_get(v_x_960_, 0);
                    v_tail_963_ = leanh::lean_ctor_get(v_x_960_, 2);
                    v___x_964_ = lean_name_eq(v_key_962_, v_a_959_);
                    if v___x_964_ == 0 {
                        v_x_960_ = v_tail_963_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_964_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg___boxed(
    mut v_a_966_: *mut leanh::LeanObject,
    mut v_x_967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_968_: u8 = 0;
    let mut v_r_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_968_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_966_, v_x_967_);
    leanh::lean_dec(v_x_967_);
    leanh::lean_dec(v_a_966_);
    v_r_969_ = leanh::lean_box((v_res_968_) as usize);
    return v_r_969_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(
    mut v_m_970_: *mut leanh::LeanObject,
    mut v_a_971_: *mut leanh::LeanObject,
    mut v_b_972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_977_: u8 = 0;
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_980_: u64 = 0;
    let mut v___x_981_: u64 = 0;
    let mut v___x_982_: u64 = 0;
    let mut v_fold_983_: u64 = 0;
    let mut v___x_984_: u64 = 0;
    let mut v___x_985_: u64 = 0;
    let mut v___x_986_: u64 = 0;
    let mut v___x_987_: usize = 0;
    let mut v___x_988_: usize = 0;
    let mut v___x_989_: usize = 0;
    let mut v___x_990_: usize = 0;
    let mut v___x_991_: usize = 0;
    let mut v_bkt_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: u8 = 0;
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u8 = 0;
    let mut v_val_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: u64 = 0;
    let mut v_hash_1019_: u64 = 0;
    let mut v_isSharedCheck_1020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_973_ = leanh::lean_ctor_get(v_m_970_, 0);
                v_buckets_974_ = leanh::lean_ctor_get(v_m_970_, 1);
                v_isSharedCheck_1020_ = (!leanh::lean_is_exclusive(v_m_970_)) as u8;
                if v_isSharedCheck_1020_ == 0 {
                    v___x_976_ = v_m_970_;
                    v_isShared_977_ = v_isSharedCheck_1020_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_974_);
                    leanh::lean_inc(v_size_973_);
                    leanh::lean_dec(v_m_970_);
                    v___x_976_ = leanh::lean_box(0);
                    v_isShared_977_ = v_isSharedCheck_1020_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_978_ = lean_array_get_size(v_buckets_974_);
                if leanh::lean_obj_tag(v_a_971_) == 0 {
                    v___x_1018_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0);
                    v___y_980_ = v___x_1018_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1019_ = leanh::lean_ctor_get_uint64(
                        v_a_971_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_980_ = v_hash_1019_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_981_ = 32u64;
                v___x_982_ = lean_uint64_shift_right(v___y_980_, v___x_981_);
                v_fold_983_ = lean_uint64_xor(v___y_980_, v___x_982_);
                v___x_984_ = 16u64;
                v___x_985_ = lean_uint64_shift_right(v_fold_983_, v___x_984_);
                v___x_986_ = lean_uint64_xor(v_fold_983_, v___x_985_);
                v___x_987_ = lean_uint64_to_usize(v___x_986_);
                v___x_988_ = lean_usize_of_nat(v___x_978_);
                v___x_989_ = 1usize;
                v___x_990_ = lean_usize_sub(v___x_988_, v___x_989_);
                v___x_991_ = lean_usize_land(v___x_987_, v___x_990_);
                v_bkt_992_ = lean_array_uget_borrowed(v_buckets_974_, v___x_991_);
                v___x_993_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_971_, v_bkt_992_);
                if v___x_993_ == 0 {
                    v___x_994_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_995_ = lean_nat_add(v_size_973_, v___x_994_);
                    leanh::lean_dec(v_size_973_);
                    leanh::lean_inc(v_bkt_992_);
                    v___x_996_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_996_, 0, v_a_971_);
                    leanh::lean_ctor_set(v___x_996_, 1, v_b_972_);
                    leanh::lean_ctor_set(v___x_996_, 2, v_bkt_992_);
                    v_buckets_x27_997_ = lean_array_uset(v_buckets_974_, v___x_991_, v___x_996_);
                    v___x_998_ = leanh::lean_unsigned_to_nat(4);
                    v___x_999_ = lean_nat_mul(v_size_x27_995_, v___x_998_);
                    v___x_1000_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1001_ = lean_nat_div(v___x_999_, v___x_1000_);
                    leanh::lean_dec(v___x_999_);
                    v___x_1002_ = lean_array_get_size(v_buckets_x27_997_);
                    v___x_1003_ = lean_nat_dec_le(v___x_1001_, v___x_1002_);
                    leanh::lean_dec(v___x_1001_);
                    if v___x_1003_ == 0 {
                        v_val_1004_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(v_buckets_x27_997_);
                        if v_isShared_977_ == 0 {
                            leanh::lean_ctor_set(v___x_976_, 1, v_val_1004_);
                            leanh::lean_ctor_set(v___x_976_, 0, v_size_x27_995_);
                            v___x_1006_ = v___x_976_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1007_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_size_x27_995_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_val_1004_);
                            v___x_1006_ = v_reuseFailAlloc_1007_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_977_ == 0 {
                            leanh::lean_ctor_set(v___x_976_, 1, v_buckets_x27_997_);
                            leanh::lean_ctor_set(v___x_976_, 0, v_size_x27_995_);
                            v___x_1009_ = v___x_976_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1010_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_size_x27_995_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1010_,
                                1,
                                v_buckets_x27_997_,
                            );
                            v___x_1009_ = v_reuseFailAlloc_1010_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_992_);
                    v___x_1011_ = leanh::lean_box(0);
                    v_buckets_x27_1012_ = lean_array_uset(v_buckets_974_, v___x_991_, v___x_1011_);
                    v___x_1013_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_971_, v_b_972_, v_bkt_992_);
                    v___x_1014_ = lean_array_uset(v_buckets_x27_1012_, v___x_991_, v___x_1013_);
                    if v_isShared_977_ == 0 {
                        leanh::lean_ctor_set(v___x_976_, 1, v___x_1014_);
                        v___x_1016_ = v___x_976_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1017_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_size_973_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1014_);
                        v___x_1016_ = v_reuseFailAlloc_1017_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1006_;
            }
            4 => {
                return v___x_1009_;
            }
            5 => {
                return v___x_1016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(
    mut v_a_1021_: *mut leanh::LeanObject,
    mut v_x_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: u8 = 0;
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1022_) == 0 {
                    v___x_1023_ = leanh::lean_box(0);
                    return v___x_1023_;
                } else {
                    v_key_1024_ = leanh::lean_ctor_get(v_x_1022_, 0);
                    v_value_1025_ = leanh::lean_ctor_get(v_x_1022_, 1);
                    v_tail_1026_ = leanh::lean_ctor_get(v_x_1022_, 2);
                    v___x_1027_ = lean_name_eq(v_key_1024_, v_a_1021_);
                    if v___x_1027_ == 0 {
                        v_x_1022_ = v_tail_1026_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1025_);
                        v___x_1029_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1029_, 0, v_value_1025_);
                        return v___x_1029_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg___boxed(
    mut v_a_1030_: *mut leanh::LeanObject,
    mut v_x_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1032_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_1030_, v_x_1031_);
    leanh::lean_dec(v_x_1031_);
    leanh::lean_dec(v_a_1030_);
    return v_res_1032_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(
    mut v_m_1033_: *mut leanh::LeanObject,
    mut v_a_1034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1038_: u64 = 0;
    let mut v___x_1039_: u64 = 0;
    let mut v___x_1040_: u64 = 0;
    let mut v_fold_1041_: u64 = 0;
    let mut v___x_1042_: u64 = 0;
    let mut v___x_1043_: u64 = 0;
    let mut v___x_1044_: u64 = 0;
    let mut v___x_1045_: usize = 0;
    let mut v___x_1046_: usize = 0;
    let mut v___x_1047_: usize = 0;
    let mut v___x_1048_: usize = 0;
    let mut v___x_1049_: usize = 0;
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: u64 = 0;
    let mut v_hash_1053_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1035_ = leanh::lean_ctor_get(v_m_1033_, 1);
                v___x_1036_ = lean_array_get_size(v_buckets_1035_);
                if leanh::lean_obj_tag(v_a_1034_) == 0 {
                    v___x_1052_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0);
                    v___y_1038_ = v___x_1052_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1053_ = leanh::lean_ctor_get_uint64(
                        v_a_1034_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1038_ = v_hash_1053_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1039_ = 32u64;
                v___x_1040_ = lean_uint64_shift_right(v___y_1038_, v___x_1039_);
                v_fold_1041_ = lean_uint64_xor(v___y_1038_, v___x_1040_);
                v___x_1042_ = 16u64;
                v___x_1043_ = lean_uint64_shift_right(v_fold_1041_, v___x_1042_);
                v___x_1044_ = lean_uint64_xor(v_fold_1041_, v___x_1043_);
                v___x_1045_ = lean_uint64_to_usize(v___x_1044_);
                v___x_1046_ = lean_usize_of_nat(v___x_1036_);
                v___x_1047_ = 1usize;
                v___x_1048_ = lean_usize_sub(v___x_1046_, v___x_1047_);
                v___x_1049_ = lean_usize_land(v___x_1045_, v___x_1048_);
                v___x_1050_ = lean_array_uget_borrowed(v_buckets_1035_, v___x_1049_);
                v___x_1051_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_1034_, v___x_1050_);
                return v___x_1051_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg___boxed(
    mut v_m_1054_: *mut leanh::LeanObject,
    mut v_a_1055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_1054_, v_a_1055_);
    leanh::lean_dec(v_a_1055_);
    leanh::lean_dec_ref(v_m_1054_);
    return v_res_1056_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1063_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4;
    v___x_1064_ = leanh::lean_unsigned_to_nat(19);
    v___x_1065_ = leanh::lean_unsigned_to_nat(55);
    v___x_1066_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__3;
    v___x_1067_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2;
    v___x_1068_ = l_mkPanicMessageWithDecl(
        v___x_1067_,
        v___x_1066_,
        v___x_1065_,
        v___x_1064_,
        v___x_1063_,
    );
    return v___x_1068_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormLevelParam_normLevel(
    mut v_u_1069_: *mut leanh::LeanObject,
    mut v_a_1070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1071_: u8 = 0;
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v___x_1081_: usize = 0;
    let mut v___x_1082_: usize = 0;
    let mut v___x_1083_: u8 = 0;
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1091_: u8 = 0;
    let mut v_a_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1102_: u8 = 0;
    let mut v___y_1104_: u8 = 0;
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: usize = 0;
    let mut v___x_1114_: usize = 0;
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1116_: usize = 0;
    let mut v___x_1117_: usize = 0;
    let mut v___x_1118_: u8 = 0;
    let mut v_isSharedCheck_1119_: u8 = 0;
    let mut v_a_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1130_: u8 = 0;
    let mut v___y_1132_: u8 = 0;
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: usize = 0;
    let mut v___x_1142_: usize = 0;
    let mut v___x_1143_: u8 = 0;
    let mut v___x_1144_: usize = 0;
    let mut v___x_1145_: usize = 0;
    let mut v___x_1146_: u8 = 0;
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_a_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1155_: u8 = 0;
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut v_unused_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1071_ = l_Lean_Level_hasParam(v_u_1069_);
                if v___x_1071_ == 0 {
                    v___x_1072_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1072_, 0, v_u_1069_);
                    leanh::lean_ctor_set(v___x_1072_, 1, v_a_1070_);
                    return v___x_1072_;
                } else {
                    match leanh::lean_obj_tag(v_u_1069_) {
                        0 => {
                            v___x_1073_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1073_, 0, v_u_1069_);
                            leanh::lean_ctor_set(v___x_1073_, 1, v_a_1070_);
                            return v___x_1073_;
                        }
                        1 => {
                            v_a_1074_ = leanh::lean_ctor_get(v_u_1069_, 0);
                            leanh::lean_inc(v_a_1074_);
                            v___x_1075_ =
                                l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_1074_, v_a_1070_);
                            v_fst_1076_ = leanh::lean_ctor_get(v___x_1075_, 0);
                            v_snd_1077_ = leanh::lean_ctor_get(v___x_1075_, 1);
                            v_isSharedCheck_1091_ =
                                (!leanh::lean_is_exclusive(v___x_1075_)) as u8;
                            if v_isSharedCheck_1091_ == 0 {
                                v___x_1079_ = v___x_1075_;
                                v_isShared_1080_ = v_isSharedCheck_1091_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1077_);
                                leanh::lean_inc(v_fst_1076_);
                                leanh::lean_dec(v___x_1075_);
                                v___x_1079_ = leanh::lean_box(0);
                                v_isShared_1080_ = v_isSharedCheck_1091_;
                                state = 1;
                                continue;
                            }
                        }
                        2 => {
                            v_a_1092_ = leanh::lean_ctor_get(v_u_1069_, 0);
                            v_a_1093_ = leanh::lean_ctor_get(v_u_1069_, 1);
                            leanh::lean_inc(v_a_1092_);
                            v___x_1094_ =
                                l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_1092_, v_a_1070_);
                            v_fst_1095_ = leanh::lean_ctor_get(v___x_1094_, 0);
                            leanh::lean_inc(v_fst_1095_);
                            v_snd_1096_ = leanh::lean_ctor_get(v___x_1094_, 1);
                            leanh::lean_inc(v_snd_1096_);
                            leanh::lean_dec_ref(v___x_1094_);
                            leanh::lean_inc(v_a_1093_);
                            v___x_1097_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(
                                v_a_1093_,
                                v_snd_1096_,
                            );
                            v_fst_1098_ = leanh::lean_ctor_get(v___x_1097_, 0);
                            v_snd_1099_ = leanh::lean_ctor_get(v___x_1097_, 1);
                            v_isSharedCheck_1119_ =
                                (!leanh::lean_is_exclusive(v___x_1097_)) as u8;
                            if v_isSharedCheck_1119_ == 0 {
                                v___x_1101_ = v___x_1097_;
                                v_isShared_1102_ = v_isSharedCheck_1119_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1099_);
                                leanh::lean_inc(v_fst_1098_);
                                leanh::lean_dec(v___x_1097_);
                                v___x_1101_ = leanh::lean_box(0);
                                v_isShared_1102_ = v_isSharedCheck_1119_;
                                state = 4;
                                continue;
                            }
                        }
                        3 => {
                            v_a_1120_ = leanh::lean_ctor_get(v_u_1069_, 0);
                            v_a_1121_ = leanh::lean_ctor_get(v_u_1069_, 1);
                            leanh::lean_inc(v_a_1120_);
                            v___x_1122_ =
                                l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_1120_, v_a_1070_);
                            v_fst_1123_ = leanh::lean_ctor_get(v___x_1122_, 0);
                            leanh::lean_inc(v_fst_1123_);
                            v_snd_1124_ = leanh::lean_ctor_get(v___x_1122_, 1);
                            leanh::lean_inc(v_snd_1124_);
                            leanh::lean_dec_ref(v___x_1122_);
                            leanh::lean_inc(v_a_1121_);
                            v___x_1125_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(
                                v_a_1121_,
                                v_snd_1124_,
                            );
                            v_fst_1126_ = leanh::lean_ctor_get(v___x_1125_, 0);
                            v_snd_1127_ = leanh::lean_ctor_get(v___x_1125_, 1);
                            v_isSharedCheck_1147_ =
                                (!leanh::lean_is_exclusive(v___x_1125_)) as u8;
                            if v_isSharedCheck_1147_ == 0 {
                                v___x_1129_ = v___x_1125_;
                                v_isShared_1130_ = v_isSharedCheck_1147_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1127_);
                                leanh::lean_inc(v_fst_1126_);
                                leanh::lean_dec(v___x_1125_);
                                v___x_1129_ = leanh::lean_box(0);
                                v_isShared_1130_ = v_isSharedCheck_1147_;
                                state = 8;
                                continue;
                            }
                        }
                        4 => {
                            v_a_1148_ = leanh::lean_ctor_get(v_u_1069_, 0);
                            leanh::lean_inc(v_a_1148_);
                            leanh::lean_dec_ref_known(v_u_1069_, 1);
                            v_nextIdx_1149_ = leanh::lean_ctor_get(v_a_1070_, 0);
                            v_map_1150_ = leanh::lean_ctor_get(v_a_1070_, 1);
                            v_paramNames_1151_ = leanh::lean_ctor_get(v_a_1070_, 2);
                            v___x_1152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_map_1150_, v_a_1148_);
                            if leanh::lean_obj_tag(v___x_1152_) == 0 {
                                leanh::lean_inc_ref(v_paramNames_1151_);
                                leanh::lean_inc_ref(v_map_1150_);
                                leanh::lean_inc(v_nextIdx_1149_);
                                v_isSharedCheck_1167_ =
                                    (!leanh::lean_is_exclusive(v_a_1070_)) as u8;
                                if v_isSharedCheck_1167_ == 0 {
                                    v_unused_1168_ = leanh::lean_ctor_get(v_a_1070_, 2);
                                    leanh::lean_dec(v_unused_1168_);
                                    v_unused_1169_ = leanh::lean_ctor_get(v_a_1070_, 1);
                                    leanh::lean_dec(v_unused_1169_);
                                    v_unused_1170_ = leanh::lean_ctor_get(v_a_1070_, 0);
                                    leanh::lean_dec(v_unused_1170_);
                                    v___x_1154_ = v_a_1070_;
                                    v_isShared_1155_ = v_isSharedCheck_1167_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_1070_);
                                    v___x_1154_ = leanh::lean_box(0);
                                    v_isShared_1155_ = v_isSharedCheck_1167_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_1148_);
                                v_val_1171_ = leanh::lean_ctor_get(v___x_1152_, 0);
                                leanh::lean_inc(v_val_1171_);
                                leanh::lean_dec_ref_known(v___x_1152_, 1);
                                v___x_1172_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1172_, 0, v_val_1171_);
                                leanh::lean_ctor_set(v___x_1172_, 1, v_a_1070_);
                                return v___x_1172_;
                            }
                        }
                        _ => {
                            leanh::lean_dec_ref_known(v_u_1069_, 1);
                            v___x_1173_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5_once
                                ),
                                _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5,
                            );
                            v___x_1174_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(v___x_1173_, v_a_1070_);
                            return v___x_1174_;
                        }
                    }
                }
            }
            1 => {
                v___x_1081_ = lean_ptr_addr(v_a_1074_);
                v___x_1082_ = lean_ptr_addr(v_fst_1076_);
                v___x_1083_ = lean_usize_dec_eq(v___x_1081_, v___x_1082_);
                if v___x_1083_ == 0 {
                    leanh::lean_dec_ref_known(v_u_1069_, 1);
                    v___x_1084_ = l_Lean_Level_succ___override(v_fst_1076_);
                    if v_isShared_1080_ == 0 {
                        leanh::lean_ctor_set(v___x_1079_, 0, v___x_1084_);
                        v___x_1086_ = v___x_1079_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1087_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_snd_1077_);
                        v___x_1086_ = v_reuseFailAlloc_1087_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1076_);
                    if v_isShared_1080_ == 0 {
                        leanh::lean_ctor_set(v___x_1079_, 0, v_u_1069_);
                        v___x_1089_ = v___x_1079_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1090_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_u_1069_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_snd_1077_);
                        v___x_1089_ = v_reuseFailAlloc_1090_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1086_;
            }
            3 => {
                return v___x_1089_;
            }
            4 => {
                v___x_1113_ = lean_ptr_addr(v_a_1092_);
                v___x_1114_ = lean_ptr_addr(v_fst_1095_);
                v___x_1115_ = lean_usize_dec_eq(v___x_1113_, v___x_1114_);
                if v___x_1115_ == 0 {
                    v___y_1104_ = v___x_1115_;
                    state = 5;
                    continue;
                } else {
                    v___x_1116_ = lean_ptr_addr(v_a_1093_);
                    v___x_1117_ = lean_ptr_addr(v_fst_1098_);
                    v___x_1118_ = lean_usize_dec_eq(v___x_1116_, v___x_1117_);
                    v___y_1104_ = v___x_1118_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_1104_ == 0 {
                    leanh::lean_dec_ref_known(v_u_1069_, 2);
                    v___x_1105_ = l_Lean_mkLevelMax_x27(v_fst_1095_, v_fst_1098_);
                    if v_isShared_1102_ == 0 {
                        leanh::lean_ctor_set(v___x_1101_, 0, v___x_1105_);
                        v___x_1107_ = v___x_1101_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1108_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_snd_1099_);
                        v___x_1107_ = v_reuseFailAlloc_1108_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_1109_ = l_Lean_simpLevelMax_x27(v_fst_1095_, v_fst_1098_, v_u_1069_);
                    leanh::lean_dec_ref_known(v_u_1069_, 2);
                    leanh::lean_dec(v_fst_1098_);
                    leanh::lean_dec(v_fst_1095_);
                    if v_isShared_1102_ == 0 {
                        leanh::lean_ctor_set(v___x_1101_, 0, v___x_1109_);
                        v___x_1111_ = v___x_1101_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1112_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_snd_1099_);
                        v___x_1111_ = v_reuseFailAlloc_1112_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1107_;
            }
            7 => {
                return v___x_1111_;
            }
            8 => {
                v___x_1141_ = lean_ptr_addr(v_a_1120_);
                v___x_1142_ = lean_ptr_addr(v_fst_1123_);
                v___x_1143_ = lean_usize_dec_eq(v___x_1141_, v___x_1142_);
                if v___x_1143_ == 0 {
                    v___y_1132_ = v___x_1143_;
                    state = 9;
                    continue;
                } else {
                    v___x_1144_ = lean_ptr_addr(v_a_1121_);
                    v___x_1145_ = lean_ptr_addr(v_fst_1126_);
                    v___x_1146_ = lean_usize_dec_eq(v___x_1144_, v___x_1145_);
                    v___y_1132_ = v___x_1146_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v___y_1132_ == 0 {
                    leanh::lean_dec_ref_known(v_u_1069_, 2);
                    v___x_1133_ = l_Lean_mkLevelIMax_x27(v_fst_1123_, v_fst_1126_);
                    if v_isShared_1130_ == 0 {
                        leanh::lean_ctor_set(v___x_1129_, 0, v___x_1133_);
                        v___x_1135_ = v___x_1129_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1136_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_snd_1127_);
                        v___x_1135_ = v_reuseFailAlloc_1136_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___x_1137_ = l_Lean_simpLevelIMax_x27(v_fst_1123_, v_fst_1126_, v_u_1069_);
                    leanh::lean_dec_ref_known(v_u_1069_, 2);
                    if v_isShared_1130_ == 0 {
                        leanh::lean_ctor_set(v___x_1129_, 0, v___x_1137_);
                        v___x_1139_ = v___x_1129_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1140_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_snd_1127_);
                        v___x_1139_ = v_reuseFailAlloc_1140_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_1135_;
            }
            11 => {
                return v___x_1139_;
            }
            12 => {
                v___x_1156_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1;
                leanh::lean_inc(v_nextIdx_1149_);
                v___x_1157_ = lean_name_append_index_after(v___x_1156_, v_nextIdx_1149_);
                v___x_1158_ = l_Lean_Level_param___override(v___x_1157_);
                v___x_1159_ = leanh::lean_unsigned_to_nat(1);
                v___x_1160_ = lean_nat_add(v_nextIdx_1149_, v___x_1159_);
                leanh::lean_dec(v_nextIdx_1149_);
                leanh::lean_inc(v___x_1158_);
                leanh::lean_inc(v_a_1148_);
                v___x_1161_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_map_1150_, v_a_1148_, v___x_1158_);
                v___x_1162_ = lean_array_push(v_paramNames_1151_, v_a_1148_);
                if v_isShared_1155_ == 0 {
                    leanh::lean_ctor_set(v___x_1154_, 2, v___x_1162_);
                    leanh::lean_ctor_set(v___x_1154_, 1, v___x_1161_);
                    leanh::lean_ctor_set(v___x_1154_, 0, v___x_1160_);
                    v___x_1164_ = v___x_1154_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1166_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1161_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 2, v___x_1162_);
                    v___x_1164_ = v_reuseFailAlloc_1166_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1165_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1165_, 0, v___x_1158_);
                leanh::lean_ctor_set(v___x_1165_, 1, v___x_1164_);
                return v___x_1165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(
    mut v_00_u03b2_1175_: *mut leanh::LeanObject,
    mut v_m_1176_: *mut leanh::LeanObject,
    mut v_a_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_1176_, v_a_1177_);
    return v___x_1178_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___boxed(
    mut v_00_u03b2_1179_: *mut leanh::LeanObject,
    mut v_m_1180_: *mut leanh::LeanObject,
    mut v_a_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1182_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(v_00_u03b2_1179_, v_m_1180_, v_a_1181_);
    leanh::lean_dec(v_a_1181_);
    leanh::lean_dec_ref(v_m_1180_);
    return v_res_1182_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1(
    mut v_00_u03b2_1183_: *mut leanh::LeanObject,
    mut v_m_1184_: *mut leanh::LeanObject,
    mut v_a_1185_: *mut leanh::LeanObject,
    mut v_b_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1187_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_m_1184_, v_a_1185_, v_b_1186_);
    return v___x_1187_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(
    mut v_00_u03b2_1188_: *mut leanh::LeanObject,
    mut v_a_1189_: *mut leanh::LeanObject,
    mut v_x_1190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1191_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_1189_, v_x_1190_);
    return v___x_1191_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___boxed(
    mut v_00_u03b2_1192_: *mut leanh::LeanObject,
    mut v_a_1193_: *mut leanh::LeanObject,
    mut v_x_1194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1195_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(v_00_u03b2_1192_, v_a_1193_, v_x_1194_);
    leanh::lean_dec(v_x_1194_);
    leanh::lean_dec(v_a_1193_);
    return v_res_1195_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(
    mut v_00_u03b2_1196_: *mut leanh::LeanObject,
    mut v_a_1197_: *mut leanh::LeanObject,
    mut v_x_1198_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1199_: u8 = 0;
    v___x_1199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_1197_, v_x_1198_);
    return v___x_1199_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___boxed(
    mut v_00_u03b2_1200_: *mut leanh::LeanObject,
    mut v_a_1201_: *mut leanh::LeanObject,
    mut v_x_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1203_: u8 = 0;
    let mut v_r_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1203_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(v_00_u03b2_1200_, v_a_1201_, v_x_1202_);
    leanh::lean_dec(v_x_1202_);
    leanh::lean_dec(v_a_1201_);
    v_r_1204_ = leanh::lean_box((v_res_1203_) as usize);
    return v_r_1204_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3(
    mut v_00_u03b2_1205_: *mut leanh::LeanObject,
    mut v_data_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1207_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(v_data_1206_);
    return v___x_1207_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4(
    mut v_00_u03b2_1208_: *mut leanh::LeanObject,
    mut v_a_1209_: *mut leanh::LeanObject,
    mut v_b_1210_: *mut leanh::LeanObject,
    mut v_x_1211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_1209_, v_b_1210_, v_x_1211_);
    return v___x_1212_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5(
    mut v_00_u03b2_1213_: *mut leanh::LeanObject,
    mut v_i_1214_: *mut leanh::LeanObject,
    mut v_source_1215_: *mut leanh::LeanObject,
    mut v_target_1216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(v_i_1214_, v_source_1215_, v_target_1216_);
    return v___x_1217_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6(
    mut v_00_u03b2_1218_: *mut leanh::LeanObject,
    mut v_x_1219_: *mut leanh::LeanObject,
    mut v_x_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(v_x_1219_, v_x_1220_);
    return v___x_1221_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(
    mut v_msg_1222_: *mut leanh::LeanObject,
    mut v___y_1223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181__overap_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1224_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0;
    v___f_1225_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1;
    v___f_1226_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2;
    v___f_1227_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3;
    v___f_1228_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4;
    v___f_1229_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5;
    v___f_1230_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6;
    v___x_1231_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1231_, 0, v___f_1224_);
    leanh::lean_ctor_set(v___x_1231_, 1, v___f_1225_);
    v___x_1232_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1232_, 0, v___x_1231_);
    leanh::lean_ctor_set(v___x_1232_, 1, v___f_1226_);
    leanh::lean_ctor_set(v___x_1232_, 2, v___f_1227_);
    leanh::lean_ctor_set(v___x_1232_, 3, v___f_1228_);
    leanh::lean_ctor_set(v___x_1232_, 4, v___f_1229_);
    v___x_1233_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1233_, 0, v___x_1232_);
    leanh::lean_ctor_set(v___x_1233_, 1, v___f_1230_);
    leanh::lean_inc_ref_n(v___x_1233_, 6);
    v___f_1234_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1234_, 0, v___x_1233_);
    v___f_1235_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1235_, 0, v___x_1233_);
    v___f_1236_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1236_, 0, v___x_1233_);
    v___f_1237_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1237_, 0, v___x_1233_);
    v___x_1238_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_1238_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1238_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1238_, 2, v___x_1233_);
    v___x_1239_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1239_, 0, v___x_1238_);
    leanh::lean_ctor_set(v___x_1239_, 1, v___f_1234_);
    v___x_1240_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_1240_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1240_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1240_, 2, v___x_1233_);
    v___x_1241_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1241_, 0, v___x_1239_);
    leanh::lean_ctor_set(v___x_1241_, 1, v___x_1240_);
    leanh::lean_ctor_set(v___x_1241_, 2, v___f_1235_);
    leanh::lean_ctor_set(v___x_1241_, 3, v___f_1236_);
    leanh::lean_ctor_set(v___x_1241_, 4, v___f_1237_);
    v___x_1242_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_1242_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1242_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1242_, 2, v___x_1233_);
    v___x_1243_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1243_, 0, v___x_1241_);
    leanh::lean_ctor_set(v___x_1243_, 1, v___x_1242_);
    v___x_1244_ = l_Lean_instInhabitedExpr;
    v___x_1245_ = l_instInhabitedOfMonad___redArg(v___x_1243_, v___x_1244_);
    v___x_5181__overap_1246_ = lean_panic_fn_borrowed(v___x_1245_, v_msg_1222_);
    leanh::lean_dec(v___x_1245_);
    v___x_1247_ = leanh::lean_apply_1(v___x_5181__overap_1246_, v___y_1223_);
    return v___x_1247_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(
    mut v_x_1248_: *mut leanh::LeanObject,
    mut v_x_1249_: *mut leanh::LeanObject,
    mut v___y_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1257_: u8 = 0;
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1248_) == 0 {
                    v___x_1251_ = l_List_reverse___redArg(v_x_1249_);
                    v___x_1252_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1252_, 0, v___x_1251_);
                    leanh::lean_ctor_set(v___x_1252_, 1, v___y_1250_);
                    return v___x_1252_;
                } else {
                    v_head_1253_ = leanh::lean_ctor_get(v_x_1248_, 0);
                    v_tail_1254_ = leanh::lean_ctor_get(v_x_1248_, 1);
                    v_isSharedCheck_1265_ = (!leanh::lean_is_exclusive(v_x_1248_)) as u8;
                    if v_isSharedCheck_1265_ == 0 {
                        v___x_1256_ = v_x_1248_;
                        v_isShared_1257_ = v_isSharedCheck_1265_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1254_);
                        leanh::lean_inc(v_head_1253_);
                        leanh::lean_dec(v_x_1248_);
                        v___x_1256_ = leanh::lean_box(0);
                        v_isShared_1257_ = v_isSharedCheck_1265_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1258_ =
                    l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_head_1253_, v___y_1250_);
                v_fst_1259_ = leanh::lean_ctor_get(v___x_1258_, 0);
                leanh::lean_inc(v_fst_1259_);
                v_snd_1260_ = leanh::lean_ctor_get(v___x_1258_, 1);
                leanh::lean_inc(v_snd_1260_);
                leanh::lean_dec_ref(v___x_1258_);
                if v_isShared_1257_ == 0 {
                    leanh::lean_ctor_set(v___x_1256_, 1, v_x_1249_);
                    leanh::lean_ctor_set(v___x_1256_, 0, v_fst_1259_);
                    v___x_1262_ = v___x_1256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1264_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_fst_1259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_x_1249_);
                    v___x_1262_ = v_reuseFailAlloc_1264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_1248_ = v_tail_1254_;
                v_x_1249_ = v___x_1262_;
                v___y_1250_ = v_snd_1260_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1267_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4;
    v___x_1268_ = leanh::lean_unsigned_to_nat(26);
    v___x_1269_ = leanh::lean_unsigned_to_nat(79);
    v___x_1270_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0;
    v___x_1271_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2;
    v___x_1272_ = l_mkPanicMessageWithDecl(
        v___x_1271_,
        v___x_1270_,
        v___x_1269_,
        v___x_1268_,
        v___x_1267_,
    );
    return v___x_1272_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormLevelParam_normExpr(
    mut v_e_1273_: *mut leanh::LeanObject,
    mut v_a_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1275_: u8 = 0;
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1285_: u8 = 0;
    let mut v___x_1286_: u8 = 0;
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut v_u_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1301_: u8 = 0;
    let mut v___x_1302_: usize = 0;
    let mut v___x_1303_: usize = 0;
    let mut v___x_1304_: u8 = 0;
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1312_: u8 = 0;
    let mut v_fn_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1323_: u8 = 0;
    let mut v___y_1325_: u8 = 0;
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: usize = 0;
    let mut v___x_1334_: usize = 0;
    let mut v___x_1335_: u8 = 0;
    let mut v___x_1336_: usize = 0;
    let mut v___x_1337_: usize = 0;
    let mut v___x_1338_: u8 = 0;
    let mut v_isSharedCheck_1339_: u8 = 0;
    let mut v_declName_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1344_: u8 = 0;
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1356_: u8 = 0;
    let mut v___y_1358_: u8 = 0;
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: usize = 0;
    let mut v___x_1364_: usize = 0;
    let mut v___x_1365_: u8 = 0;
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: usize = 0;
    let mut v___x_1374_: usize = 0;
    let mut v___x_1375_: u8 = 0;
    let mut v___x_1376_: usize = 0;
    let mut v___x_1377_: usize = 0;
    let mut v___x_1378_: u8 = 0;
    let mut v_isSharedCheck_1379_: u8 = 0;
    let mut v_binderName_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1383_: u8 = 0;
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1392_: u8 = 0;
    let mut v___y_1394_: u8 = 0;
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: u8 = 0;
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: usize = 0;
    let mut v___x_1408_: usize = 0;
    let mut v___x_1409_: u8 = 0;
    let mut v___x_1410_: usize = 0;
    let mut v___x_1411_: usize = 0;
    let mut v___x_1412_: u8 = 0;
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut v_binderName_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1417_: u8 = 0;
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1426_: u8 = 0;
    let mut v___y_1428_: u8 = 0;
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: usize = 0;
    let mut v___x_1442_: usize = 0;
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: usize = 0;
    let mut v___x_1445_: usize = 0;
    let mut v___x_1446_: u8 = 0;
    let mut v_isSharedCheck_1447_: u8 = 0;
    let mut v_data_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1455_: u8 = 0;
    let mut v___x_1456_: usize = 0;
    let mut v___x_1457_: usize = 0;
    let mut v___x_1458_: u8 = 0;
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1466_: u8 = 0;
    let mut v_typeName_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: usize = 0;
    let mut v___x_1477_: usize = 0;
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1275_ = l_Lean_Expr_hasLevelParam(v_e_1273_);
                if v___x_1275_ == 0 {
                    v___x_1276_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1276_, 0, v_e_1273_);
                    leanh::lean_ctor_set(v___x_1276_, 1, v_a_1274_);
                    return v___x_1276_;
                } else {
                    match leanh::lean_obj_tag(v_e_1273_) {
                        4 => {
                            v_declName_1277_ = leanh::lean_ctor_get(v_e_1273_, 0);
                            v_us_1278_ = leanh::lean_ctor_get(v_e_1273_, 1);
                            v___x_1279_ = leanh::lean_box(0);
                            leanh::lean_inc(v_us_1278_);
                            v___x_1280_ = l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(v_us_1278_, v___x_1279_, v_a_1274_);
                            v_fst_1281_ = leanh::lean_ctor_get(v___x_1280_, 0);
                            v_snd_1282_ = leanh::lean_ctor_get(v___x_1280_, 1);
                            v_isSharedCheck_1294_ =
                                (!leanh::lean_is_exclusive(v___x_1280_)) as u8;
                            if v_isSharedCheck_1294_ == 0 {
                                v___x_1284_ = v___x_1280_;
                                v_isShared_1285_ = v_isSharedCheck_1294_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1282_);
                                leanh::lean_inc(v_fst_1281_);
                                leanh::lean_dec(v___x_1280_);
                                v___x_1284_ = leanh::lean_box(0);
                                v_isShared_1285_ = v_isSharedCheck_1294_;
                                state = 1;
                                continue;
                            }
                        }
                        3 => {
                            v_u_1295_ = leanh::lean_ctor_get(v_e_1273_, 0);
                            leanh::lean_inc(v_u_1295_);
                            v___x_1296_ =
                                l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_u_1295_, v_a_1274_);
                            v_fst_1297_ = leanh::lean_ctor_get(v___x_1296_, 0);
                            v_snd_1298_ = leanh::lean_ctor_get(v___x_1296_, 1);
                            v_isSharedCheck_1312_ =
                                (!leanh::lean_is_exclusive(v___x_1296_)) as u8;
                            if v_isSharedCheck_1312_ == 0 {
                                v___x_1300_ = v___x_1296_;
                                v_isShared_1301_ = v_isSharedCheck_1312_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1298_);
                                leanh::lean_inc(v_fst_1297_);
                                leanh::lean_dec(v___x_1296_);
                                v___x_1300_ = leanh::lean_box(0);
                                v_isShared_1301_ = v_isSharedCheck_1312_;
                                state = 4;
                                continue;
                            }
                        }
                        5 => {
                            v_fn_1313_ = leanh::lean_ctor_get(v_e_1273_, 0);
                            v_arg_1314_ = leanh::lean_ctor_get(v_e_1273_, 1);
                            leanh::lean_inc_ref(v_fn_1313_);
                            v___x_1315_ =
                                l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_fn_1313_, v_a_1274_);
                            v_fst_1316_ = leanh::lean_ctor_get(v___x_1315_, 0);
                            leanh::lean_inc(v_fst_1316_);
                            v_snd_1317_ = leanh::lean_ctor_get(v___x_1315_, 1);
                            leanh::lean_inc(v_snd_1317_);
                            leanh::lean_dec_ref(v___x_1315_);
                            leanh::lean_inc_ref(v_arg_1314_);
                            v___x_1318_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(
                                v_arg_1314_,
                                v_snd_1317_,
                            );
                            v_fst_1319_ = leanh::lean_ctor_get(v___x_1318_, 0);
                            v_snd_1320_ = leanh::lean_ctor_get(v___x_1318_, 1);
                            v_isSharedCheck_1339_ =
                                (!leanh::lean_is_exclusive(v___x_1318_)) as u8;
                            if v_isSharedCheck_1339_ == 0 {
                                v___x_1322_ = v___x_1318_;
                                v_isShared_1323_ = v_isSharedCheck_1339_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1320_);
                                leanh::lean_inc(v_fst_1319_);
                                leanh::lean_dec(v___x_1318_);
                                v___x_1322_ = leanh::lean_box(0);
                                v_isShared_1323_ = v_isSharedCheck_1339_;
                                state = 7;
                                continue;
                            }
                        }
                        8 => {
                            v_declName_1340_ = leanh::lean_ctor_get(v_e_1273_, 0);
                            v_type_1341_ = leanh::lean_ctor_get(v_e_1273_, 1);
                            v_value_1342_ = leanh::lean_ctor_get(v_e_1273_, 2);
                            v_body_1343_ = leanh::lean_ctor_get(v_e_1273_, 3);
                            v_nondep_1344_ = leanh::lean_ctor_get_uint8(
                                v_e_1273_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8)
                                    as u32,
                            );
                            leanh::lean_inc_ref(v_type_1341_);
                            v___x_1345_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(
                                v_type_1341_,
                                v_a_1274_,
                            );
                            v_fst_1346_ = leanh::lean_ctor_get(v___x_1345_, 0);
                            leanh::lean_inc(v_fst_1346_);
                            v_snd_1347_ = leanh::lean_ctor_get(v___x_1345_, 1);
                            leanh::lean_inc(v_snd_1347_);
                            leanh::lean_dec_ref(v___x_1345_);
                            leanh::lean_inc_ref(v_value_1342_);
                            v___x_1348_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(
                                v_value_1342_,
                                v_snd_1347_,
                            );
                            v_fst_1349_ = leanh::lean_ctor_get(v___x_1348_, 0);
                            leanh::lean_inc(v_fst_1349_);
                            v_snd_1350_ = leanh::lean_ctor_get(v___x_1348_, 1);
                            leanh::lean_inc(v_snd_1350_);
                            leanh::lean_dec_ref(v___x_1348_);
                            leanh::lean_inc_ref(v_body_1343_);
                            v___x_1351_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(
                                v_body_1343_,
                                v_snd_1350_,
                            );
                            v_fst_1352_ = leanh::lean_ctor_get(v___x_1351_, 0);
                            v_snd_1353_ = leanh::lean_ctor_get(v___x_1351_, 1);
                            v_isSharedCheck_1379_ =
                                (!leanh::lean_is_exclusive(v___x_1351_)) as u8;
                            if v_isSharedCheck_1379_ == 0 {
                                v___x_1355_ = v___x_1351_;
                                v_isShared_1356_ = v_isSharedCheck_1379_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1353_);
                                leanh::lean_inc(v_fst_1352_);
                                leanh::lean_dec(v___x_1351_);
                                v___x_1355_ = leanh::lean_box(0);
                                v_isShared_1356_ = v_isSharedCheck_1379_;
                                state = 11;
                                continue;
                            }
                        }
                        7 => {
                            v_binderName_1380_ = leanh::lean_ctor_get(v_e_1273_, 0);
                            v_binderType_1381_ = leanh::lean_ctor_get(v_e_1273_, 1);
                            v_body_1382_ = leanh::lean_ctor_get(v_e_1273_, 2);
                            v_binderInfo_1383_ = leanh::lean_ctor_get_uint8(
                                v_e_1273_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            leanh::lean_inc_ref(v_binderType_1381_);
                            v___x_1384_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(
                                v_binderType_1381_,
                                v_a_1274_,
                            );
                            v_fst_1385_ = leanh::lean_ctor_get(v___x_1384_, 0);
                            leanh::lean_inc(v_fst_1385_);
                            v_snd_1386_ = leanh::lean_ctor_get(v___x_1384_, 1);
                            leanh::lean_inc(v_snd_1386_);
                            leanh::lean_dec_ref(v___x_1384_);
                            leanh::lean_inc_ref(v_body_1382_);
                            v___x_1387_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(
                                v_body_1382_,
                                v_snd_1386_,
                            );
                            v_fst_1388_ = leanh::lean_ctor_get(v___x_1387_, 0);
                            v_snd_1389_ = leanh::lean_ctor_get(v___x_1387_, 1);
                            v_isSharedCheck_1413_ =
                                (!leanh::lean_is_exclusive(v___x_1387_)) as u8;
                            if v_isSharedCheck_1413_ == 0 {
                                v___x_1391_ = v___x_1387_;
                                v_isShared_1392_ = v_isSharedCheck_1413_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1389_);
                                leanh::lean_inc(v_fst_1388_);
                                leanh::lean_dec(v___x_1387_);
                                v___x_1391_ = leanh::lean_box(0);
                                v_isShared_1392_ = v_isSharedCheck_1413_;
                                state = 16;
                                continue;
                            }
                        }
                        6 => {
                            v_binderName_1414_ = leanh::lean_ctor_get(v_e_1273_, 0);
                            v_binderType_1415_ = leanh::lean_ctor_get(v_e_1273_, 1);
                            v_body_1416_ = leanh::lean_ctor_get(v_e_1273_, 2);
                            v_binderInfo_1417_ = leanh::lean_ctor_get_uint8(
                                v_e_1273_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            leanh::lean_inc_ref(v_binderType_1415_);
                            v___x_1418_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(
                                v_binderType_1415_,
                                v_a_1274_,
                            );
                            v_fst_1419_ = leanh::lean_ctor_get(v___x_1418_, 0);
                            leanh::lean_inc(v_fst_1419_);
                            v_snd_1420_ = leanh::lean_ctor_get(v___x_1418_, 1);
                            leanh::lean_inc(v_snd_1420_);
                            leanh::lean_dec_ref(v___x_1418_);
                            leanh::lean_inc_ref(v_body_1416_);
                            v___x_1421_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(
                                v_body_1416_,
                                v_snd_1420_,
                            );
                            v_fst_1422_ = leanh::lean_ctor_get(v___x_1421_, 0);
                            v_snd_1423_ = leanh::lean_ctor_get(v___x_1421_, 1);
                            v_isSharedCheck_1447_ =
                                (!leanh::lean_is_exclusive(v___x_1421_)) as u8;
                            if v_isSharedCheck_1447_ == 0 {
                                v___x_1425_ = v___x_1421_;
                                v_isShared_1426_ = v_isSharedCheck_1447_;
                                state = 21;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1423_);
                                leanh::lean_inc(v_fst_1422_);
                                leanh::lean_dec(v___x_1421_);
                                v___x_1425_ = leanh::lean_box(0);
                                v_isShared_1426_ = v_isSharedCheck_1447_;
                                state = 21;
                                continue;
                            }
                        }
                        10 => {
                            v_data_1448_ = leanh::lean_ctor_get(v_e_1273_, 0);
                            v_expr_1449_ = leanh::lean_ctor_get(v_e_1273_, 1);
                            leanh::lean_inc_ref(v_expr_1449_);
                            v___x_1450_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(
                                v_expr_1449_,
                                v_a_1274_,
                            );
                            v_fst_1451_ = leanh::lean_ctor_get(v___x_1450_, 0);
                            v_snd_1452_ = leanh::lean_ctor_get(v___x_1450_, 1);
                            v_isSharedCheck_1466_ =
                                (!leanh::lean_is_exclusive(v___x_1450_)) as u8;
                            if v_isSharedCheck_1466_ == 0 {
                                v___x_1454_ = v___x_1450_;
                                v_isShared_1455_ = v_isSharedCheck_1466_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1452_);
                                leanh::lean_inc(v_fst_1451_);
                                leanh::lean_dec(v___x_1450_);
                                v___x_1454_ = leanh::lean_box(0);
                                v_isShared_1455_ = v_isSharedCheck_1466_;
                                state = 26;
                                continue;
                            }
                        }
                        11 => {
                            v_typeName_1467_ = leanh::lean_ctor_get(v_e_1273_, 0);
                            v_idx_1468_ = leanh::lean_ctor_get(v_e_1273_, 1);
                            v_struct_1469_ = leanh::lean_ctor_get(v_e_1273_, 2);
                            leanh::lean_inc_ref(v_struct_1469_);
                            v___x_1470_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(
                                v_struct_1469_,
                                v_a_1274_,
                            );
                            v_fst_1471_ = leanh::lean_ctor_get(v___x_1470_, 0);
                            v_snd_1472_ = leanh::lean_ctor_get(v___x_1470_, 1);
                            v_isSharedCheck_1486_ =
                                (!leanh::lean_is_exclusive(v___x_1470_)) as u8;
                            if v_isSharedCheck_1486_ == 0 {
                                v___x_1474_ = v___x_1470_;
                                v_isShared_1475_ = v_isSharedCheck_1486_;
                                state = 29;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1472_);
                                leanh::lean_inc(v_fst_1471_);
                                leanh::lean_dec(v___x_1470_);
                                v___x_1474_ = leanh::lean_box(0);
                                v_isShared_1475_ = v_isSharedCheck_1486_;
                                state = 29;
                                continue;
                            }
                        }
                        2 => {
                            leanh::lean_dec_ref_known(v_e_1273_, 1);
                            v___x_1487_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1_once
                                ),
                                _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1,
                            );
                            v___x_1488_ =
                                l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(
                                    v___x_1487_,
                                    v_a_1274_,
                                );
                            return v___x_1488_;
                        }
                        _ => {
                            v___x_1489_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1489_, 0, v_e_1273_);
                            leanh::lean_ctor_set(v___x_1489_, 1, v_a_1274_);
                            return v___x_1489_;
                        }
                    }
                }
            }
            1 => {
                v___x_1286_ = l_ptrEqList___redArg(v_us_1278_, v_fst_1281_);
                if v___x_1286_ == 0 {
                    leanh::lean_inc(v_declName_1277_);
                    leanh::lean_dec_ref_known(v_e_1273_, 2);
                    v___x_1287_ = l_Lean_Expr_const___override(v_declName_1277_, v_fst_1281_);
                    if v_isShared_1285_ == 0 {
                        leanh::lean_ctor_set(v___x_1284_, 0, v___x_1287_);
                        v___x_1289_ = v___x_1284_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1290_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_snd_1282_);
                        v___x_1289_ = v_reuseFailAlloc_1290_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1281_);
                    if v_isShared_1285_ == 0 {
                        leanh::lean_ctor_set(v___x_1284_, 0, v_e_1273_);
                        v___x_1292_ = v___x_1284_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1293_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_e_1273_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_snd_1282_);
                        v___x_1292_ = v_reuseFailAlloc_1293_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1289_;
            }
            3 => {
                return v___x_1292_;
            }
            4 => {
                v___x_1302_ = lean_ptr_addr(v_u_1295_);
                v___x_1303_ = lean_ptr_addr(v_fst_1297_);
                v___x_1304_ = lean_usize_dec_eq(v___x_1302_, v___x_1303_);
                if v___x_1304_ == 0 {
                    leanh::lean_dec_ref_known(v_e_1273_, 1);
                    v___x_1305_ = l_Lean_Expr_sort___override(v_fst_1297_);
                    if v_isShared_1301_ == 0 {
                        leanh::lean_ctor_set(v___x_1300_, 0, v___x_1305_);
                        v___x_1307_ = v___x_1300_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1308_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_snd_1298_);
                        v___x_1307_ = v_reuseFailAlloc_1308_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1297_);
                    if v_isShared_1301_ == 0 {
                        leanh::lean_ctor_set(v___x_1300_, 0, v_e_1273_);
                        v___x_1310_ = v___x_1300_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1311_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_e_1273_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_snd_1298_);
                        v___x_1310_ = v_reuseFailAlloc_1311_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1307_;
            }
            6 => {
                return v___x_1310_;
            }
            7 => {
                v___x_1333_ = lean_ptr_addr(v_fn_1313_);
                v___x_1334_ = lean_ptr_addr(v_fst_1316_);
                v___x_1335_ = lean_usize_dec_eq(v___x_1333_, v___x_1334_);
                if v___x_1335_ == 0 {
                    v___y_1325_ = v___x_1335_;
                    state = 8;
                    continue;
                } else {
                    v___x_1336_ = lean_ptr_addr(v_arg_1314_);
                    v___x_1337_ = lean_ptr_addr(v_fst_1319_);
                    v___x_1338_ = lean_usize_dec_eq(v___x_1336_, v___x_1337_);
                    v___y_1325_ = v___x_1338_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_1325_ == 0 {
                    leanh::lean_dec_ref_known(v_e_1273_, 2);
                    v___x_1326_ = l_Lean_Expr_app___override(v_fst_1316_, v_fst_1319_);
                    if v_isShared_1323_ == 0 {
                        leanh::lean_ctor_set(v___x_1322_, 0, v___x_1326_);
                        v___x_1328_ = v___x_1322_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1329_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_snd_1320_);
                        v___x_1328_ = v_reuseFailAlloc_1329_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1319_);
                    leanh::lean_dec(v_fst_1316_);
                    if v_isShared_1323_ == 0 {
                        leanh::lean_ctor_set(v___x_1322_, 0, v_e_1273_);
                        v___x_1331_ = v___x_1322_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1332_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_e_1273_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_snd_1320_);
                        v___x_1331_ = v_reuseFailAlloc_1332_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_1328_;
            }
            10 => {
                return v___x_1331_;
            }
            11 => {
                v___x_1373_ = lean_ptr_addr(v_type_1341_);
                v___x_1374_ = lean_ptr_addr(v_fst_1346_);
                v___x_1375_ = lean_usize_dec_eq(v___x_1373_, v___x_1374_);
                if v___x_1375_ == 0 {
                    v___y_1358_ = v___x_1375_;
                    state = 12;
                    continue;
                } else {
                    v___x_1376_ = lean_ptr_addr(v_value_1342_);
                    v___x_1377_ = lean_ptr_addr(v_fst_1349_);
                    v___x_1378_ = lean_usize_dec_eq(v___x_1376_, v___x_1377_);
                    v___y_1358_ = v___x_1378_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v___y_1358_ == 0 {
                    leanh::lean_inc(v_declName_1340_);
                    leanh::lean_dec_ref_known(v_e_1273_, 4);
                    v___x_1359_ = l_Lean_Expr_letE___override(
                        v_declName_1340_,
                        v_fst_1346_,
                        v_fst_1349_,
                        v_fst_1352_,
                        v_nondep_1344_,
                    );
                    if v_isShared_1356_ == 0 {
                        leanh::lean_ctor_set(v___x_1355_, 0, v___x_1359_);
                        v___x_1361_ = v___x_1355_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_1362_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_snd_1353_);
                        v___x_1361_ = v_reuseFailAlloc_1362_;
                        state = 13;
                        continue;
                    }
                } else {
                    v___x_1363_ = lean_ptr_addr(v_body_1343_);
                    v___x_1364_ = lean_ptr_addr(v_fst_1352_);
                    v___x_1365_ = lean_usize_dec_eq(v___x_1363_, v___x_1364_);
                    if v___x_1365_ == 0 {
                        leanh::lean_inc(v_declName_1340_);
                        leanh::lean_dec_ref_known(v_e_1273_, 4);
                        v___x_1366_ = l_Lean_Expr_letE___override(
                            v_declName_1340_,
                            v_fst_1346_,
                            v_fst_1349_,
                            v_fst_1352_,
                            v_nondep_1344_,
                        );
                        if v_isShared_1356_ == 0 {
                            leanh::lean_ctor_set(v___x_1355_, 0, v___x_1366_);
                            v___x_1368_ = v___x_1355_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_1369_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_snd_1353_);
                            v___x_1368_ = v_reuseFailAlloc_1369_;
                            state = 14;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fst_1352_);
                        leanh::lean_dec(v_fst_1349_);
                        leanh::lean_dec(v_fst_1346_);
                        if v_isShared_1356_ == 0 {
                            leanh::lean_ctor_set(v___x_1355_, 0, v_e_1273_);
                            v___x_1371_ = v___x_1355_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_1372_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_e_1273_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_snd_1353_);
                            v___x_1371_ = v_reuseFailAlloc_1372_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            13 => {
                return v___x_1361_;
            }
            14 => {
                return v___x_1368_;
            }
            15 => {
                return v___x_1371_;
            }
            16 => {
                v___x_1407_ = lean_ptr_addr(v_binderType_1381_);
                v___x_1408_ = lean_ptr_addr(v_fst_1385_);
                v___x_1409_ = lean_usize_dec_eq(v___x_1407_, v___x_1408_);
                if v___x_1409_ == 0 {
                    v___y_1394_ = v___x_1409_;
                    state = 17;
                    continue;
                } else {
                    v___x_1410_ = lean_ptr_addr(v_body_1382_);
                    v___x_1411_ = lean_ptr_addr(v_fst_1388_);
                    v___x_1412_ = lean_usize_dec_eq(v___x_1410_, v___x_1411_);
                    v___y_1394_ = v___x_1412_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v___y_1394_ == 0 {
                    leanh::lean_inc(v_binderName_1380_);
                    leanh::lean_dec_ref_known(v_e_1273_, 3);
                    v___x_1395_ = l_Lean_Expr_forallE___override(
                        v_binderName_1380_,
                        v_fst_1385_,
                        v_fst_1388_,
                        v_binderInfo_1383_,
                    );
                    if v_isShared_1392_ == 0 {
                        leanh::lean_ctor_set(v___x_1391_, 0, v___x_1395_);
                        v___x_1397_ = v___x_1391_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1398_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_snd_1389_);
                        v___x_1397_ = v_reuseFailAlloc_1398_;
                        state = 18;
                        continue;
                    }
                } else {
                    v___x_1399_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1383_, v_binderInfo_1383_);
                    if v___x_1399_ == 0 {
                        leanh::lean_inc(v_binderName_1380_);
                        leanh::lean_dec_ref_known(v_e_1273_, 3);
                        v___x_1400_ = l_Lean_Expr_forallE___override(
                            v_binderName_1380_,
                            v_fst_1385_,
                            v_fst_1388_,
                            v_binderInfo_1383_,
                        );
                        if v_isShared_1392_ == 0 {
                            leanh::lean_ctor_set(v___x_1391_, 0, v___x_1400_);
                            v___x_1402_ = v___x_1391_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_1403_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_snd_1389_);
                            v___x_1402_ = v_reuseFailAlloc_1403_;
                            state = 19;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fst_1388_);
                        leanh::lean_dec(v_fst_1385_);
                        if v_isShared_1392_ == 0 {
                            leanh::lean_ctor_set(v___x_1391_, 0, v_e_1273_);
                            v___x_1405_ = v___x_1391_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_1406_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_e_1273_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_snd_1389_);
                            v___x_1405_ = v_reuseFailAlloc_1406_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            18 => {
                return v___x_1397_;
            }
            19 => {
                return v___x_1402_;
            }
            20 => {
                return v___x_1405_;
            }
            21 => {
                v___x_1441_ = lean_ptr_addr(v_binderType_1415_);
                v___x_1442_ = lean_ptr_addr(v_fst_1419_);
                v___x_1443_ = lean_usize_dec_eq(v___x_1441_, v___x_1442_);
                if v___x_1443_ == 0 {
                    v___y_1428_ = v___x_1443_;
                    state = 22;
                    continue;
                } else {
                    v___x_1444_ = lean_ptr_addr(v_body_1416_);
                    v___x_1445_ = lean_ptr_addr(v_fst_1422_);
                    v___x_1446_ = lean_usize_dec_eq(v___x_1444_, v___x_1445_);
                    v___y_1428_ = v___x_1446_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v___y_1428_ == 0 {
                    leanh::lean_inc(v_binderName_1414_);
                    leanh::lean_dec_ref_known(v_e_1273_, 3);
                    v___x_1429_ = l_Lean_Expr_lam___override(
                        v_binderName_1414_,
                        v_fst_1419_,
                        v_fst_1422_,
                        v_binderInfo_1417_,
                    );
                    if v_isShared_1426_ == 0 {
                        leanh::lean_ctor_set(v___x_1425_, 0, v___x_1429_);
                        v___x_1431_ = v___x_1425_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_1432_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_snd_1423_);
                        v___x_1431_ = v_reuseFailAlloc_1432_;
                        state = 23;
                        continue;
                    }
                } else {
                    v___x_1433_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1417_, v_binderInfo_1417_);
                    if v___x_1433_ == 0 {
                        leanh::lean_inc(v_binderName_1414_);
                        leanh::lean_dec_ref_known(v_e_1273_, 3);
                        v___x_1434_ = l_Lean_Expr_lam___override(
                            v_binderName_1414_,
                            v_fst_1419_,
                            v_fst_1422_,
                            v_binderInfo_1417_,
                        );
                        if v_isShared_1426_ == 0 {
                            leanh::lean_ctor_set(v___x_1425_, 0, v___x_1434_);
                            v___x_1436_ = v___x_1425_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_1437_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_snd_1423_);
                            v___x_1436_ = v_reuseFailAlloc_1437_;
                            state = 24;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fst_1422_);
                        leanh::lean_dec(v_fst_1419_);
                        if v_isShared_1426_ == 0 {
                            leanh::lean_ctor_set(v___x_1425_, 0, v_e_1273_);
                            v___x_1439_ = v___x_1425_;
                            state = 25;
                            continue;
                        } else {
                            v_reuseFailAlloc_1440_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_e_1273_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_snd_1423_);
                            v___x_1439_ = v_reuseFailAlloc_1440_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            23 => {
                return v___x_1431_;
            }
            24 => {
                return v___x_1436_;
            }
            25 => {
                return v___x_1439_;
            }
            26 => {
                v___x_1456_ = lean_ptr_addr(v_expr_1449_);
                v___x_1457_ = lean_ptr_addr(v_fst_1451_);
                v___x_1458_ = lean_usize_dec_eq(v___x_1456_, v___x_1457_);
                if v___x_1458_ == 0 {
                    leanh::lean_inc(v_data_1448_);
                    leanh::lean_dec_ref_known(v_e_1273_, 2);
                    v___x_1459_ = l_Lean_Expr_mdata___override(v_data_1448_, v_fst_1451_);
                    if v_isShared_1455_ == 0 {
                        leanh::lean_ctor_set(v___x_1454_, 0, v___x_1459_);
                        v___x_1461_ = v___x_1454_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_1462_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_snd_1452_);
                        v___x_1461_ = v_reuseFailAlloc_1462_;
                        state = 27;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1451_);
                    if v_isShared_1455_ == 0 {
                        leanh::lean_ctor_set(v___x_1454_, 0, v_e_1273_);
                        v___x_1464_ = v___x_1454_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_1465_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_e_1273_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_snd_1452_);
                        v___x_1464_ = v_reuseFailAlloc_1465_;
                        state = 28;
                        continue;
                    }
                }
            }
            27 => {
                return v___x_1461_;
            }
            28 => {
                return v___x_1464_;
            }
            29 => {
                v___x_1476_ = lean_ptr_addr(v_struct_1469_);
                v___x_1477_ = lean_ptr_addr(v_fst_1471_);
                v___x_1478_ = lean_usize_dec_eq(v___x_1476_, v___x_1477_);
                if v___x_1478_ == 0 {
                    leanh::lean_inc(v_idx_1468_);
                    leanh::lean_inc(v_typeName_1467_);
                    leanh::lean_dec_ref_known(v_e_1273_, 3);
                    v___x_1479_ =
                        l_Lean_Expr_proj___override(v_typeName_1467_, v_idx_1468_, v_fst_1471_);
                    if v_isShared_1475_ == 0 {
                        leanh::lean_ctor_set(v___x_1474_, 0, v___x_1479_);
                        v___x_1481_ = v___x_1474_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_1482_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_snd_1472_);
                        v___x_1481_ = v_reuseFailAlloc_1482_;
                        state = 30;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1471_);
                    if v_isShared_1475_ == 0 {
                        leanh::lean_ctor_set(v___x_1474_, 0, v_e_1273_);
                        v___x_1484_ = v___x_1474_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1485_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_e_1273_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_snd_1472_);
                        v___x_1484_ = v_reuseFailAlloc_1485_;
                        state = 31;
                        continue;
                    }
                }
            }
            30 => {
                return v___x_1481_;
            }
            31 => {
                return v___x_1484_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1490_ = leanh::lean_box(0);
    v___x_1491_ = leanh::lean_unsigned_to_nat(16);
    v___x_1492_ = lean_mk_array(v___x_1491_, v___x_1490_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_normLevelParams___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_normLevelParams___closed__0_once),
        _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0,
    );
    v___x_1494_ = leanh::lean_unsigned_to_nat(0);
    v___x_1495_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
    leanh::lean_ctor_set(v___x_1495_, 1, v___x_1493_);
    return v___x_1495_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1498_ = l_Lean_Compiler_LCNF_normLevelParams___closed__2;
    v___x_1499_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_normLevelParams___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_normLevelParams___closed__1_once),
        _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1,
    );
    v___x_1500_ = leanh::lean_unsigned_to_nat(1);
    v___x_1501_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1501_, 0, v___x_1500_);
    leanh::lean_ctor_set(v___x_1501_, 1, v___x_1499_);
    leanh::lean_ctor_set(v___x_1501_, 2, v___x_1498_);
    return v___x_1501_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLevelParams(
    mut v_e_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v_paramNames_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1515_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1503_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_normLevelParams___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_normLevelParams___closed__3_once),
                    _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3,
                );
                v___x_1504_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_e_1502_, v___x_1503_);
                v_snd_1505_ = leanh::lean_ctor_get(v___x_1504_, 1);
                v_fst_1506_ = leanh::lean_ctor_get(v___x_1504_, 0);
                v_isSharedCheck_1515_ = (!leanh::lean_is_exclusive(v___x_1504_)) as u8;
                if v_isSharedCheck_1515_ == 0 {
                    v___x_1508_ = v___x_1504_;
                    v_isShared_1509_ = v_isSharedCheck_1515_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1505_);
                    leanh::lean_inc(v_fst_1506_);
                    leanh::lean_dec(v___x_1504_);
                    v___x_1508_ = leanh::lean_box(0);
                    v_isShared_1509_ = v_isSharedCheck_1515_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_paramNames_1510_ = leanh::lean_ctor_get(v_snd_1505_, 2);
                leanh::lean_inc_ref(v_paramNames_1510_);
                leanh::lean_dec(v_snd_1505_);
                v___x_1511_ = lean_array_to_list(v_paramNames_1510_);
                if v_isShared_1509_ == 0 {
                    leanh::lean_ctor_set(v___x_1508_, 1, v___x_1511_);
                    v___x_1513_ = v___x_1508_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_fst_1506_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___x_1511_);
                    v___x_1513_ = v_reuseFailAlloc_1514_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1513_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitType(
    mut v_type_1516_: *mut leanh::LeanObject,
    mut v_a_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1518_ = l_Lean_CollectLevelParams_visitExpr(v_type_1516_, v_a_1517_);
    return v___x_1518_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(
    mut v_arg_1519_: *mut leanh::LeanObject,
    mut v_a_1520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_arg_1519_) == 2 {
        let mut v_expr_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_expr_1521_ = leanh::lean_ctor_get(v_arg_1519_, 0);
        leanh::lean_inc_ref(v_expr_1521_);
        leanh::lean_dec_ref_known(v_arg_1519_, 1);
        v___x_1522_ = l_Lean_CollectLevelParams_visitExpr(v_expr_1521_, v_a_1520_);
        return v___x_1522_;
    } else {
        leanh::lean_dec(v_arg_1519_);
        return v_a_1520_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(
    mut v_as_1523_: *mut leanh::LeanObject,
    mut v_i_1524_: usize,
    mut v_stop_1525_: usize,
    mut v_b_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1527_: u8 = 0;
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: usize = 0;
    let mut v___x_1531_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1527_ = lean_usize_dec_eq(v_i_1524_, v_stop_1525_);
                if v___x_1527_ == 0 {
                    v___x_1528_ = lean_array_uget_borrowed(v_as_1523_, v_i_1524_);
                    leanh::lean_inc(v___x_1528_);
                    v___x_1529_ =
                        l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(v___x_1528_, v_b_1526_);
                    v___x_1530_ = 1usize;
                    v___x_1531_ = lean_usize_add(v_i_1524_, v___x_1530_);
                    v_i_1524_ = v___x_1531_;
                    v_b_1526_ = v___x_1529_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1526_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0___boxed(
    mut v_as_1533_: *mut leanh::LeanObject,
    mut v_i_1534_: *mut leanh::LeanObject,
    mut v_stop_1535_: *mut leanh::LeanObject,
    mut v_b_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1537_: usize = 0;
    let mut v_stop_boxed_1538_: usize = 0;
    let mut v_res_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1537_ = leanh::lean_unbox_usize(v_i_1534_);
    leanh::lean_dec(v_i_1534_);
    v_stop_boxed_1538_ = leanh::lean_unbox_usize(v_stop_1535_);
    leanh::lean_dec(v_stop_1535_);
    v_res_1539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_as_1533_, v_i_boxed_1537_, v_stop_boxed_1538_, v_b_1536_);
    leanh::lean_dec_ref(v_as_1533_);
    return v_res_1539_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(
    mut v_args_1540_: *mut leanh::LeanObject,
    mut v_s_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: u8 = 0;
    v___x_1542_ = leanh::lean_unsigned_to_nat(0);
    v___x_1543_ = lean_array_get_size(v_args_1540_);
    v___x_1544_ = lean_nat_dec_lt(v___x_1542_, v___x_1543_);
    if v___x_1544_ == 0 {
        return v_s_1541_;
    } else {
        let mut v___x_1545_: u8 = 0;
        v___x_1545_ = lean_nat_dec_le(v___x_1543_, v___x_1543_);
        if v___x_1545_ == 0 {
            if v___x_1544_ == 0 {
                return v_s_1541_;
            } else {
                let mut v___x_1546_: usize = 0;
                let mut v___x_1547_: usize = 0;
                let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1546_ = 0usize;
                v___x_1547_ = lean_usize_of_nat(v___x_1543_);
                v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_1540_, v___x_1546_, v___x_1547_, v_s_1541_);
                return v___x_1548_;
            }
        } else {
            let mut v___x_1549_: usize = 0;
            let mut v___x_1550_: usize = 0;
            let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1549_ = 0usize;
            v___x_1550_ = lean_usize_of_nat(v___x_1543_);
            v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_1540_, v___x_1549_, v___x_1550_, v_s_1541_);
            return v___x_1551_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs___boxed(
    mut v_args_1552_: *mut leanh::LeanObject,
    mut v_s_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_1552_, v_s_1553_);
    leanh::lean_dec_ref(v_args_1552_);
    return v_res_1554_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(
    mut v_e_1555_: *mut leanh::LeanObject,
    mut v_a_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_e_1555_) {
        3 => {
            let mut v_us_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_args_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_us_1557_ = leanh::lean_ctor_get(v_e_1555_, 1);
            leanh::lean_inc(v_us_1557_);
            v_args_1558_ = leanh::lean_ctor_get(v_e_1555_, 2);
            leanh::lean_inc_ref(v_args_1558_);
            leanh::lean_dec_ref_known(v_e_1555_, 3);
            v___x_1559_ =
                l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_1558_, v_a_1556_);
            leanh::lean_dec_ref(v_args_1558_);
            v___x_1560_ = l_Lean_CollectLevelParams_visitLevels(v_us_1557_, v___x_1559_);
            return v___x_1560_;
        }
        4 => {
            let mut v_args_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_args_1561_ = leanh::lean_ctor_get(v_e_1555_, 1);
            leanh::lean_inc_ref(v_args_1561_);
            leanh::lean_dec_ref_known(v_e_1555_, 2);
            v___x_1562_ =
                l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_1561_, v_a_1556_);
            leanh::lean_dec_ref(v_args_1561_);
            return v___x_1562_;
        }
        _ => {
            leanh::lean_dec(v_e_1555_);
            return v_a_1556_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(
    mut v_p_1563_: *mut leanh::LeanObject,
    mut v_a_1564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_type_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_1565_ = leanh::lean_ctor_get(v_p_1563_, 2);
    leanh::lean_inc_ref(v_type_1565_);
    leanh::lean_dec_ref(v_p_1563_);
    v___x_1566_ = l_Lean_CollectLevelParams_visitExpr(v_type_1565_, v_a_1564_);
    return v___x_1566_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(
    mut v_as_1567_: *mut leanh::LeanObject,
    mut v_i_1568_: usize,
    mut v_stop_1569_: usize,
    mut v_b_1570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: usize = 0;
    let mut v___x_1575_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1571_ = lean_usize_dec_eq(v_i_1568_, v_stop_1569_);
                if v___x_1571_ == 0 {
                    v___x_1572_ = lean_array_uget_borrowed(v_as_1567_, v_i_1568_);
                    leanh::lean_inc(v___x_1572_);
                    v___x_1573_ =
                        l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(v___x_1572_, v_b_1570_);
                    v___x_1574_ = 1usize;
                    v___x_1575_ = lean_usize_add(v_i_1568_, v___x_1574_);
                    v_i_1568_ = v___x_1575_;
                    v_b_1570_ = v___x_1573_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1570_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0___boxed(
    mut v_as_1577_: *mut leanh::LeanObject,
    mut v_i_1578_: *mut leanh::LeanObject,
    mut v_stop_1579_: *mut leanh::LeanObject,
    mut v_b_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1581_: usize = 0;
    let mut v_stop_boxed_1582_: usize = 0;
    let mut v_res_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1581_ = leanh::lean_unbox_usize(v_i_1578_);
    leanh::lean_dec(v_i_1578_);
    v_stop_boxed_1582_ = leanh::lean_unbox_usize(v_stop_1579_);
    leanh::lean_dec(v_stop_1579_);
    v_res_1583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_as_1577_, v_i_boxed_1581_, v_stop_boxed_1582_, v_b_1580_);
    leanh::lean_dec_ref(v_as_1577_);
    return v_res_1583_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(
    mut v_ps_1584_: *mut leanh::LeanObject,
    mut v_s_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: u8 = 0;
    v___x_1586_ = leanh::lean_unsigned_to_nat(0);
    v___x_1587_ = lean_array_get_size(v_ps_1584_);
    v___x_1588_ = lean_nat_dec_lt(v___x_1586_, v___x_1587_);
    if v___x_1588_ == 0 {
        return v_s_1585_;
    } else {
        let mut v___x_1589_: u8 = 0;
        v___x_1589_ = lean_nat_dec_le(v___x_1587_, v___x_1587_);
        if v___x_1589_ == 0 {
            if v___x_1588_ == 0 {
                return v_s_1585_;
            } else {
                let mut v___x_1590_: usize = 0;
                let mut v___x_1591_: usize = 0;
                let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1590_ = 0usize;
                v___x_1591_ = lean_usize_of_nat(v___x_1587_);
                v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_1584_, v___x_1590_, v___x_1591_, v_s_1585_);
                return v___x_1592_;
            }
        } else {
            let mut v___x_1593_: usize = 0;
            let mut v___x_1594_: usize = 0;
            let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1593_ = 0usize;
            v___x_1594_ = lean_usize_of_nat(v___x_1587_);
            v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_1584_, v___x_1593_, v___x_1594_, v_s_1585_);
            return v___x_1595_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitParams___boxed(
    mut v_ps_1596_: *mut leanh::LeanObject,
    mut v_s_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_ps_1596_, v_s_1597_);
    leanh::lean_dec_ref(v_ps_1596_);
    return v_res_1598_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(
    mut v_as_1599_: *mut leanh::LeanObject,
    mut v_i_1600_: usize,
    mut v_stop_1601_: usize,
    mut v_b_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: usize = 0;
    let mut v___x_1607_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1603_ = lean_usize_dec_eq(v_i_1600_, v_stop_1601_);
                if v___x_1603_ == 0 {
                    v___x_1604_ = lean_array_uget_borrowed(v_as_1599_, v_i_1600_);
                    leanh::lean_inc(v___x_1604_);
                    v___x_1605_ =
                        l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(v___x_1604_, v_b_1602_);
                    v___x_1606_ = 1usize;
                    v___x_1607_ = lean_usize_add(v_i_1600_, v___x_1606_);
                    v_i_1600_ = v___x_1607_;
                    v_b_1602_ = v___x_1605_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1602_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(
    mut v_alts_1609_: *mut leanh::LeanObject,
    mut v_s_1610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: u8 = 0;
    v___x_1611_ = leanh::lean_unsigned_to_nat(0);
    v___x_1612_ = lean_array_get_size(v_alts_1609_);
    v___x_1613_ = lean_nat_dec_lt(v___x_1611_, v___x_1612_);
    if v___x_1613_ == 0 {
        return v_s_1610_;
    } else {
        let mut v___x_1614_: u8 = 0;
        v___x_1614_ = lean_nat_dec_le(v___x_1612_, v___x_1612_);
        if v___x_1614_ == 0 {
            if v___x_1613_ == 0 {
                return v_s_1610_;
            } else {
                let mut v___x_1615_: usize = 0;
                let mut v___x_1616_: usize = 0;
                let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1615_ = 0usize;
                v___x_1616_ = lean_usize_of_nat(v___x_1612_);
                v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_1609_, v___x_1615_, v___x_1616_, v_s_1610_);
                return v___x_1617_;
            }
        } else {
            let mut v___x_1618_: usize = 0;
            let mut v___x_1619_: usize = 0;
            let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1618_ = 0usize;
            v___x_1619_ = lean_usize_of_nat(v___x_1612_);
            v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_1609_, v___x_1618_, v___x_1619_, v_s_1610_);
            return v___x_1620_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(
    mut v_x_1621_: *mut leanh::LeanObject,
    mut v_a_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1621_) {
                0 => {
                    v_decl_1623_ = leanh::lean_ctor_get(v_x_1621_, 0);
                    leanh::lean_inc_ref(v_decl_1623_);
                    v_k_1624_ = leanh::lean_ctor_get(v_x_1621_, 1);
                    leanh::lean_inc_ref(v_k_1624_);
                    leanh::lean_dec_ref_known(v_x_1621_, 2);
                    v_type_1625_ = leanh::lean_ctor_get(v_decl_1623_, 2);
                    leanh::lean_inc_ref(v_type_1625_);
                    v_value_1626_ = leanh::lean_ctor_get(v_decl_1623_, 3);
                    leanh::lean_inc(v_value_1626_);
                    leanh::lean_dec_ref(v_decl_1623_);
                    v___x_1627_ = l_Lean_CollectLevelParams_visitExpr(v_type_1625_, v_a_1622_);
                    v___x_1628_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(
                        v_value_1626_,
                        v___x_1627_,
                    );
                    v_x_1621_ = v_k_1624_;
                    v_a_1622_ = v___x_1628_;
                    state = 0;
                    continue;
                }
                3 => {
                    v_args_1630_ = leanh::lean_ctor_get(v_x_1621_, 1);
                    leanh::lean_inc_ref(v_args_1630_);
                    leanh::lean_dec_ref_known(v_x_1621_, 2);
                    v___x_1631_ =
                        l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_1630_, v_a_1622_);
                    leanh::lean_dec_ref(v_args_1630_);
                    return v___x_1631_;
                }
                4 => {
                    v_cases_1632_ = leanh::lean_ctor_get(v_x_1621_, 0);
                    leanh::lean_inc_ref(v_cases_1632_);
                    leanh::lean_dec_ref_known(v_x_1621_, 1);
                    v_resultType_1633_ = leanh::lean_ctor_get(v_cases_1632_, 1);
                    leanh::lean_inc_ref(v_resultType_1633_);
                    v_alts_1634_ = leanh::lean_ctor_get(v_cases_1632_, 3);
                    leanh::lean_inc_ref(v_alts_1634_);
                    leanh::lean_dec_ref(v_cases_1632_);
                    v___x_1635_ =
                        l_Lean_CollectLevelParams_visitExpr(v_resultType_1633_, v_a_1622_);
                    v___x_1636_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(
                        v_alts_1634_,
                        v___x_1635_,
                    );
                    leanh::lean_dec_ref(v_alts_1634_);
                    return v___x_1636_;
                }
                5 => {
                    leanh::lean_dec_ref_known(v_x_1621_, 1);
                    return v_a_1622_;
                }
                6 => {
                    v_type_1637_ = leanh::lean_ctor_get(v_x_1621_, 0);
                    leanh::lean_inc_ref(v_type_1637_);
                    leanh::lean_dec_ref_known(v_x_1621_, 1);
                    v___x_1638_ = l_Lean_CollectLevelParams_visitExpr(v_type_1637_, v_a_1622_);
                    return v___x_1638_;
                }
                _ => {
                    v_decl_1639_ = leanh::lean_ctor_get(v_x_1621_, 0);
                    leanh::lean_inc_ref(v_decl_1639_);
                    v_k_1640_ = leanh::lean_ctor_get(v_x_1621_, 1);
                    leanh::lean_inc_ref(v_k_1640_);
                    leanh::lean_dec_ref(v_x_1621_);
                    v_params_1641_ = leanh::lean_ctor_get(v_decl_1639_, 2);
                    leanh::lean_inc_ref(v_params_1641_);
                    v_type_1642_ = leanh::lean_ctor_get(v_decl_1639_, 3);
                    leanh::lean_inc_ref(v_type_1642_);
                    v_value_1643_ = leanh::lean_ctor_get(v_decl_1639_, 4);
                    leanh::lean_inc_ref(v_value_1643_);
                    leanh::lean_dec_ref(v_decl_1639_);
                    v___x_1644_ = l_Lean_CollectLevelParams_visitExpr(v_type_1642_, v_a_1622_);
                    v___x_1645_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(
                        v_params_1641_,
                        v___x_1644_,
                    );
                    leanh::lean_dec_ref(v_params_1641_);
                    v___x_1646_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(
                        v_value_1643_,
                        v___x_1645_,
                    );
                    v_x_1621_ = v_k_1640_;
                    v_a_1622_ = v___x_1646_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(
    mut v_alt_1648_: *mut leanh::LeanObject,
    mut v_a_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_alt_1648_) == 0 {
        let mut v_params_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_code_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_params_1650_ = leanh::lean_ctor_get(v_alt_1648_, 1);
        leanh::lean_inc_ref(v_params_1650_);
        v_code_1651_ = leanh::lean_ctor_get(v_alt_1648_, 2);
        leanh::lean_inc_ref(v_code_1651_);
        leanh::lean_dec_ref_known(v_alt_1648_, 3);
        v___x_1652_ =
            l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_1650_, v_a_1649_);
        leanh::lean_dec_ref(v_params_1650_);
        v___x_1653_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_1651_, v___x_1652_);
        return v___x_1653_;
    } else {
        let mut v_code_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_code_1654_ = leanh::lean_ctor_get(v_alt_1648_, 0);
        leanh::lean_inc_ref(v_code_1654_);
        leanh::lean_dec_ref_known(v_alt_1648_, 1);
        v___x_1655_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_1654_, v_a_1649_);
        return v___x_1655_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2___boxed(
    mut v_as_1656_: *mut leanh::LeanObject,
    mut v_i_1657_: *mut leanh::LeanObject,
    mut v_stop_1658_: *mut leanh::LeanObject,
    mut v_b_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1660_: usize = 0;
    let mut v_stop_boxed_1661_: usize = 0;
    let mut v_res_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1660_ = leanh::lean_unbox_usize(v_i_1657_);
    leanh::lean_dec(v_i_1657_);
    v_stop_boxed_1661_ = leanh::lean_unbox_usize(v_stop_1658_);
    leanh::lean_dec(v_stop_1658_);
    v_res_1662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_as_1656_, v_i_boxed_1660_, v_stop_boxed_1661_, v_b_1659_);
    leanh::lean_dec_ref(v_as_1656_);
    return v_res_1662_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts___boxed(
    mut v_alts_1663_: *mut leanh::LeanObject,
    mut v_s_1664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1665_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_1663_, v_s_1664_);
    leanh::lean_dec_ref(v_alts_1663_);
    return v_res_1665_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(
    mut v_x_1666_: *mut leanh::LeanObject,
    mut v_a_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1666_) == 0 {
        let mut v_code_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_code_1668_ = leanh::lean_ctor_get(v_x_1666_, 0);
        leanh::lean_inc_ref(v_code_1668_);
        leanh::lean_dec_ref_known(v_x_1666_, 1);
        v___x_1669_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_1668_, v_a_1667_);
        return v___x_1669_;
    } else {
        leanh::lean_dec_ref_known(v_x_1666_, 1);
        return v_a_1667_;
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1670_ = leanh::lean_box(0);
    v___x_1671_ = leanh::lean_unsigned_to_nat(16);
    v___x_1672_ = lean_mk_array(v___x_1671_, v___x_1670_);
    return v___x_1672_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0_once),
        _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0,
    );
    v___x_1674_ = leanh::lean_unsigned_to_nat(0);
    v___x_1675_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1675_, 0, v___x_1674_);
    leanh::lean_ctor_set(v___x_1675_, 1, v___x_1673_);
    return v___x_1675_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1676_ = l_Lean_Compiler_LCNF_normLevelParams___closed__2;
    v___x_1677_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1_once),
        _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1,
    );
    v___x_1678_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1678_, 0, v___x_1677_);
    leanh::lean_ctor_set(v___x_1678_, 1, v___x_1677_);
    leanh::lean_ctor_set(v___x_1678_, 2, v___x_1676_);
    return v___x_1678_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_setLevelParams(
    mut v_decl_1679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSignature_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_1682_: u8 = 0;
    let mut v_inlineAttr_x3f_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1686_: u8 = 0;
    let mut v_name_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_1690_: u8 = 0;
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1706_: u8 = 0;
    let mut v_unused_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_1680_ = leanh::lean_ctor_get(v_decl_1679_, 0);
                v_value_1681_ = leanh::lean_ctor_get(v_decl_1679_, 1);
                v_recursive_1682_ = leanh::lean_ctor_get_uint8(
                    v_decl_1679_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_1683_ = leanh::lean_ctor_get(v_decl_1679_, 2);
                v_isSharedCheck_1708_ = (!leanh::lean_is_exclusive(v_decl_1679_)) as u8;
                if v_isSharedCheck_1708_ == 0 {
                    v___x_1685_ = v_decl_1679_;
                    v_isShared_1686_ = v_isSharedCheck_1708_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_inlineAttr_x3f_1683_);
                    leanh::lean_inc(v_value_1681_);
                    leanh::lean_inc(v_toSignature_1680_);
                    leanh::lean_dec(v_decl_1679_);
                    v___x_1685_ = leanh::lean_box(0);
                    v_isShared_1686_ = v_isSharedCheck_1708_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_1687_ = leanh::lean_ctor_get(v_toSignature_1680_, 0);
                v_type_1688_ = leanh::lean_ctor_get(v_toSignature_1680_, 2);
                v_params_1689_ = leanh::lean_ctor_get(v_toSignature_1680_, 3);
                v_safe_1690_ = leanh::lean_ctor_get_uint8(
                    v_toSignature_1680_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_1706_ =
                    (!leanh::lean_is_exclusive(v_toSignature_1680_)) as u8;
                if v_isSharedCheck_1706_ == 0 {
                    v_unused_1707_ = leanh::lean_ctor_get(v_toSignature_1680_, 1);
                    leanh::lean_dec(v_unused_1707_);
                    v___x_1692_ = v_toSignature_1680_;
                    v_isShared_1693_ = v_isSharedCheck_1706_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_params_1689_);
                    leanh::lean_inc(v_type_1688_);
                    leanh::lean_inc(v_name_1687_);
                    leanh::lean_dec(v_toSignature_1680_);
                    v___x_1692_ = leanh::lean_box(0);
                    v_isShared_1693_ = v_isSharedCheck_1706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1694_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2,
                );
                leanh::lean_inc_ref(v_type_1688_);
                v___x_1695_ = l_Lean_CollectLevelParams_visitExpr(v_type_1688_, v___x_1694_);
                v___x_1696_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(
                    v_params_1689_,
                    v___x_1695_,
                );
                leanh::lean_inc_ref(v_value_1681_);
                v___x_1697_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(
                    v_value_1681_,
                    v___x_1696_,
                );
                v_params_1698_ = leanh::lean_ctor_get(v___x_1697_, 2);
                leanh::lean_inc_ref(v_params_1698_);
                leanh::lean_dec_ref(v___x_1697_);
                v_levelParams_1699_ = lean_array_to_list(v_params_1698_);
                if v_isShared_1693_ == 0 {
                    leanh::lean_ctor_set(v___x_1692_, 1, v_levelParams_1699_);
                    v___x_1701_ = v___x_1692_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1705_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_name_1687_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_levelParams_1699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 2, v_type_1688_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 3, v_params_1689_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1705_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v_safe_1690_,
                    );
                    v___x_1701_ = v_reuseFailAlloc_1705_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1686_ == 0 {
                    leanh::lean_ctor_set(v___x_1685_, 0, v___x_1701_);
                    v___x_1703_ = v___x_1685_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1704_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_value_1681_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 2, v_inlineAttr_x3f_1683_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1704_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_recursive_1682_,
                    );
                    v___x_1703_ = v_reuseFailAlloc_1704_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1703_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Level(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Level(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Level(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_CollectLevelParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Level(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Level(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Level(builtin);
}