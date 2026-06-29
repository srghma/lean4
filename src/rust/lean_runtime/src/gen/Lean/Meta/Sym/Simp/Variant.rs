// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Variant
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.ScopedEnvExtension
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr1,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::ScopedEnvExtension::{
    initialize_Lean_ScopedEnvExtension, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg, runtime_initialize_Lean_ScopedEnvExtension,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_uint64_of_nat,
};
pub static l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((100000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0: u64 = 0;
pub static l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [115, 121, 109, 83, 105, 109, 112, 86, 97, 114, 105, 97, 110, 116, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2905407695528355166 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Simp_symSimpVariantExtension: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__0_value:
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
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__1_value:
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
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(
    mut v_x_298_: *mut crate::leanh::LeanObject,
    mut v_a_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_300_, 0, v_a_299_);
    crate::leanh::lean_inc_ref_n(v___x_300_, 2);
    v___x_301_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_301_, 0, v___x_300_);
    crate::leanh::lean_ctor_set(v___x_301_, 1, v___x_300_);
    crate::leanh::lean_ctor_set(v___x_301_, 2, v___x_300_);
    return v___x_301_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(
    mut v_x_302_: *mut crate::leanh::LeanObject,
    mut v_a_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_304_ = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(v_x_302_, v_a_303_);
    crate::leanh::lean_dec_ref(v_x_302_);
    return v_res_304_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(
    mut v_a_305_: *mut crate::leanh::LeanObject,
    mut v_b_306_: *mut crate::leanh::LeanObject,
    mut v_x_307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_313_: u8 = 0;
    let mut v___x_314_: u8 = 0;
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_307_) == 0 {
                    crate::leanh::lean_dec(v_b_306_);
                    crate::leanh::lean_dec(v_a_305_);
                    return v_x_307_;
                } else {
                    v_key_308_ = crate::leanh::lean_ctor_get(v_x_307_, 0);
                    v_value_309_ = crate::leanh::lean_ctor_get(v_x_307_, 1);
                    v_tail_310_ = crate::leanh::lean_ctor_get(v_x_307_, 2);
                    v_isSharedCheck_322_ = (!crate::leanh::lean_is_exclusive(v_x_307_)) as u8;
                    if v_isSharedCheck_322_ == 0 {
                        v___x_312_ = v_x_307_;
                        v_isShared_313_ = v_isSharedCheck_322_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_310_);
                        crate::leanh::lean_inc(v_value_309_);
                        crate::leanh::lean_inc(v_key_308_);
                        crate::leanh::lean_dec(v_x_307_);
                        v___x_312_ = crate::leanh::lean_box(0);
                        v_isShared_313_ = v_isSharedCheck_322_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_314_ = lean_name_eq(v_key_308_, v_a_305_);
                if v___x_314_ == 0 {
                    v___x_315_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_305_, v_b_306_, v_tail_310_);
                    if v_isShared_313_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_312_, 2, v___x_315_);
                        v___x_317_ = v___x_312_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_318_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_318_, 0, v_key_308_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_318_, 1, v_value_309_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_318_, 2, v___x_315_);
                        v___x_317_ = v_reuseFailAlloc_318_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_309_);
                    crate::leanh::lean_dec(v_key_308_);
                    if v_isShared_313_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_312_, 1, v_b_306_);
                        crate::leanh::lean_ctor_set(v___x_312_, 0, v_a_305_);
                        v___x_320_ = v___x_312_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_321_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_305_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_321_, 1, v_b_306_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_321_, 2, v_tail_310_);
                        v___x_320_ = v_reuseFailAlloc_321_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_317_;
            }
            3 => {
                return v___x_320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: u64 = 0;
    v___x_323_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_324_ = lean_uint64_of_nat(v___x_323_);
    return v___x_324_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_325_: *mut crate::leanh::LeanObject,
    mut v_x_326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_332_: u8 = 0;
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_335_: u64 = 0;
    let mut v___x_336_: u64 = 0;
    let mut v___x_337_: u64 = 0;
    let mut v_fold_338_: u64 = 0;
    let mut v___x_339_: u64 = 0;
    let mut v___x_340_: u64 = 0;
    let mut v___x_341_: u64 = 0;
    let mut v___x_342_: usize = 0;
    let mut v___x_343_: usize = 0;
    let mut v___x_344_: usize = 0;
    let mut v___x_345_: usize = 0;
    let mut v___x_346_: usize = 0;
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: u64 = 0;
    let mut v_hash_354_: u64 = 0;
    let mut v_isSharedCheck_355_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_326_) == 0 {
                    return v_x_325_;
                } else {
                    v_key_327_ = crate::leanh::lean_ctor_get(v_x_326_, 0);
                    v_value_328_ = crate::leanh::lean_ctor_get(v_x_326_, 1);
                    v_tail_329_ = crate::leanh::lean_ctor_get(v_x_326_, 2);
                    v_isSharedCheck_355_ = (!crate::leanh::lean_is_exclusive(v_x_326_)) as u8;
                    if v_isSharedCheck_355_ == 0 {
                        v___x_331_ = v_x_326_;
                        v_isShared_332_ = v_isSharedCheck_355_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_329_);
                        crate::leanh::lean_inc(v_value_328_);
                        crate::leanh::lean_inc(v_key_327_);
                        crate::leanh::lean_dec(v_x_326_);
                        v___x_331_ = crate::leanh::lean_box(0);
                        v_isShared_332_ = v_isSharedCheck_355_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_333_ = lean_array_get_size(v_x_325_);
                if crate::leanh::lean_obj_tag(v_key_327_) == 0 {
                    v___x_353_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_335_ = v___x_353_;
                    state = 2;
                    continue;
                } else {
                    v_hash_354_ = crate::leanh::lean_ctor_get_uint64(
                        v_key_327_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_335_ = v_hash_354_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_336_ = 32u64;
                v___x_337_ = lean_uint64_shift_right(v___y_335_, v___x_336_);
                v_fold_338_ = lean_uint64_xor(v___y_335_, v___x_337_);
                v___x_339_ = 16u64;
                v___x_340_ = lean_uint64_shift_right(v_fold_338_, v___x_339_);
                v___x_341_ = lean_uint64_xor(v_fold_338_, v___x_340_);
                v___x_342_ = lean_uint64_to_usize(v___x_341_);
                v___x_343_ = lean_usize_of_nat(v___x_333_);
                v___x_344_ = 1usize;
                v___x_345_ = lean_usize_sub(v___x_343_, v___x_344_);
                v___x_346_ = lean_usize_land(v___x_342_, v___x_345_);
                v___x_347_ = lean_array_uget_borrowed(v_x_325_, v___x_346_);
                crate::leanh::lean_inc(v___x_347_);
                if v_isShared_332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_331_, 2, v___x_347_);
                    v___x_349_ = v___x_331_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_352_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_352_, 0, v_key_327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_352_, 1, v_value_328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_352_, 2, v___x_347_);
                    v___x_349_ = v_reuseFailAlloc_352_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_350_ = lean_array_uset(v_x_325_, v___x_346_, v___x_349_);
                v_x_325_ = v___x_350_;
                v_x_326_ = v_tail_329_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(
    mut v_i_356_: *mut crate::leanh::LeanObject,
    mut v_source_357_: *mut crate::leanh::LeanObject,
    mut v_target_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: u8 = 0;
    let mut v_es_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_359_ = lean_array_get_size(v_source_357_);
                v___x_360_ = lean_nat_dec_lt(v_i_356_, v___x_359_);
                if v___x_360_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_357_);
                    crate::leanh::lean_dec(v_i_356_);
                    return v_target_358_;
                } else {
                    v_es_361_ = lean_array_fget(v_source_357_, v_i_356_);
                    v___x_362_ = crate::leanh::lean_box(0);
                    v_source_363_ = lean_array_fset(v_source_357_, v_i_356_, v___x_362_);
                    v_target_364_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_target_358_, v_es_361_);
                    v___x_365_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_366_ = lean_nat_add(v_i_356_, v___x_365_);
                    crate::leanh::lean_dec(v_i_356_);
                    v_i_356_ = v___x_366_;
                    v_source_357_ = v_source_363_;
                    v_target_358_ = v_target_364_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_data_368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = lean_array_get_size(v_data_368_);
    v___x_370_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_371_ = lean_nat_mul(v___x_369_, v___x_370_);
    v___x_372_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_373_ = crate::leanh::lean_box(0);
    v___x_374_ = lean_mk_array(v_nbuckets_371_, v___x_373_);
    v___x_375_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_372_, v_data_368_, v___x_374_);
    return v___x_375_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_a_376_: *mut crate::leanh::LeanObject,
    mut v_x_377_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_378_: u8 = 0;
    let mut v_key_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_377_) == 0 {
                    v___x_378_ = 0;
                    return v___x_378_;
                } else {
                    v_key_379_ = crate::leanh::lean_ctor_get(v_x_377_, 0);
                    v_tail_380_ = crate::leanh::lean_ctor_get(v_x_377_, 2);
                    v___x_381_ = lean_name_eq(v_key_379_, v_a_376_);
                    if v___x_381_ == 0 {
                        v_x_377_ = v_tail_380_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_381_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_a_383_: *mut crate::leanh::LeanObject,
    mut v_x_384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_385_: u8 = 0;
    let mut v_r_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_385_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_383_, v_x_384_);
    crate::leanh::lean_dec(v_x_384_);
    crate::leanh::lean_dec(v_a_383_);
    v_r_386_ = crate::leanh::lean_box((v_res_385_) as usize);
    return v_r_386_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0___redArg(
    mut v_m_387_: *mut crate::leanh::LeanObject,
    mut v_a_388_: *mut crate::leanh::LeanObject,
    mut v_b_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_394_: u8 = 0;
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_397_: u64 = 0;
    let mut v___x_398_: u64 = 0;
    let mut v___x_399_: u64 = 0;
    let mut v_fold_400_: u64 = 0;
    let mut v___x_401_: u64 = 0;
    let mut v___x_402_: u64 = 0;
    let mut v___x_403_: u64 = 0;
    let mut v___x_404_: usize = 0;
    let mut v___x_405_: usize = 0;
    let mut v___x_406_: usize = 0;
    let mut v___x_407_: usize = 0;
    let mut v___x_408_: usize = 0;
    let mut v_bkt_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: u8 = 0;
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: u8 = 0;
    let mut v_val_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: u64 = 0;
    let mut v_hash_436_: u64 = 0;
    let mut v_isSharedCheck_437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_390_ = crate::leanh::lean_ctor_get(v_m_387_, 0);
                v_buckets_391_ = crate::leanh::lean_ctor_get(v_m_387_, 1);
                v_isSharedCheck_437_ = (!crate::leanh::lean_is_exclusive(v_m_387_)) as u8;
                if v_isSharedCheck_437_ == 0 {
                    v___x_393_ = v_m_387_;
                    v_isShared_394_ = v_isSharedCheck_437_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_391_);
                    crate::leanh::lean_inc(v_size_390_);
                    crate::leanh::lean_dec(v_m_387_);
                    v___x_393_ = crate::leanh::lean_box(0);
                    v_isShared_394_ = v_isSharedCheck_437_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_395_ = lean_array_get_size(v_buckets_391_);
                if crate::leanh::lean_obj_tag(v_a_388_) == 0 {
                    v___x_435_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_397_ = v___x_435_;
                    state = 2;
                    continue;
                } else {
                    v_hash_436_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_388_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_397_ = v_hash_436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_398_ = 32u64;
                v___x_399_ = lean_uint64_shift_right(v___y_397_, v___x_398_);
                v_fold_400_ = lean_uint64_xor(v___y_397_, v___x_399_);
                v___x_401_ = 16u64;
                v___x_402_ = lean_uint64_shift_right(v_fold_400_, v___x_401_);
                v___x_403_ = lean_uint64_xor(v_fold_400_, v___x_402_);
                v___x_404_ = lean_uint64_to_usize(v___x_403_);
                v___x_405_ = lean_usize_of_nat(v___x_395_);
                v___x_406_ = 1usize;
                v___x_407_ = lean_usize_sub(v___x_405_, v___x_406_);
                v___x_408_ = lean_usize_land(v___x_404_, v___x_407_);
                v_bkt_409_ = lean_array_uget_borrowed(v_buckets_391_, v___x_408_);
                v___x_410_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_388_, v_bkt_409_);
                if v___x_410_ == 0 {
                    v___x_411_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_412_ = lean_nat_add(v_size_390_, v___x_411_);
                    crate::leanh::lean_dec(v_size_390_);
                    crate::leanh::lean_inc(v_bkt_409_);
                    v___x_413_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_413_, 0, v_a_388_);
                    crate::leanh::lean_ctor_set(v___x_413_, 1, v_b_389_);
                    crate::leanh::lean_ctor_set(v___x_413_, 2, v_bkt_409_);
                    v_buckets_x27_414_ = lean_array_uset(v_buckets_391_, v___x_408_, v___x_413_);
                    v___x_415_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_416_ = lean_nat_mul(v_size_x27_412_, v___x_415_);
                    v___x_417_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_418_ = lean_nat_div(v___x_416_, v___x_417_);
                    crate::leanh::lean_dec(v___x_416_);
                    v___x_419_ = lean_array_get_size(v_buckets_x27_414_);
                    v___x_420_ = lean_nat_dec_le(v___x_418_, v___x_419_);
                    crate::leanh::lean_dec(v___x_418_);
                    if v___x_420_ == 0 {
                        v_val_421_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_414_);
                        if v_isShared_394_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_393_, 1, v_val_421_);
                            crate::leanh::lean_ctor_set(v___x_393_, 0, v_size_x27_412_);
                            v___x_423_ = v___x_393_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_424_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_424_, 0, v_size_x27_412_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_424_, 1, v_val_421_);
                            v___x_423_ = v_reuseFailAlloc_424_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_394_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_393_, 1, v_buckets_x27_414_);
                            crate::leanh::lean_ctor_set(v___x_393_, 0, v_size_x27_412_);
                            v___x_426_ = v___x_393_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_427_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_427_, 0, v_size_x27_412_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_427_,
                                1,
                                v_buckets_x27_414_,
                            );
                            v___x_426_ = v_reuseFailAlloc_427_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_409_);
                    v___x_428_ = crate::leanh::lean_box(0);
                    v_buckets_x27_429_ = lean_array_uset(v_buckets_391_, v___x_408_, v___x_428_);
                    v___x_430_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_388_, v_b_389_, v_bkt_409_);
                    v___x_431_ = lean_array_uset(v_buckets_x27_429_, v___x_408_, v___x_430_);
                    if v_isShared_394_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_393_, 1, v___x_431_);
                        v___x_433_ = v___x_393_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_434_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_434_, 0, v_size_390_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_431_);
                        v___x_433_ = v_reuseFailAlloc_434_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_423_;
            }
            4 => {
                return v___x_426_;
            }
            5 => {
                return v___x_433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(
    mut v_map_438_: *mut crate::leanh::LeanObject,
    mut v_entry_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_variant_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_440_ = crate::leanh::lean_ctor_get(v_entry_439_, 0);
    crate::leanh::lean_inc(v_name_440_);
    v_variant_441_ = crate::leanh::lean_ctor_get(v_entry_439_, 1);
    crate::leanh::lean_inc_ref(v_variant_441_);
    crate::leanh::lean_dec_ref(v_entry_439_);
    v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0___redArg(v_map_438_, v_name_440_, v_variant_441_);
    return v___x_442_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(
    mut v___y_443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v___y_443_);
    return v___y_443_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(
    mut v___y_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_445_ = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(v___y_444_);
    crate::leanh::lean_dec_ref(v___y_444_);
    return v_res_445_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = crate::leanh::lean_box(0);
    v___x_453_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_454_ = lean_mk_array(v___x_453_, v___x_452_);
    return v___x_454_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_);
    v___x_456_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_457_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_457_, 0, v___x_456_);
    crate::leanh::lean_ctor_set(v___x_457_, 1, v___x_455_);
    return v___x_457_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_458_ = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_;
    v___f_459_ = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_;
    v___x_460_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_);
    v___f_461_ = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_;
    v___x_462_ = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_;
    v___x_463_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_463_, 0, v___x_462_);
    crate::leanh::lean_ctor_set(v___x_463_, 1, v___f_461_);
    crate::leanh::lean_ctor_set(v___x_463_, 2, v___x_460_);
    crate::leanh::lean_ctor_set(v___x_463_, 3, v___f_459_);
    crate::leanh::lean_ctor_set(v___x_463_, 4, v___f_458_);
    return v___x_463_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_465_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_);
    v___x_466_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_465_);
    return v___x_466_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(
    mut v_a_467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_468_ = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_();
    return v_res_468_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_469_: *mut crate::leanh::LeanObject,
    mut v_m_470_: *mut crate::leanh::LeanObject,
    mut v_a_471_: *mut crate::leanh::LeanObject,
    mut v_b_472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0___redArg(v_m_470_, v_a_471_, v_b_472_);
    return v___x_473_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_474_: *mut crate::leanh::LeanObject,
    mut v_a_475_: *mut crate::leanh::LeanObject,
    mut v_x_476_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_477_: u8 = 0;
    v___x_477_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_475_, v_x_476_);
    return v___x_477_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b2_478_: *mut crate::leanh::LeanObject,
    mut v_a_479_: *mut crate::leanh::LeanObject,
    mut v_x_480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_481_: u8 = 0;
    let mut v_r_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_478_, v_a_479_, v_x_480_);
    crate::leanh::lean_dec(v_x_480_);
    crate::leanh::lean_dec(v_a_479_);
    v_r_482_ = crate::leanh::lean_box((v_res_481_) as usize);
    return v_r_482_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_483_: *mut crate::leanh::LeanObject,
    mut v_data_484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_485_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_484_);
    return v___x_485_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2(
    mut v_00_u03b2_486_: *mut crate::leanh::LeanObject,
    mut v_a_487_: *mut crate::leanh::LeanObject,
    mut v_b_488_: *mut crate::leanh::LeanObject,
    mut v_x_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_487_, v_b_488_, v_x_489_);
    return v___x_490_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2(
    mut v_00_u03b2_491_: *mut crate::leanh::LeanObject,
    mut v_i_492_: *mut crate::leanh::LeanObject,
    mut v_source_493_: *mut crate::leanh::LeanObject,
    mut v_target_494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_495_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_492_, v_source_493_, v_target_494_);
    return v___x_495_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_496_: *mut crate::leanh::LeanObject,
    mut v_x_497_: *mut crate::leanh::LeanObject,
    mut v_x_498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_497_, v_x_498_);
    return v___x_499_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(
    mut v_a_500_: *mut crate::leanh::LeanObject,
    mut v_x_501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: u8 = 0;
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_501_) == 0 {
                    v___x_502_ = crate::leanh::lean_box(0);
                    return v___x_502_;
                } else {
                    v_key_503_ = crate::leanh::lean_ctor_get(v_x_501_, 0);
                    v_value_504_ = crate::leanh::lean_ctor_get(v_x_501_, 1);
                    v_tail_505_ = crate::leanh::lean_ctor_get(v_x_501_, 2);
                    v___x_506_ = lean_name_eq(v_key_503_, v_a_500_);
                    if v___x_506_ == 0 {
                        v_x_501_ = v_tail_505_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_504_);
                        v___x_508_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_508_, 0, v_value_504_);
                        return v___x_508_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg___boxed(
    mut v_a_509_: *mut crate::leanh::LeanObject,
    mut v_x_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_511_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(v_a_509_, v_x_510_);
    crate::leanh::lean_dec(v_x_510_);
    crate::leanh::lean_dec(v_a_509_);
    return v_res_511_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(
    mut v_m_512_: *mut crate::leanh::LeanObject,
    mut v_a_513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_517_: u64 = 0;
    let mut v___x_518_: u64 = 0;
    let mut v___x_519_: u64 = 0;
    let mut v_fold_520_: u64 = 0;
    let mut v___x_521_: u64 = 0;
    let mut v___x_522_: u64 = 0;
    let mut v___x_523_: u64 = 0;
    let mut v___x_524_: usize = 0;
    let mut v___x_525_: usize = 0;
    let mut v___x_526_: usize = 0;
    let mut v___x_527_: usize = 0;
    let mut v___x_528_: usize = 0;
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: u64 = 0;
    let mut v_hash_532_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_514_ = crate::leanh::lean_ctor_get(v_m_512_, 1);
                v___x_515_ = lean_array_get_size(v_buckets_514_);
                if crate::leanh::lean_obj_tag(v_a_513_) == 0 {
                    v___x_531_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_517_ = v___x_531_;
                    state = 1;
                    continue;
                } else {
                    v_hash_532_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_513_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_517_ = v_hash_532_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_518_ = 32u64;
                v___x_519_ = lean_uint64_shift_right(v___y_517_, v___x_518_);
                v_fold_520_ = lean_uint64_xor(v___y_517_, v___x_519_);
                v___x_521_ = 16u64;
                v___x_522_ = lean_uint64_shift_right(v_fold_520_, v___x_521_);
                v___x_523_ = lean_uint64_xor(v_fold_520_, v___x_522_);
                v___x_524_ = lean_uint64_to_usize(v___x_523_);
                v___x_525_ = lean_usize_of_nat(v___x_515_);
                v___x_526_ = 1usize;
                v___x_527_ = lean_usize_sub(v___x_525_, v___x_526_);
                v___x_528_ = lean_usize_land(v___x_524_, v___x_527_);
                v___x_529_ = lean_array_uget_borrowed(v_buckets_514_, v___x_528_);
                v___x_530_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(v_a_513_, v___x_529_);
                return v___x_530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg___boxed(
    mut v_m_533_: *mut crate::leanh::LeanObject,
    mut v_a_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(v_m_533_, v_a_534_);
    crate::leanh::lean_dec(v_a_534_);
    crate::leanh::lean_dec_ref(v_m_533_);
    return v_res_535_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_538_ = l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__1;
    v___x_539_ = l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__0;
    v___x_540_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_539_,
        v___x_538_,
    );
    return v___x_540_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(
    mut v_env_541_: *mut crate::leanh::LeanObject,
    mut v_name_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = l_Lean_Meta_Sym_Simp_symSimpVariantExtension;
    v_ext_544_ = crate::leanh::lean_ctor_get(v___x_543_, 1);
    v_toEnvExtension_545_ = crate::leanh::lean_ctor_get(v_ext_544_, 0);
    v_asyncMode_546_ = crate::leanh::lean_ctor_get(v_toEnvExtension_545_, 2);
    v___x_547_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2_once),
        _init_l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2,
    );
    v___x_548_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_547_,
        v___x_543_,
        v_env_541_,
        v_asyncMode_546_,
    );
    v___x_549_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(v___x_548_, v_name_542_);
    crate::leanh::lean_dec(v___x_548_);
    return v___x_549_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___boxed(
    mut v_env_550_: *mut crate::leanh::LeanObject,
    mut v_name_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_552_ = l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(v_env_550_, v_name_551_);
    crate::leanh::lean_dec(v_name_551_);
    return v_res_552_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0(
    mut v_00_u03b2_553_: *mut crate::leanh::LeanObject,
    mut v_m_554_: *mut crate::leanh::LeanObject,
    mut v_a_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(v_m_554_, v_a_555_);
    return v___x_556_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___boxed(
    mut v_00_u03b2_557_: *mut crate::leanh::LeanObject,
    mut v_m_558_: *mut crate::leanh::LeanObject,
    mut v_a_559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0(v_00_u03b2_557_, v_m_558_, v_a_559_);
    crate::leanh::lean_dec(v_a_559_);
    crate::leanh::lean_dec_ref(v_m_558_);
    return v_res_560_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0(
    mut v_00_u03b2_561_: *mut crate::leanh::LeanObject,
    mut v_a_562_: *mut crate::leanh::LeanObject,
    mut v_x_563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(v_a_562_, v_x_563_);
    return v___x_564_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_565_: *mut crate::leanh::LeanObject,
    mut v_a_566_: *mut crate::leanh::LeanObject,
    mut v_x_567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_568_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0(v_00_u03b2_565_, v_a_566_, v_x_567_);
    crate::leanh::lean_dec(v_x_567_);
    crate::leanh::lean_dec(v_a_566_);
    return v_res_568_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Variant(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Sym_Simp_symSimpVariantExtension = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Sym_Simp_symSimpVariantExtension);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Variant(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Variant(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_ScopedEnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Variant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Variant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Variant(builtin);
}
