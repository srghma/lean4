// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Variant
// Imports: Lean.Meta.Sym.DSimp.DSimpM Lean.ScopedEnvExtension
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_uget_borrowed,
    lean_array_uset, lean_mk_array, lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed};
use crate::r#gen::Lean::Meta::Sym::DSimp::DSimpM::{
    initialize_Lean_Meta_Sym_DSimp_DSimpM, runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM,
};
use crate::r#gen::Lean::ScopedEnvExtension::{
    initialize_Lean_ScopedEnvExtension, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg, runtime_initialize_Lean_ScopedEnvExtension,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((100000 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant: *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value
)
    as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0: u64 = 0;
pub static l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__3_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [115, 121, 109, 68, 83, 105, 109, 112, 86, 97, 114, 105, 97, 110, 116, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__3_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__3_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__4_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__3_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6486340147710861728 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__4_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__4_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0_value:
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
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__1_value:
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
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(
    mut v_x_292_: *mut leanh::LeanObject,
    mut v_a_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_294_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_294_, 0, v_a_293_);
    leanh::lean_inc_ref_n(v___x_294_, 2);
    v___x_295_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_295_, 0, v___x_294_);
    leanh::lean_ctor_set(v___x_295_, 1, v___x_294_);
    leanh::lean_ctor_set(v___x_295_, 2, v___x_294_);
    return v___x_295_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(
    mut v_x_296_: *mut leanh::LeanObject,
    mut v_a_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_298_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(v_x_296_, v_a_297_);
    leanh::lean_dec_ref(v_x_296_);
    return v_res_298_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: u64 = 0;
    v___x_299_ = leanh::lean_unsigned_to_nat(1723);
    v___x_300_ = lean_uint64_of_nat(v___x_299_);
    return v___x_300_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_301_: *mut leanh::LeanObject,
    mut v_x_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_308_: u8 = 0;
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_311_: u64 = 0;
    let mut v___x_312_: u64 = 0;
    let mut v___x_313_: u64 = 0;
    let mut v_fold_314_: u64 = 0;
    let mut v___x_315_: u64 = 0;
    let mut v___x_316_: u64 = 0;
    let mut v___x_317_: u64 = 0;
    let mut v___x_318_: usize = 0;
    let mut v___x_319_: usize = 0;
    let mut v___x_320_: usize = 0;
    let mut v___x_321_: usize = 0;
    let mut v___x_322_: usize = 0;
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: u64 = 0;
    let mut v_hash_330_: u64 = 0;
    let mut v_isSharedCheck_331_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_302_) == 0 {
                    return v_x_301_;
                } else {
                    v_key_303_ = leanh::lean_ctor_get(v_x_302_, 0);
                    v_value_304_ = leanh::lean_ctor_get(v_x_302_, 1);
                    v_tail_305_ = leanh::lean_ctor_get(v_x_302_, 2);
                    v_isSharedCheck_331_ = (!leanh::lean_is_exclusive(v_x_302_)) as u8;
                    if v_isSharedCheck_331_ == 0 {
                        v___x_307_ = v_x_302_;
                        v_isShared_308_ = v_isSharedCheck_331_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_305_);
                        leanh::lean_inc(v_value_304_);
                        leanh::lean_inc(v_key_303_);
                        leanh::lean_dec(v_x_302_);
                        v___x_307_ = leanh::lean_box(0);
                        v_isShared_308_ = v_isSharedCheck_331_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_309_ = lean_array_get_size(v_x_301_);
                if leanh::lean_obj_tag(v_key_303_) == 0 {
                    v___x_329_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_311_ = v___x_329_;
                    state = 2;
                    continue;
                } else {
                    v_hash_330_ = leanh::lean_ctor_get_uint64(
                        v_key_303_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_311_ = v_hash_330_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_312_ = 32u64;
                v___x_313_ = lean_uint64_shift_right(v___y_311_, v___x_312_);
                v_fold_314_ = lean_uint64_xor(v___y_311_, v___x_313_);
                v___x_315_ = 16u64;
                v___x_316_ = lean_uint64_shift_right(v_fold_314_, v___x_315_);
                v___x_317_ = lean_uint64_xor(v_fold_314_, v___x_316_);
                v___x_318_ = lean_uint64_to_usize(v___x_317_);
                v___x_319_ = lean_usize_of_nat(v___x_309_);
                v___x_320_ = 1usize;
                v___x_321_ = lean_usize_sub(v___x_319_, v___x_320_);
                v___x_322_ = lean_usize_land(v___x_318_, v___x_321_);
                v___x_323_ = lean_array_uget_borrowed(v_x_301_, v___x_322_);
                leanh::lean_inc(v___x_323_);
                if v_isShared_308_ == 0 {
                    leanh::lean_ctor_set(v___x_307_, 2, v___x_323_);
                    v___x_325_ = v___x_307_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_328_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_328_, 0, v_key_303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_328_, 1, v_value_304_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_328_, 2, v___x_323_);
                    v___x_325_ = v_reuseFailAlloc_328_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_326_ = lean_array_uset(v_x_301_, v___x_322_, v___x_325_);
                v_x_301_ = v___x_326_;
                v_x_302_ = v_tail_305_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(
    mut v_i_332_: *mut leanh::LeanObject,
    mut v_source_333_: *mut leanh::LeanObject,
    mut v_target_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: u8 = 0;
    let mut v_es_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_335_ = lean_array_get_size(v_source_333_);
                v___x_336_ = lean_nat_dec_lt(v_i_332_, v___x_335_);
                if v___x_336_ == 0 {
                    leanh::lean_dec_ref(v_source_333_);
                    leanh::lean_dec(v_i_332_);
                    return v_target_334_;
                } else {
                    v_es_337_ = lean_array_fget(v_source_333_, v_i_332_);
                    v___x_338_ = leanh::lean_box(0);
                    v_source_339_ = lean_array_fset(v_source_333_, v_i_332_, v___x_338_);
                    v_target_340_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_target_334_, v_es_337_);
                    v___x_341_ = leanh::lean_unsigned_to_nat(1);
                    v___x_342_ = lean_nat_add(v_i_332_, v___x_341_);
                    leanh::lean_dec(v_i_332_);
                    v_i_332_ = v___x_342_;
                    v_source_333_ = v_source_339_;
                    v_target_334_ = v_target_340_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_data_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_345_ = lean_array_get_size(v_data_344_);
    v___x_346_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_347_ = lean_nat_mul(v___x_345_, v___x_346_);
    v___x_348_ = leanh::lean_unsigned_to_nat(0);
    v___x_349_ = leanh::lean_box(0);
    v___x_350_ = lean_mk_array(v_nbuckets_347_, v___x_349_);
    v___x_351_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_348_, v_data_344_, v___x_350_);
    return v___x_351_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_a_352_: *mut leanh::LeanObject,
    mut v_x_353_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_354_: u8 = 0;
    let mut v_key_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_353_) == 0 {
                    v___x_354_ = 0;
                    return v___x_354_;
                } else {
                    v_key_355_ = leanh::lean_ctor_get(v_x_353_, 0);
                    v_tail_356_ = leanh::lean_ctor_get(v_x_353_, 2);
                    v___x_357_ = lean_name_eq(v_key_355_, v_a_352_);
                    if v___x_357_ == 0 {
                        v_x_353_ = v_tail_356_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_357_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_a_359_: *mut leanh::LeanObject,
    mut v_x_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_361_: u8 = 0;
    let mut v_r_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_359_, v_x_360_);
    leanh::lean_dec(v_x_360_);
    leanh::lean_dec(v_a_359_);
    v_r_362_ = leanh::lean_box((v_res_361_) as usize);
    return v_r_362_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(
    mut v_a_363_: *mut leanh::LeanObject,
    mut v_b_364_: *mut leanh::LeanObject,
    mut v_x_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_371_: u8 = 0;
    let mut v___x_372_: u8 = 0;
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_365_) == 0 {
                    leanh::lean_dec(v_b_364_);
                    leanh::lean_dec(v_a_363_);
                    return v_x_365_;
                } else {
                    v_key_366_ = leanh::lean_ctor_get(v_x_365_, 0);
                    v_value_367_ = leanh::lean_ctor_get(v_x_365_, 1);
                    v_tail_368_ = leanh::lean_ctor_get(v_x_365_, 2);
                    v_isSharedCheck_380_ = (!leanh::lean_is_exclusive(v_x_365_)) as u8;
                    if v_isSharedCheck_380_ == 0 {
                        v___x_370_ = v_x_365_;
                        v_isShared_371_ = v_isSharedCheck_380_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_368_);
                        leanh::lean_inc(v_value_367_);
                        leanh::lean_inc(v_key_366_);
                        leanh::lean_dec(v_x_365_);
                        v___x_370_ = leanh::lean_box(0);
                        v_isShared_371_ = v_isSharedCheck_380_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_372_ = lean_name_eq(v_key_366_, v_a_363_);
                if v___x_372_ == 0 {
                    v___x_373_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_363_, v_b_364_, v_tail_368_);
                    if v_isShared_371_ == 0 {
                        leanh::lean_ctor_set(v___x_370_, 2, v___x_373_);
                        v___x_375_ = v___x_370_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_376_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_376_, 0, v_key_366_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_376_, 1, v_value_367_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_376_, 2, v___x_373_);
                        v___x_375_ = v_reuseFailAlloc_376_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_367_);
                    leanh::lean_dec(v_key_366_);
                    if v_isShared_371_ == 0 {
                        leanh::lean_ctor_set(v___x_370_, 1, v_b_364_);
                        leanh::lean_ctor_set(v___x_370_, 0, v_a_363_);
                        v___x_378_ = v___x_370_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_379_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_363_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_379_, 1, v_b_364_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_379_, 2, v_tail_368_);
                        v___x_378_ = v_reuseFailAlloc_379_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_375_;
            }
            3 => {
                return v___x_378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(
    mut v_m_381_: *mut leanh::LeanObject,
    mut v_a_382_: *mut leanh::LeanObject,
    mut v_b_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_388_: u8 = 0;
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_391_: u64 = 0;
    let mut v___x_392_: u64 = 0;
    let mut v___x_393_: u64 = 0;
    let mut v_fold_394_: u64 = 0;
    let mut v___x_395_: u64 = 0;
    let mut v___x_396_: u64 = 0;
    let mut v___x_397_: u64 = 0;
    let mut v___x_398_: usize = 0;
    let mut v___x_399_: usize = 0;
    let mut v___x_400_: usize = 0;
    let mut v___x_401_: usize = 0;
    let mut v___x_402_: usize = 0;
    let mut v_bkt_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: u8 = 0;
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: u8 = 0;
    let mut v_val_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: u64 = 0;
    let mut v_hash_430_: u64 = 0;
    let mut v_isSharedCheck_431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_384_ = leanh::lean_ctor_get(v_m_381_, 0);
                v_buckets_385_ = leanh::lean_ctor_get(v_m_381_, 1);
                v_isSharedCheck_431_ = (!leanh::lean_is_exclusive(v_m_381_)) as u8;
                if v_isSharedCheck_431_ == 0 {
                    v___x_387_ = v_m_381_;
                    v_isShared_388_ = v_isSharedCheck_431_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_385_);
                    leanh::lean_inc(v_size_384_);
                    leanh::lean_dec(v_m_381_);
                    v___x_387_ = leanh::lean_box(0);
                    v_isShared_388_ = v_isSharedCheck_431_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_389_ = lean_array_get_size(v_buckets_385_);
                if leanh::lean_obj_tag(v_a_382_) == 0 {
                    v___x_429_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_391_ = v___x_429_;
                    state = 2;
                    continue;
                } else {
                    v_hash_430_ = leanh::lean_ctor_get_uint64(
                        v_a_382_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_391_ = v_hash_430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_392_ = 32u64;
                v___x_393_ = lean_uint64_shift_right(v___y_391_, v___x_392_);
                v_fold_394_ = lean_uint64_xor(v___y_391_, v___x_393_);
                v___x_395_ = 16u64;
                v___x_396_ = lean_uint64_shift_right(v_fold_394_, v___x_395_);
                v___x_397_ = lean_uint64_xor(v_fold_394_, v___x_396_);
                v___x_398_ = lean_uint64_to_usize(v___x_397_);
                v___x_399_ = lean_usize_of_nat(v___x_389_);
                v___x_400_ = 1usize;
                v___x_401_ = lean_usize_sub(v___x_399_, v___x_400_);
                v___x_402_ = lean_usize_land(v___x_398_, v___x_401_);
                v_bkt_403_ = lean_array_uget_borrowed(v_buckets_385_, v___x_402_);
                v___x_404_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_382_, v_bkt_403_);
                if v___x_404_ == 0 {
                    v___x_405_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_406_ = lean_nat_add(v_size_384_, v___x_405_);
                    leanh::lean_dec(v_size_384_);
                    leanh::lean_inc(v_bkt_403_);
                    v___x_407_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_407_, 0, v_a_382_);
                    leanh::lean_ctor_set(v___x_407_, 1, v_b_383_);
                    leanh::lean_ctor_set(v___x_407_, 2, v_bkt_403_);
                    v_buckets_x27_408_ = lean_array_uset(v_buckets_385_, v___x_402_, v___x_407_);
                    v___x_409_ = leanh::lean_unsigned_to_nat(4);
                    v___x_410_ = lean_nat_mul(v_size_x27_406_, v___x_409_);
                    v___x_411_ = leanh::lean_unsigned_to_nat(3);
                    v___x_412_ = lean_nat_div(v___x_410_, v___x_411_);
                    leanh::lean_dec(v___x_410_);
                    v___x_413_ = lean_array_get_size(v_buckets_x27_408_);
                    v___x_414_ = lean_nat_dec_le(v___x_412_, v___x_413_);
                    leanh::lean_dec(v___x_412_);
                    if v___x_414_ == 0 {
                        v_val_415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_408_);
                        if v_isShared_388_ == 0 {
                            leanh::lean_ctor_set(v___x_387_, 1, v_val_415_);
                            leanh::lean_ctor_set(v___x_387_, 0, v_size_x27_406_);
                            v___x_417_ = v___x_387_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_418_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_418_, 0, v_size_x27_406_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_418_, 1, v_val_415_);
                            v___x_417_ = v_reuseFailAlloc_418_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_388_ == 0 {
                            leanh::lean_ctor_set(v___x_387_, 1, v_buckets_x27_408_);
                            leanh::lean_ctor_set(v___x_387_, 0, v_size_x27_406_);
                            v___x_420_ = v___x_387_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_421_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_421_, 0, v_size_x27_406_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_421_,
                                1,
                                v_buckets_x27_408_,
                            );
                            v___x_420_ = v_reuseFailAlloc_421_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_403_);
                    v___x_422_ = leanh::lean_box(0);
                    v_buckets_x27_423_ = lean_array_uset(v_buckets_385_, v___x_402_, v___x_422_);
                    v___x_424_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_382_, v_b_383_, v_bkt_403_);
                    v___x_425_ = lean_array_uset(v_buckets_x27_423_, v___x_402_, v___x_424_);
                    if v_isShared_388_ == 0 {
                        leanh::lean_ctor_set(v___x_387_, 1, v___x_425_);
                        v___x_427_ = v___x_387_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_428_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_428_, 0, v_size_384_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_428_, 1, v___x_425_);
                        v___x_427_ = v_reuseFailAlloc_428_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_417_;
            }
            4 => {
                return v___x_420_;
            }
            5 => {
                return v___x_427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(
    mut v_map_432_: *mut leanh::LeanObject,
    mut v_entry_433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_variant_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_434_ = leanh::lean_ctor_get(v_entry_433_, 0);
    leanh::lean_inc(v_name_434_);
    v_variant_435_ = leanh::lean_ctor_get(v_entry_433_, 1);
    leanh::lean_inc_ref(v_variant_435_);
    leanh::lean_dec_ref(v_entry_433_);
    v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_map_432_, v_name_434_, v_variant_435_);
    return v___x_436_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(
    mut v___y_437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v___y_437_);
    return v___y_437_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(
    mut v___y_438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_439_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(v___y_438_);
    leanh::lean_dec_ref(v___y_438_);
    return v_res_439_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = leanh::lean_box(0);
    v___x_447_ = leanh::lean_unsigned_to_nat(16);
    v___x_448_ = lean_mk_array(v___x_447_, v___x_446_);
    return v___x_448_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_449_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
    v___x_450_ = leanh::lean_unsigned_to_nat(0);
    v___x_451_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_451_, 0, v___x_450_);
    leanh::lean_ctor_set(v___x_451_, 1, v___x_449_);
    return v___x_451_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_452_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_;
    v___f_453_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_;
    v___x_454_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
    v___f_455_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_;
    v___x_456_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__4_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_;
    v___x_457_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_457_, 0, v___x_456_);
    leanh::lean_ctor_set(v___x_457_, 1, v___f_455_);
    leanh::lean_ctor_set(v___x_457_, 2, v___x_454_);
    leanh::lean_ctor_set(v___x_457_, 3, v___f_453_);
    leanh::lean_ctor_set(v___x_457_, 4, v___f_452_);
    return v___x_457_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_459_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
    v___x_460_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_459_);
    return v___x_460_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(
    mut v_a_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_();
    return v_res_462_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_463_: *mut leanh::LeanObject,
    mut v_m_464_: *mut leanh::LeanObject,
    mut v_a_465_: *mut leanh::LeanObject,
    mut v_b_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_m_464_, v_a_465_, v_b_466_);
    return v___x_467_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_468_: *mut leanh::LeanObject,
    mut v_a_469_: *mut leanh::LeanObject,
    mut v_x_470_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_471_: u8 = 0;
    v___x_471_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_469_, v_x_470_);
    return v___x_471_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b2_472_: *mut leanh::LeanObject,
    mut v_a_473_: *mut leanh::LeanObject,
    mut v_x_474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_475_: u8 = 0;
    let mut v_r_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_475_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_472_, v_a_473_, v_x_474_);
    leanh::lean_dec(v_x_474_);
    leanh::lean_dec(v_a_473_);
    v_r_476_ = leanh::lean_box((v_res_475_) as usize);
    return v_r_476_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_477_: *mut leanh::LeanObject,
    mut v_data_478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_478_);
    return v___x_479_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2(
    mut v_00_u03b2_480_: *mut leanh::LeanObject,
    mut v_a_481_: *mut leanh::LeanObject,
    mut v_b_482_: *mut leanh::LeanObject,
    mut v_x_483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_484_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_481_, v_b_482_, v_x_483_);
    return v___x_484_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2(
    mut v_00_u03b2_485_: *mut leanh::LeanObject,
    mut v_i_486_: *mut leanh::LeanObject,
    mut v_source_487_: *mut leanh::LeanObject,
    mut v_target_488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_486_, v_source_487_, v_target_488_);
    return v___x_489_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_490_: *mut leanh::LeanObject,
    mut v_x_491_: *mut leanh::LeanObject,
    mut v_x_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_491_, v_x_492_);
    return v___x_493_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(
    mut v_a_494_: *mut leanh::LeanObject,
    mut v_x_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_495_) == 0 {
                    v___x_496_ = leanh::lean_box(0);
                    return v___x_496_;
                } else {
                    v_key_497_ = leanh::lean_ctor_get(v_x_495_, 0);
                    v_value_498_ = leanh::lean_ctor_get(v_x_495_, 1);
                    v_tail_499_ = leanh::lean_ctor_get(v_x_495_, 2);
                    v___x_500_ = lean_name_eq(v_key_497_, v_a_494_);
                    if v___x_500_ == 0 {
                        v_x_495_ = v_tail_499_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_498_);
                        v___x_502_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_502_, 0, v_value_498_);
                        return v___x_502_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg___boxed(
    mut v_a_503_: *mut leanh::LeanObject,
    mut v_x_504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_505_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_503_, v_x_504_);
    leanh::lean_dec(v_x_504_);
    leanh::lean_dec(v_a_503_);
    return v_res_505_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(
    mut v_m_506_: *mut leanh::LeanObject,
    mut v_a_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_511_: u64 = 0;
    let mut v___x_512_: u64 = 0;
    let mut v___x_513_: u64 = 0;
    let mut v_fold_514_: u64 = 0;
    let mut v___x_515_: u64 = 0;
    let mut v___x_516_: u64 = 0;
    let mut v___x_517_: u64 = 0;
    let mut v___x_518_: usize = 0;
    let mut v___x_519_: usize = 0;
    let mut v___x_520_: usize = 0;
    let mut v___x_521_: usize = 0;
    let mut v___x_522_: usize = 0;
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: u64 = 0;
    let mut v_hash_526_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_508_ = leanh::lean_ctor_get(v_m_506_, 1);
                v___x_509_ = lean_array_get_size(v_buckets_508_);
                if leanh::lean_obj_tag(v_a_507_) == 0 {
                    v___x_525_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_511_ = v___x_525_;
                    state = 1;
                    continue;
                } else {
                    v_hash_526_ = leanh::lean_ctor_get_uint64(
                        v_a_507_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_511_ = v_hash_526_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_512_ = 32u64;
                v___x_513_ = lean_uint64_shift_right(v___y_511_, v___x_512_);
                v_fold_514_ = lean_uint64_xor(v___y_511_, v___x_513_);
                v___x_515_ = 16u64;
                v___x_516_ = lean_uint64_shift_right(v_fold_514_, v___x_515_);
                v___x_517_ = lean_uint64_xor(v_fold_514_, v___x_516_);
                v___x_518_ = lean_uint64_to_usize(v___x_517_);
                v___x_519_ = lean_usize_of_nat(v___x_509_);
                v___x_520_ = 1usize;
                v___x_521_ = lean_usize_sub(v___x_519_, v___x_520_);
                v___x_522_ = lean_usize_land(v___x_518_, v___x_521_);
                v___x_523_ = lean_array_uget_borrowed(v_buckets_508_, v___x_522_);
                v___x_524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_507_, v___x_523_);
                return v___x_524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg___boxed(
    mut v_m_527_: *mut leanh::LeanObject,
    mut v_a_528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v_m_527_, v_a_528_);
    leanh::lean_dec(v_a_528_);
    leanh::lean_dec_ref(v_m_527_);
    return v_res_529_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_532_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__1;
    v___x_533_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0;
    v___x_534_ = l_Std_HashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_533_,
        v___x_532_,
    );
    return v___x_534_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(
    mut v_env_535_: *mut leanh::LeanObject,
    mut v_name_536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_537_ = l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension;
    v_ext_538_ = leanh::lean_ctor_get(v___x_537_, 1);
    v_toEnvExtension_539_ = leanh::lean_ctor_get(v_ext_538_, 0);
    v_asyncMode_540_ = leanh::lean_ctor_get(v_toEnvExtension_539_, 2);
    v___x_541_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2_once),
        _init_l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2,
    );
    v___x_542_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_541_,
        v___x_537_,
        v_env_535_,
        v_asyncMode_540_,
    );
    v___x_543_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v___x_542_, v_name_536_);
    leanh::lean_dec(v___x_542_);
    return v___x_543_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___boxed(
    mut v_env_544_: *mut leanh::LeanObject,
    mut v_name_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_546_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(v_env_544_, v_name_545_);
    leanh::lean_dec(v_name_545_);
    return v_res_546_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0(
    mut v_00_u03b2_547_: *mut leanh::LeanObject,
    mut v_m_548_: *mut leanh::LeanObject,
    mut v_a_549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v_m_548_, v_a_549_);
    return v___x_550_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___boxed(
    mut v_00_u03b2_551_: *mut leanh::LeanObject,
    mut v_m_552_: *mut leanh::LeanObject,
    mut v_a_553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0(v_00_u03b2_551_, v_m_552_, v_a_553_);
    leanh::lean_dec(v_a_553_);
    leanh::lean_dec_ref(v_m_552_);
    return v_res_554_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(
    mut v_00_u03b2_555_: *mut leanh::LeanObject,
    mut v_a_556_: *mut leanh::LeanObject,
    mut v_x_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_558_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_556_, v_x_557_);
    return v___x_558_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_559_: *mut leanh::LeanObject,
    mut v_a_560_: *mut leanh::LeanObject,
    mut v_x_561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(v_00_u03b2_559_, v_a_560_, v_x_561_);
    leanh::lean_dec(v_x_561_);
    leanh::lean_dec(v_a_560_);
    return v_res_562_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_Variant(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_Variant(
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
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_Variant(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ScopedEnvExtension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Variant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_Variant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_Variant(builtin);
}