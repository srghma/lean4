// Lean compiler output
// Module: Lean.OriginalConstKind
// Imports: Lean.Environment Lean.EnvExtension
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_add,
    lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_mkMapDeclarationExtension___redArg, runtime_initialize_Lean_EnvExtension,
};
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment, l_Lean_Environment_contains, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_setExporting, runtime_initialize_Lean_Environment,
};
pub static l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__1_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__1_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__1_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__2_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__2_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__2_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__3_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__1_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__2_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__3_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__3_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__4_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [79, 114, 105, 103, 105, 110, 97, 108, 67, 111, 110, 115, 116, 75, 105, 110, 100, 0]};
static mut l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__4_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__4_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__5_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__3_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__4_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1388370937901884198 as *mut leanh::LeanObject] };
static mut l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__5_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__5_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__6_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_OriginalConstKind_0__Lean_initFn___lam__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__6_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__6_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__7_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__5_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,5771600792973796655 as *mut leanh::LeanObject] };
static mut l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__7_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__7_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__8_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__7_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__2_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7478783436812563650 as *mut leanh::LeanObject] };
static mut l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__8_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__8_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__9_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [112, 114, 105, 118, 97, 116, 101, 67, 111, 110, 115, 116, 75, 105, 110, 100, 115, 69, 120, 116, 0]};
static mut l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__9_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__9_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__10_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__8_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__9_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15297386339186615410 as *mut leanh::LeanObject] };
static mut l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__10_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__10_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_142_: *mut leanh::LeanObject,
    mut v_x_143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_143_) == 0 {
                    v_k_144_ = leanh::lean_ctor_get(v_x_143_, 1);
                    v_v_145_ = leanh::lean_ctor_get(v_x_143_, 2);
                    v_l_146_ = leanh::lean_ctor_get(v_x_143_, 3);
                    v_r_147_ = leanh::lean_ctor_get(v_x_143_, 4);
                    v___x_148_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0(v_init_142_, v_l_146_);
                    leanh::lean_inc(v_v_145_);
                    leanh::lean_inc(v_k_144_);
                    v___x_149_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_149_, 0, v_k_144_);
                    leanh::lean_ctor_set(v___x_149_, 1, v_v_145_);
                    v___x_150_ = lean_array_push(v___x_148_, v___x_149_);
                    v_init_142_ = v___x_150_;
                    v_x_143_ = v_r_147_;
                    state = 0;
                    continue;
                } else {
                    return v_init_142_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_152_: *mut leanh::LeanObject,
    mut v_x_153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_154_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0(v_init_152_, v_x_153_);
    leanh::lean_dec(v_x_153_);
    return v_res_154_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1(
    mut v_env_155_: *mut leanh::LeanObject,
    mut v_as_156_: *mut leanh::LeanObject,
    mut v_i_157_: usize,
    mut v_stop_158_: usize,
    mut v_b_159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: usize = 0;
    let mut v___x_163_: usize = 0;
    let mut v___x_165_: u8 = 0;
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: u8 = 0;
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_165_ = lean_usize_dec_eq(v_i_157_, v_stop_158_);
                if v___x_165_ == 0 {
                    v___x_166_ = lean_array_uget_borrowed(v_as_156_, v_i_157_);
                    v_fst_167_ = leanh::lean_ctor_get(v___x_166_, 0);
                    leanh::lean_inc(v_fst_167_);
                    leanh::lean_inc_ref(v_env_155_);
                    v___x_168_ = l_Lean_Environment_contains(v_env_155_, v_fst_167_, v___x_165_);
                    if v___x_168_ == 0 {
                        v___y_161_ = v_b_159_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_166_);
                        v___x_169_ = lean_array_push(v_b_159_, v___x_166_);
                        v___y_161_ = v___x_169_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_155_);
                    return v_b_159_;
                }
            }
            1 => {
                v___x_162_ = 1usize;
                v___x_163_ = lean_usize_add(v_i_157_, v___x_162_);
                v_i_157_ = v___x_163_;
                v_b_159_ = v___y_161_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1___boxed(
    mut v_env_170_: *mut leanh::LeanObject,
    mut v_as_171_: *mut leanh::LeanObject,
    mut v_i_172_: *mut leanh::LeanObject,
    mut v_stop_173_: *mut leanh::LeanObject,
    mut v_b_174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_175_: usize = 0;
    let mut v_stop_boxed_176_: usize = 0;
    let mut v_res_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_175_ = leanh::lean_unbox_usize(v_i_172_);
    leanh::lean_dec(v_i_172_);
    v_stop_boxed_176_ = leanh::lean_unbox_usize(v_stop_173_);
    leanh::lean_dec(v_stop_173_);
    v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1(v_env_170_, v_as_171_, v_i_boxed_175_, v_stop_boxed_176_, v_b_174_);
    leanh::lean_dec_ref(v_as_171_);
    return v_res_177_;
}
pub unsafe fn l___private_Lean_OriginalConstKind_0__Lean_initFn___lam__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_(
    mut v___x_178_: *mut leanh::LeanObject,
    mut v_env_179_: *mut leanh::LeanObject,
    mut v_s_180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: u8 = 0;
    v___x_181_ = lean_mk_empty_array_with_capacity(v___x_178_);
    v___x_182_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0(v___x_181_, v_s_180_);
    v___x_183_ = lean_array_get_size(v___x_182_);
    v___x_184_ = lean_mk_empty_array_with_capacity(v___x_178_);
    v___x_185_ = lean_nat_dec_lt(v___x_178_, v___x_183_);
    if v___x_185_ == 0 {
        let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_182_);
        leanh::lean_dec_ref(v_env_179_);
        leanh::lean_inc_ref_n(v___x_184_, 2);
        v___x_186_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_186_, 0, v___x_184_);
        leanh::lean_ctor_set(v___x_186_, 1, v___x_184_);
        leanh::lean_ctor_set(v___x_186_, 2, v___x_184_);
        return v___x_186_;
    } else {
        let mut v___x_187_: u8 = 0;
        v___x_187_ = lean_nat_dec_le(v___x_183_, v___x_183_);
        if v___x_187_ == 0 {
            if v___x_185_ == 0 {
                let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___x_182_);
                leanh::lean_dec_ref(v_env_179_);
                leanh::lean_inc_ref_n(v___x_184_, 2);
                v___x_188_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_188_, 0, v___x_184_);
                leanh::lean_ctor_set(v___x_188_, 1, v___x_184_);
                leanh::lean_ctor_set(v___x_188_, 2, v___x_184_);
                return v___x_188_;
            } else {
                let mut v___x_189_: usize = 0;
                let mut v___x_190_: usize = 0;
                let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_189_ = 0usize;
                v___x_190_ = lean_usize_of_nat(v___x_183_);
                v___x_191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1(v_env_179_, v___x_182_, v___x_189_, v___x_190_, v___x_184_);
                leanh::lean_dec_ref(v___x_182_);
                leanh::lean_inc_ref_n(v___x_191_, 2);
                v___x_192_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_192_, 0, v___x_191_);
                leanh::lean_ctor_set(v___x_192_, 1, v___x_191_);
                leanh::lean_ctor_set(v___x_192_, 2, v___x_191_);
                return v___x_192_;
            }
        } else {
            let mut v___x_193_: usize = 0;
            let mut v___x_194_: usize = 0;
            let mut v___x_195_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_193_ = 0usize;
            v___x_194_ = lean_usize_of_nat(v___x_183_);
            v___x_195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__1(v_env_179_, v___x_182_, v___x_193_, v___x_194_, v___x_184_);
            leanh::lean_dec_ref(v___x_182_);
            leanh::lean_inc_ref_n(v___x_195_, 2);
            v___x_196_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_196_, 0, v___x_195_);
            leanh::lean_ctor_set(v___x_196_, 1, v___x_195_);
            leanh::lean_ctor_set(v___x_196_, 2, v___x_195_);
            return v___x_196_;
        }
    }
}
pub unsafe fn l___private_Lean_OriginalConstKind_0__Lean_initFn___lam__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2____boxed(
    mut v___x_197_: *mut leanh::LeanObject,
    mut v_env_198_: *mut leanh::LeanObject,
    mut v_s_199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_200_ = l___private_Lean_OriginalConstKind_0__Lean_initFn___lam__0_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_(v___x_197_, v_env_198_, v_s_199_);
    leanh::lean_dec(v_s_199_);
    leanh::lean_dec(v___x_197_);
    return v_res_200_;
}
pub unsafe fn l___private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_226_ = l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__6_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_;
    v___x_227_ = l___private_Lean_OriginalConstKind_0__Lean_initFn___closed__10_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_;
    v___x_228_ = leanh::lean_box(0);
    v___x_229_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_227_, v___x_228_, v___f_226_);
    return v___x_229_;
}
pub unsafe fn l___private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2____boxed(
    mut v_a_230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_231_ = l___private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_();
    return v_res_231_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0(
    mut v_init_232_: *mut leanh::LeanObject,
    mut v_t_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0_spec__0(v_init_232_, v_t_233_);
    return v___x_234_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_235_: *mut leanh::LeanObject,
    mut v_t_236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_237_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2__spec__0(v_init_235_, v_t_236_);
    leanh::lean_dec(v_t_236_);
    return v_res_237_;
}
pub unsafe fn l_Lean_getOriginalConstKind_x3f(
    mut v_env_238_: *mut leanh::LeanObject,
    mut v_declName_239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_240_: u8 = 0;
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: u8 = 0;
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: u8 = 0;
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_252_: u8 = 0;
    let mut v_kind_253_: u8 = 0;
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_258_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_240_ = 0;
                v___x_241_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
                v___x_242_ = leanh::lean_box(1);
                v___x_243_ = 0;
                v___x_244_ = leanh::lean_box((v___x_240_) as usize);
                leanh::lean_inc(v_declName_239_);
                leanh::lean_inc_ref(v_env_238_);
                v___x_245_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                    v___x_244_,
                    v___x_241_,
                    v_env_238_,
                    v_declName_239_,
                    v___x_242_,
                    v___x_243_,
                );
                if leanh::lean_obj_tag(v___x_245_) == 0 {
                    v___x_246_ = 0;
                    v___x_247_ = l_Lean_Environment_setExporting(v_env_238_, v___x_246_);
                    v___x_248_ =
                        l_Lean_Environment_findAsync_x3f(v___x_247_, v_declName_239_, v___x_246_);
                    if leanh::lean_obj_tag(v___x_248_) == 0 {
                        return v___x_245_;
                    } else {
                        v_val_249_ = leanh::lean_ctor_get(v___x_248_, 0);
                        v_isSharedCheck_258_ = (!leanh::lean_is_exclusive(v___x_248_)) as u8;
                        if v_isSharedCheck_258_ == 0 {
                            v___x_251_ = v___x_248_;
                            v_isShared_252_ = v_isSharedCheck_258_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_249_);
                            leanh::lean_dec(v___x_248_);
                            v___x_251_ = leanh::lean_box(0);
                            v_isShared_252_ = v_isSharedCheck_258_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_declName_239_);
                    leanh::lean_dec_ref(v_env_238_);
                    return v___x_245_;
                }
            }
            1 => {
                v_kind_253_ = leanh::lean_ctor_get_uint8(
                    v_val_249_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec(v_val_249_);
                v___x_254_ = leanh::lean_box((v_kind_253_) as usize);
                if v_isShared_252_ == 0 {
                    leanh::lean_ctor_set(v___x_251_, 0, v___x_254_);
                    v___x_256_ = v___x_251_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_257_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
                    v___x_256_ = v_reuseFailAlloc_257_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_wasOriginallyDefn(
    mut v_env_259_: *mut leanh::LeanObject,
    mut v_declName_260_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_261_ = l_Lean_getOriginalConstKind_x3f(v_env_259_, v_declName_260_);
    if leanh::lean_obj_tag(v___x_261_) == 0 {
        let mut v___x_262_: u8 = 0;
        v___x_262_ = 0;
        return v___x_262_;
    } else {
        let mut v_val_263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_264_: u8 = 0;
        v_val_263_ = leanh::lean_ctor_get(v___x_261_, 0);
        leanh::lean_inc(v_val_263_);
        leanh::lean_dec_ref_known(v___x_261_, 1);
        v___x_264_ = (leanh::lean_unbox(v_val_263_) as u8);
        leanh::lean_dec(v_val_263_);
        if v___x_264_ == 0 {
            let mut v___x_265_: u8 = 0;
            v___x_265_ = 1;
            return v___x_265_;
        } else {
            let mut v___x_266_: u8 = 0;
            v___x_266_ = 0;
            return v___x_266_;
        }
    }
}
pub unsafe fn l_Lean_wasOriginallyDefn___boxed(
    mut v_env_267_: *mut leanh::LeanObject,
    mut v_declName_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_269_: u8 = 0;
    let mut v_r_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_269_ = l_Lean_wasOriginallyDefn(v_env_267_, v_declName_268_);
    v_r_270_ = leanh::lean_box((v_res_269_) as usize);
    return v_r_270_;
}
pub unsafe fn l_Lean_wasOriginallyTheorem(
    mut v_env_271_: *mut leanh::LeanObject,
    mut v_declName_272_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_273_ = l_Lean_getOriginalConstKind_x3f(v_env_271_, v_declName_272_);
    if leanh::lean_obj_tag(v___x_273_) == 0 {
        let mut v___x_274_: u8 = 0;
        v___x_274_ = 0;
        return v___x_274_;
    } else {
        let mut v_val_275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_276_: u8 = 0;
        v_val_275_ = leanh::lean_ctor_get(v___x_273_, 0);
        leanh::lean_inc(v_val_275_);
        leanh::lean_dec_ref_known(v___x_273_, 1);
        v___x_276_ = (leanh::lean_unbox(v_val_275_) as u8);
        leanh::lean_dec(v_val_275_);
        if v___x_276_ == 1 {
            let mut v___x_277_: u8 = 0;
            v___x_277_ = 1;
            return v___x_277_;
        } else {
            let mut v___x_278_: u8 = 0;
            v___x_278_ = 0;
            return v___x_278_;
        }
    }
}
pub unsafe fn l_Lean_wasOriginallyTheorem___boxed(
    mut v_env_279_: *mut leanh::LeanObject,
    mut v_declName_280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_281_: u8 = 0;
    let mut v_r_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_281_ = l_Lean_wasOriginallyTheorem(v_env_279_, v_declName_280_);
    v_r_282_ = leanh::lean_box((v_res_281_) as usize);
    return v_r_282_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_OriginalConstKind(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_OriginalConstKind_0__Lean_initFn_00___x40_Lean_OriginalConstKind_2239415342____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt,
    );
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_OriginalConstKind(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_OriginalConstKind(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_EnvExtension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_OriginalConstKind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_OriginalConstKind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_OriginalConstKind(builtin);
}