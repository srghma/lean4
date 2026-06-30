// Lean compiler output
// Module: Lean.Data.Json.FromToJson.Extra
// Imports: Lean.Data.Json.FromToJson.Basic Std.Data.TreeMap.AdditionalOperations
use crate::r#gen::Init::Control::Except::{
    l_Except_bind, l_Except_instMonad___lam__0, l_Except_instMonad___lam__1,
    l_Except_instMonad___lam__2___boxed, l_Except_instMonad___lam__3, l_Except_map, l_Except_pure,
};
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_Json_getObj_x3f;
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    initialize_Lean_Data_Json_FromToJson_Basic, runtime_initialize_Lean_Data_Json_FromToJson_Basic,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_insert___redArg, l_Std_DTreeMap_Internal_Impl_map___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_foldlM___redArg;
use crate::r#gen::Std::Data::TreeMap::AdditionalOperations::{
    initialize_Std_Data_TreeMap_AdditionalOperations,
    runtime_initialize_Std_Data_TreeMap_AdditionalOperations,
};
pub static l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Except_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Except_instMonad___lam__1 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Except_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Except_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__4_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Except_map as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__6_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Except_pure as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__7_value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__3_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__8_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Except_bind as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__8_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__9_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___redArg___lam__0(
    mut v_inst_110_: *mut leanh::LeanObject,
    mut v_x_111_: *mut leanh::LeanObject,
    mut v___y_112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_113_ = leanh::lean_apply_1(v_inst_110_, v___y_112_);
    return v___x_113_;
}
pub unsafe fn l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___redArg___lam__0___boxed(
    mut v_inst_114_: *mut leanh::LeanObject,
    mut v_x_115_: *mut leanh::LeanObject,
    mut v___y_116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_117_ =
        l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___redArg___lam__0(
            v_inst_114_,
            v_x_115_,
            v___y_116_,
        );
    leanh::lean_dec_ref(v_x_115_);
    return v_res_117_;
}
pub unsafe fn l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___redArg(
    mut v_inst_118_: *mut leanh::LeanObject,
    mut v_map_119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_120_ = leanh::lean_alloc_closure(
        l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_120_, 0, v_inst_118_);
    v___x_121_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v___f_120_, v_map_119_);
    v___x_122_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_122_, 0, v___x_121_);
    return v___x_122_;
}
pub unsafe fn l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson(
    mut v_00_u03b1_123_: *mut leanh::LeanObject,
    mut v_inst_124_: *mut leanh::LeanObject,
    mut v_map_125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_126_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___redArg(
        v_inst_124_,
        v_map_125_,
    );
    return v___x_126_;
}
pub unsafe fn l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___lam__0(
    mut v_inst_127_: *mut leanh::LeanObject,
    mut v_cmp_128_: *mut leanh::LeanObject,
    mut v_x_129_: *mut leanh::LeanObject,
    mut v_k_130_: *mut leanh::LeanObject,
    mut v_v_131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_136_: u8 = 0;
    let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_140_: u8 = 0;
    let mut v_a_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_144_: u8 = 0;
    let mut v___x_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_132_ = leanh::lean_apply_1(v_inst_127_, v_v_131_);
                if leanh::lean_obj_tag(v___x_132_) == 0 {
                    leanh::lean_dec_ref(v_k_130_);
                    leanh::lean_dec(v_x_129_);
                    leanh::lean_dec_ref(v_cmp_128_);
                    v_a_133_ = leanh::lean_ctor_get(v___x_132_, 0);
                    v_isSharedCheck_140_ = (!leanh::lean_is_exclusive(v___x_132_)) as u8;
                    if v_isSharedCheck_140_ == 0 {
                        v___x_135_ = v___x_132_;
                        v_isShared_136_ = v_isSharedCheck_140_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_133_);
                        leanh::lean_dec(v___x_132_);
                        v___x_135_ = leanh::lean_box(0);
                        v_isShared_136_ = v_isSharedCheck_140_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_141_ = leanh::lean_ctor_get(v___x_132_, 0);
                    v_isSharedCheck_149_ = (!leanh::lean_is_exclusive(v___x_132_)) as u8;
                    if v_isSharedCheck_149_ == 0 {
                        v___x_143_ = v___x_132_;
                        v_isShared_144_ = v_isSharedCheck_149_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_141_);
                        leanh::lean_dec(v___x_132_);
                        v___x_143_ = leanh::lean_box(0);
                        v_isShared_144_ = v_isSharedCheck_149_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_136_ == 0 {
                    v___x_138_ = v___x_135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_139_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
                    v___x_138_ = v_reuseFailAlloc_139_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_138_;
            }
            3 => {
                v___x_145_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v_cmp_128_, v_k_130_, v_a_141_, v_x_129_,
                );
                if v_isShared_144_ == 0 {
                    leanh::lean_ctor_set(v___x_143_, 0, v___x_145_);
                    v___x_147_ = v___x_143_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_148_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
                    v___x_147_ = v_reuseFailAlloc_148_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg(
    mut v_cmp_169_: *mut leanh::LeanObject,
    mut v_inst_170_: *mut leanh::LeanObject,
    mut v_j_171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_177_: u8 = 0;
    let mut v___x_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_181_: u8 = 0;
    let mut v_a_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_172_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___closed__9;
                v___x_173_ = l_Lean_Json_getObj_x3f(v_j_171_);
                if leanh::lean_obj_tag(v___x_173_) == 0 {
                    leanh::lean_dec_ref(v_inst_170_);
                    leanh::lean_dec_ref(v_cmp_169_);
                    v_a_174_ = leanh::lean_ctor_get(v___x_173_, 0);
                    v_isSharedCheck_181_ = (!leanh::lean_is_exclusive(v___x_173_)) as u8;
                    if v_isSharedCheck_181_ == 0 {
                        v___x_176_ = v___x_173_;
                        v_isShared_177_ = v_isSharedCheck_181_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_174_);
                        leanh::lean_dec(v___x_173_);
                        v___x_176_ = leanh::lean_box(0);
                        v_isShared_177_ = v_isSharedCheck_181_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_182_ = leanh::lean_ctor_get(v___x_173_, 0);
                    leanh::lean_inc(v_a_182_);
                    leanh::lean_dec_ref_known(v___x_173_, 1);
                    v___f_183_ = leanh::lean_alloc_closure(l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg___lam__0 as *mut core::ffi::c_void, 5, 2);
                    leanh::lean_closure_set(v___f_183_, 0, v_inst_170_);
                    leanh::lean_closure_set(v___f_183_, 1, v_cmp_169_);
                    v___x_184_ = leanh::lean_box(1);
                    v___x_185_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
                        v___x_172_, v___f_183_, v___x_184_, v_a_182_,
                    );
                    return v___x_185_;
                }
            }
            1 => {
                if v_isShared_177_ == 0 {
                    v___x_179_ = v___x_176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
                    v___x_179_ = v_reuseFailAlloc_180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f(
    mut v_00_u03b1_186_: *mut leanh::LeanObject,
    mut v_cmp_187_: *mut leanh::LeanObject,
    mut v_inst_188_: *mut leanh::LeanObject,
    mut v_j_189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_190_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg(
        v_cmp_187_,
        v_inst_188_,
        v_j_189_,
    );
    return v___x_190_;
}
pub unsafe fn l_Lean_instToJsonTreeMapStringCompare___private__1___redArg(
    mut v_inst_191_: *mut leanh::LeanObject,
    mut v_map_192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_193_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___redArg(
        v_inst_191_,
        v_map_192_,
    );
    return v___x_193_;
}
pub unsafe fn l_Lean_instToJsonTreeMapStringCompare___private__1(
    mut v_00_u03b1_194_: *mut leanh::LeanObject,
    mut v_inst_195_: *mut leanh::LeanObject,
    mut v_map_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_197_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___redArg(
        v_inst_195_,
        v_map_196_,
    );
    return v___x_197_;
}
pub unsafe fn l_Lean_instToJsonTreeMapStringCompare___redArg(
    mut v_inst_198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_199_ = leanh::lean_alloc_closure(
        l_Lean_instToJsonTreeMapStringCompare___private__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_199_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_199_, 1, v_inst_198_);
    return v___x_199_;
}
pub unsafe fn l_Lean_instToJsonTreeMapStringCompare(
    mut v_00_u03b1_200_: *mut leanh::LeanObject,
    mut v_inst_201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_202_ = leanh::lean_alloc_closure(
        l_Lean_instToJsonTreeMapStringCompare___private__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_202_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_202_, 1, v_inst_201_);
    return v___x_202_;
}
pub unsafe fn l_Lean_instFromJsonTreeMapString___private__1___redArg(
    mut v_cmp_203_: *mut leanh::LeanObject,
    mut v_inst_204_: *mut leanh::LeanObject,
    mut v_j_205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_206_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg(
        v_cmp_203_,
        v_inst_204_,
        v_j_205_,
    );
    return v___x_206_;
}
pub unsafe fn l_Lean_instFromJsonTreeMapString___private__1(
    mut v_00_u03b1_207_: *mut leanh::LeanObject,
    mut v_cmp_208_: *mut leanh::LeanObject,
    mut v_inst_209_: *mut leanh::LeanObject,
    mut v_j_210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_211_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___redArg(
        v_cmp_208_,
        v_inst_209_,
        v_j_210_,
    );
    return v___x_211_;
}
pub unsafe fn l_Lean_instFromJsonTreeMapString___redArg(
    mut v_cmp_212_: *mut leanh::LeanObject,
    mut v_inst_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_214_ = leanh::lean_alloc_closure(
        l_Lean_instFromJsonTreeMapString___private__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___x_214_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_214_, 1, v_cmp_212_);
    leanh::lean_closure_set(v___x_214_, 2, v_inst_213_);
    return v___x_214_;
}
pub unsafe fn l_Lean_instFromJsonTreeMapString(
    mut v_00_u03b1_215_: *mut leanh::LeanObject,
    mut v_cmp_216_: *mut leanh::LeanObject,
    mut v_inst_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_218_ = leanh::lean_alloc_closure(
        l_Lean_instFromJsonTreeMapString___private__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___x_218_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_218_, 1, v_cmp_216_);
    leanh::lean_closure_set(v___x_218_, 2, v_inst_217_);
    return v___x_218_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Json_FromToJson_Extra(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Json_FromToJson_Extra(
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
pub unsafe fn initialize_Lean_Data_Json_FromToJson_Extra(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_FromToJson_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Json_FromToJson_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Json_FromToJson_Extra(builtin);
}