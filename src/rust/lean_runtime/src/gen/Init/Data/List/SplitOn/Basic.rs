// Lean compiler output
// Module: Init.Data.List.SplitOn.Basic
// Imports: Init.Data.List.Basic Init.NotationExtra Init.Data.Array.Bootstrap Init.Data.List.Lemmas
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold;
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::List::Basic::{
    initialize_Init_Data_List_Basic, runtime_initialize_Init_Data_List_Basic,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_dec_lt,
};
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___lam__0(
    mut v_x1_127_: *mut crate::leanh::LeanObject,
    mut v_x2_128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_129_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_129_, 0, v_x1_127_);
    crate::leanh::lean_ctor_set(v___x_129_, 1, v_x2_128_);
    return v___x_129_;
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
    mut v_p_152_: *mut crate::leanh::LeanObject,
    mut v_a_153_: *mut crate::leanh::LeanObject,
    mut v_a_154_: *mut crate::leanh::LeanObject,
    mut v_a_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: u8 = 0;
    let mut v___f_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: usize = 0;
    let mut v___x_165_: usize = 0;
    let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: u8 = 0;
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_153_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_152_);
                    v___x_156_ = lean_array_to_list(v_a_154_);
                    v___x_157_ = crate::leanh::lean_box(0);
                    v___x_158_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_158_, 0, v___x_156_);
                    crate::leanh::lean_ctor_set(v___x_158_, 1, v___x_157_);
                    v___x_159_ = lean_array_get_size(v_a_155_);
                    v___x_160_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_161_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9;
                    v___x_162_ = lean_nat_dec_lt(v___x_160_, v___x_159_);
                    if v___x_162_ == 0 {
                        crate::leanh::lean_dec_ref(v_a_155_);
                        return v___x_158_;
                    } else {
                        v___f_163_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10;
                        v___x_164_ = lean_usize_of_nat(v___x_159_);
                        v___x_165_ = 0usize;
                        v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_161_,
                            v___f_163_,
                            v_a_155_,
                            v___x_164_,
                            v___x_165_,
                            v___x_158_,
                        );
                        return v___x_166_;
                    }
                } else {
                    v_head_167_ = crate::leanh::lean_ctor_get(v_a_153_, 0);
                    crate::leanh::lean_inc_n(v_head_167_, 2);
                    v_tail_168_ = crate::leanh::lean_ctor_get(v_a_153_, 1);
                    crate::leanh::lean_inc(v_tail_168_);
                    crate::leanh::lean_dec_ref_known(v_a_153_, 2);
                    crate::leanh::lean_inc_ref(v_p_152_);
                    v___x_169_ = crate::leanh::lean_apply_1(v_p_152_, v_head_167_);
                    v___x_170_ = (crate::leanh::lean_unbox(v___x_169_) as u8);
                    if v___x_170_ == 0 {
                        v___x_171_ = lean_array_push(v_a_154_, v_head_167_);
                        v_a_153_ = v_tail_168_;
                        v_a_154_ = v___x_171_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_head_167_);
                        v___x_173_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11;
                        v___x_174_ = lean_array_to_list(v_a_154_);
                        v___x_175_ = lean_array_push(v_a_155_, v___x_174_);
                        v_a_153_ = v_tail_168_;
                        v_a_154_ = v___x_173_;
                        v_a_155_ = v___x_175_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go(
    mut v_00_u03b1_177_: *mut crate::leanh::LeanObject,
    mut v_p_178_: *mut crate::leanh::LeanObject,
    mut v_a_179_: *mut crate::leanh::LeanObject,
    mut v_a_180_: *mut crate::leanh::LeanObject,
    mut v_a_181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_182_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
        v_p_178_, v_a_179_, v_a_180_, v_a_181_,
    );
    return v___x_182_;
}
pub unsafe fn l_List_splitOnPTR___redArg(
    mut v_p_183_: *mut crate::leanh::LeanObject,
    mut v_l_184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_185_ =
        l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11;
    v___x_186_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
        v_p_183_, v_l_184_, v___x_185_, v___x_185_,
    );
    return v___x_186_;
}
pub unsafe fn l_List_splitOnPTR(
    mut v_00_u03b1_187_: *mut crate::leanh::LeanObject,
    mut v_p_188_: *mut crate::leanh::LeanObject,
    mut v_l_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_190_ =
        l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11;
    v___x_191_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
        v_p_188_, v_l_189_, v___x_190_, v___x_190_,
    );
    return v___x_191_;
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter___redArg(
    mut v_x_192_: *mut crate::leanh::LeanObject,
    mut v_x_193_: *mut crate::leanh::LeanObject,
    mut v_h__1_194_: *mut crate::leanh::LeanObject,
    mut v_h__2_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_192_) == 0 {
        let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_195_);
        v___x_196_ = crate::leanh::lean_apply_1(v_h__1_194_, v_x_193_);
        return v___x_196_;
    } else {
        let mut v_head_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_194_);
        v_head_197_ = crate::leanh::lean_ctor_get(v_x_192_, 0);
        crate::leanh::lean_inc(v_head_197_);
        v_tail_198_ = crate::leanh::lean_ctor_get(v_x_192_, 1);
        crate::leanh::lean_inc(v_tail_198_);
        crate::leanh::lean_dec_ref_known(v_x_192_, 2);
        v___x_199_ = crate::leanh::lean_apply_3(v_h__2_195_, v_head_197_, v_tail_198_, v_x_193_);
        return v___x_199_;
    }
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter(
    mut v_00_u03b1_200_: *mut crate::leanh::LeanObject,
    mut v_motive_201_: *mut crate::leanh::LeanObject,
    mut v_x_202_: *mut crate::leanh::LeanObject,
    mut v_x_203_: *mut crate::leanh::LeanObject,
    mut v_h__1_204_: *mut crate::leanh::LeanObject,
    mut v_h__2_205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_202_) == 0 {
        let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_205_);
        v___x_206_ = crate::leanh::lean_apply_1(v_h__1_204_, v_x_203_);
        return v___x_206_;
    } else {
        let mut v_head_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_204_);
        v_head_207_ = crate::leanh::lean_ctor_get(v_x_202_, 0);
        crate::leanh::lean_inc(v_head_207_);
        v_tail_208_ = crate::leanh::lean_ctor_get(v_x_202_, 1);
        crate::leanh::lean_inc(v_tail_208_);
        crate::leanh::lean_dec_ref_known(v_x_202_, 2);
        v___x_209_ = crate::leanh::lean_apply_3(v_h__2_205_, v_head_207_, v_tail_208_, v_x_203_);
        return v___x_209_;
    }
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter___redArg(
    mut v_x_210_: *mut crate::leanh::LeanObject,
    mut v_x_211_: *mut crate::leanh::LeanObject,
    mut v_x_212_: *mut crate::leanh::LeanObject,
    mut v_h__1_213_: *mut crate::leanh::LeanObject,
    mut v_h__2_214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_210_) == 0 {
        let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_214_);
        v___x_215_ = crate::leanh::lean_apply_2(v_h__1_213_, v_x_211_, v_x_212_);
        return v___x_215_;
    } else {
        let mut v_head_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_213_);
        v_head_216_ = crate::leanh::lean_ctor_get(v_x_210_, 0);
        crate::leanh::lean_inc(v_head_216_);
        v_tail_217_ = crate::leanh::lean_ctor_get(v_x_210_, 1);
        crate::leanh::lean_inc(v_tail_217_);
        crate::leanh::lean_dec_ref_known(v_x_210_, 2);
        v___x_218_ =
            crate::leanh::lean_apply_4(v_h__2_214_, v_head_216_, v_tail_217_, v_x_211_, v_x_212_);
        return v___x_218_;
    }
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter(
    mut v_00_u03b1_219_: *mut crate::leanh::LeanObject,
    mut v_motive_220_: *mut crate::leanh::LeanObject,
    mut v_x_221_: *mut crate::leanh::LeanObject,
    mut v_x_222_: *mut crate::leanh::LeanObject,
    mut v_x_223_: *mut crate::leanh::LeanObject,
    mut v_h__1_224_: *mut crate::leanh::LeanObject,
    mut v_h__2_225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_221_) == 0 {
        let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_225_);
        v___x_226_ = crate::leanh::lean_apply_2(v_h__1_224_, v_x_222_, v_x_223_);
        return v___x_226_;
    } else {
        let mut v_head_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_224_);
        v_head_227_ = crate::leanh::lean_ctor_get(v_x_221_, 0);
        crate::leanh::lean_inc(v_head_227_);
        v_tail_228_ = crate::leanh::lean_ctor_get(v_x_221_, 1);
        crate::leanh::lean_inc(v_tail_228_);
        crate::leanh::lean_dec_ref_known(v_x_221_, 2);
        v___x_229_ =
            crate::leanh::lean_apply_4(v_h__2_225_, v_head_227_, v_tail_228_, v_x_222_, v_x_223_);
        return v___x_229_;
    }
}
pub unsafe fn l_List_splitOn___redArg___lam__0(
    mut v_inst_230_: *mut crate::leanh::LeanObject,
    mut v_a_231_: *mut crate::leanh::LeanObject,
    mut v_x_232_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: u8 = 0;
    v___x_233_ = crate::leanh::lean_apply_2(v_inst_230_, v_x_232_, v_a_231_);
    v___x_234_ = (crate::leanh::lean_unbox(v___x_233_) as u8);
    return v___x_234_;
}
pub unsafe fn l_List_splitOn___redArg___lam__0___boxed(
    mut v_inst_235_: *mut crate::leanh::LeanObject,
    mut v_a_236_: *mut crate::leanh::LeanObject,
    mut v_x_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_238_: u8 = 0;
    let mut v_r_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_238_ = l_List_splitOn___redArg___lam__0(v_inst_235_, v_a_236_, v_x_237_);
    v_r_239_ = crate::leanh::lean_box((v_res_238_) as usize);
    return v_r_239_;
}
pub unsafe fn l_List_splitOn___redArg(
    mut v_inst_240_: *mut crate::leanh::LeanObject,
    mut v_a_241_: *mut crate::leanh::LeanObject,
    mut v_as_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_243_ = crate::leanh::lean_alloc_closure(
        l_List_splitOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_243_, 0, v_inst_240_);
    crate::leanh::lean_closure_set(v___f_243_, 1, v_a_241_);
    v___x_244_ =
        l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11;
    v___x_245_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
        v___f_243_, v_as_242_, v___x_244_, v___x_244_,
    );
    return v___x_245_;
}
pub unsafe fn l_List_splitOn(
    mut v_00_u03b1_246_: *mut crate::leanh::LeanObject,
    mut v_inst_247_: *mut crate::leanh::LeanObject,
    mut v_a_248_: *mut crate::leanh::LeanObject,
    mut v_as_249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_250_ = crate::leanh::lean_alloc_closure(
        l_List_splitOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_250_, 0, v_inst_247_);
    crate::leanh::lean_closure_set(v___f_250_, 1, v_a_248_);
    v___x_251_ =
        l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11;
    v___x_252_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(
        v___f_250_, v_as_249_, v___x_251_, v___x_251_,
    );
    return v___x_252_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_SplitOn_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_SplitOn_Basic(
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
pub unsafe fn initialize_Init_Data_List_SplitOn_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_SplitOn_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_SplitOn_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_SplitOn_Basic(builtin);
}
