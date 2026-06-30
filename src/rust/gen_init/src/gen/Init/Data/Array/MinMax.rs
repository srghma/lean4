// Lean compiler output
// Module: Init.Data.Array.MinMax
// Imports: Init.Data.Array.Lemmas Init.Data.List.MinMax Init.Data.Order.Classes Init.Data.Array.Bootstrap Init.Data.Array.DecidableEq Init.Data.List.TakeDrop Init.Data.Order.Lemmas
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::DecidableEq::{
    initialize_Init_Data_Array_DecidableEq, runtime_initialize_Init_Data_Array_DecidableEq,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::List::MinMax::{
    initialize_Init_Data_List_MinMax, runtime_initialize_Init_Data_List_MinMax,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
pub static l_Array_min___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_min___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_min___redArg___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_min___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array_min___redArg___closed__2_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_min___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Array_min___redArg___closed__3_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_min___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Array_min___redArg___closed__4_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_min___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_Array_min___redArg___closed__5_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_min___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Array_min___redArg___closed__6_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_min___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_Array_min___redArg___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_min___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_min___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_Array_min___redArg___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_min___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_min___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l_Array_min___redArg___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_min___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_min___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_min___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_min___redArg___closed__9_value) as *mut leanh::LeanObject;
pub unsafe fn l_Array_min___redArg___lam__0(
    mut v_inst_90_: *mut leanh::LeanObject,
    mut v_x1_91_: *mut leanh::LeanObject,
    mut v_x2_92_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_93_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_93_ = leanh::lean_apply_2(v_inst_90_, v_x1_91_, v_x2_92_);
    return v___x_93_;
}
pub unsafe fn l_Array_min___redArg(
    mut v_inst_113_: *mut leanh::LeanObject,
    mut v_arr_114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: u8 = 0;
    v___x_115_ = leanh::lean_unsigned_to_nat(0);
    v___x_116_ = lean_array_fget(v_arr_114_, v___x_115_);
    v___x_117_ = leanh::lean_unsigned_to_nat(1);
    v___x_118_ = lean_array_get_size(v_arr_114_);
    v___x_119_ = l_Array_min___redArg___closed__9;
    v___x_120_ = lean_nat_dec_lt(v___x_117_, v___x_118_);
    if v___x_120_ == 0 {
        leanh::lean_dec_ref(v_arr_114_);
        leanh::lean_dec(v_inst_113_);
        return v___x_116_;
    } else {
        let mut v___f_121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_122_: u8 = 0;
        v___f_121_ = leanh::lean_alloc_closure(
            l_Array_min___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_121_, 0, v_inst_113_);
        v___x_122_ = lean_nat_dec_le(v___x_118_, v___x_118_);
        if v___x_122_ == 0 {
            if v___x_120_ == 0 {
                leanh::lean_dec_ref(v___f_121_);
                leanh::lean_dec_ref(v_arr_114_);
                return v___x_116_;
            } else {
                let mut v___x_123_: usize = 0;
                let mut v___x_124_: usize = 0;
                let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_123_ = 1usize;
                v___x_124_ = lean_usize_of_nat(v___x_118_);
                v___x_125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_119_,
                    v___f_121_,
                    v_arr_114_,
                    v___x_123_,
                    v___x_124_,
                    v___x_116_,
                );
                return v___x_125_;
            }
        } else {
            let mut v___x_126_: usize = 0;
            let mut v___x_127_: usize = 0;
            let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_126_ = 1usize;
            v___x_127_ = lean_usize_of_nat(v___x_118_);
            v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_119_,
                v___f_121_,
                v_arr_114_,
                v___x_126_,
                v___x_127_,
                v___x_116_,
            );
            return v___x_128_;
        }
    }
}
pub unsafe fn l_Array_min(
    mut v_00_u03b1_129_: *mut leanh::LeanObject,
    mut v_inst_130_: *mut leanh::LeanObject,
    mut v_arr_131_: *mut leanh::LeanObject,
    mut v_h_132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_133_ = l_Array_min___redArg(v_inst_130_, v_arr_131_);
    return v___x_133_;
}
pub unsafe fn l_Array_min_x3f___redArg(
    mut v_inst_134_: *mut leanh::LeanObject,
    mut v_arr_135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: u8 = 0;
    v___x_136_ = lean_array_get_size(v_arr_135_);
    v___x_137_ = leanh::lean_unsigned_to_nat(0);
    v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
    if v___x_138_ == 0 {
        let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_139_ = l_Array_min___redArg(v_inst_134_, v_arr_135_);
        v___x_140_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_140_, 0, v___x_139_);
        return v___x_140_;
    } else {
        let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_arr_135_);
        leanh::lean_dec(v_inst_134_);
        v___x_141_ = leanh::lean_box(0);
        return v___x_141_;
    }
}
pub unsafe fn l_Array_min_x3f(
    mut v_00_u03b1_142_: *mut leanh::LeanObject,
    mut v_inst_143_: *mut leanh::LeanObject,
    mut v_arr_144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_145_ = l_Array_min_x3f___redArg(v_inst_143_, v_arr_144_);
    return v___x_145_;
}
pub unsafe fn l_Array_max___redArg(
    mut v_inst_146_: *mut leanh::LeanObject,
    mut v_arr_147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: u8 = 0;
    v___x_148_ = leanh::lean_unsigned_to_nat(0);
    v___x_149_ = lean_array_fget(v_arr_147_, v___x_148_);
    v___x_150_ = leanh::lean_unsigned_to_nat(1);
    v___x_151_ = lean_array_get_size(v_arr_147_);
    v___x_152_ = l_Array_min___redArg___closed__9;
    v___x_153_ = lean_nat_dec_lt(v___x_150_, v___x_151_);
    if v___x_153_ == 0 {
        leanh::lean_dec_ref(v_arr_147_);
        leanh::lean_dec(v_inst_146_);
        return v___x_149_;
    } else {
        let mut v___f_154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_155_: u8 = 0;
        v___f_154_ = leanh::lean_alloc_closure(
            l_Array_min___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_154_, 0, v_inst_146_);
        v___x_155_ = lean_nat_dec_le(v___x_151_, v___x_151_);
        if v___x_155_ == 0 {
            if v___x_153_ == 0 {
                leanh::lean_dec_ref(v___f_154_);
                leanh::lean_dec_ref(v_arr_147_);
                return v___x_149_;
            } else {
                let mut v___x_156_: usize = 0;
                let mut v___x_157_: usize = 0;
                let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_156_ = 1usize;
                v___x_157_ = lean_usize_of_nat(v___x_151_);
                v___x_158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_152_,
                    v___f_154_,
                    v_arr_147_,
                    v___x_156_,
                    v___x_157_,
                    v___x_149_,
                );
                return v___x_158_;
            }
        } else {
            let mut v___x_159_: usize = 0;
            let mut v___x_160_: usize = 0;
            let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_159_ = 1usize;
            v___x_160_ = lean_usize_of_nat(v___x_151_);
            v___x_161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_152_,
                v___f_154_,
                v_arr_147_,
                v___x_159_,
                v___x_160_,
                v___x_149_,
            );
            return v___x_161_;
        }
    }
}
pub unsafe fn l_Array_max(
    mut v_00_u03b1_162_: *mut leanh::LeanObject,
    mut v_inst_163_: *mut leanh::LeanObject,
    mut v_arr_164_: *mut leanh::LeanObject,
    mut v_h_165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_166_ = l_Array_max___redArg(v_inst_163_, v_arr_164_);
    return v___x_166_;
}
pub unsafe fn l_Array_max_x3f___redArg(
    mut v_inst_167_: *mut leanh::LeanObject,
    mut v_arr_168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: u8 = 0;
    v___x_169_ = lean_array_get_size(v_arr_168_);
    v___x_170_ = leanh::lean_unsigned_to_nat(0);
    v___x_171_ = lean_nat_dec_eq(v___x_169_, v___x_170_);
    if v___x_171_ == 0 {
        let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_172_ = l_Array_max___redArg(v_inst_167_, v_arr_168_);
        v___x_173_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_173_, 0, v___x_172_);
        return v___x_173_;
    } else {
        let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_arr_168_);
        leanh::lean_dec(v_inst_167_);
        v___x_174_ = leanh::lean_box(0);
        return v___x_174_;
    }
}
pub unsafe fn l_Array_max_x3f(
    mut v_00_u03b1_175_: *mut leanh::LeanObject,
    mut v_inst_176_: *mut leanh::LeanObject,
    mut v_arr_177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_178_ = l_Array_max_x3f___redArg(v_inst_176_, v_arr_177_);
    return v___x_178_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_MinMax(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_MinMax(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_MinMax(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_DecidableEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_MinMax(builtin);
}