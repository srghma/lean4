// Lean compiler output
// Module: Init.Data.Ord.SInt
// Imports: Init.Data.Order.Ord Init.Data.Order.ClassesExtra Init.Data.SInt.Basic Init.Data.SInt.Lemmas Init.Data.Order.Lemmas
use crate::r#gen::Init::Data::Order::ClassesExtra::{
    initialize_Init_Data_Order_ClassesExtra, runtime_initialize_Init_Data_Order_ClassesExtra,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::Order::Ord::{
    initialize_Init_Data_Order_Ord, runtime_initialize_Init_Data_Order_Ord,
};
use crate::r#gen::Init::Data::SInt::Basic::{
    initialize_Init_Data_SInt_Basic, runtime_initialize_Init_Data_SInt_Basic,
};
use crate::r#gen::Init::Data::SInt::Lemmas::{
    initialize_Init_Data_SInt_Lemmas, runtime_initialize_Init_Data_SInt_Lemmas,
};
use crate::ffi::{
    lean_int8_dec_eq, lean_int8_dec_lt, lean_int16_dec_eq, lean_int16_dec_lt, lean_int32_dec_eq,
    lean_int32_dec_lt, lean_int64_dec_eq, lean_int64_dec_lt, lean_isize_dec_eq, lean_isize_dec_lt,
};
pub static l_Int8_instOrd___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int8_instOrd___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int8_instOrd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int8_instOrd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int16_instOrd___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int16_instOrd___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int16_instOrd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int16_instOrd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int32_instOrd___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int32_instOrd___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int32_instOrd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int32_instOrd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int64_instOrd___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int64_instOrd___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int64_instOrd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int64_instOrd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_ISize_instOrd___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_ISize_instOrd___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ISize_instOrd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_ISize_instOrd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Int8_instOrd___lam__0(mut v_x_76_: u8, mut v_y_77_: u8) -> u8 {
    let mut v___x_78_: u8 = 0;
    v___x_78_ = lean_int8_dec_lt(v_x_76_, v_y_77_);
    if v___x_78_ == 0 {
        let mut v___x_79_: u8 = 0;
        v___x_79_ = lean_int8_dec_eq(v_x_76_, v_y_77_);
        if v___x_79_ == 0 {
            let mut v___x_80_: u8 = 0;
            v___x_80_ = 2;
            return v___x_80_;
        } else {
            let mut v___x_81_: u8 = 0;
            v___x_81_ = 1;
            return v___x_81_;
        }
    } else {
        let mut v___x_82_: u8 = 0;
        v___x_82_ = 0;
        return v___x_82_;
    }
}
pub unsafe fn l_Int8_instOrd___lam__0___boxed(
    mut v_x_83_: *mut crate::leanh::LeanObject,
    mut v_y_84_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_85_: u8 = 0;
    let mut v_y_boxed_86_: u8 = 0;
    let mut v_res_87_: u8 = 0;
    let mut v_r_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_85_ = (crate::leanh::lean_unbox(v_x_83_) as u8);
    v_y_boxed_86_ = (crate::leanh::lean_unbox(v_y_84_) as u8);
    v_res_87_ = l_Int8_instOrd___lam__0(v_x_boxed_85_, v_y_boxed_86_);
    v_r_88_ = crate::leanh::lean_box((v_res_87_) as usize);
    return v_r_88_;
}
pub unsafe fn l_Int16_instOrd___lam__0(mut v_x_91_: u16, mut v_y_92_: u16) -> u8 {
    let mut v___x_93_: u8 = 0;
    v___x_93_ = lean_int16_dec_lt(v_x_91_, v_y_92_);
    if v___x_93_ == 0 {
        let mut v___x_94_: u8 = 0;
        v___x_94_ = lean_int16_dec_eq(v_x_91_, v_y_92_);
        if v___x_94_ == 0 {
            let mut v___x_95_: u8 = 0;
            v___x_95_ = 2;
            return v___x_95_;
        } else {
            let mut v___x_96_: u8 = 0;
            v___x_96_ = 1;
            return v___x_96_;
        }
    } else {
        let mut v___x_97_: u8 = 0;
        v___x_97_ = 0;
        return v___x_97_;
    }
}
pub unsafe fn l_Int16_instOrd___lam__0___boxed(
    mut v_x_98_: *mut crate::leanh::LeanObject,
    mut v_y_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_100_: u16 = 0;
    let mut v_y_boxed_101_: u16 = 0;
    let mut v_res_102_: u8 = 0;
    let mut v_r_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_100_ = (crate::leanh::lean_unbox(v_x_98_) as u16);
    v_y_boxed_101_ = (crate::leanh::lean_unbox(v_y_99_) as u16);
    v_res_102_ = l_Int16_instOrd___lam__0(v_x_boxed_100_, v_y_boxed_101_);
    v_r_103_ = crate::leanh::lean_box((v_res_102_) as usize);
    return v_r_103_;
}
pub unsafe fn l_Int32_instOrd___lam__0(mut v_x_106_: u32, mut v_y_107_: u32) -> u8 {
    let mut v___x_108_: u8 = 0;
    v___x_108_ = lean_int32_dec_lt(v_x_106_, v_y_107_);
    if v___x_108_ == 0 {
        let mut v___x_109_: u8 = 0;
        v___x_109_ = lean_int32_dec_eq(v_x_106_, v_y_107_);
        if v___x_109_ == 0 {
            let mut v___x_110_: u8 = 0;
            v___x_110_ = 2;
            return v___x_110_;
        } else {
            let mut v___x_111_: u8 = 0;
            v___x_111_ = 1;
            return v___x_111_;
        }
    } else {
        let mut v___x_112_: u8 = 0;
        v___x_112_ = 0;
        return v___x_112_;
    }
}
pub unsafe fn l_Int32_instOrd___lam__0___boxed(
    mut v_x_113_: *mut crate::leanh::LeanObject,
    mut v_y_114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_115_: u32 = 0;
    let mut v_y_boxed_116_: u32 = 0;
    let mut v_res_117_: u8 = 0;
    let mut v_r_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_115_ = crate::leanh::lean_unbox_uint32(v_x_113_);
    crate::leanh::lean_dec(v_x_113_);
    v_y_boxed_116_ = crate::leanh::lean_unbox_uint32(v_y_114_);
    crate::leanh::lean_dec(v_y_114_);
    v_res_117_ = l_Int32_instOrd___lam__0(v_x_boxed_115_, v_y_boxed_116_);
    v_r_118_ = crate::leanh::lean_box((v_res_117_) as usize);
    return v_r_118_;
}
pub unsafe fn l_Int64_instOrd___lam__0(mut v_x_121_: u64, mut v_y_122_: u64) -> u8 {
    let mut v___x_123_: u8 = 0;
    v___x_123_ = lean_int64_dec_lt(v_x_121_, v_y_122_);
    if v___x_123_ == 0 {
        let mut v___x_124_: u8 = 0;
        v___x_124_ = lean_int64_dec_eq(v_x_121_, v_y_122_);
        if v___x_124_ == 0 {
            let mut v___x_125_: u8 = 0;
            v___x_125_ = 2;
            return v___x_125_;
        } else {
            let mut v___x_126_: u8 = 0;
            v___x_126_ = 1;
            return v___x_126_;
        }
    } else {
        let mut v___x_127_: u8 = 0;
        v___x_127_ = 0;
        return v___x_127_;
    }
}
pub unsafe fn l_Int64_instOrd___lam__0___boxed(
    mut v_x_128_: *mut crate::leanh::LeanObject,
    mut v_y_129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_130_: u64 = 0;
    let mut v_y_boxed_131_: u64 = 0;
    let mut v_res_132_: u8 = 0;
    let mut v_r_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_130_ = crate::leanh::lean_unbox_uint64(v_x_128_);
    crate::leanh::lean_dec_ref(v_x_128_);
    v_y_boxed_131_ = crate::leanh::lean_unbox_uint64(v_y_129_);
    crate::leanh::lean_dec_ref(v_y_129_);
    v_res_132_ = l_Int64_instOrd___lam__0(v_x_boxed_130_, v_y_boxed_131_);
    v_r_133_ = crate::leanh::lean_box((v_res_132_) as usize);
    return v_r_133_;
}
pub unsafe fn l_ISize_instOrd___lam__0(mut v_x_136_: usize, mut v_y_137_: usize) -> u8 {
    let mut v___x_138_: u8 = 0;
    v___x_138_ = lean_isize_dec_lt(v_x_136_, v_y_137_);
    if v___x_138_ == 0 {
        let mut v___x_139_: u8 = 0;
        v___x_139_ = lean_isize_dec_eq(v_x_136_, v_y_137_);
        if v___x_139_ == 0 {
            let mut v___x_140_: u8 = 0;
            v___x_140_ = 2;
            return v___x_140_;
        } else {
            let mut v___x_141_: u8 = 0;
            v___x_141_ = 1;
            return v___x_141_;
        }
    } else {
        let mut v___x_142_: u8 = 0;
        v___x_142_ = 0;
        return v___x_142_;
    }
}
pub unsafe fn l_ISize_instOrd___lam__0___boxed(
    mut v_x_143_: *mut crate::leanh::LeanObject,
    mut v_y_144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_145_: usize = 0;
    let mut v_y_boxed_146_: usize = 0;
    let mut v_res_147_: u8 = 0;
    let mut v_r_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_145_ = crate::leanh::lean_unbox_usize(v_x_143_);
    crate::leanh::lean_dec(v_x_143_);
    v_y_boxed_146_ = crate::leanh::lean_unbox_usize(v_y_144_);
    crate::leanh::lean_dec(v_y_144_);
    v_res_147_ = l_ISize_instOrd___lam__0(v_x_boxed_145_, v_y_boxed_146_);
    v_r_148_ = crate::leanh::lean_box((v_res_147_) as usize);
    return v_r_148_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Ord_SInt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Ord(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_ClassesExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Ord_SInt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Ord_SInt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Ord(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_ClassesExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_SInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Ord_SInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Ord_SInt(builtin);
}
