// Lean compiler output
// Module: Lean.Util.RecDepth
// Imports: Lean.Data.Options
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_defaultMaxRecDepth,
};
use crate::r#gen::Lean::Data::Options::{
    initialize_Lean_Data_Options, lean_register_option, runtime_initialize_Lean_Data_Options,
};
pub static l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12806419848908435157 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<67> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 102, 111, 114, 32, 109, 97, 110, 121, 32, 76, 101, 97, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 115, 44, 32, 48, 32, 109, 101, 97, 110, 115, 32, 110, 111, 32, 108, 105, 109, 105, 116, 0]};
static mut l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__4_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__0_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4317123172558175340 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_maxRecDepth: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_RecDepth_0__Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__spec__0(
    mut v_name_52_: *mut crate::leanh::LeanObject,
    mut v_decl_53_: *mut crate::leanh::LeanObject,
    mut v_ref_54_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_64_: u8 = 0;
    let mut v___x_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_69_: u8 = 0;
    let mut v_unused_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_74_: u8 = 0;
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_78_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_56_ = crate::leanh::lean_ctor_get(v_decl_53_, 0);
                v_descr_57_ = crate::leanh::lean_ctor_get(v_decl_53_, 1);
                v_deprecation_x3f_58_ = crate::leanh::lean_ctor_get(v_decl_53_, 2);
                crate::leanh::lean_inc(v_defValue_56_);
                v___x_59_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_59_, 0, v_defValue_56_);
                crate::leanh::lean_inc(v_deprecation_x3f_58_);
                crate::leanh::lean_inc_ref(v_descr_57_);
                crate::leanh::lean_inc_n(v_name_52_, 2);
                v___x_60_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_60_, 0, v_name_52_);
                crate::leanh::lean_ctor_set(v___x_60_, 1, v_ref_54_);
                crate::leanh::lean_ctor_set(v___x_60_, 2, v___x_59_);
                crate::leanh::lean_ctor_set(v___x_60_, 3, v_descr_57_);
                crate::leanh::lean_ctor_set(v___x_60_, 4, v_deprecation_x3f_58_);
                v___x_61_ = lean_register_option(v_name_52_, v___x_60_);
                if crate::leanh::lean_obj_tag(v___x_61_) == 0 {
                    v_isSharedCheck_69_ = (!crate::leanh::lean_is_exclusive(v___x_61_)) as u8;
                    if v_isSharedCheck_69_ == 0 {
                        v_unused_70_ = crate::leanh::lean_ctor_get(v___x_61_, 0);
                        crate::leanh::lean_dec(v_unused_70_);
                        v___x_63_ = v___x_61_;
                        v_isShared_64_ = v_isSharedCheck_69_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_61_);
                        v___x_63_ = crate::leanh::lean_box(0);
                        v_isShared_64_ = v_isSharedCheck_69_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_52_);
                    v_a_71_ = crate::leanh::lean_ctor_get(v___x_61_, 0);
                    v_isSharedCheck_78_ = (!crate::leanh::lean_is_exclusive(v___x_61_)) as u8;
                    if v_isSharedCheck_78_ == 0 {
                        v___x_73_ = v___x_61_;
                        v_isShared_74_ = v_isSharedCheck_78_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_71_);
                        crate::leanh::lean_dec(v___x_61_);
                        v___x_73_ = crate::leanh::lean_box(0);
                        v_isShared_74_ = v_isSharedCheck_78_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_56_);
                v___x_65_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_65_, 0, v_name_52_);
                crate::leanh::lean_ctor_set(v___x_65_, 1, v_defValue_56_);
                if v_isShared_64_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_63_, 0, v___x_65_);
                    v___x_67_ = v___x_63_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_68_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_65_);
                    v___x_67_ = v_reuseFailAlloc_68_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_67_;
            }
            3 => {
                if v_isShared_74_ == 0 {
                    v___x_76_ = v___x_73_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_77_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_71_);
                    v___x_76_ = v_reuseFailAlloc_77_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_76_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_RecDepth_0__Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_79_: *mut crate::leanh::LeanObject,
    mut v_decl_80_: *mut crate::leanh::LeanObject,
    mut v_ref_81_: *mut crate::leanh::LeanObject,
    mut v_a_82_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_83_ = l_Lean_Option_register___at___00__private_Lean_Util_RecDepth_0__Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__spec__0(v_name_79_, v_decl_80_, v_ref_81_);
    crate::leanh::lean_dec_ref(v_decl_80_);
    return v_res_83_;
}
pub unsafe fn _init_l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_88_ = crate::leanh::lean_box(0);
    v___x_89_ = l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__2_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_;
    v___x_90_ = l_Lean_defaultMaxRecDepth;
    v___x_91_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_91_, 0, v___x_90_);
    crate::leanh::lean_ctor_set(v___x_91_, 1, v___x_89_);
    crate::leanh::lean_ctor_set(v___x_91_, 2, v___x_88_);
    return v___x_91_;
}
pub unsafe fn l___private_Lean_Util_RecDepth_0__Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_97_ = l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__1_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_;
    v___x_98_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_), core::ptr::addr_of_mut!(l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__once), _init_l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__3_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_);
    v___x_99_ = l___private_Lean_Util_RecDepth_0__Lean_initFn___closed__5_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_;
    v___x_100_ = l_Lean_Option_register___at___00__private_Lean_Util_RecDepth_0__Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4__spec__0(v___x_97_, v___x_98_, v___x_99_);
    return v___x_100_;
}
pub unsafe fn l___private_Lean_Util_RecDepth_0__Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4____boxed(
    mut v_a_101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_102_ = l___private_Lean_Util_RecDepth_0__Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_();
    return v_res_102_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_RecDepth(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_RecDepth_0__Lean_initFn_00___x40_Lean_Util_RecDepth_797063591____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_maxRecDepth = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_maxRecDepth);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_RecDepth(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_RecDepth(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_RecDepth(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_RecDepth(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_RecDepth(builtin);
}
