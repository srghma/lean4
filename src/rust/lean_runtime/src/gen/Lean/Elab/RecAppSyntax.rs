// Lean compiler output
// Module: Lean.Elab.RecAppSyntax
// Imports: Lean.Expr
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Syntax_getPos_x3f};
use crate::r#gen::Lean::Data::KVMap::{
    l_Lean_KVMap_contains, l_Lean_KVMap_empty, l_Lean_KVMap_find, l_Lean_KVMap_insert,
};
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_mkMData, runtime_initialize_Lean_Expr,
};
pub static l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [95, 114, 101, 99, 65, 112, 112, 0],
};
static mut l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5349567883337469548 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [95, 114, 101, 99, 65, 112, 112, 80, 111, 115, 0],
};
static mut l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        2302941783115023138 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_mkRecAppWithSyntax(
    mut v_e_68_: *mut crate::leanh::LeanObject,
    mut v_stx_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_74_: u8 = 0;
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_80_: u8 = 0;
    let mut v___x_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_87_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_70_ = l_Lean_KVMap_empty;
                v___x_71_ = l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey;
                crate::leanh::lean_inc(v_stx_69_);
                v___x_72_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_72_, 0, v_stx_69_);
                v_m_73_ = l_Lean_KVMap_insert(v___x_70_, v___x_71_, v___x_72_);
                v___x_74_ = 0;
                v___x_75_ = l_Lean_Syntax_getPos_x3f(v_stx_69_, v___x_74_);
                crate::leanh::lean_dec(v_stx_69_);
                if crate::leanh::lean_obj_tag(v___x_75_) == 0 {
                    v___x_76_ = l_Lean_mkMData(v_m_73_, v_e_68_);
                    return v___x_76_;
                } else {
                    v_val_77_ = crate::leanh::lean_ctor_get(v___x_75_, 0);
                    v_isSharedCheck_87_ = (!crate::leanh::lean_is_exclusive(v___x_75_)) as u8;
                    if v_isSharedCheck_87_ == 0 {
                        v___x_79_ = v___x_75_;
                        v_isShared_80_ = v_isSharedCheck_87_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_77_);
                        crate::leanh::lean_dec(v___x_75_);
                        v___x_79_ = crate::leanh::lean_box(0);
                        v_isShared_80_ = v_isSharedCheck_87_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_81_ = l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey;
                if v_isShared_80_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_79_, 3);
                    v___x_83_ = v___x_79_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_86_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_86_, 0, v_val_77_);
                    v___x_83_ = v_reuseFailAlloc_86_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_84_ = l_Lean_KVMap_insert(v_m_73_, v___x_81_, v___x_83_);
                v___x_85_ = l_Lean_mkMData(v___x_84_, v_e_68_);
                return v___x_85_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getRecAppSyntax_x3f(
    mut v_e_88_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_95_: u8 = 0;
    let mut v_v_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_101_: u8 = 0;
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_88_) == 10 {
                    v_data_89_ = crate::leanh::lean_ctor_get(v_e_88_, 0);
                    v___x_90_ = l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey;
                    v___x_91_ = l_Lean_KVMap_find(v_data_89_, v___x_90_);
                    if crate::leanh::lean_obj_tag(v___x_91_) == 1 {
                        v_val_92_ = crate::leanh::lean_ctor_get(v___x_91_, 0);
                        v_isSharedCheck_101_ = (!crate::leanh::lean_is_exclusive(v___x_91_)) as u8;
                        if v_isSharedCheck_101_ == 0 {
                            v___x_94_ = v___x_91_;
                            v_isShared_95_ = v_isSharedCheck_101_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_92_);
                            crate::leanh::lean_dec(v___x_91_);
                            v___x_94_ = crate::leanh::lean_box(0);
                            v_isShared_95_ = v_isSharedCheck_101_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_91_);
                        v___x_102_ = crate::leanh::lean_box(0);
                        return v___x_102_;
                    }
                } else {
                    v___x_103_ = crate::leanh::lean_box(0);
                    return v___x_103_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_val_92_) == 5 {
                    v_v_96_ = crate::leanh::lean_ctor_get(v_val_92_, 0);
                    crate::leanh::lean_inc(v_v_96_);
                    crate::leanh::lean_dec_ref_known(v_val_92_, 1);
                    if v_isShared_95_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_94_, 0, v_v_96_);
                        v___x_98_ = v___x_94_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_99_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_99_, 0, v_v_96_);
                        v___x_98_ = v_reuseFailAlloc_99_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_94_);
                    crate::leanh::lean_dec(v_val_92_);
                    v___x_100_ = crate::leanh::lean_box(0);
                    return v___x_100_;
                }
            }
            2 => {
                return v___x_98_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getRecAppSyntax_x3f___boxed(
    mut v_e_104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_105_ = l_Lean_getRecAppSyntax_x3f(v_e_104_);
    crate::leanh::lean_dec_ref(v_e_104_);
    return v_res_105_;
}
pub unsafe fn l_Lean_MData_isRecApp(mut v_d_106_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: u8 = 0;
    v___x_107_ = l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey;
    v___x_108_ = l_Lean_KVMap_contains(v_d_106_, v___x_107_);
    return v___x_108_;
}
pub unsafe fn l_Lean_MData_isRecApp___boxed(
    mut v_d_109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_110_: u8 = 0;
    let mut v_r_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_110_ = l_Lean_MData_isRecApp(v_d_109_);
    crate::leanh::lean_dec(v_d_109_);
    v_r_111_ = crate::leanh::lean_box((v_res_110_) as usize);
    return v_r_111_;
}
pub unsafe fn l_Lean_hasRecAppSyntax(mut v_e_112_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_112_) == 10 {
        let mut v_data_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_114_: u8 = 0;
        v_data_113_ = crate::leanh::lean_ctor_get(v_e_112_, 0);
        v___x_114_ = l_Lean_MData_isRecApp(v_data_113_);
        return v___x_114_;
    } else {
        let mut v___x_115_: u8 = 0;
        v___x_115_ = 0;
        return v___x_115_;
    }
}
pub unsafe fn l_Lean_hasRecAppSyntax___boxed(
    mut v_e_116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_117_: u8 = 0;
    let mut v_r_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_117_ = l_Lean_hasRecAppSyntax(v_e_116_);
    crate::leanh::lean_dec_ref(v_e_116_);
    v_r_118_ = crate::leanh::lean_box((v_res_117_) as usize);
    return v_r_118_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_RecAppSyntax(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_RecAppSyntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_RecAppSyntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_RecAppSyntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_RecAppSyntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_RecAppSyntax(builtin);
}
