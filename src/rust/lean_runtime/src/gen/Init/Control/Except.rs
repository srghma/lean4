// Lean compiler output
// Module: Init.Control.Except
// Imports: Init.Control.Basic Init.Control.Id
use crate::r#gen::Init::Control::Basic::{
    initialize_Init_Control_Basic, runtime_initialize_Init_Control_Basic,
};
use crate::r#gen::Init::Control::Id::{
    initialize_Init_Control_Id, runtime_initialize_Init_Control_Id,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
};
pub static l_Except_instMonad___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Except_instMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Except_instMonad___closed__0_value) as *mut LeanObject;
pub static l_Except_instMonad___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_instMonad___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Except_instMonad___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Except_instMonad___closed__1_value) as *mut LeanObject;
pub static l_Except_instMonad___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Except_instMonad___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Except_instMonad___closed__2_value) as *mut LeanObject;
pub static l_Except_instMonad___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Except_instMonad___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Except_instMonad___closed__3_value) as *mut LeanObject;
pub static l_Except_instMonad___closed__4_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_map as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Except_instMonad___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Except_instMonad___closed__4_value) as *mut LeanObject;
pub static l_Except_instMonad___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Except_instMonad___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Except_instMonad___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Except_instMonad___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Except_instMonad___closed__5_value) as *mut LeanObject;
pub static l_Except_instMonad___closed__6_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_pure as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Except_instMonad___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Except_instMonad___closed__6_value) as *mut LeanObject;
pub static l_Except_instMonad___closed__7_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Except_instMonad___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Except_instMonad___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Except_instMonad___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Except_instMonad___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Except_instMonad___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Except_instMonad___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Except_instMonad___closed__7_value) as *mut LeanObject;
pub static l_Except_instMonad___closed__8_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_bind as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Except_instMonad___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Except_instMonad___closed__8_value) as *mut LeanObject;
pub static l_Except_instMonad___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Except_instMonad___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Except_instMonad___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Except_instMonad___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Except_instMonad___closed__9_value) as *mut LeanObject;
pub static l_ExceptT_lift___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ExceptT_lift___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ExceptT_lift___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptT_lift___redArg___closed__0_value) as *mut LeanObject;
pub static l_ExceptT_instMonadFunctor___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ExceptT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ExceptT_instMonadFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptT_instMonadFunctor___closed__0_value) as *mut LeanObject;
pub static l_instMonadExceptOfExcept___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadExceptOfExcept___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadExceptOfExcept___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfExcept___closed__0_value) as *mut LeanObject;
pub static l_instMonadExceptOfExcept___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_tryCatch as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instMonadExceptOfExcept___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfExcept___closed__1_value) as *mut LeanObject;
pub static l_instMonadExceptOfExcept___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadExceptOfExcept___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadExceptOfExcept___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_instMonadExceptOfExcept___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfExcept___closed__2_value) as *mut LeanObject;
pub static l_instMonadControlExceptTOfMonad___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadControlExceptTOfMonad___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadControlExceptTOfMonad___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlExceptTOfMonad___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_instMonadControlExceptTOfMonad___redArg___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadControlExceptTOfMonad___redArg___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadControlExceptTOfMonad___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlExceptTOfMonad___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_tryFinally___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_tryFinally___redArg___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_tryFinally___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_tryFinally___redArg___closed__0_value) as *mut LeanObject;
pub static l_Id_finally___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_finally___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Id_finally___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Id_finally___closed__0_value) as *mut LeanObject;
pub static mut l_Id_finally: *mut LeanObject =
    core::ptr::addr_of!(l_Id_finally___closed__0_value) as *mut LeanObject;
pub static l_instMonadAttachExceptTOfMonad___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadAttachExceptTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadAttachExceptTOfMonad___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadAttachExceptTOfMonad___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Except_pure___redArg(mut v_a_1096_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    v___x_1097_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1097_, 0, v_a_1096_);
    return v___x_1097_;
}
pub unsafe fn l_Except_pure(
    mut v_00_u03b5_1098_: *mut LeanObject,
    mut v_00_u03b1_1099_: *mut LeanObject,
    mut v_a_1100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    v___x_1101_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1101_, 0, v_a_1100_);
    return v___x_1101_;
}
pub unsafe fn l_Except_map___redArg(
    mut v_f_1102_: *mut LeanObject,
    mut v_x_1103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1107_: u8 = 0;
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut v_a_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1115_: u8 = 0;
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1103_) == 0 {
                    lean_dec(v_f_1102_);
                    v_a_1104_ = lean_ctor_get(v_x_1103_, 0);
                    v_isSharedCheck_1111_ = (!lean_is_exclusive(v_x_1103_)) as u8;
                    if v_isSharedCheck_1111_ == 0 {
                        v___x_1106_ = v_x_1103_;
                        v_isShared_1107_ = v_isSharedCheck_1111_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1104_);
                        lean_dec(v_x_1103_);
                        v___x_1106_ = lean_box(0);
                        v_isShared_1107_ = v_isSharedCheck_1111_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1112_ = lean_ctor_get(v_x_1103_, 0);
                    v_isSharedCheck_1120_ = (!lean_is_exclusive(v_x_1103_)) as u8;
                    if v_isSharedCheck_1120_ == 0 {
                        v___x_1114_ = v_x_1103_;
                        v_isShared_1115_ = v_isSharedCheck_1120_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1112_);
                        lean_dec(v_x_1103_);
                        v___x_1114_ = lean_box(0);
                        v_isShared_1115_ = v_isSharedCheck_1120_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1107_ == 0 {
                    v___x_1109_ = v___x_1106_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
                    v___x_1109_ = v_reuseFailAlloc_1110_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1109_;
            }
            3 => {
                v___x_1116_ = lean_apply_1(v_f_1102_, v_a_1112_);
                if v_isShared_1115_ == 0 {
                    lean_ctor_set(v___x_1114_, 0, v___x_1116_);
                    v___x_1118_ = v___x_1114_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
                    v___x_1118_ = v_reuseFailAlloc_1119_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Except_map(
    mut v_00_u03b5_1121_: *mut LeanObject,
    mut v_00_u03b1_1122_: *mut LeanObject,
    mut v_00_u03b2_1123_: *mut LeanObject,
    mut v_f_1124_: *mut LeanObject,
    mut v_x_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1129_: u8 = 0;
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1133_: u8 = 0;
    let mut v_a_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1137_: u8 = 0;
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1125_) == 0 {
                    lean_dec(v_f_1124_);
                    v_a_1126_ = lean_ctor_get(v_x_1125_, 0);
                    v_isSharedCheck_1133_ = (!lean_is_exclusive(v_x_1125_)) as u8;
                    if v_isSharedCheck_1133_ == 0 {
                        v___x_1128_ = v_x_1125_;
                        v_isShared_1129_ = v_isSharedCheck_1133_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1126_);
                        lean_dec(v_x_1125_);
                        v___x_1128_ = lean_box(0);
                        v_isShared_1129_ = v_isSharedCheck_1133_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1134_ = lean_ctor_get(v_x_1125_, 0);
                    v_isSharedCheck_1142_ = (!lean_is_exclusive(v_x_1125_)) as u8;
                    if v_isSharedCheck_1142_ == 0 {
                        v___x_1136_ = v_x_1125_;
                        v_isShared_1137_ = v_isSharedCheck_1142_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1134_);
                        lean_dec(v_x_1125_);
                        v___x_1136_ = lean_box(0);
                        v_isShared_1137_ = v_isSharedCheck_1142_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1129_ == 0 {
                    v___x_1131_ = v___x_1128_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
                    v___x_1131_ = v_reuseFailAlloc_1132_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1131_;
            }
            3 => {
                v___x_1138_ = lean_apply_1(v_f_1124_, v_a_1134_);
                if v_isShared_1137_ == 0 {
                    lean_ctor_set(v___x_1136_, 0, v___x_1138_);
                    v___x_1140_ = v___x_1136_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
                    v___x_1140_ = v_reuseFailAlloc_1141_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Control_Except_0__Except_map_match__1_splitter___redArg(
    mut v_x_1143_: *mut LeanObject,
    mut v_h__1_1144_: *mut LeanObject,
    mut v_h__2_1145_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1143_) == 0 {
        let mut v_a_1146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1145_);
        v_a_1146_ = lean_ctor_get(v_x_1143_, 0);
        lean_inc(v_a_1146_);
        lean_dec_ref_known(v_x_1143_, 1);
        v___x_1147_ = lean_apply_1(v_h__1_1144_, v_a_1146_);
        return v___x_1147_;
    } else {
        let mut v_a_1148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1144_);
        v_a_1148_ = lean_ctor_get(v_x_1143_, 0);
        lean_inc(v_a_1148_);
        lean_dec_ref_known(v_x_1143_, 1);
        v___x_1149_ = lean_apply_1(v_h__2_1145_, v_a_1148_);
        return v___x_1149_;
    }
}
pub unsafe fn l___private_Init_Control_Except_0__Except_map_match__1_splitter(
    mut v_00_u03b5_1150_: *mut LeanObject,
    mut v_00_u03b1_1151_: *mut LeanObject,
    mut v_motive_1152_: *mut LeanObject,
    mut v_x_1153_: *mut LeanObject,
    mut v_h__1_1154_: *mut LeanObject,
    mut v_h__2_1155_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1153_) == 0 {
        let mut v_a_1156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1155_);
        v_a_1156_ = lean_ctor_get(v_x_1153_, 0);
        lean_inc(v_a_1156_);
        lean_dec_ref_known(v_x_1153_, 1);
        v___x_1157_ = lean_apply_1(v_h__1_1154_, v_a_1156_);
        return v___x_1157_;
    } else {
        let mut v_a_1158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1154_);
        v_a_1158_ = lean_ctor_get(v_x_1153_, 0);
        lean_inc(v_a_1158_);
        lean_dec_ref_known(v_x_1153_, 1);
        v___x_1159_ = lean_apply_1(v_h__2_1155_, v_a_1158_);
        return v___x_1159_;
    }
}
pub unsafe fn l_Except_mapError___redArg(
    mut v_f_1160_: *mut LeanObject,
    mut v_x_1161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1170_: u8 = 0;
    let mut v_a_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1174_: u8 = 0;
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1161_) == 0 {
                    v_a_1162_ = lean_ctor_get(v_x_1161_, 0);
                    v_isSharedCheck_1170_ = (!lean_is_exclusive(v_x_1161_)) as u8;
                    if v_isSharedCheck_1170_ == 0 {
                        v___x_1164_ = v_x_1161_;
                        v_isShared_1165_ = v_isSharedCheck_1170_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1162_);
                        lean_dec(v_x_1161_);
                        v___x_1164_ = lean_box(0);
                        v_isShared_1165_ = v_isSharedCheck_1170_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_1160_);
                    v_a_1171_ = lean_ctor_get(v_x_1161_, 0);
                    v_isSharedCheck_1178_ = (!lean_is_exclusive(v_x_1161_)) as u8;
                    if v_isSharedCheck_1178_ == 0 {
                        v___x_1173_ = v_x_1161_;
                        v_isShared_1174_ = v_isSharedCheck_1178_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1171_);
                        lean_dec(v_x_1161_);
                        v___x_1173_ = lean_box(0);
                        v_isShared_1174_ = v_isSharedCheck_1178_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1166_ = lean_apply_1(v_f_1160_, v_a_1162_);
                if v_isShared_1165_ == 0 {
                    lean_ctor_set(v___x_1164_, 0, v___x_1166_);
                    v___x_1168_ = v___x_1164_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
                    v___x_1168_ = v_reuseFailAlloc_1169_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1168_;
            }
            3 => {
                if v_isShared_1174_ == 0 {
                    v___x_1176_ = v___x_1173_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
                    v___x_1176_ = v_reuseFailAlloc_1177_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Except_mapError(
    mut v_00_u03b5_1179_: *mut LeanObject,
    mut v_00_u03b5_x27_1180_: *mut LeanObject,
    mut v_00_u03b1_1181_: *mut LeanObject,
    mut v_f_1182_: *mut LeanObject,
    mut v_x_1183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1187_: u8 = 0;
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1192_: u8 = 0;
    let mut v_a_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1196_: u8 = 0;
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1200_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1183_) == 0 {
                    v_a_1184_ = lean_ctor_get(v_x_1183_, 0);
                    v_isSharedCheck_1192_ = (!lean_is_exclusive(v_x_1183_)) as u8;
                    if v_isSharedCheck_1192_ == 0 {
                        v___x_1186_ = v_x_1183_;
                        v_isShared_1187_ = v_isSharedCheck_1192_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1184_);
                        lean_dec(v_x_1183_);
                        v___x_1186_ = lean_box(0);
                        v_isShared_1187_ = v_isSharedCheck_1192_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_1182_);
                    v_a_1193_ = lean_ctor_get(v_x_1183_, 0);
                    v_isSharedCheck_1200_ = (!lean_is_exclusive(v_x_1183_)) as u8;
                    if v_isSharedCheck_1200_ == 0 {
                        v___x_1195_ = v_x_1183_;
                        v_isShared_1196_ = v_isSharedCheck_1200_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1193_);
                        lean_dec(v_x_1183_);
                        v___x_1195_ = lean_box(0);
                        v_isShared_1196_ = v_isSharedCheck_1200_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1188_ = lean_apply_1(v_f_1182_, v_a_1184_);
                if v_isShared_1187_ == 0 {
                    lean_ctor_set(v___x_1186_, 0, v___x_1188_);
                    v___x_1190_ = v___x_1186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
                    v___x_1190_ = v_reuseFailAlloc_1191_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1190_;
            }
            3 => {
                if v_isShared_1196_ == 0 {
                    v___x_1198_ = v___x_1195_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
                    v___x_1198_ = v_reuseFailAlloc_1199_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Except_bind___redArg(
    mut v_ma_1201_: *mut LeanObject,
    mut v_f_1202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1206_: u8 = 0;
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1210_: u8 = 0;
    let mut v_a_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_ma_1201_) == 0 {
                    lean_dec_ref(v_f_1202_);
                    v_a_1203_ = lean_ctor_get(v_ma_1201_, 0);
                    v_isSharedCheck_1210_ = (!lean_is_exclusive(v_ma_1201_)) as u8;
                    if v_isSharedCheck_1210_ == 0 {
                        v___x_1205_ = v_ma_1201_;
                        v_isShared_1206_ = v_isSharedCheck_1210_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1203_);
                        lean_dec(v_ma_1201_);
                        v___x_1205_ = lean_box(0);
                        v_isShared_1206_ = v_isSharedCheck_1210_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1211_ = lean_ctor_get(v_ma_1201_, 0);
                    lean_inc(v_a_1211_);
                    lean_dec_ref_known(v_ma_1201_, 1);
                    v___x_1212_ = lean_apply_1(v_f_1202_, v_a_1211_);
                    return v___x_1212_;
                }
            }
            1 => {
                if v_isShared_1206_ == 0 {
                    v___x_1208_ = v___x_1205_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
                    v___x_1208_ = v_reuseFailAlloc_1209_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Except_bind(
    mut v_00_u03b5_1213_: *mut LeanObject,
    mut v_00_u03b1_1214_: *mut LeanObject,
    mut v_00_u03b2_1215_: *mut LeanObject,
    mut v_ma_1216_: *mut LeanObject,
    mut v_f_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut v_a_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_ma_1216_) == 0 {
                    lean_dec_ref(v_f_1217_);
                    v_a_1218_ = lean_ctor_get(v_ma_1216_, 0);
                    v_isSharedCheck_1225_ = (!lean_is_exclusive(v_ma_1216_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v___x_1220_ = v_ma_1216_;
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1218_);
                        lean_dec(v_ma_1216_);
                        v___x_1220_ = lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1226_ = lean_ctor_get(v_ma_1216_, 0);
                    lean_inc(v_a_1226_);
                    lean_dec_ref_known(v_ma_1216_, 1);
                    v___x_1227_ = lean_apply_1(v_f_1217_, v_a_1226_);
                    return v___x_1227_;
                }
            }
            1 => {
                if v_isShared_1221_ == 0 {
                    v___x_1223_ = v___x_1220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
                    v___x_1223_ = v_reuseFailAlloc_1224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Except_toBool___redArg(mut v_x_1228_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_1228_) == 0 {
        let mut v___x_1229_: u8 = 0;
        v___x_1229_ = 0;
        return v___x_1229_;
    } else {
        let mut v___x_1230_: u8 = 0;
        v___x_1230_ = 1;
        return v___x_1230_;
    }
}
pub unsafe fn l_Except_toBool___redArg___boxed(mut v_x_1231_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1232_: u8 = 0;
    let mut v_r_1233_: *mut LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Except_toBool___redArg(v_x_1231_);
    lean_dec_ref(v_x_1231_);
    v_r_1233_ = lean_box((v_res_1232_) as usize);
    return v_r_1233_;
}
pub unsafe fn l_Except_toBool(
    mut v_00_u03b5_1234_: *mut LeanObject,
    mut v_00_u03b1_1235_: *mut LeanObject,
    mut v_x_1236_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1236_) == 0 {
        let mut v___x_1237_: u8 = 0;
        v___x_1237_ = 0;
        return v___x_1237_;
    } else {
        let mut v___x_1238_: u8 = 0;
        v___x_1238_ = 1;
        return v___x_1238_;
    }
}
pub unsafe fn l_Except_toBool___boxed(
    mut v_00_u03b5_1239_: *mut LeanObject,
    mut v_00_u03b1_1240_: *mut LeanObject,
    mut v_x_1241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1242_: u8 = 0;
    let mut v_r_1243_: *mut LeanObject = core::ptr::null_mut();
    v_res_1242_ = l_Except_toBool(v_00_u03b5_1239_, v_00_u03b1_1240_, v_x_1241_);
    lean_dec_ref(v_x_1241_);
    v_r_1243_ = lean_box((v_res_1242_) as usize);
    return v_r_1243_;
}
pub unsafe fn l_Except_isOk___redArg(mut v_a_1244_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_a_1244_) == 0 {
        let mut v___x_1245_: u8 = 0;
        v___x_1245_ = 0;
        return v___x_1245_;
    } else {
        let mut v___x_1246_: u8 = 0;
        v___x_1246_ = 1;
        return v___x_1246_;
    }
}
pub unsafe fn l_Except_isOk___redArg___boxed(mut v_a_1247_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1248_: u8 = 0;
    let mut v_r_1249_: *mut LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Except_isOk___redArg(v_a_1247_);
    lean_dec_ref(v_a_1247_);
    v_r_1249_ = lean_box((v_res_1248_) as usize);
    return v_r_1249_;
}
pub unsafe fn l_Except_isOk(
    mut v_00_u03b5_1250_: *mut LeanObject,
    mut v_00_u03b1_1251_: *mut LeanObject,
    mut v_a_1252_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_a_1252_) == 0 {
        let mut v___x_1253_: u8 = 0;
        v___x_1253_ = 0;
        return v___x_1253_;
    } else {
        let mut v___x_1254_: u8 = 0;
        v___x_1254_ = 1;
        return v___x_1254_;
    }
}
pub unsafe fn l_Except_isOk___boxed(
    mut v_00_u03b5_1255_: *mut LeanObject,
    mut v_00_u03b1_1256_: *mut LeanObject,
    mut v_a_1257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1258_: u8 = 0;
    let mut v_r_1259_: *mut LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Except_isOk(v_00_u03b5_1255_, v_00_u03b1_1256_, v_a_1257_);
    lean_dec_ref(v_a_1257_);
    v_r_1259_ = lean_box((v_res_1258_) as usize);
    return v_r_1259_;
}
pub unsafe fn l_Except_toOption___redArg(mut v_x_1260_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1265_: u8 = 0;
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1260_) == 0 {
                    lean_dec_ref_known(v_x_1260_, 1);
                    v___x_1261_ = lean_box(0);
                    return v___x_1261_;
                } else {
                    v_a_1262_ = lean_ctor_get(v_x_1260_, 0);
                    v_isSharedCheck_1269_ = (!lean_is_exclusive(v_x_1260_)) as u8;
                    if v_isSharedCheck_1269_ == 0 {
                        v___x_1264_ = v_x_1260_;
                        v_isShared_1265_ = v_isSharedCheck_1269_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1262_);
                        lean_dec(v_x_1260_);
                        v___x_1264_ = lean_box(0);
                        v_isShared_1265_ = v_isSharedCheck_1269_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1265_ == 0 {
                    v___x_1267_ = v___x_1264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
                    v___x_1267_ = v_reuseFailAlloc_1268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Except_toOption(
    mut v_00_u03b5_1270_: *mut LeanObject,
    mut v_00_u03b1_1271_: *mut LeanObject,
    mut v_x_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1277_: u8 = 0;
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1272_) == 0 {
                    lean_dec_ref_known(v_x_1272_, 1);
                    v___x_1273_ = lean_box(0);
                    return v___x_1273_;
                } else {
                    v_a_1274_ = lean_ctor_get(v_x_1272_, 0);
                    v_isSharedCheck_1281_ = (!lean_is_exclusive(v_x_1272_)) as u8;
                    if v_isSharedCheck_1281_ == 0 {
                        v___x_1276_ = v_x_1272_;
                        v_isShared_1277_ = v_isSharedCheck_1281_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1274_);
                        lean_dec(v_x_1272_);
                        v___x_1276_ = lean_box(0);
                        v_isShared_1277_ = v_isSharedCheck_1281_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1277_ == 0 {
                    v___x_1279_ = v___x_1276_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
                    v___x_1279_ = v_reuseFailAlloc_1280_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Except_tryCatch___redArg(
    mut v_ma_1282_: *mut LeanObject,
    mut v_handle_1283_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_ma_1282_) == 0 {
        let mut v_a_1284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
        v_a_1284_ = lean_ctor_get(v_ma_1282_, 0);
        lean_inc(v_a_1284_);
        lean_dec_ref_known(v_ma_1282_, 1);
        v___x_1285_ = lean_apply_1(v_handle_1283_, v_a_1284_);
        return v___x_1285_;
    } else {
        lean_dec_ref(v_handle_1283_);
        return v_ma_1282_;
    }
}
pub unsafe fn l_Except_tryCatch(
    mut v_00_u03b5_1286_: *mut LeanObject,
    mut v_00_u03b1_1287_: *mut LeanObject,
    mut v_ma_1288_: *mut LeanObject,
    mut v_handle_1289_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_ma_1288_) == 0 {
        let mut v_a_1290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
        v_a_1290_ = lean_ctor_get(v_ma_1288_, 0);
        lean_inc(v_a_1290_);
        lean_dec_ref_known(v_ma_1288_, 1);
        v___x_1291_ = lean_apply_1(v_handle_1289_, v_a_1290_);
        return v___x_1291_;
    } else {
        lean_dec_ref(v_handle_1289_);
        return v_ma_1288_;
    }
}
pub unsafe fn l_Except_orElseLazy___redArg(
    mut v_x_1292_: *mut LeanObject,
    mut v_y_1293_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1292_) == 0 {
        let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
        v___x_1294_ = lean_box(0);
        v___x_1295_ = lean_apply_1(v_y_1293_, v___x_1294_);
        return v___x_1295_;
    } else {
        lean_dec_ref(v_y_1293_);
        lean_inc_ref(v_x_1292_);
        return v_x_1292_;
    }
}
pub unsafe fn l_Except_orElseLazy___redArg___boxed(
    mut v_x_1296_: *mut LeanObject,
    mut v_y_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1298_: *mut LeanObject = core::ptr::null_mut();
    v_res_1298_ = l_Except_orElseLazy___redArg(v_x_1296_, v_y_1297_);
    lean_dec_ref(v_x_1296_);
    return v_res_1298_;
}
pub unsafe fn l_Except_orElseLazy(
    mut v_00_u03b5_1299_: *mut LeanObject,
    mut v_00_u03b1_1300_: *mut LeanObject,
    mut v_x_1301_: *mut LeanObject,
    mut v_y_1302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    v___x_1303_ = l_Except_orElseLazy___redArg(v_x_1301_, v_y_1302_);
    return v___x_1303_;
}
pub unsafe fn l_Except_orElseLazy___boxed(
    mut v_00_u03b5_1304_: *mut LeanObject,
    mut v_00_u03b1_1305_: *mut LeanObject,
    mut v_x_1306_: *mut LeanObject,
    mut v_y_1307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1308_: *mut LeanObject = core::ptr::null_mut();
    v_res_1308_ = l_Except_orElseLazy(v_00_u03b5_1304_, v_00_u03b1_1305_, v_x_1306_, v_y_1307_);
    lean_dec_ref(v_x_1306_);
    return v_res_1308_;
}
pub unsafe fn l_Except_instMonad___lam__0(
    mut v_00_u03b1_1309_: *mut LeanObject,
    mut v_00_u03b2_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
    mut v___y_1312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1316_: u8 = 0;
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1320_: u8 = 0;
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1323_: u8 = 0;
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1327_: u8 = 0;
    let mut v_unused_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___y_1312_) == 0 {
                    lean_dec(v___y_1311_);
                    v_a_1313_ = lean_ctor_get(v___y_1312_, 0);
                    v_isSharedCheck_1320_ = (!lean_is_exclusive(v___y_1312_)) as u8;
                    if v_isSharedCheck_1320_ == 0 {
                        v___x_1315_ = v___y_1312_;
                        v_isShared_1316_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1313_);
                        lean_dec(v___y_1312_);
                        v___x_1315_ = lean_box(0);
                        v_isShared_1316_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_1327_ = (!lean_is_exclusive(v___y_1312_)) as u8;
                    if v_isSharedCheck_1327_ == 0 {
                        v_unused_1328_ = lean_ctor_get(v___y_1312_, 0);
                        lean_dec(v_unused_1328_);
                        v___x_1322_ = v___y_1312_;
                        v_isShared_1323_ = v_isSharedCheck_1327_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___y_1312_);
                        v___x_1322_ = lean_box(0);
                        v_isShared_1323_ = v_isSharedCheck_1327_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1316_ == 0 {
                    v___x_1318_ = v___x_1315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
                    v___x_1318_ = v_reuseFailAlloc_1319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1318_;
            }
            3 => {
                if v_isShared_1323_ == 0 {
                    lean_ctor_set(v___x_1322_, 0, v___y_1311_);
                    v___x_1325_ = v___x_1322_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___y_1311_);
                    v___x_1325_ = v_reuseFailAlloc_1326_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1325_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Except_instMonad___lam__1(
    mut v_00_u03b1_1329_: *mut LeanObject,
    mut v_00_u03b2_1330_: *mut LeanObject,
    mut v_f_1331_: *mut LeanObject,
    mut v_x_1332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1336_: u8 = 0;
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1340_: u8 = 0;
    let mut v_a_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1351_: u8 = 0;
    let mut v_a_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1355_: u8 = 0;
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_f_1331_) == 0 {
                    lean_dec_ref(v_x_1332_);
                    v_a_1333_ = lean_ctor_get(v_f_1331_, 0);
                    v_isSharedCheck_1340_ = (!lean_is_exclusive(v_f_1331_)) as u8;
                    if v_isSharedCheck_1340_ == 0 {
                        v___x_1335_ = v_f_1331_;
                        v_isShared_1336_ = v_isSharedCheck_1340_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1333_);
                        lean_dec(v_f_1331_);
                        v___x_1335_ = lean_box(0);
                        v_isShared_1336_ = v_isSharedCheck_1340_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1341_ = lean_ctor_get(v_f_1331_, 0);
                    lean_inc(v_a_1341_);
                    lean_dec_ref_known(v_f_1331_, 1);
                    v___x_1342_ = lean_box(0);
                    v___x_1343_ = lean_apply_1(v_x_1332_, v___x_1342_);
                    if lean_obj_tag(v___x_1343_) == 0 {
                        lean_dec(v_a_1341_);
                        v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
                        v_isSharedCheck_1351_ = (!lean_is_exclusive(v___x_1343_)) as u8;
                        if v_isSharedCheck_1351_ == 0 {
                            v___x_1346_ = v___x_1343_;
                            v_isShared_1347_ = v_isSharedCheck_1351_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1344_);
                            lean_dec(v___x_1343_);
                            v___x_1346_ = lean_box(0);
                            v_isShared_1347_ = v_isSharedCheck_1351_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1352_ = lean_ctor_get(v___x_1343_, 0);
                        v_isSharedCheck_1360_ = (!lean_is_exclusive(v___x_1343_)) as u8;
                        if v_isSharedCheck_1360_ == 0 {
                            v___x_1354_ = v___x_1343_;
                            v_isShared_1355_ = v_isSharedCheck_1360_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1352_);
                            lean_dec(v___x_1343_);
                            v___x_1354_ = lean_box(0);
                            v_isShared_1355_ = v_isSharedCheck_1360_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1336_ == 0 {
                    v___x_1338_ = v___x_1335_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
                    v___x_1338_ = v_reuseFailAlloc_1339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1338_;
            }
            3 => {
                if v_isShared_1347_ == 0 {
                    v___x_1349_ = v___x_1346_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
                    v___x_1349_ = v_reuseFailAlloc_1350_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1349_;
            }
            5 => {
                v___x_1356_ = lean_apply_1(v_a_1341_, v_a_1352_);
                if v_isShared_1355_ == 0 {
                    lean_ctor_set(v___x_1354_, 0, v___x_1356_);
                    v___x_1358_ = v___x_1354_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
                    v___x_1358_ = v_reuseFailAlloc_1359_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Except_instMonad___lam__2(
    mut v_00_u03b1_1361_: *mut LeanObject,
    mut v_00_u03b2_1362_: *mut LeanObject,
    mut v_x_1363_: *mut LeanObject,
    mut v_y_1364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1363_) == 0 {
                    lean_dec_ref(v_y_1364_);
                    lean_inc_ref(v_x_1363_);
                    return v_x_1363_;
                } else {
                    v___x_1365_ = lean_box(0);
                    v___x_1366_ = lean_apply_1(v_y_1364_, v___x_1365_);
                    if lean_obj_tag(v___x_1366_) == 0 {
                        v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
                        v_isSharedCheck_1374_ = (!lean_is_exclusive(v___x_1366_)) as u8;
                        if v_isSharedCheck_1374_ == 0 {
                            v___x_1369_ = v___x_1366_;
                            v_isShared_1370_ = v_isSharedCheck_1374_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1367_);
                            lean_dec(v___x_1366_);
                            v___x_1369_ = lean_box(0);
                            v_isShared_1370_ = v_isSharedCheck_1374_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_1366_, 1);
                        lean_inc_ref(v_x_1363_);
                        return v_x_1363_;
                    }
                }
            }
            1 => {
                if v_isShared_1370_ == 0 {
                    v___x_1372_ = v___x_1369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
                    v___x_1372_ = v_reuseFailAlloc_1373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Except_instMonad___lam__2___boxed(
    mut v_00_u03b1_1375_: *mut LeanObject,
    mut v_00_u03b2_1376_: *mut LeanObject,
    mut v_x_1377_: *mut LeanObject,
    mut v_y_1378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1379_: *mut LeanObject = core::ptr::null_mut();
    v_res_1379_ =
        l_Except_instMonad___lam__2(v_00_u03b1_1375_, v_00_u03b2_1376_, v_x_1377_, v_y_1378_);
    lean_dec_ref(v_x_1377_);
    return v_res_1379_;
}
pub unsafe fn l_Except_instMonad___lam__3(
    mut v_00_u03b1_1380_: *mut LeanObject,
    mut v_00_u03b2_1381_: *mut LeanObject,
    mut v_x_1382_: *mut LeanObject,
    mut v_y_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1387_: u8 = 0;
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1391_: u8 = 0;
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1382_) == 0 {
                    lean_dec_ref(v_y_1383_);
                    v_a_1384_ = lean_ctor_get(v_x_1382_, 0);
                    v_isSharedCheck_1391_ = (!lean_is_exclusive(v_x_1382_)) as u8;
                    if v_isSharedCheck_1391_ == 0 {
                        v___x_1386_ = v_x_1382_;
                        v_isShared_1387_ = v_isSharedCheck_1391_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1384_);
                        lean_dec(v_x_1382_);
                        v___x_1386_ = lean_box(0);
                        v_isShared_1387_ = v_isSharedCheck_1391_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_1382_, 1);
                    v___x_1392_ = lean_box(0);
                    v___x_1393_ = lean_apply_1(v_y_1383_, v___x_1392_);
                    return v___x_1393_;
                }
            }
            1 => {
                if v_isShared_1387_ == 0 {
                    v___x_1389_ = v___x_1386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
                    v___x_1389_ = v_reuseFailAlloc_1390_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Except_instMonad(mut v_00_u03b5_1413_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    v___x_1414_ = l_Except_instMonad___closed__9;
    return v___x_1414_;
}
pub unsafe fn l_ExceptT_mk___redArg(mut v_x_1415_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_x_1415_);
    return v_x_1415_;
}
pub unsafe fn l_ExceptT_mk___redArg___boxed(mut v_x_1416_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1417_: *mut LeanObject = core::ptr::null_mut();
    v_res_1417_ = l_ExceptT_mk___redArg(v_x_1416_);
    lean_dec(v_x_1416_);
    return v_res_1417_;
}
pub unsafe fn l_ExceptT_mk(
    mut v_00_u03b5_1418_: *mut LeanObject,
    mut v_m_1419_: *mut LeanObject,
    mut v_00_u03b1_1420_: *mut LeanObject,
    mut v_x_1421_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1421_);
    return v_x_1421_;
}
pub unsafe fn l_ExceptT_mk___boxed(
    mut v_00_u03b5_1422_: *mut LeanObject,
    mut v_m_1423_: *mut LeanObject,
    mut v_00_u03b1_1424_: *mut LeanObject,
    mut v_x_1425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1426_: *mut LeanObject = core::ptr::null_mut();
    v_res_1426_ = l_ExceptT_mk(v_00_u03b5_1422_, v_m_1423_, v_00_u03b1_1424_, v_x_1425_);
    lean_dec(v_x_1425_);
    return v_res_1426_;
}
pub unsafe fn l_ExceptT_run___redArg(mut v_x_1427_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_x_1427_);
    return v_x_1427_;
}
pub unsafe fn l_ExceptT_run___redArg___boxed(mut v_x_1428_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1429_: *mut LeanObject = core::ptr::null_mut();
    v_res_1429_ = l_ExceptT_run___redArg(v_x_1428_);
    lean_dec(v_x_1428_);
    return v_res_1429_;
}
pub unsafe fn l_ExceptT_run(
    mut v_00_u03b5_1430_: *mut LeanObject,
    mut v_m_1431_: *mut LeanObject,
    mut v_00_u03b1_1432_: *mut LeanObject,
    mut v_x_1433_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1433_);
    return v_x_1433_;
}
pub unsafe fn l_ExceptT_run___boxed(
    mut v_00_u03b5_1434_: *mut LeanObject,
    mut v_m_1435_: *mut LeanObject,
    mut v_00_u03b1_1436_: *mut LeanObject,
    mut v_x_1437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1438_: *mut LeanObject = core::ptr::null_mut();
    v_res_1438_ = l_ExceptT_run(v_00_u03b5_1434_, v_m_1435_, v_00_u03b1_1436_, v_x_1437_);
    lean_dec(v_x_1437_);
    return v_res_1438_;
}
pub unsafe fn l_ExceptT_runK___redArg___lam__0(
    mut v_error_1439_: *mut LeanObject,
    mut v_ok_1440_: *mut LeanObject,
    mut v_x_1441_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1441_) == 0 {
        let mut v_a_1442_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_ok_1440_);
        v_a_1442_ = lean_ctor_get(v_x_1441_, 0);
        lean_inc(v_a_1442_);
        lean_dec_ref_known(v_x_1441_, 1);
        v___x_1443_ = lean_apply_1(v_error_1439_, v_a_1442_);
        return v___x_1443_;
    } else {
        let mut v_a_1444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_error_1439_);
        v_a_1444_ = lean_ctor_get(v_x_1441_, 0);
        lean_inc(v_a_1444_);
        lean_dec_ref_known(v_x_1441_, 1);
        v___x_1445_ = lean_apply_1(v_ok_1440_, v_a_1444_);
        return v___x_1445_;
    }
}
pub unsafe fn l_ExceptT_runK___redArg(
    mut v_inst_1446_: *mut LeanObject,
    mut v_x_1447_: *mut LeanObject,
    mut v_ok_1448_: *mut LeanObject,
    mut v_error_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1450_ = lean_ctor_get(v_inst_1446_, 1);
    lean_inc(v_toBind_1450_);
    lean_dec_ref(v_inst_1446_);
    v___f_1451_ = lean_alloc_closure(
        l_ExceptT_runK___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1451_, 0, v_error_1449_);
    lean_closure_set(v___f_1451_, 1, v_ok_1448_);
    v___x_1452_ = lean_apply_4(
        v_toBind_1450_,
        lean_box(0),
        lean_box(0),
        v_x_1447_,
        v___f_1451_,
    );
    return v___x_1452_;
}
pub unsafe fn l_ExceptT_runK(
    mut v_m_1453_: *mut LeanObject,
    mut v_00_u03b5_1454_: *mut LeanObject,
    mut v_00_u03b1_1455_: *mut LeanObject,
    mut v_00_u03b2_1456_: *mut LeanObject,
    mut v_inst_1457_: *mut LeanObject,
    mut v_x_1458_: *mut LeanObject,
    mut v_ok_1459_: *mut LeanObject,
    mut v_error_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1461_ = lean_ctor_get(v_inst_1457_, 1);
    lean_inc(v_toBind_1461_);
    lean_dec_ref(v_inst_1457_);
    v___f_1462_ = lean_alloc_closure(
        l_ExceptT_runK___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1462_, 0, v_error_1460_);
    lean_closure_set(v___f_1462_, 1, v_ok_1459_);
    v___x_1463_ = lean_apply_4(
        v_toBind_1461_,
        lean_box(0),
        lean_box(0),
        v_x_1458_,
        v___f_1462_,
    );
    return v___x_1463_;
}
pub unsafe fn l_ExceptT_runCatch___redArg___lam__0(
    mut v_toPure_1464_: *mut LeanObject,
    mut v_x_1465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    v_a_1466_ = lean_ctor_get(v_x_1465_, 0);
    lean_inc(v_a_1466_);
    lean_dec_ref(v_x_1465_);
    v___x_1467_ = lean_apply_2(v_toPure_1464_, lean_box(0), v_a_1466_);
    return v___x_1467_;
}
pub unsafe fn l_ExceptT_runCatch___redArg(
    mut v_inst_1468_: *mut LeanObject,
    mut v_x_1469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1470_ = lean_ctor_get(v_inst_1468_, 0);
    lean_inc_ref(v_toApplicative_1470_);
    v_toBind_1471_ = lean_ctor_get(v_inst_1468_, 1);
    lean_inc(v_toBind_1471_);
    lean_dec_ref(v_inst_1468_);
    v_toPure_1472_ = lean_ctor_get(v_toApplicative_1470_, 1);
    lean_inc(v_toPure_1472_);
    lean_dec_ref(v_toApplicative_1470_);
    v___f_1473_ = lean_alloc_closure(
        l_ExceptT_runCatch___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1473_, 0, v_toPure_1472_);
    v___x_1474_ = lean_apply_4(
        v_toBind_1471_,
        lean_box(0),
        lean_box(0),
        v_x_1469_,
        v___f_1473_,
    );
    return v___x_1474_;
}
pub unsafe fn l_ExceptT_runCatch(
    mut v_m_1475_: *mut LeanObject,
    mut v_00_u03b1_1476_: *mut LeanObject,
    mut v_inst_1477_: *mut LeanObject,
    mut v_x_1478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1479_ = lean_ctor_get(v_inst_1477_, 0);
    lean_inc_ref(v_toApplicative_1479_);
    v_toBind_1480_ = lean_ctor_get(v_inst_1477_, 1);
    lean_inc(v_toBind_1480_);
    lean_dec_ref(v_inst_1477_);
    v_toPure_1481_ = lean_ctor_get(v_toApplicative_1479_, 1);
    lean_inc(v_toPure_1481_);
    lean_dec_ref(v_toApplicative_1479_);
    v___f_1482_ = lean_alloc_closure(
        l_ExceptT_runCatch___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1482_, 0, v_toPure_1481_);
    v___x_1483_ = lean_apply_4(
        v_toBind_1480_,
        lean_box(0),
        lean_box(0),
        v_x_1478_,
        v___f_1482_,
    );
    return v___x_1483_;
}
pub unsafe fn l_ExceptT_pure___redArg(
    mut v_inst_1484_: *mut LeanObject,
    mut v_a_1485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1486_ = lean_ctor_get(v_inst_1484_, 0);
    lean_inc_ref(v_toApplicative_1486_);
    lean_dec_ref(v_inst_1484_);
    v_toPure_1487_ = lean_ctor_get(v_toApplicative_1486_, 1);
    lean_inc(v_toPure_1487_);
    lean_dec_ref(v_toApplicative_1486_);
    v___x_1488_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1488_, 0, v_a_1485_);
    v___x_1489_ = lean_apply_2(v_toPure_1487_, lean_box(0), v___x_1488_);
    return v___x_1489_;
}
pub unsafe fn l_ExceptT_pure(
    mut v_00_u03b5_1490_: *mut LeanObject,
    mut v_m_1491_: *mut LeanObject,
    mut v_inst_1492_: *mut LeanObject,
    mut v_00_u03b1_1493_: *mut LeanObject,
    mut v_a_1494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1495_ = lean_ctor_get(v_inst_1492_, 0);
    lean_inc_ref(v_toApplicative_1495_);
    lean_dec_ref(v_inst_1492_);
    v_toPure_1496_ = lean_ctor_get(v_toApplicative_1495_, 1);
    lean_inc(v_toPure_1496_);
    lean_dec_ref(v_toApplicative_1495_);
    v___x_1497_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1497_, 0, v_a_1494_);
    v___x_1498_ = lean_apply_2(v_toPure_1496_, lean_box(0), v___x_1497_);
    return v___x_1498_;
}
pub unsafe fn l_ExceptT_bindCont___redArg(
    mut v_inst_1499_: *mut LeanObject,
    mut v_f_1500_: *mut LeanObject,
    mut v_x_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1507_: u8 = 0;
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_a_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1502_ = lean_ctor_get(v_inst_1499_, 0);
                lean_inc_ref(v_toApplicative_1502_);
                lean_dec_ref(v_inst_1499_);
                if lean_obj_tag(v_x_1501_) == 0 {
                    lean_dec(v_f_1500_);
                    v_toPure_1503_ = lean_ctor_get(v_toApplicative_1502_, 1);
                    lean_inc(v_toPure_1503_);
                    lean_dec_ref(v_toApplicative_1502_);
                    v_a_1504_ = lean_ctor_get(v_x_1501_, 0);
                    v_isSharedCheck_1512_ = (!lean_is_exclusive(v_x_1501_)) as u8;
                    if v_isSharedCheck_1512_ == 0 {
                        v___x_1506_ = v_x_1501_;
                        v_isShared_1507_ = v_isSharedCheck_1512_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1504_);
                        lean_dec(v_x_1501_);
                        v___x_1506_ = lean_box(0);
                        v_isShared_1507_ = v_isSharedCheck_1512_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_toApplicative_1502_);
                    v_a_1513_ = lean_ctor_get(v_x_1501_, 0);
                    lean_inc(v_a_1513_);
                    lean_dec_ref_known(v_x_1501_, 1);
                    v___x_1514_ = lean_apply_1(v_f_1500_, v_a_1513_);
                    return v___x_1514_;
                }
            }
            1 => {
                if v_isShared_1507_ == 0 {
                    v___x_1509_ = v___x_1506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1504_);
                    v___x_1509_ = v_reuseFailAlloc_1511_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1510_ = lean_apply_2(v_toPure_1503_, lean_box(0), v___x_1509_);
                return v___x_1510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ExceptT_bindCont(
    mut v_00_u03b5_1515_: *mut LeanObject,
    mut v_m_1516_: *mut LeanObject,
    mut v_inst_1517_: *mut LeanObject,
    mut v_00_u03b1_1518_: *mut LeanObject,
    mut v_00_u03b2_1519_: *mut LeanObject,
    mut v_f_1520_: *mut LeanObject,
    mut v_x_1521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1527_: u8 = 0;
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1532_: u8 = 0;
    let mut v_a_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1522_ = lean_ctor_get(v_inst_1517_, 0);
                lean_inc_ref(v_toApplicative_1522_);
                lean_dec_ref(v_inst_1517_);
                if lean_obj_tag(v_x_1521_) == 0 {
                    lean_dec(v_f_1520_);
                    v_toPure_1523_ = lean_ctor_get(v_toApplicative_1522_, 1);
                    lean_inc(v_toPure_1523_);
                    lean_dec_ref(v_toApplicative_1522_);
                    v_a_1524_ = lean_ctor_get(v_x_1521_, 0);
                    v_isSharedCheck_1532_ = (!lean_is_exclusive(v_x_1521_)) as u8;
                    if v_isSharedCheck_1532_ == 0 {
                        v___x_1526_ = v_x_1521_;
                        v_isShared_1527_ = v_isSharedCheck_1532_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1524_);
                        lean_dec(v_x_1521_);
                        v___x_1526_ = lean_box(0);
                        v_isShared_1527_ = v_isSharedCheck_1532_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_toApplicative_1522_);
                    v_a_1533_ = lean_ctor_get(v_x_1521_, 0);
                    lean_inc(v_a_1533_);
                    lean_dec_ref_known(v_x_1521_, 1);
                    v___x_1534_ = lean_apply_1(v_f_1520_, v_a_1533_);
                    return v___x_1534_;
                }
            }
            1 => {
                if v_isShared_1527_ == 0 {
                    v___x_1529_ = v___x_1526_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1524_);
                    v___x_1529_ = v_reuseFailAlloc_1531_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1530_ = lean_apply_2(v_toPure_1523_, lean_box(0), v___x_1529_);
                return v___x_1530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ExceptT_bind___redArg(
    mut v_inst_1535_: *mut LeanObject,
    mut v_ma_1536_: *mut LeanObject,
    mut v_f_1537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1538_ = lean_ctor_get(v_inst_1535_, 1);
    lean_inc(v_toBind_1538_);
    v___x_1539_ = lean_alloc_closure(l_ExceptT_bindCont as *mut core::ffi::c_void, 7, 6);
    lean_closure_set(v___x_1539_, 0, lean_box(0));
    lean_closure_set(v___x_1539_, 1, lean_box(0));
    lean_closure_set(v___x_1539_, 2, v_inst_1535_);
    lean_closure_set(v___x_1539_, 3, lean_box(0));
    lean_closure_set(v___x_1539_, 4, lean_box(0));
    lean_closure_set(v___x_1539_, 5, v_f_1537_);
    v___x_1540_ = lean_apply_4(
        v_toBind_1538_,
        lean_box(0),
        lean_box(0),
        v_ma_1536_,
        v___x_1539_,
    );
    return v___x_1540_;
}
pub unsafe fn l_ExceptT_bind(
    mut v_00_u03b5_1541_: *mut LeanObject,
    mut v_m_1542_: *mut LeanObject,
    mut v_inst_1543_: *mut LeanObject,
    mut v_00_u03b1_1544_: *mut LeanObject,
    mut v_00_u03b2_1545_: *mut LeanObject,
    mut v_ma_1546_: *mut LeanObject,
    mut v_f_1547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1548_ = lean_ctor_get(v_inst_1543_, 1);
    lean_inc(v_toBind_1548_);
    v___x_1549_ = lean_alloc_closure(l_ExceptT_bindCont as *mut core::ffi::c_void, 7, 6);
    lean_closure_set(v___x_1549_, 0, lean_box(0));
    lean_closure_set(v___x_1549_, 1, lean_box(0));
    lean_closure_set(v___x_1549_, 2, v_inst_1543_);
    lean_closure_set(v___x_1549_, 3, lean_box(0));
    lean_closure_set(v___x_1549_, 4, lean_box(0));
    lean_closure_set(v___x_1549_, 5, v_f_1547_);
    v___x_1550_ = lean_apply_4(
        v_toBind_1548_,
        lean_box(0),
        lean_box(0),
        v_ma_1546_,
        v___x_1549_,
    );
    return v___x_1550_;
}
pub unsafe fn l_ExceptT_map___redArg___lam__0(
    mut v_toPure_1551_: *mut LeanObject,
    mut v_f_1552_: *mut LeanObject,
    mut v_a_1553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1557_: u8 = 0;
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1562_: u8 = 0;
    let mut v_a_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1566_: u8 = 0;
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1553_) == 0 {
                    lean_dec(v_f_1552_);
                    v_a_1554_ = lean_ctor_get(v_a_1553_, 0);
                    v_isSharedCheck_1562_ = (!lean_is_exclusive(v_a_1553_)) as u8;
                    if v_isSharedCheck_1562_ == 0 {
                        v___x_1556_ = v_a_1553_;
                        v_isShared_1557_ = v_isSharedCheck_1562_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1554_);
                        lean_dec(v_a_1553_);
                        v___x_1556_ = lean_box(0);
                        v_isShared_1557_ = v_isSharedCheck_1562_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1563_ = lean_ctor_get(v_a_1553_, 0);
                    v_isSharedCheck_1572_ = (!lean_is_exclusive(v_a_1553_)) as u8;
                    if v_isSharedCheck_1572_ == 0 {
                        v___x_1565_ = v_a_1553_;
                        v_isShared_1566_ = v_isSharedCheck_1572_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1563_);
                        lean_dec(v_a_1553_);
                        v___x_1565_ = lean_box(0);
                        v_isShared_1566_ = v_isSharedCheck_1572_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1557_ == 0 {
                    v___x_1559_ = v___x_1556_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1554_);
                    v___x_1559_ = v_reuseFailAlloc_1561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1560_ = lean_apply_2(v_toPure_1551_, lean_box(0), v___x_1559_);
                return v___x_1560_;
            }
            3 => {
                v___x_1567_ = lean_apply_1(v_f_1552_, v_a_1563_);
                if v_isShared_1566_ == 0 {
                    lean_ctor_set(v___x_1565_, 0, v___x_1567_);
                    v___x_1569_ = v___x_1565_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1567_);
                    v___x_1569_ = v_reuseFailAlloc_1571_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1570_ = lean_apply_2(v_toPure_1551_, lean_box(0), v___x_1569_);
                return v___x_1570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ExceptT_map___redArg(
    mut v_inst_1573_: *mut LeanObject,
    mut v_f_1574_: *mut LeanObject,
    mut v_x_1575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1576_ = lean_ctor_get(v_inst_1573_, 0);
    lean_inc_ref(v_toApplicative_1576_);
    v_toBind_1577_ = lean_ctor_get(v_inst_1573_, 1);
    lean_inc(v_toBind_1577_);
    lean_dec_ref(v_inst_1573_);
    v_toPure_1578_ = lean_ctor_get(v_toApplicative_1576_, 1);
    lean_inc(v_toPure_1578_);
    lean_dec_ref(v_toApplicative_1576_);
    v___f_1579_ = lean_alloc_closure(
        l_ExceptT_map___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1579_, 0, v_toPure_1578_);
    lean_closure_set(v___f_1579_, 1, v_f_1574_);
    v___x_1580_ = lean_apply_4(
        v_toBind_1577_,
        lean_box(0),
        lean_box(0),
        v_x_1575_,
        v___f_1579_,
    );
    return v___x_1580_;
}
pub unsafe fn l_ExceptT_map(
    mut v_00_u03b5_1581_: *mut LeanObject,
    mut v_m_1582_: *mut LeanObject,
    mut v_inst_1583_: *mut LeanObject,
    mut v_00_u03b1_1584_: *mut LeanObject,
    mut v_00_u03b2_1585_: *mut LeanObject,
    mut v_f_1586_: *mut LeanObject,
    mut v_x_1587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1588_ = lean_ctor_get(v_inst_1583_, 0);
    lean_inc_ref(v_toApplicative_1588_);
    v_toBind_1589_ = lean_ctor_get(v_inst_1583_, 1);
    lean_inc(v_toBind_1589_);
    lean_dec_ref(v_inst_1583_);
    v_toPure_1590_ = lean_ctor_get(v_toApplicative_1588_, 1);
    lean_inc(v_toPure_1590_);
    lean_dec_ref(v_toApplicative_1588_);
    v___f_1591_ = lean_alloc_closure(
        l_ExceptT_map___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1591_, 0, v_toPure_1590_);
    lean_closure_set(v___f_1591_, 1, v_f_1586_);
    v___x_1592_ = lean_apply_4(
        v_toBind_1589_,
        lean_box(0),
        lean_box(0),
        v_x_1587_,
        v___f_1591_,
    );
    return v___x_1592_;
}
pub unsafe fn l_ExceptT_lift___redArg___lam__0(mut v_a_1593_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    v___x_1594_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1594_, 0, v_a_1593_);
    return v___x_1594_;
}
pub unsafe fn l_ExceptT_lift___redArg(
    mut v_inst_1596_: *mut LeanObject,
    mut v_t_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1598_ = lean_ctor_get(v_inst_1596_, 0);
    lean_inc_ref(v_toApplicative_1598_);
    lean_dec_ref(v_inst_1596_);
    v_toFunctor_1599_ = lean_ctor_get(v_toApplicative_1598_, 0);
    lean_inc_ref(v_toFunctor_1599_);
    lean_dec_ref(v_toApplicative_1598_);
    v_map_1600_ = lean_ctor_get(v_toFunctor_1599_, 0);
    lean_inc(v_map_1600_);
    lean_dec_ref(v_toFunctor_1599_);
    v___f_1601_ = l_ExceptT_lift___redArg___closed__0;
    v___x_1602_ = lean_apply_4(
        v_map_1600_,
        lean_box(0),
        lean_box(0),
        v___f_1601_,
        v_t_1597_,
    );
    return v___x_1602_;
}
pub unsafe fn l_ExceptT_lift(
    mut v_00_u03b5_1603_: *mut LeanObject,
    mut v_m_1604_: *mut LeanObject,
    mut v_inst_1605_: *mut LeanObject,
    mut v_00_u03b1_1606_: *mut LeanObject,
    mut v_t_1607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1608_ = lean_ctor_get(v_inst_1605_, 0);
    lean_inc_ref(v_toApplicative_1608_);
    lean_dec_ref(v_inst_1605_);
    v_toFunctor_1609_ = lean_ctor_get(v_toApplicative_1608_, 0);
    lean_inc_ref(v_toFunctor_1609_);
    lean_dec_ref(v_toApplicative_1608_);
    v_map_1610_ = lean_ctor_get(v_toFunctor_1609_, 0);
    lean_inc(v_map_1610_);
    lean_dec_ref(v_toFunctor_1609_);
    v___f_1611_ = l_ExceptT_lift___redArg___closed__0;
    v___x_1612_ = lean_apply_4(
        v_map_1610_,
        lean_box(0),
        lean_box(0),
        v___f_1611_,
        v_t_1607_,
    );
    return v___x_1612_;
}
pub unsafe fn l_ExceptT_instMonadLiftExcept___redArg___lam__0(
    mut v_toPure_1613_: *mut LeanObject,
    mut v_00_u03b1_1614_: *mut LeanObject,
    mut v_e_1615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    v___x_1616_ = lean_apply_2(v_toPure_1613_, lean_box(0), v_e_1615_);
    return v___x_1616_;
}
pub unsafe fn l_ExceptT_instMonadLiftExcept___redArg(
    mut v_inst_1617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1620_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1618_ = lean_ctor_get(v_inst_1617_, 0);
    lean_inc_ref(v_toApplicative_1618_);
    lean_dec_ref(v_inst_1617_);
    v_toPure_1619_ = lean_ctor_get(v_toApplicative_1618_, 1);
    lean_inc(v_toPure_1619_);
    lean_dec_ref(v_toApplicative_1618_);
    v___f_1620_ = lean_alloc_closure(
        l_ExceptT_instMonadLiftExcept___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1620_, 0, v_toPure_1619_);
    return v___f_1620_;
}
pub unsafe fn l_ExceptT_instMonadLiftExcept(
    mut v_00_u03b5_1621_: *mut LeanObject,
    mut v_m_1622_: *mut LeanObject,
    mut v_inst_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1626_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1624_ = lean_ctor_get(v_inst_1623_, 0);
    lean_inc_ref(v_toApplicative_1624_);
    lean_dec_ref(v_inst_1623_);
    v_toPure_1625_ = lean_ctor_get(v_toApplicative_1624_, 1);
    lean_inc(v_toPure_1625_);
    lean_dec_ref(v_toApplicative_1624_);
    v___f_1626_ = lean_alloc_closure(
        l_ExceptT_instMonadLiftExcept___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1626_, 0, v_toPure_1625_);
    return v___f_1626_;
}
pub unsafe fn l_ExceptT_instMonadLift___redArg(
    mut v_inst_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    v___x_1628_ = lean_alloc_closure(l_ExceptT_lift as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_1628_, 0, lean_box(0));
    lean_closure_set(v___x_1628_, 1, lean_box(0));
    lean_closure_set(v___x_1628_, 2, v_inst_1627_);
    return v___x_1628_;
}
pub unsafe fn l_ExceptT_instMonadLift(
    mut v_00_u03b5_1629_: *mut LeanObject,
    mut v_m_1630_: *mut LeanObject,
    mut v_inst_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    v___x_1632_ = lean_alloc_closure(l_ExceptT_lift as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_1632_, 0, lean_box(0));
    lean_closure_set(v___x_1632_, 1, lean_box(0));
    lean_closure_set(v___x_1632_, 2, v_inst_1631_);
    return v___x_1632_;
}
pub unsafe fn l_ExceptT_tryCatch___redArg___lam__0(
    mut v_handle_1633_: *mut LeanObject,
    mut v_toPure_1634_: *mut LeanObject,
    mut v_res_1635_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_res_1635_) == 0 {
        let mut v_a_1636_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1634_);
        v_a_1636_ = lean_ctor_get(v_res_1635_, 0);
        lean_inc(v_a_1636_);
        lean_dec_ref_known(v_res_1635_, 1);
        v___x_1637_ = lean_apply_1(v_handle_1633_, v_a_1636_);
        return v___x_1637_;
    } else {
        let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_handle_1633_);
        v___x_1638_ = lean_apply_2(v_toPure_1634_, lean_box(0), v_res_1635_);
        return v___x_1638_;
    }
}
pub unsafe fn l_ExceptT_tryCatch___redArg(
    mut v_inst_1639_: *mut LeanObject,
    mut v_ma_1640_: *mut LeanObject,
    mut v_handle_1641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1642_ = lean_ctor_get(v_inst_1639_, 0);
    lean_inc_ref(v_toApplicative_1642_);
    v_toBind_1643_ = lean_ctor_get(v_inst_1639_, 1);
    lean_inc(v_toBind_1643_);
    lean_dec_ref(v_inst_1639_);
    v_toPure_1644_ = lean_ctor_get(v_toApplicative_1642_, 1);
    lean_inc(v_toPure_1644_);
    lean_dec_ref(v_toApplicative_1642_);
    v___f_1645_ = lean_alloc_closure(
        l_ExceptT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1645_, 0, v_handle_1641_);
    lean_closure_set(v___f_1645_, 1, v_toPure_1644_);
    v___x_1646_ = lean_apply_4(
        v_toBind_1643_,
        lean_box(0),
        lean_box(0),
        v_ma_1640_,
        v___f_1645_,
    );
    return v___x_1646_;
}
pub unsafe fn l_ExceptT_tryCatch(
    mut v_00_u03b5_1647_: *mut LeanObject,
    mut v_m_1648_: *mut LeanObject,
    mut v_inst_1649_: *mut LeanObject,
    mut v_00_u03b1_1650_: *mut LeanObject,
    mut v_ma_1651_: *mut LeanObject,
    mut v_handle_1652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1653_ = lean_ctor_get(v_inst_1649_, 0);
    lean_inc_ref(v_toApplicative_1653_);
    v_toBind_1654_ = lean_ctor_get(v_inst_1649_, 1);
    lean_inc(v_toBind_1654_);
    lean_dec_ref(v_inst_1649_);
    v_toPure_1655_ = lean_ctor_get(v_toApplicative_1653_, 1);
    lean_inc(v_toPure_1655_);
    lean_dec_ref(v_toApplicative_1653_);
    v___f_1656_ = lean_alloc_closure(
        l_ExceptT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1656_, 0, v_handle_1652_);
    lean_closure_set(v___f_1656_, 1, v_toPure_1655_);
    v___x_1657_ = lean_apply_4(
        v_toBind_1654_,
        lean_box(0),
        lean_box(0),
        v_ma_1651_,
        v___f_1656_,
    );
    return v___x_1657_;
}
pub unsafe fn l_ExceptT_instMonadFunctor___lam__0(
    mut v_00_u03b1_1658_: *mut LeanObject,
    mut v_f_1659_: *mut LeanObject,
    mut v_x_1660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    v___x_1661_ = lean_apply_2(v_f_1659_, lean_box(0), v_x_1660_);
    return v___x_1661_;
}
pub unsafe fn l_ExceptT_instMonadFunctor(
    mut v_00_u03b5_1663_: *mut LeanObject,
    mut v_m_1664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1665_: *mut LeanObject = core::ptr::null_mut();
    v___f_1665_ = l_ExceptT_instMonadFunctor___closed__0;
    return v___f_1665_;
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__0(
    mut v_toPure_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
    mut v_a_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1685_: u8 = 0;
    let mut v_unused_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1668_) == 0 {
                    lean_dec(v___y_1667_);
                    v_a_1669_ = lean_ctor_get(v_a_1668_, 0);
                    v_isSharedCheck_1677_ = (!lean_is_exclusive(v_a_1668_)) as u8;
                    if v_isSharedCheck_1677_ == 0 {
                        v___x_1671_ = v_a_1668_;
                        v_isShared_1672_ = v_isSharedCheck_1677_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1669_);
                        lean_dec(v_a_1668_);
                        v___x_1671_ = lean_box(0);
                        v_isShared_1672_ = v_isSharedCheck_1677_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_1685_ = (!lean_is_exclusive(v_a_1668_)) as u8;
                    if v_isSharedCheck_1685_ == 0 {
                        v_unused_1686_ = lean_ctor_get(v_a_1668_, 0);
                        lean_dec(v_unused_1686_);
                        v___x_1679_ = v_a_1668_;
                        v_isShared_1680_ = v_isSharedCheck_1685_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_a_1668_);
                        v___x_1679_ = lean_box(0);
                        v_isShared_1680_ = v_isSharedCheck_1685_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1672_ == 0 {
                    v___x_1674_ = v___x_1671_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1669_);
                    v___x_1674_ = v_reuseFailAlloc_1676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1675_ = lean_apply_2(v_toPure_1666_, lean_box(0), v___x_1674_);
                return v___x_1675_;
            }
            3 => {
                if v_isShared_1680_ == 0 {
                    lean_ctor_set(v___x_1679_, 0, v___y_1667_);
                    v___x_1682_ = v___x_1679_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___y_1667_);
                    v___x_1682_ = v_reuseFailAlloc_1684_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1683_ = lean_apply_2(v_toPure_1666_, lean_box(0), v___x_1682_);
                return v___x_1683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__1(
    mut v_inst_1687_: *mut LeanObject,
    mut v_00_u03b1_1688_: *mut LeanObject,
    mut v_00_u03b2_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1692_ = lean_ctor_get(v_inst_1687_, 0);
    lean_inc_ref(v_toApplicative_1692_);
    v_toBind_1693_ = lean_ctor_get(v_inst_1687_, 1);
    lean_inc(v_toBind_1693_);
    lean_dec_ref(v_inst_1687_);
    v_toPure_1694_ = lean_ctor_get(v_toApplicative_1692_, 1);
    lean_inc(v_toPure_1694_);
    lean_dec_ref(v_toApplicative_1692_);
    v___f_1695_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1695_, 0, v_toPure_1694_);
    lean_closure_set(v___f_1695_, 1, v___y_1690_);
    v___x_1696_ = lean_apply_4(
        v_toBind_1693_,
        lean_box(0),
        lean_box(0),
        v___y_1691_,
        v___f_1695_,
    );
    return v___x_1696_;
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__2(
    mut v_toPure_1697_: *mut LeanObject,
    mut v_y_1698_: *mut LeanObject,
    mut v_a_1699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut v_a_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1699_) == 0 {
                    lean_dec(v_y_1698_);
                    v_a_1700_ = lean_ctor_get(v_a_1699_, 0);
                    v_isSharedCheck_1708_ = (!lean_is_exclusive(v_a_1699_)) as u8;
                    if v_isSharedCheck_1708_ == 0 {
                        v___x_1702_ = v_a_1699_;
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1700_);
                        lean_dec(v_a_1699_);
                        v___x_1702_ = lean_box(0);
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1709_ = lean_ctor_get(v_a_1699_, 0);
                    v_isSharedCheck_1718_ = (!lean_is_exclusive(v_a_1699_)) as u8;
                    if v_isSharedCheck_1718_ == 0 {
                        v___x_1711_ = v_a_1699_;
                        v_isShared_1712_ = v_isSharedCheck_1718_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1709_);
                        lean_dec(v_a_1699_);
                        v___x_1711_ = lean_box(0);
                        v_isShared_1712_ = v_isSharedCheck_1718_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1703_ == 0 {
                    v___x_1705_ = v___x_1702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1700_);
                    v___x_1705_ = v_reuseFailAlloc_1707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1706_ = lean_apply_2(v_toPure_1697_, lean_box(0), v___x_1705_);
                return v___x_1706_;
            }
            3 => {
                v___x_1713_ = lean_apply_1(v_y_1698_, v_a_1709_);
                if v_isShared_1712_ == 0 {
                    lean_ctor_set(v___x_1711_, 0, v___x_1713_);
                    v___x_1715_ = v___x_1711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1713_);
                    v___x_1715_ = v_reuseFailAlloc_1717_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1716_ = lean_apply_2(v_toPure_1697_, lean_box(0), v___x_1715_);
                return v___x_1716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__3(
    mut v_toApplicative_1719_: *mut LeanObject,
    mut v_x_1720_: *mut LeanObject,
    mut v_toBind_1721_: *mut LeanObject,
    mut v_y_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_1723_ = lean_ctor_get(v_toApplicative_1719_, 1);
    lean_inc(v_toPure_1723_);
    lean_dec_ref(v_toApplicative_1719_);
    v___x_1724_ = lean_box(0);
    v___x_1725_ = lean_apply_1(v_x_1720_, v___x_1724_);
    v___f_1726_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1726_, 0, v_toPure_1723_);
    lean_closure_set(v___f_1726_, 1, v_y_1722_);
    v___x_1727_ = lean_apply_4(
        v_toBind_1721_,
        lean_box(0),
        lean_box(0),
        v___x_1725_,
        v___f_1726_,
    );
    return v___x_1727_;
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__4(
    mut v_inst_1728_: *mut LeanObject,
    mut v_00_u03b1_1729_: *mut LeanObject,
    mut v_00_u03b2_1730_: *mut LeanObject,
    mut v_f_1731_: *mut LeanObject,
    mut v_x_1732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1733_ = lean_ctor_get(v_inst_1728_, 0);
    v_toBind_1734_ = lean_ctor_get(v_inst_1728_, 1);
    lean_inc_n(v_toBind_1734_, 2);
    lean_inc_ref(v_toApplicative_1733_);
    v___f_1735_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1735_, 0, v_toApplicative_1733_);
    lean_closure_set(v___f_1735_, 1, v_x_1732_);
    lean_closure_set(v___f_1735_, 2, v_toBind_1734_);
    v___x_1736_ = lean_alloc_closure(l_ExceptT_bindCont as *mut core::ffi::c_void, 7, 6);
    lean_closure_set(v___x_1736_, 0, lean_box(0));
    lean_closure_set(v___x_1736_, 1, lean_box(0));
    lean_closure_set(v___x_1736_, 2, v_inst_1728_);
    lean_closure_set(v___x_1736_, 3, lean_box(0));
    lean_closure_set(v___x_1736_, 4, lean_box(0));
    lean_closure_set(v___x_1736_, 5, v___f_1735_);
    v___x_1737_ = lean_apply_4(
        v_toBind_1734_,
        lean_box(0),
        lean_box(0),
        v_f_1731_,
        v___x_1736_,
    );
    return v___x_1737_;
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__5(
    mut v_toApplicative_1738_: *mut LeanObject,
    mut v_a_1739_: *mut LeanObject,
    mut v_x_1740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_1741_ = lean_ctor_get(v_toApplicative_1738_, 1);
    lean_inc(v_toPure_1741_);
    lean_dec_ref(v_toApplicative_1738_);
    v___x_1742_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1742_, 0, v_a_1739_);
    v___x_1743_ = lean_apply_2(v_toPure_1741_, lean_box(0), v___x_1742_);
    return v___x_1743_;
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__5___boxed(
    mut v_toApplicative_1744_: *mut LeanObject,
    mut v_a_1745_: *mut LeanObject,
    mut v_x_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1747_: *mut LeanObject = core::ptr::null_mut();
    v_res_1747_ =
        l_ExceptT_instMonad___redArg___lam__5(v_toApplicative_1744_, v_a_1745_, v_x_1746_);
    lean_dec(v_x_1746_);
    return v_res_1747_;
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__6(
    mut v_toApplicative_1748_: *mut LeanObject,
    mut v_y_1749_: *mut LeanObject,
    mut v_inst_1750_: *mut LeanObject,
    mut v_toBind_1751_: *mut LeanObject,
    mut v_a_1752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    v___f_1753_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__5___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1753_, 0, v_toApplicative_1748_);
    lean_closure_set(v___f_1753_, 1, v_a_1752_);
    v___x_1754_ = lean_box(0);
    v___x_1755_ = lean_apply_1(v_y_1749_, v___x_1754_);
    v___x_1756_ = lean_alloc_closure(l_ExceptT_bindCont as *mut core::ffi::c_void, 7, 6);
    lean_closure_set(v___x_1756_, 0, lean_box(0));
    lean_closure_set(v___x_1756_, 1, lean_box(0));
    lean_closure_set(v___x_1756_, 2, v_inst_1750_);
    lean_closure_set(v___x_1756_, 3, lean_box(0));
    lean_closure_set(v___x_1756_, 4, lean_box(0));
    lean_closure_set(v___x_1756_, 5, v___f_1753_);
    v___x_1757_ = lean_apply_4(
        v_toBind_1751_,
        lean_box(0),
        lean_box(0),
        v___x_1755_,
        v___x_1756_,
    );
    return v___x_1757_;
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__7(
    mut v_inst_1758_: *mut LeanObject,
    mut v_00_u03b1_1759_: *mut LeanObject,
    mut v_00_u03b2_1760_: *mut LeanObject,
    mut v_x_1761_: *mut LeanObject,
    mut v_y_1762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1763_ = lean_ctor_get(v_inst_1758_, 0);
    v_toBind_1764_ = lean_ctor_get(v_inst_1758_, 1);
    lean_inc_n(v_toBind_1764_, 2);
    lean_inc_ref(v_inst_1758_);
    lean_inc_ref(v_toApplicative_1763_);
    v___f_1765_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1765_, 0, v_toApplicative_1763_);
    lean_closure_set(v___f_1765_, 1, v_y_1762_);
    lean_closure_set(v___f_1765_, 2, v_inst_1758_);
    lean_closure_set(v___f_1765_, 3, v_toBind_1764_);
    v___x_1766_ = lean_alloc_closure(l_ExceptT_bindCont as *mut core::ffi::c_void, 7, 6);
    lean_closure_set(v___x_1766_, 0, lean_box(0));
    lean_closure_set(v___x_1766_, 1, lean_box(0));
    lean_closure_set(v___x_1766_, 2, v_inst_1758_);
    lean_closure_set(v___x_1766_, 3, lean_box(0));
    lean_closure_set(v___x_1766_, 4, lean_box(0));
    lean_closure_set(v___x_1766_, 5, v___f_1765_);
    v___x_1767_ = lean_apply_4(
        v_toBind_1764_,
        lean_box(0),
        lean_box(0),
        v_x_1761_,
        v___x_1766_,
    );
    return v___x_1767_;
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__8(
    mut v_y_1768_: *mut LeanObject,
    mut v_x_1769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    v___x_1770_ = lean_box(0);
    v___x_1771_ = lean_apply_1(v_y_1768_, v___x_1770_);
    return v___x_1771_;
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__8___boxed(
    mut v_y_1772_: *mut LeanObject,
    mut v_x_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1774_: *mut LeanObject = core::ptr::null_mut();
    v_res_1774_ = l_ExceptT_instMonad___redArg___lam__8(v_y_1772_, v_x_1773_);
    lean_dec(v_x_1773_);
    return v_res_1774_;
}
pub unsafe fn l_ExceptT_instMonad___redArg___lam__9(
    mut v_inst_1775_: *mut LeanObject,
    mut v_00_u03b1_1776_: *mut LeanObject,
    mut v_00_u03b2_1777_: *mut LeanObject,
    mut v_x_1778_: *mut LeanObject,
    mut v_y_1779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1780_ = lean_ctor_get(v_inst_1775_, 1);
    lean_inc(v_toBind_1780_);
    v___f_1781_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__8___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1781_, 0, v_y_1779_);
    v___x_1782_ = lean_alloc_closure(l_ExceptT_bindCont as *mut core::ffi::c_void, 7, 6);
    lean_closure_set(v___x_1782_, 0, lean_box(0));
    lean_closure_set(v___x_1782_, 1, lean_box(0));
    lean_closure_set(v___x_1782_, 2, v_inst_1775_);
    lean_closure_set(v___x_1782_, 3, lean_box(0));
    lean_closure_set(v___x_1782_, 4, lean_box(0));
    lean_closure_set(v___x_1782_, 5, v___f_1781_);
    v___x_1783_ = lean_apply_4(
        v_toBind_1780_,
        lean_box(0),
        lean_box(0),
        v_x_1778_,
        v___x_1782_,
    );
    return v___x_1783_;
}
pub unsafe fn l_ExceptT_instMonad___redArg(mut v_inst_1784_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1784_, 6);
    v___f_1785_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1785_, 0, v_inst_1784_);
    v___f_1786_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1786_, 0, v_inst_1784_);
    v___f_1787_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1787_, 0, v_inst_1784_);
    v___f_1788_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1788_, 0, v_inst_1784_);
    v___x_1789_ = lean_alloc_closure(l_ExceptT_map as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___x_1789_, 0, lean_box(0));
    lean_closure_set(v___x_1789_, 1, lean_box(0));
    lean_closure_set(v___x_1789_, 2, v_inst_1784_);
    v___x_1790_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1790_, 0, v___x_1789_);
    lean_ctor_set(v___x_1790_, 1, v___f_1785_);
    v___x_1791_ = lean_alloc_closure(l_ExceptT_pure as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_1791_, 0, lean_box(0));
    lean_closure_set(v___x_1791_, 1, lean_box(0));
    lean_closure_set(v___x_1791_, 2, v_inst_1784_);
    v___x_1792_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1792_, 0, v___x_1790_);
    lean_ctor_set(v___x_1792_, 1, v___x_1791_);
    lean_ctor_set(v___x_1792_, 2, v___f_1786_);
    lean_ctor_set(v___x_1792_, 3, v___f_1787_);
    lean_ctor_set(v___x_1792_, 4, v___f_1788_);
    v___x_1793_ = lean_alloc_closure(l_ExceptT_bind as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___x_1793_, 0, lean_box(0));
    lean_closure_set(v___x_1793_, 1, lean_box(0));
    lean_closure_set(v___x_1793_, 2, v_inst_1784_);
    v___x_1794_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1794_, 0, v___x_1792_);
    lean_ctor_set(v___x_1794_, 1, v___x_1793_);
    return v___x_1794_;
}
pub unsafe fn l_ExceptT_instMonad(
    mut v_00_u03b5_1795_: *mut LeanObject,
    mut v_m_1796_: *mut LeanObject,
    mut v_inst_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1797_, 6);
    v___f_1798_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1798_, 0, v_inst_1797_);
    v___f_1799_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1799_, 0, v_inst_1797_);
    v___f_1800_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1800_, 0, v_inst_1797_);
    v___f_1801_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1801_, 0, v_inst_1797_);
    v___x_1802_ = lean_alloc_closure(l_ExceptT_map as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___x_1802_, 0, lean_box(0));
    lean_closure_set(v___x_1802_, 1, lean_box(0));
    lean_closure_set(v___x_1802_, 2, v_inst_1797_);
    v___x_1803_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1803_, 0, v___x_1802_);
    lean_ctor_set(v___x_1803_, 1, v___f_1798_);
    v___x_1804_ = lean_alloc_closure(l_ExceptT_pure as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_1804_, 0, lean_box(0));
    lean_closure_set(v___x_1804_, 1, lean_box(0));
    lean_closure_set(v___x_1804_, 2, v_inst_1797_);
    v___x_1805_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1805_, 0, v___x_1803_);
    lean_ctor_set(v___x_1805_, 1, v___x_1804_);
    lean_ctor_set(v___x_1805_, 2, v___f_1799_);
    lean_ctor_set(v___x_1805_, 3, v___f_1800_);
    lean_ctor_set(v___x_1805_, 4, v___f_1801_);
    v___x_1806_ = lean_alloc_closure(l_ExceptT_bind as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___x_1806_, 0, lean_box(0));
    lean_closure_set(v___x_1806_, 1, lean_box(0));
    lean_closure_set(v___x_1806_, 2, v_inst_1797_);
    v___x_1807_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1807_, 0, v___x_1805_);
    lean_ctor_set(v___x_1807_, 1, v___x_1806_);
    return v___x_1807_;
}
pub unsafe fn l_ExceptT_adapt___redArg(
    mut v_inst_1808_: *mut LeanObject,
    mut v_f_1809_: *mut LeanObject,
    mut v_x_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1811_ = lean_ctor_get(v_inst_1808_, 0);
    lean_inc_ref(v_toApplicative_1811_);
    lean_dec_ref(v_inst_1808_);
    v_toFunctor_1812_ = lean_ctor_get(v_toApplicative_1811_, 0);
    lean_inc_ref(v_toFunctor_1812_);
    lean_dec_ref(v_toApplicative_1811_);
    v_map_1813_ = lean_ctor_get(v_toFunctor_1812_, 0);
    lean_inc(v_map_1813_);
    lean_dec_ref(v_toFunctor_1812_);
    v___x_1814_ = lean_alloc_closure(l_Except_mapError as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_1814_, 0, lean_box(0));
    lean_closure_set(v___x_1814_, 1, lean_box(0));
    lean_closure_set(v___x_1814_, 2, lean_box(0));
    lean_closure_set(v___x_1814_, 3, v_f_1809_);
    v___x_1815_ = lean_apply_4(
        v_map_1813_,
        lean_box(0),
        lean_box(0),
        v___x_1814_,
        v_x_1810_,
    );
    return v___x_1815_;
}
pub unsafe fn l_ExceptT_adapt(
    mut v_00_u03b5_1816_: *mut LeanObject,
    mut v_m_1817_: *mut LeanObject,
    mut v_inst_1818_: *mut LeanObject,
    mut v_00_u03b5_x27_1819_: *mut LeanObject,
    mut v_00_u03b1_1820_: *mut LeanObject,
    mut v_f_1821_: *mut LeanObject,
    mut v_x_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1823_ = lean_ctor_get(v_inst_1818_, 0);
    lean_inc_ref(v_toApplicative_1823_);
    lean_dec_ref(v_inst_1818_);
    v_toFunctor_1824_ = lean_ctor_get(v_toApplicative_1823_, 0);
    lean_inc_ref(v_toFunctor_1824_);
    lean_dec_ref(v_toApplicative_1823_);
    v_map_1825_ = lean_ctor_get(v_toFunctor_1824_, 0);
    lean_inc(v_map_1825_);
    lean_dec_ref(v_toFunctor_1824_);
    v___x_1826_ = lean_alloc_closure(l_Except_mapError as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_1826_, 0, lean_box(0));
    lean_closure_set(v___x_1826_, 1, lean_box(0));
    lean_closure_set(v___x_1826_, 2, lean_box(0));
    lean_closure_set(v___x_1826_, 3, v_f_1821_);
    v___x_1827_ = lean_apply_4(
        v_map_1825_,
        lean_box(0),
        lean_box(0),
        v___x_1826_,
        v_x_1822_,
    );
    return v___x_1827_;
}
pub unsafe fn l_instMonadExceptOfExceptT___redArg___lam__0(
    mut v_inst_1828_: *mut LeanObject,
    mut v_00_u03b1_1829_: *mut LeanObject,
    mut v_e_1830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    v_throw_1831_ = lean_ctor_get(v_inst_1828_, 0);
    lean_inc(v_throw_1831_);
    lean_dec_ref(v_inst_1828_);
    v___x_1832_ = lean_apply_2(v_throw_1831_, lean_box(0), v_e_1830_);
    return v___x_1832_;
}
pub unsafe fn l_instMonadExceptOfExceptT___redArg___lam__1(
    mut v_inst_1833_: *mut LeanObject,
    mut v_00_u03b1_1834_: *mut LeanObject,
    mut v_x_1835_: *mut LeanObject,
    mut v_handle_1836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_1837_ = lean_ctor_get(v_inst_1833_, 1);
    lean_inc(v_tryCatch_1837_);
    lean_dec_ref(v_inst_1833_);
    v___x_1838_ = lean_apply_3(v_tryCatch_1837_, lean_box(0), v_x_1835_, v_handle_1836_);
    return v___x_1838_;
}
pub unsafe fn l_instMonadExceptOfExceptT___redArg(
    mut v_inst_1839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1839_);
    v___f_1840_ = lean_alloc_closure(
        l_instMonadExceptOfExceptT___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1840_, 0, v_inst_1839_);
    v___f_1841_ = lean_alloc_closure(
        l_instMonadExceptOfExceptT___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1841_, 0, v_inst_1839_);
    v___x_1842_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1842_, 0, v___f_1840_);
    lean_ctor_set(v___x_1842_, 1, v___f_1841_);
    return v___x_1842_;
}
pub unsafe fn l_instMonadExceptOfExceptT(
    mut v_m_1843_: *mut LeanObject,
    mut v_00_u03b5_u2081_1844_: *mut LeanObject,
    mut v_00_u03b5_u2082_1845_: *mut LeanObject,
    mut v_inst_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1846_);
    v___f_1847_ = lean_alloc_closure(
        l_instMonadExceptOfExceptT___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1847_, 0, v_inst_1846_);
    v___f_1848_ = lean_alloc_closure(
        l_instMonadExceptOfExceptT___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1848_, 0, v_inst_1846_);
    v___x_1849_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1849_, 0, v___f_1847_);
    lean_ctor_set(v___x_1849_, 1, v___f_1848_);
    return v___x_1849_;
}
pub unsafe fn l_instMonadExceptOfExceptTOfMonad___redArg___lam__0(
    mut v_toPure_1850_: *mut LeanObject,
    mut v_00_u03b1_1851_: *mut LeanObject,
    mut v_e_1852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    v___x_1853_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1853_, 0, v_e_1852_);
    v___x_1854_ = lean_apply_2(v_toPure_1850_, lean_box(0), v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn l_instMonadExceptOfExceptTOfMonad___redArg(
    mut v_inst_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1856_ = lean_ctor_get(v_inst_1855_, 0);
    v_toPure_1857_ = lean_ctor_get(v_toApplicative_1856_, 1);
    lean_inc(v_toPure_1857_);
    v___f_1858_ = lean_alloc_closure(
        l_instMonadExceptOfExceptTOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1858_, 0, v_toPure_1857_);
    v___x_1859_ = lean_alloc_closure(l_ExceptT_tryCatch as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1859_, 0, lean_box(0));
    lean_closure_set(v___x_1859_, 1, lean_box(0));
    lean_closure_set(v___x_1859_, 2, v_inst_1855_);
    v___x_1860_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1860_, 0, v___f_1858_);
    lean_ctor_set(v___x_1860_, 1, v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn l_instMonadExceptOfExceptTOfMonad(
    mut v_m_1861_: *mut LeanObject,
    mut v_00_u03b5_1862_: *mut LeanObject,
    mut v_inst_1863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1864_ = lean_ctor_get(v_inst_1863_, 0);
    v_toPure_1865_ = lean_ctor_get(v_toApplicative_1864_, 1);
    lean_inc(v_toPure_1865_);
    v___f_1866_ = lean_alloc_closure(
        l_instMonadExceptOfExceptTOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1866_, 0, v_toPure_1865_);
    v___x_1867_ = lean_alloc_closure(l_ExceptT_tryCatch as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1867_, 0, lean_box(0));
    lean_closure_set(v___x_1867_, 1, lean_box(0));
    lean_closure_set(v___x_1867_, 2, v_inst_1863_);
    v___x_1868_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1868_, 0, v___f_1866_);
    lean_ctor_set(v___x_1868_, 1, v___x_1867_);
    return v___x_1868_;
}
pub unsafe fn l_instInhabitedExceptTOfMonad___redArg(
    mut v_inst_1869_: *mut LeanObject,
    mut v_inst_1870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1871_ = lean_ctor_get(v_inst_1869_, 0);
    lean_inc_ref(v_toApplicative_1871_);
    lean_dec_ref(v_inst_1869_);
    v_toPure_1872_ = lean_ctor_get(v_toApplicative_1871_, 1);
    lean_inc(v_toPure_1872_);
    lean_dec_ref(v_toApplicative_1871_);
    v___x_1873_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1873_, 0, v_inst_1870_);
    v___x_1874_ = lean_apply_2(v_toPure_1872_, lean_box(0), v___x_1873_);
    return v___x_1874_;
}
pub unsafe fn l_instInhabitedExceptTOfMonad(
    mut v_m_1875_: *mut LeanObject,
    mut v_00_u03b5_1876_: *mut LeanObject,
    mut v_00_u03b1_1877_: *mut LeanObject,
    mut v_inst_1878_: *mut LeanObject,
    mut v_inst_1879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    v___x_1880_ = l_instInhabitedExceptTOfMonad___redArg(v_inst_1878_, v_inst_1879_);
    return v___x_1880_;
}
pub unsafe fn l_instMonadExceptOfExcept___lam__0(
    mut v_00_u03b1_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    v___x_1883_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1883_, 0, v___y_1882_);
    return v___x_1883_;
}
pub unsafe fn l_instMonadExceptOfExcept(mut v_00_u03b5_1889_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    v___x_1890_ = l_instMonadExceptOfExcept___closed__2;
    return v___x_1890_;
}
pub unsafe fn l_MonadExcept_orelse_x27___redArg___lam__0(
    mut v_useFirstEx_1891_: u8,
    mut v_throw_1892_: *mut LeanObject,
    mut v_e_u2081_1893_: *mut LeanObject,
    mut v_e_u2082_1894_: *mut LeanObject,
) -> *mut LeanObject {
    if v_useFirstEx_1891_ == 0 {
        let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_e_u2081_1893_);
        v___x_1895_ = lean_apply_2(v_throw_1892_, lean_box(0), v_e_u2082_1894_);
        return v___x_1895_;
    } else {
        let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_e_u2082_1894_);
        v___x_1896_ = lean_apply_2(v_throw_1892_, lean_box(0), v_e_u2081_1893_);
        return v___x_1896_;
    }
}
pub unsafe fn l_MonadExcept_orelse_x27___redArg___lam__0___boxed(
    mut v_useFirstEx_1897_: *mut LeanObject,
    mut v_throw_1898_: *mut LeanObject,
    mut v_e_u2081_1899_: *mut LeanObject,
    mut v_e_u2082_1900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useFirstEx_boxed_1901_: u8 = 0;
    let mut v_res_1902_: *mut LeanObject = core::ptr::null_mut();
    v_useFirstEx_boxed_1901_ = (lean_unbox(v_useFirstEx_1897_) as u8);
    v_res_1902_ = l_MonadExcept_orelse_x27___redArg___lam__0(
        v_useFirstEx_boxed_1901_,
        v_throw_1898_,
        v_e_u2081_1899_,
        v_e_u2082_1900_,
    );
    return v_res_1902_;
}
pub unsafe fn l_MonadExcept_orelse_x27___redArg___lam__1(
    mut v_useFirstEx_1903_: u8,
    mut v_throw_1904_: *mut LeanObject,
    mut v_tryCatch_1905_: *mut LeanObject,
    mut v_t_u2082_1906_: *mut LeanObject,
    mut v_e_u2081_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    v___x_1908_ = lean_box((v_useFirstEx_1903_) as usize);
    v___f_1909_ = lean_alloc_closure(
        l_MonadExcept_orelse_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1909_, 0, v___x_1908_);
    lean_closure_set(v___f_1909_, 1, v_throw_1904_);
    lean_closure_set(v___f_1909_, 2, v_e_u2081_1907_);
    v___x_1910_ = lean_apply_3(v_tryCatch_1905_, lean_box(0), v_t_u2082_1906_, v___f_1909_);
    return v___x_1910_;
}
pub unsafe fn l_MonadExcept_orelse_x27___redArg___lam__1___boxed(
    mut v_useFirstEx_1911_: *mut LeanObject,
    mut v_throw_1912_: *mut LeanObject,
    mut v_tryCatch_1913_: *mut LeanObject,
    mut v_t_u2082_1914_: *mut LeanObject,
    mut v_e_u2081_1915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useFirstEx_boxed_1916_: u8 = 0;
    let mut v_res_1917_: *mut LeanObject = core::ptr::null_mut();
    v_useFirstEx_boxed_1916_ = (lean_unbox(v_useFirstEx_1911_) as u8);
    v_res_1917_ = l_MonadExcept_orelse_x27___redArg___lam__1(
        v_useFirstEx_boxed_1916_,
        v_throw_1912_,
        v_tryCatch_1913_,
        v_t_u2082_1914_,
        v_e_u2081_1915_,
    );
    return v_res_1917_;
}
pub unsafe fn l_MonadExcept_orelse_x27___redArg(
    mut v_inst_1918_: *mut LeanObject,
    mut v_t_u2081_1919_: *mut LeanObject,
    mut v_t_u2082_1920_: *mut LeanObject,
    mut v_useFirstEx_1921_: u8,
) -> *mut LeanObject {
    let mut v_throw_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    v_throw_1922_ = lean_ctor_get(v_inst_1918_, 0);
    lean_inc(v_throw_1922_);
    v_tryCatch_1923_ = lean_ctor_get(v_inst_1918_, 1);
    lean_inc_n(v_tryCatch_1923_, 2);
    lean_dec_ref(v_inst_1918_);
    v___x_1924_ = lean_box((v_useFirstEx_1921_) as usize);
    v___f_1925_ = lean_alloc_closure(
        l_MonadExcept_orelse_x27___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1925_, 0, v___x_1924_);
    lean_closure_set(v___f_1925_, 1, v_throw_1922_);
    lean_closure_set(v___f_1925_, 2, v_tryCatch_1923_);
    lean_closure_set(v___f_1925_, 3, v_t_u2082_1920_);
    v___x_1926_ = lean_apply_3(v_tryCatch_1923_, lean_box(0), v_t_u2081_1919_, v___f_1925_);
    return v___x_1926_;
}
pub unsafe fn l_MonadExcept_orelse_x27___redArg___boxed(
    mut v_inst_1927_: *mut LeanObject,
    mut v_t_u2081_1928_: *mut LeanObject,
    mut v_t_u2082_1929_: *mut LeanObject,
    mut v_useFirstEx_1930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useFirstEx_boxed_1931_: u8 = 0;
    let mut v_res_1932_: *mut LeanObject = core::ptr::null_mut();
    v_useFirstEx_boxed_1931_ = (lean_unbox(v_useFirstEx_1930_) as u8);
    v_res_1932_ = l_MonadExcept_orelse_x27___redArg(
        v_inst_1927_,
        v_t_u2081_1928_,
        v_t_u2082_1929_,
        v_useFirstEx_boxed_1931_,
    );
    return v_res_1932_;
}
pub unsafe fn l_MonadExcept_orelse_x27(
    mut v_00_u03b5_1933_: *mut LeanObject,
    mut v_m_1934_: *mut LeanObject,
    mut v_inst_1935_: *mut LeanObject,
    mut v_00_u03b1_1936_: *mut LeanObject,
    mut v_t_u2081_1937_: *mut LeanObject,
    mut v_t_u2082_1938_: *mut LeanObject,
    mut v_useFirstEx_1939_: u8,
) -> *mut LeanObject {
    let mut v_throw_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    v_throw_1940_ = lean_ctor_get(v_inst_1935_, 0);
    lean_inc(v_throw_1940_);
    v_tryCatch_1941_ = lean_ctor_get(v_inst_1935_, 1);
    lean_inc_n(v_tryCatch_1941_, 2);
    lean_dec_ref(v_inst_1935_);
    v___x_1942_ = lean_box((v_useFirstEx_1939_) as usize);
    v___f_1943_ = lean_alloc_closure(
        l_MonadExcept_orelse_x27___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1943_, 0, v___x_1942_);
    lean_closure_set(v___f_1943_, 1, v_throw_1940_);
    lean_closure_set(v___f_1943_, 2, v_tryCatch_1941_);
    lean_closure_set(v___f_1943_, 3, v_t_u2082_1938_);
    v___x_1944_ = lean_apply_3(v_tryCatch_1941_, lean_box(0), v_t_u2081_1937_, v___f_1943_);
    return v___x_1944_;
}
pub unsafe fn l_MonadExcept_orelse_x27___boxed(
    mut v_00_u03b5_1945_: *mut LeanObject,
    mut v_m_1946_: *mut LeanObject,
    mut v_inst_1947_: *mut LeanObject,
    mut v_00_u03b1_1948_: *mut LeanObject,
    mut v_t_u2081_1949_: *mut LeanObject,
    mut v_t_u2082_1950_: *mut LeanObject,
    mut v_useFirstEx_1951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useFirstEx_boxed_1952_: u8 = 0;
    let mut v_res_1953_: *mut LeanObject = core::ptr::null_mut();
    v_useFirstEx_boxed_1952_ = (lean_unbox(v_useFirstEx_1951_) as u8);
    v_res_1953_ = l_MonadExcept_orelse_x27(
        v_00_u03b5_1945_,
        v_m_1946_,
        v_inst_1947_,
        v_00_u03b1_1948_,
        v_t_u2081_1949_,
        v_t_u2082_1950_,
        v_useFirstEx_boxed_1952_,
    );
    return v_res_1953_;
}
pub unsafe fn l_observing___redArg___lam__0(
    mut v_toPure_1954_: *mut LeanObject,
    mut v_a_1955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    v___x_1956_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1956_, 0, v_a_1955_);
    v___x_1957_ = lean_apply_2(v_toPure_1954_, lean_box(0), v___x_1956_);
    return v___x_1957_;
}
pub unsafe fn l_observing___redArg___lam__1(
    mut v_toPure_1958_: *mut LeanObject,
    mut v_ex_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    v___x_1960_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1960_, 0, v_ex_1959_);
    v___x_1961_ = lean_apply_2(v_toPure_1958_, lean_box(0), v___x_1960_);
    return v___x_1961_;
}
pub unsafe fn l_observing___redArg(
    mut v_inst_1962_: *mut LeanObject,
    mut v_inst_1963_: *mut LeanObject,
    mut v_x_1964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1965_ = lean_ctor_get(v_inst_1962_, 0);
    lean_inc_ref(v_toApplicative_1965_);
    v_tryCatch_1966_ = lean_ctor_get(v_inst_1963_, 1);
    lean_inc(v_tryCatch_1966_);
    lean_dec_ref(v_inst_1963_);
    v_toBind_1967_ = lean_ctor_get(v_inst_1962_, 1);
    lean_inc(v_toBind_1967_);
    lean_dec_ref(v_inst_1962_);
    v_toPure_1968_ = lean_ctor_get(v_toApplicative_1965_, 1);
    lean_inc_n(v_toPure_1968_, 2);
    lean_dec_ref(v_toApplicative_1965_);
    v___f_1969_ = lean_alloc_closure(
        l_observing___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1969_, 0, v_toPure_1968_);
    v___f_1970_ = lean_alloc_closure(
        l_observing___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1970_, 0, v_toPure_1968_);
    v___x_1971_ = lean_apply_4(
        v_toBind_1967_,
        lean_box(0),
        lean_box(0),
        v_x_1964_,
        v___f_1969_,
    );
    v___x_1972_ = lean_apply_3(v_tryCatch_1966_, lean_box(0), v___x_1971_, v___f_1970_);
    return v___x_1972_;
}
pub unsafe fn l_observing(
    mut v_00_u03b5_1973_: *mut LeanObject,
    mut v_00_u03b1_1974_: *mut LeanObject,
    mut v_m_1975_: *mut LeanObject,
    mut v_inst_1976_: *mut LeanObject,
    mut v_inst_1977_: *mut LeanObject,
    mut v_x_1978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1979_ = lean_ctor_get(v_inst_1976_, 0);
    lean_inc_ref(v_toApplicative_1979_);
    v_tryCatch_1980_ = lean_ctor_get(v_inst_1977_, 1);
    lean_inc(v_tryCatch_1980_);
    lean_dec_ref(v_inst_1977_);
    v_toBind_1981_ = lean_ctor_get(v_inst_1976_, 1);
    lean_inc(v_toBind_1981_);
    lean_dec_ref(v_inst_1976_);
    v_toPure_1982_ = lean_ctor_get(v_toApplicative_1979_, 1);
    lean_inc_n(v_toPure_1982_, 2);
    lean_dec_ref(v_toApplicative_1979_);
    v___f_1983_ = lean_alloc_closure(
        l_observing___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1983_, 0, v_toPure_1982_);
    v___f_1984_ = lean_alloc_closure(
        l_observing___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1984_, 0, v_toPure_1982_);
    v___x_1985_ = lean_apply_4(
        v_toBind_1981_,
        lean_box(0),
        lean_box(0),
        v_x_1978_,
        v___f_1983_,
    );
    v___x_1986_ = lean_apply_3(v_tryCatch_1980_, lean_box(0), v___x_1985_, v___f_1984_);
    return v___x_1986_;
}
pub unsafe fn l_liftExcept___redArg(
    mut v_inst_1987_: *mut LeanObject,
    mut v_inst_1988_: *mut LeanObject,
    mut v_x_1989_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1989_) == 0 {
        let mut v_a_1990_: *mut LeanObject = core::ptr::null_mut();
        let mut v_throw_1991_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_1988_);
        v_a_1990_ = lean_ctor_get(v_x_1989_, 0);
        lean_inc(v_a_1990_);
        lean_dec_ref_known(v_x_1989_, 1);
        v_throw_1991_ = lean_ctor_get(v_inst_1987_, 0);
        lean_inc(v_throw_1991_);
        lean_dec_ref(v_inst_1987_);
        v___x_1992_ = lean_apply_2(v_throw_1991_, lean_box(0), v_a_1990_);
        return v___x_1992_;
    } else {
        let mut v_a_1993_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1987_);
        v_a_1993_ = lean_ctor_get(v_x_1989_, 0);
        lean_inc(v_a_1993_);
        lean_dec_ref_known(v_x_1989_, 1);
        v___x_1994_ = lean_apply_2(v_inst_1988_, lean_box(0), v_a_1993_);
        return v___x_1994_;
    }
}
pub unsafe fn l_liftExcept(
    mut v_00_u03b5_1995_: *mut LeanObject,
    mut v_m_1996_: *mut LeanObject,
    mut v_00_u03b1_1997_: *mut LeanObject,
    mut v_inst_1998_: *mut LeanObject,
    mut v_inst_1999_: *mut LeanObject,
    mut v_x_2000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    v___x_2001_ = l_liftExcept___redArg(v_inst_1998_, v_inst_1999_, v_x_2000_);
    return v___x_2001_;
}
pub unsafe fn l_instMonadControlExceptTOfMonad___redArg___lam__0(
    mut v_00_u03b2_2002_: *mut LeanObject,
    mut v_x_2003_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_2003_);
    return v_x_2003_;
}
pub unsafe fn l_instMonadControlExceptTOfMonad___redArg___lam__0___boxed(
    mut v_00_u03b2_2004_: *mut LeanObject,
    mut v_x_2005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2006_: *mut LeanObject = core::ptr::null_mut();
    v_res_2006_ = l_instMonadControlExceptTOfMonad___redArg___lam__0(v_00_u03b2_2004_, v_x_2005_);
    lean_dec(v_x_2005_);
    return v_res_2006_;
}
pub unsafe fn l_instMonadControlExceptTOfMonad___redArg___lam__2(
    mut v_inst_2007_: *mut LeanObject,
    mut v___f_2008_: *mut LeanObject,
    mut v___f_2009_: *mut LeanObject,
    mut v_00_u03b1_2010_: *mut LeanObject,
    mut v_f_2011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2012_ = lean_ctor_get(v_inst_2007_, 0);
    lean_inc_ref(v_toApplicative_2012_);
    lean_dec_ref(v_inst_2007_);
    v_toFunctor_2013_ = lean_ctor_get(v_toApplicative_2012_, 0);
    lean_inc_ref(v_toFunctor_2013_);
    lean_dec_ref(v_toApplicative_2012_);
    v_map_2014_ = lean_ctor_get(v_toFunctor_2013_, 0);
    lean_inc(v_map_2014_);
    lean_dec_ref(v_toFunctor_2013_);
    v___x_2015_ = lean_apply_1(v_f_2011_, v___f_2008_);
    v___x_2016_ = lean_apply_4(
        v_map_2014_,
        lean_box(0),
        lean_box(0),
        v___f_2009_,
        v___x_2015_,
    );
    return v___x_2016_;
}
pub unsafe fn l_instMonadControlExceptTOfMonad___redArg___lam__1(
    mut v_00_u03b1_2017_: *mut LeanObject,
    mut v_x_2018_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_2018_);
    return v_x_2018_;
}
pub unsafe fn l_instMonadControlExceptTOfMonad___redArg___lam__1___boxed(
    mut v_00_u03b1_2019_: *mut LeanObject,
    mut v_x_2020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2021_: *mut LeanObject = core::ptr::null_mut();
    v_res_2021_ = l_instMonadControlExceptTOfMonad___redArg___lam__1(v_00_u03b1_2019_, v_x_2020_);
    lean_dec(v_x_2020_);
    return v_res_2021_;
}
pub unsafe fn l_instMonadControlExceptTOfMonad___redArg(
    mut v_inst_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    v___f_2025_ = l_instMonadControlExceptTOfMonad___redArg___closed__0;
    v___f_2026_ = l_ExceptT_lift___redArg___closed__0;
    v___f_2027_ = lean_alloc_closure(
        l_instMonadControlExceptTOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2027_, 0, v_inst_2024_);
    lean_closure_set(v___f_2027_, 1, v___f_2025_);
    lean_closure_set(v___f_2027_, 2, v___f_2026_);
    v___f_2028_ = l_instMonadControlExceptTOfMonad___redArg___closed__1;
    v___x_2029_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2029_, 0, v___f_2027_);
    lean_ctor_set(v___x_2029_, 1, v___f_2028_);
    return v___x_2029_;
}
pub unsafe fn l_instMonadControlExceptTOfMonad(
    mut v_00_u03b5_2030_: *mut LeanObject,
    mut v_m_2031_: *mut LeanObject,
    mut v_inst_2032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    v___x_2033_ = l_instMonadControlExceptTOfMonad___redArg(v_inst_2032_);
    return v___x_2033_;
}
pub unsafe fn l_tryFinally___redArg___lam__0(
    mut v_finalizer_2034_: *mut LeanObject,
    mut v_x_2035_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_finalizer_2034_);
    return v_finalizer_2034_;
}
pub unsafe fn l_tryFinally___redArg___lam__0___boxed(
    mut v_finalizer_2036_: *mut LeanObject,
    mut v_x_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2038_: *mut LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_tryFinally___redArg___lam__0(v_finalizer_2036_, v_x_2037_);
    lean_dec(v_x_2037_);
    lean_dec(v_finalizer_2036_);
    return v_res_2038_;
}
pub unsafe fn l_tryFinally___redArg___lam__1(mut v_x_2039_: *mut LeanObject) -> *mut LeanObject {
    let mut v_fst_2040_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2040_ = lean_ctor_get(v_x_2039_, 0);
    lean_inc(v_fst_2040_);
    return v_fst_2040_;
}
pub unsafe fn l_tryFinally___redArg___lam__1___boxed(
    mut v_x_2041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2042_: *mut LeanObject = core::ptr::null_mut();
    v_res_2042_ = l_tryFinally___redArg___lam__1(v_x_2041_);
    lean_dec_ref(v_x_2041_);
    return v_res_2042_;
}
pub unsafe fn l_tryFinally___redArg(
    mut v_inst_2044_: *mut LeanObject,
    mut v_inst_2045_: *mut LeanObject,
    mut v_x_2046_: *mut LeanObject,
    mut v_finalizer_2047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    v_map_2048_ = lean_ctor_get(v_inst_2045_, 0);
    lean_inc(v_map_2048_);
    lean_dec_ref(v_inst_2045_);
    v___f_2049_ = lean_alloc_closure(
        l_tryFinally___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2049_, 0, v_finalizer_2047_);
    v___f_2050_ = l_tryFinally___redArg___closed__0;
    v_y_2051_ = lean_apply_4(
        v_inst_2044_,
        lean_box(0),
        lean_box(0),
        v_x_2046_,
        v___f_2049_,
    );
    v___x_2052_ = lean_apply_4(
        v_map_2048_,
        lean_box(0),
        lean_box(0),
        v___f_2050_,
        v_y_2051_,
    );
    return v___x_2052_;
}
pub unsafe fn l_tryFinally(
    mut v_m_2053_: *mut LeanObject,
    mut v_00_u03b1_2054_: *mut LeanObject,
    mut v_00_u03b2_2055_: *mut LeanObject,
    mut v_inst_2056_: *mut LeanObject,
    mut v_inst_2057_: *mut LeanObject,
    mut v_x_2058_: *mut LeanObject,
    mut v_finalizer_2059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    v_map_2060_ = lean_ctor_get(v_inst_2057_, 0);
    lean_inc(v_map_2060_);
    lean_dec_ref(v_inst_2057_);
    v___f_2061_ = lean_alloc_closure(
        l_tryFinally___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2061_, 0, v_finalizer_2059_);
    v___f_2062_ = l_tryFinally___redArg___closed__0;
    v_y_2063_ = lean_apply_4(
        v_inst_2056_,
        lean_box(0),
        lean_box(0),
        v_x_2058_,
        v___f_2061_,
    );
    v___x_2064_ = lean_apply_4(
        v_map_2060_,
        lean_box(0),
        lean_box(0),
        v___f_2062_,
        v_y_2063_,
    );
    return v___x_2064_;
}
pub unsafe fn l_Id_finally___lam__0(
    mut v_00_u03b1_2065_: *mut LeanObject,
    mut v_00_u03b2_2066_: *mut LeanObject,
    mut v_x_2067_: *mut LeanObject,
    mut v_h_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_x_2067_);
    v___x_2069_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2069_, 0, v_x_2067_);
    v_b_2070_ = lean_apply_1(v_h_2068_, v___x_2069_);
    v___x_2071_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2071_, 0, v_x_2067_);
    lean_ctor_set(v___x_2071_, 1, v_b_2070_);
    return v___x_2071_;
}
pub unsafe fn l_ExceptT_finally___redArg___lam__0(
    mut v_toPure_2074_: *mut LeanObject,
    mut v_r_2075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2091_: u8 = 0;
    let mut v_unused_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2096_: u8 = 0;
    let mut v_a_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2102_: u8 = 0;
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut v_isSharedCheck_2111_: u8 = 0;
    let mut v_unused_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2080_ = lean_ctor_get(v_r_2075_, 0);
                lean_inc(v_fst_2080_);
                if lean_obj_tag(v_fst_2080_) == 0 {
                    v_snd_2081_ = lean_ctor_get(v_r_2075_, 1);
                    lean_inc(v_snd_2081_);
                    lean_dec_ref(v_r_2075_);
                    if lean_obj_tag(v_snd_2081_) == 0 {
                        lean_dec_ref_known(v_fst_2080_, 1);
                        v_a_2082_ = lean_ctor_get(v_snd_2081_, 0);
                        lean_inc(v_a_2082_);
                        lean_dec_ref_known(v_snd_2081_, 1);
                        v_e_2077_ = v_a_2082_;
                        state = 1;
                        continue;
                    } else {
                        v_a_2083_ = lean_ctor_get(v_fst_2080_, 0);
                        lean_inc(v_a_2083_);
                        lean_dec_ref_known(v_fst_2080_, 1);
                        v_isSharedCheck_2091_ = (!lean_is_exclusive(v_snd_2081_)) as u8;
                        if v_isSharedCheck_2091_ == 0 {
                            v_unused_2092_ = lean_ctor_get(v_snd_2081_, 0);
                            lean_dec(v_unused_2092_);
                            v___x_2085_ = v_snd_2081_;
                            v_isShared_2086_ = v_isSharedCheck_2091_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_snd_2081_);
                            v___x_2085_ = lean_box(0);
                            v_isShared_2086_ = v_isSharedCheck_2091_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_snd_2093_ = lean_ctor_get(v_r_2075_, 1);
                    v_isSharedCheck_2111_ = (!lean_is_exclusive(v_r_2075_)) as u8;
                    if v_isSharedCheck_2111_ == 0 {
                        v_unused_2112_ = lean_ctor_get(v_r_2075_, 0);
                        lean_dec(v_unused_2112_);
                        v___x_2095_ = v_r_2075_;
                        v_isShared_2096_ = v_isSharedCheck_2111_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_2093_);
                        lean_dec(v_r_2075_);
                        v___x_2095_ = lean_box(0);
                        v_isShared_2096_ = v_isSharedCheck_2111_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2078_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2078_, 0, v_e_2077_);
                v___x_2079_ = lean_apply_2(v_toPure_2074_, lean_box(0), v___x_2078_);
                return v___x_2079_;
            }
            2 => {
                if v_isShared_2086_ == 0 {
                    lean_ctor_set_tag(v___x_2085_, 0);
                    lean_ctor_set(v___x_2085_, 0, v_a_2083_);
                    v___x_2088_ = v___x_2085_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2083_);
                    v___x_2088_ = v_reuseFailAlloc_2090_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2089_ = lean_apply_2(v_toPure_2074_, lean_box(0), v___x_2088_);
                return v___x_2089_;
            }
            4 => {
                if lean_obj_tag(v_snd_2093_) == 0 {
                    lean_del_object(v___x_2095_);
                    lean_dec_ref_known(v_fst_2080_, 1);
                    v_a_2097_ = lean_ctor_get(v_snd_2093_, 0);
                    lean_inc(v_a_2097_);
                    lean_dec_ref_known(v_snd_2093_, 1);
                    v_e_2077_ = v_a_2097_;
                    state = 1;
                    continue;
                } else {
                    v_a_2098_ = lean_ctor_get(v_fst_2080_, 0);
                    lean_inc(v_a_2098_);
                    lean_dec_ref_known(v_fst_2080_, 1);
                    v_a_2099_ = lean_ctor_get(v_snd_2093_, 0);
                    v_isSharedCheck_2110_ = (!lean_is_exclusive(v_snd_2093_)) as u8;
                    if v_isSharedCheck_2110_ == 0 {
                        v___x_2101_ = v_snd_2093_;
                        v_isShared_2102_ = v_isSharedCheck_2110_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2099_);
                        lean_dec(v_snd_2093_);
                        v___x_2101_ = lean_box(0);
                        v_isShared_2102_ = v_isSharedCheck_2110_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_2096_ == 0 {
                    lean_ctor_set(v___x_2095_, 1, v_a_2099_);
                    lean_ctor_set(v___x_2095_, 0, v_a_2098_);
                    v___x_2104_ = v___x_2095_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2098_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_a_2099_);
                    v___x_2104_ = v_reuseFailAlloc_2109_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2102_ == 0 {
                    lean_ctor_set(v___x_2101_, 0, v___x_2104_);
                    v___x_2106_ = v___x_2101_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2104_);
                    v___x_2106_ = v_reuseFailAlloc_2108_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2107_ = lean_apply_2(v_toPure_2074_, lean_box(0), v___x_2106_);
                return v___x_2107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ExceptT_finally___redArg___lam__1(
    mut v_h_2113_: *mut LeanObject,
    mut v_e_x3f_2114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2121_: u8 = 0;
    let mut v_a_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_x3f_2114_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_2118_ = lean_ctor_get(v_e_x3f_2114_, 0);
                    v_isSharedCheck_2127_ = (!lean_is_exclusive(v_e_x3f_2114_)) as u8;
                    if v_isSharedCheck_2127_ == 0 {
                        v___x_2120_ = v_e_x3f_2114_;
                        v_isShared_2121_ = v_isSharedCheck_2127_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2118_);
                        lean_dec(v_e_x3f_2114_);
                        v___x_2120_ = lean_box(0);
                        v_isShared_2121_ = v_isSharedCheck_2127_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2116_ = lean_box(0);
                v___x_2117_ = lean_apply_1(v_h_2113_, v___x_2116_);
                return v___x_2117_;
            }
            2 => {
                if lean_obj_tag(v_val_2118_) == 0 {
                    lean_dec_ref_known(v_val_2118_, 1);
                    lean_del_object(v___x_2120_);
                    state = 1;
                    continue;
                } else {
                    v_a_2122_ = lean_ctor_get(v_val_2118_, 0);
                    lean_inc(v_a_2122_);
                    lean_dec_ref_known(v_val_2118_, 1);
                    if v_isShared_2121_ == 0 {
                        lean_ctor_set(v___x_2120_, 0, v_a_2122_);
                        v___x_2124_ = v___x_2120_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2122_);
                        v___x_2124_ = v_reuseFailAlloc_2126_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2125_ = lean_apply_1(v_h_2113_, v___x_2124_);
                return v___x_2125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ExceptT_finally___redArg___lam__2(
    mut v_inst_2128_: *mut LeanObject,
    mut v_toBind_2129_: *mut LeanObject,
    mut v___f_2130_: *mut LeanObject,
    mut v_00_u03b1_2131_: *mut LeanObject,
    mut v_00_u03b2_2132_: *mut LeanObject,
    mut v_x_2133_: *mut LeanObject,
    mut v_h_2134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    v___f_2135_ = lean_alloc_closure(
        l_ExceptT_finally___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2135_, 0, v_h_2134_);
    v___x_2136_ = lean_apply_4(
        v_inst_2128_,
        lean_box(0),
        lean_box(0),
        v_x_2133_,
        v___f_2135_,
    );
    v___x_2137_ = lean_apply_4(
        v_toBind_2129_,
        lean_box(0),
        lean_box(0),
        v___x_2136_,
        v___f_2130_,
    );
    return v___x_2137_;
}
pub unsafe fn l_ExceptT_finally___redArg(
    mut v_inst_2138_: *mut LeanObject,
    mut v_inst_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2144_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2140_ = lean_ctor_get(v_inst_2139_, 0);
    lean_inc_ref(v_toApplicative_2140_);
    v_toBind_2141_ = lean_ctor_get(v_inst_2139_, 1);
    lean_inc(v_toBind_2141_);
    lean_dec_ref(v_inst_2139_);
    v_toPure_2142_ = lean_ctor_get(v_toApplicative_2140_, 1);
    lean_inc(v_toPure_2142_);
    lean_dec_ref(v_toApplicative_2140_);
    v___f_2143_ = lean_alloc_closure(
        l_ExceptT_finally___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2143_, 0, v_toPure_2142_);
    v___f_2144_ = lean_alloc_closure(
        l_ExceptT_finally___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_2144_, 0, v_inst_2138_);
    lean_closure_set(v___f_2144_, 1, v_toBind_2141_);
    lean_closure_set(v___f_2144_, 2, v___f_2143_);
    return v___f_2144_;
}
pub unsafe fn l_ExceptT_finally(
    mut v_m_2145_: *mut LeanObject,
    mut v_00_u03b5_2146_: *mut LeanObject,
    mut v_inst_2147_: *mut LeanObject,
    mut v_inst_2148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2153_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2149_ = lean_ctor_get(v_inst_2148_, 0);
    lean_inc_ref(v_toApplicative_2149_);
    v_toBind_2150_ = lean_ctor_get(v_inst_2148_, 1);
    lean_inc(v_toBind_2150_);
    lean_dec_ref(v_inst_2148_);
    v_toPure_2151_ = lean_ctor_get(v_toApplicative_2149_, 1);
    lean_inc(v_toPure_2151_);
    lean_dec_ref(v_toApplicative_2149_);
    v___f_2152_ = lean_alloc_closure(
        l_ExceptT_finally___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2152_, 0, v_toPure_2151_);
    v___f_2153_ = lean_alloc_closure(
        l_ExceptT_finally___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_2153_, 0, v_inst_2147_);
    lean_closure_set(v___f_2153_, 1, v_toBind_2150_);
    lean_closure_set(v___f_2153_, 2, v___f_2152_);
    return v___f_2153_;
}
pub unsafe fn l_instMonadAttachExceptTOfMonad___redArg___lam__0(
    mut v_x_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut v_a_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2166_: u8 = 0;
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2170_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2154_) == 0 {
                    v_a_2155_ = lean_ctor_get(v_x_2154_, 0);
                    v_isSharedCheck_2162_ = (!lean_is_exclusive(v_x_2154_)) as u8;
                    if v_isSharedCheck_2162_ == 0 {
                        v___x_2157_ = v_x_2154_;
                        v_isShared_2158_ = v_isSharedCheck_2162_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2155_);
                        lean_dec(v_x_2154_);
                        v___x_2157_ = lean_box(0);
                        v_isShared_2158_ = v_isSharedCheck_2162_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2163_ = lean_ctor_get(v_x_2154_, 0);
                    v_isSharedCheck_2170_ = (!lean_is_exclusive(v_x_2154_)) as u8;
                    if v_isSharedCheck_2170_ == 0 {
                        v___x_2165_ = v_x_2154_;
                        v_isShared_2166_ = v_isSharedCheck_2170_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2163_);
                        lean_dec(v_x_2154_);
                        v___x_2165_ = lean_box(0);
                        v_isShared_2166_ = v_isSharedCheck_2170_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2158_ == 0 {
                    v___x_2160_ = v___x_2157_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
                    v___x_2160_ = v_reuseFailAlloc_2161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2160_;
            }
            3 => {
                if v_isShared_2166_ == 0 {
                    v___x_2168_ = v___x_2165_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
                    v___x_2168_ = v_reuseFailAlloc_2169_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadAttachExceptTOfMonad___redArg___lam__1(
    mut v_toFunctor_2171_: *mut LeanObject,
    mut v_inst_2172_: *mut LeanObject,
    mut v___f_2173_: *mut LeanObject,
    mut v_00_u03b1_2174_: *mut LeanObject,
    mut v_x_2175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_this_2178_: *mut LeanObject = core::ptr::null_mut();
    v_map_2176_ = lean_ctor_get(v_toFunctor_2171_, 0);
    lean_inc(v_map_2176_);
    lean_dec_ref(v_toFunctor_2171_);
    v___x_2177_ = lean_apply_2(v_inst_2172_, lean_box(0), v_x_2175_);
    v_this_2178_ = lean_apply_4(
        v_map_2176_,
        lean_box(0),
        lean_box(0),
        v___f_2173_,
        v___x_2177_,
    );
    return v_this_2178_;
}
pub unsafe fn l_instMonadAttachExceptTOfMonad___redArg(
    mut v_inst_2180_: *mut LeanObject,
    mut v_inst_2181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2185_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2182_ = lean_ctor_get(v_inst_2180_, 0);
    lean_inc_ref(v_toApplicative_2182_);
    lean_dec_ref(v_inst_2180_);
    v_toFunctor_2183_ = lean_ctor_get(v_toApplicative_2182_, 0);
    lean_inc_ref(v_toFunctor_2183_);
    lean_dec_ref(v_toApplicative_2182_);
    v___f_2184_ = l_instMonadAttachExceptTOfMonad___redArg___closed__0;
    v___f_2185_ = lean_alloc_closure(
        l_instMonadAttachExceptTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2185_, 0, v_toFunctor_2183_);
    lean_closure_set(v___f_2185_, 1, v_inst_2181_);
    lean_closure_set(v___f_2185_, 2, v___f_2184_);
    return v___f_2185_;
}
pub unsafe fn l_instMonadAttachExceptTOfMonad(
    mut v_m_2186_: *mut LeanObject,
    mut v_00_u03b5_2187_: *mut LeanObject,
    mut v_inst_2188_: *mut LeanObject,
    mut v_inst_2189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    v___x_2190_ = l_instMonadAttachExceptTOfMonad___redArg(v_inst_2188_, v_inst_2189_);
    return v___x_2190_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Except(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Id(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Except(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Except(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Id(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Control_Except(builtin);
}
