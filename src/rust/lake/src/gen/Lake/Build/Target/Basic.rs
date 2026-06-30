// Lean compiler output
// Module: Lake.Build.Target.Basic
// Imports: Lake.Build.Key
use crate::ffi::{lean_nat_dec_le, lean_nat_to_int};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Lake::Build::Key::{
    initialize_Lake_Build_Key, l_Lake_PartialBuildKey_toString, l_Lake_instReprBuildKey_repr,
    runtime_initialize_Lake_Build_Key,
};
pub static l_Lake_Target_repr___redArg___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            76, 97, 107, 101, 46, 84, 97, 114, 103, 101, 116, 46, 109, 107, 0,
        ],
    };
static mut l_Lake_Target_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Target_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Target_repr___redArg___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Target_repr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Target_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Target_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Target_repr___redArg___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Target_repr___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Target_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Target_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lake_Target_repr___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Target_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Target_repr___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Target_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Target_instRepr___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Target_repr___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_Target_instRepr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Target_instRepr___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Target_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_PartialBuildKey_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Target_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Target_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Target_instCoePartialBuildKey___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Target_instCoePartialBuildKey___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Target_instCoePartialBuildKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Target_instCoePartialBuildKey___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lake_Target_repr___redArg___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_56_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_56_ = leanh::lean_unsigned_to_nat(2);
    v___x_57_ = lean_nat_to_int(v___x_56_);
    return v___x_57_;
}
pub unsafe fn _init_l_Lake_Target_repr___redArg___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_58_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_58_ = leanh::lean_unsigned_to_nat(1);
    v___x_59_ = lean_nat_to_int(v___x_58_);
    return v___x_59_;
}
pub unsafe fn l_Lake_Target_repr___redArg(
    mut v_x_60_: *mut leanh::LeanObject,
    mut v_prec_61_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctor_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_69_: u8 = 0;
    let mut v___x_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_73_: u8 = 0;
    let mut v___x_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_72_ = leanh::lean_unsigned_to_nat(1024);
                v___x_73_ = lean_nat_dec_le(v___x_72_, v_prec_61_);
                if v___x_73_ == 0 {
                    v___x_74_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Target_repr___redArg___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_Target_repr___redArg___closed__3_once),
                        _init_l_Lake_Target_repr___redArg___closed__3,
                    );
                    v___y_63_ = v___x_74_;
                    state = 1;
                    continue;
                } else {
                    v___x_75_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Target_repr___redArg___closed__4),
                        core::ptr::addr_of_mut!(l_Lake_Target_repr___redArg___closed__4_once),
                        _init_l_Lake_Target_repr___redArg___closed__4,
                    );
                    v___y_63_ = v___x_75_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_64_ = l_Lake_Target_repr___redArg___closed__2;
                v___x_65_ = leanh::lean_unsigned_to_nat(1024);
                v___x_66_ = l_Lake_instReprBuildKey_repr(v_x_60_, v___x_65_);
                v_ctor_67_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v_ctor_67_, 0, v___x_64_);
                leanh::lean_ctor_set(v_ctor_67_, 1, v___x_66_);
                leanh::lean_inc(v___y_63_);
                v___x_68_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_68_, 0, v___y_63_);
                leanh::lean_ctor_set(v___x_68_, 1, v_ctor_67_);
                v___x_69_ = 0;
                v___x_70_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_70_, 0, v___x_68_);
                leanh::lean_ctor_set_uint8(
                    v___x_70_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_69_,
                );
                v___x_71_ = l_Repr_addAppParen(v___x_70_, v_prec_61_);
                return v___x_71_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Target_repr___redArg___boxed(
    mut v_x_76_: *mut leanh::LeanObject,
    mut v_prec_77_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_78_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_78_ = l_Lake_Target_repr___redArg(v_x_76_, v_prec_77_);
    leanh::lean_dec(v_prec_77_);
    return v_res_78_;
}
pub unsafe fn l_Lake_Target_repr(
    mut v_00_u03b1_79_: *mut leanh::LeanObject,
    mut v_x_80_: *mut leanh::LeanObject,
    mut v_prec_81_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_82_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_82_ = l_Lake_Target_repr___redArg(v_x_80_, v_prec_81_);
    return v___x_82_;
}
pub unsafe fn l_Lake_Target_repr___boxed(
    mut v_00_u03b1_83_: *mut leanh::LeanObject,
    mut v_x_84_: *mut leanh::LeanObject,
    mut v_prec_85_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_86_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_86_ = l_Lake_Target_repr(v_00_u03b1_83_, v_x_84_, v_prec_85_);
    leanh::lean_dec(v_prec_85_);
    return v_res_86_;
}
pub unsafe fn l_Lake_Target_instRepr(
    mut v_00_u03b1_88_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_89_ = l_Lake_Target_instRepr___closed__0;
    return v___x_89_;
}
pub unsafe fn l_Lake_Target_instToString(
    mut v_00_u03b1_91_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_92_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_92_ = l_Lake_Target_instToString___closed__0;
    return v___f_92_;
}
pub unsafe fn l_Lake_Target_instCoePartialBuildKey___lam__0(
    mut v_key_93_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_key_93_);
    return v_key_93_;
}
pub unsafe fn l_Lake_Target_instCoePartialBuildKey___lam__0___boxed(
    mut v_key_94_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_95_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_95_ = l_Lake_Target_instCoePartialBuildKey___lam__0(v_key_94_);
    leanh::lean_dec_ref(v_key_94_);
    return v_res_95_;
}
pub unsafe fn l_Lake_Target_instCoePartialBuildKey(
    mut v_00_u03b1_97_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_98_ = l_Lake_Target_instCoePartialBuildKey___closed__0;
    return v___f_98_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Target_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Key(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Target_Basic(
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
pub unsafe fn initialize_Lake_Build_Target_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Key(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Target_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Target_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Target_Basic(builtin);
}