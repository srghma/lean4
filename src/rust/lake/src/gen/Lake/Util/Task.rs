// Lean compiler output
// Module: Lake.Util.Task
// Imports: Init.Control.Option Init.Control.Except
use crate::ffi::{lean_task_bind, lean_task_map, lean_task_pure};
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
use crate::r#gen::Init::Control::Option::{
    initialize_Init_Control_Option, runtime_initialize_Init_Control_Option,
};
use crate::r#gen::Init::Prelude::{l_Function_const___boxed, l_instInhabitedOfMonad___redArg};
pub static l_Lake_instMonadTask__lake___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadTask__lake___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadTask__lake___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadTask__lake___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instMonadTask__lake___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadTask__lake___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadTask__lake___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadTask__lake___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadTask__lake___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadTask__lake___closed__3_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instMonadTask__lake___lam__4 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadTask__lake___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadTask__lake___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadTask__lake___lam__5 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadTask__lake___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadTask__lake___closed__5_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instMonadTask__lake___lam__8 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadTask__lake___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadTask__lake___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadTask__lake___lam__10 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadTask__lake___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadTask__lake___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadTask__lake___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadTask__lake___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadTask__lake___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadTask__lake___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadTask__lake___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadTask__lake: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadTask__lake___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadBaseIOTask___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadBaseIOTask___aux__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadBaseIOTask___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadBaseIOTask___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadBaseIOTask___aux__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadBaseIOTask___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadBaseIOTask___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadBaseIOTask___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadBaseIOTask___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadBaseIOTask___aux__5 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadBaseIOTask___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadBaseIOTask___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadBaseIOTask___aux__7 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadBaseIOTask___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadBaseIOTask___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadBaseIOTask___aux__9 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadBaseIOTask___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadBaseIOTask___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadBaseIOTask___aux__11 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadBaseIOTask___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadBaseIOTask___closed__7_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadBaseIOTask___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadBaseIOTask___closed__8_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadBaseIOTask___aux__13 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadBaseIOTask___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadBaseIOTask___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadBaseIOTask___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadBaseIOTask: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadBaseIOTask___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedOptionIOTask___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedOptionIOTask___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lake_instMonadTask__lake___lam__0(
    mut v_00_u03b1_218_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_219_: *mut crate::leanh::LeanObject,
    mut v_f_220_: *mut crate::leanh::LeanObject,
    mut v_x_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: u8 = 0;
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_222_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_223_ = 0;
    v___x_224_ = lean_task_map(v_f_220_, v_x_221_, v___x_222_, v___x_223_);
    return v___x_224_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__1(
    mut v___f_225_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_226_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_227_: *mut crate::leanh::LeanObject,
    mut v___y_228_: *mut crate::leanh::LeanObject,
    mut v___y_229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_230_ =
        crate::leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_230_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_230_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_230_, 2, v___y_228_);
    v___x_231_ = crate::leanh::lean_apply_4(
        v___f_225_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_230_,
        v___y_229_,
    );
    return v___x_231_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__2(
    mut v_00_u03b1_232_: *mut crate::leanh::LeanObject,
    mut v___y_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = lean_task_pure(v___y_233_);
    return v___x_234_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__3(
    mut v_x_235_: *mut crate::leanh::LeanObject,
    mut v___f_236_: *mut crate::leanh::LeanObject,
    mut v_y_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_238_ = crate::leanh::lean_box(0);
    v___x_239_ = crate::leanh::lean_apply_1(v_x_235_, v___x_238_);
    v___x_240_ = crate::leanh::lean_apply_4(
        v___f_236_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_y_237_,
        v___x_239_,
    );
    return v___x_240_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__4(
    mut v___f_241_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_242_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_243_: *mut crate::leanh::LeanObject,
    mut v_f_244_: *mut crate::leanh::LeanObject,
    mut v_x_245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: u8 = 0;
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_246_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadTask__lake___lam__3 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_246_, 0, v_x_245_);
    crate::leanh::lean_closure_set(v___f_246_, 1, v___f_241_);
    v___x_247_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_248_ = 0;
    v___x_249_ = lean_task_bind(v_f_244_, v___f_246_, v___x_247_, v___x_248_);
    return v___x_249_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__5(
    mut v_00_u03b1_250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_251_: *mut crate::leanh::LeanObject,
    mut v_x_252_: *mut crate::leanh::LeanObject,
    mut v_f_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: u8 = 0;
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_254_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_255_ = 0;
    v___x_256_ = lean_task_bind(v_x_252_, v_f_253_, v___x_254_, v___x_255_);
    return v___x_256_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__6(
    mut v_a_257_: *mut crate::leanh::LeanObject,
    mut v_x_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_259_ = lean_task_pure(v_a_257_);
    return v___x_259_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__6___boxed(
    mut v_a_260_: *mut crate::leanh::LeanObject,
    mut v_x_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_262_ = l_Lake_instMonadTask__lake___lam__6(v_a_260_, v_x_261_);
    crate::leanh::lean_dec(v_x_261_);
    return v_res_262_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__7(
    mut v_y_263_: *mut crate::leanh::LeanObject,
    mut v___f_264_: *mut crate::leanh::LeanObject,
    mut v_a_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_266_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadTask__lake___lam__6___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_266_, 0, v_a_265_);
    v___x_267_ = crate::leanh::lean_box(0);
    v___x_268_ = crate::leanh::lean_apply_1(v_y_263_, v___x_267_);
    v___x_269_ = crate::leanh::lean_apply_4(
        v___f_264_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_268_,
        v___f_266_,
    );
    return v___x_269_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__8(
    mut v___f_270_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_271_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_272_: *mut crate::leanh::LeanObject,
    mut v_x_273_: *mut crate::leanh::LeanObject,
    mut v_y_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v___f_270_);
    v___f_275_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadTask__lake___lam__7 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_275_, 0, v_y_274_);
    crate::leanh::lean_closure_set(v___f_275_, 1, v___f_270_);
    v___x_276_ = crate::leanh::lean_apply_4(
        v___f_270_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_273_,
        v___f_275_,
    );
    return v___x_276_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__9(
    mut v_y_277_: *mut crate::leanh::LeanObject,
    mut v_x_278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_279_ = crate::leanh::lean_box(0);
    v___x_280_ = crate::leanh::lean_apply_1(v_y_277_, v___x_279_);
    return v___x_280_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__9___boxed(
    mut v_y_281_: *mut crate::leanh::LeanObject,
    mut v_x_282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_283_ = l_Lake_instMonadTask__lake___lam__9(v_y_281_, v_x_282_);
    crate::leanh::lean_dec(v_x_282_);
    return v_res_283_;
}
pub unsafe fn l_Lake_instMonadTask__lake___lam__10(
    mut v_00_u03b1_284_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_285_: *mut crate::leanh::LeanObject,
    mut v_x_286_: *mut crate::leanh::LeanObject,
    mut v_y_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: u8 = 0;
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_288_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadTask__lake___lam__9___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_288_, 0, v_y_287_);
    v___x_289_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_290_ = 0;
    v___x_291_ = lean_task_bind(v_x_286_, v___f_288_, v___x_289_, v___x_290_);
    return v___x_291_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__1___redArg(
    mut v_f_315_: *mut crate::leanh::LeanObject,
    mut v_x_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: u8 = 0;
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_317_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_318_ = 0;
    v___x_319_ = lean_task_map(v_f_315_, v_x_316_, v___x_317_, v___x_318_);
    return v___x_319_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__1(
    mut v_00_u03b1_320_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_321_: *mut crate::leanh::LeanObject,
    mut v_f_322_: *mut crate::leanh::LeanObject,
    mut v_x_323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: u8 = 0;
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_324_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_325_ = 0;
    v___x_326_ = lean_task_map(v_f_322_, v_x_323_, v___x_324_, v___x_325_);
    return v___x_326_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__3___redArg(
    mut v_a_327_: *mut crate::leanh::LeanObject,
    mut v_a_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: u8 = 0;
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_329_ =
        crate::leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_329_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_329_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_329_, 2, v_a_327_);
    v___x_330_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_331_ = 0;
    v___x_332_ = lean_task_map(v___x_329_, v_a_328_, v___x_330_, v___x_331_);
    return v___x_332_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__3(
    mut v_00_u03b1_333_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_334_: *mut crate::leanh::LeanObject,
    mut v_a_335_: *mut crate::leanh::LeanObject,
    mut v_a_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: u8 = 0;
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_337_ =
        crate::leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_337_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_337_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_337_, 2, v_a_335_);
    v___x_338_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_339_ = 0;
    v___x_340_ = lean_task_map(v___x_337_, v_a_336_, v___x_338_, v___x_339_);
    return v___x_340_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__5___redArg(
    mut v_get_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = lean_task_pure(v_get_341_);
    return v___x_342_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__5(
    mut v_00_u03b1_343_: *mut crate::leanh::LeanObject,
    mut v_get_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_345_ = lean_task_pure(v_get_344_);
    return v___x_345_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__7___redArg___lam__0(
    mut v_x_346_: *mut crate::leanh::LeanObject,
    mut v_y_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: u8 = 0;
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = crate::leanh::lean_box(0);
    v___x_349_ = crate::leanh::lean_apply_1(v_x_346_, v___x_348_);
    v___x_350_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_351_ = 0;
    v___x_352_ = lean_task_map(v_y_347_, v___x_349_, v___x_350_, v___x_351_);
    return v___x_352_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__7___redArg(
    mut v_f_353_: *mut crate::leanh::LeanObject,
    mut v_x_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: u8 = 0;
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_355_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadBaseIOTask___aux__7___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_355_, 0, v_x_354_);
    v___x_356_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_357_ = 0;
    v___x_358_ = lean_task_bind(v_f_353_, v___f_355_, v___x_356_, v___x_357_);
    return v___x_358_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__7(
    mut v_00_u03b1_359_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_360_: *mut crate::leanh::LeanObject,
    mut v_f_361_: *mut crate::leanh::LeanObject,
    mut v_x_362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: u8 = 0;
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_363_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadBaseIOTask___aux__7___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_363_, 0, v_x_362_);
    v___x_364_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_365_ = 0;
    v___x_366_ = lean_task_bind(v_f_361_, v___f_363_, v___x_364_, v___x_365_);
    return v___x_366_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__9___redArg(
    mut v_x_367_: *mut crate::leanh::LeanObject,
    mut v_y_368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_369_ = l_Lake_instMonadTask__lake___closed__4;
    v___f_370_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadTask__lake___lam__7 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_370_, 0, v_y_368_);
    crate::leanh::lean_closure_set(v___f_370_, 1, v___f_369_);
    v___x_371_ = l_Lake_instMonadTask__lake___lam__5(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_367_,
        v___f_370_,
    );
    return v___x_371_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__9(
    mut v_00_u03b1_372_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_373_: *mut crate::leanh::LeanObject,
    mut v_x_374_: *mut crate::leanh::LeanObject,
    mut v_y_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_376_ = l_Lake_instMonadTask__lake___closed__4;
    v___f_377_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadTask__lake___lam__7 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_377_, 0, v_y_375_);
    crate::leanh::lean_closure_set(v___f_377_, 1, v___f_376_);
    v___x_378_ = l_Lake_instMonadTask__lake___lam__5(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_374_,
        v___f_377_,
    );
    return v___x_378_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__11___redArg(
    mut v_x_379_: *mut crate::leanh::LeanObject,
    mut v_y_380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: u8 = 0;
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_381_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadTask__lake___lam__9___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_381_, 0, v_y_380_);
    v___x_382_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_383_ = 0;
    v___x_384_ = lean_task_bind(v_x_379_, v___f_381_, v___x_382_, v___x_383_);
    return v___x_384_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__11(
    mut v_00_u03b1_385_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_386_: *mut crate::leanh::LeanObject,
    mut v_x_387_: *mut crate::leanh::LeanObject,
    mut v_y_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: u8 = 0;
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_389_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadTask__lake___lam__9___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_389_, 0, v_y_388_);
    v___x_390_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_391_ = 0;
    v___x_392_ = lean_task_bind(v_x_387_, v___f_389_, v___x_390_, v___x_391_);
    return v___x_392_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__13___redArg(
    mut v_x_393_: *mut crate::leanh::LeanObject,
    mut v_f_394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: u8 = 0;
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_396_ = 0;
    v___x_397_ = lean_task_bind(v_x_393_, v_f_394_, v___x_395_, v___x_396_);
    return v___x_397_;
}
pub unsafe fn l_Lake_instMonadBaseIOTask___aux__13(
    mut v_00_u03b1_398_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_399_: *mut crate::leanh::LeanObject,
    mut v_x_400_: *mut crate::leanh::LeanObject,
    mut v_f_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: u8 = 0;
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_403_ = 0;
    v___x_404_ = lean_task_bind(v_x_400_, v_f_401_, v___x_402_, v___x_403_);
    return v___x_404_;
}
pub unsafe fn l_Lake_instInhabitedBaseIOTask___redArg(
    mut v_inst_425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_426_ = l_Lake_instMonadBaseIOTask;
    v___x_427_ = l_instInhabitedOfMonad___redArg(v___x_426_, v_inst_425_);
    return v___x_427_;
}
pub unsafe fn l_Lake_instInhabitedBaseIOTask(
    mut v_00_u03b1_428_: *mut crate::leanh::LeanObject,
    mut v_inst_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = l_Lake_instInhabitedBaseIOTask___redArg(v_inst_429_);
    return v___x_430_;
}
pub unsafe fn _init_l_Lake_instInhabitedOptionIOTask___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ = crate::leanh::lean_box(0);
    v___x_432_ = lean_task_pure(v___x_431_);
    return v___x_432_;
}
pub unsafe fn l_Lake_instInhabitedOptionIOTask(
    mut v_00_u03b1_433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOptionIOTask___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOptionIOTask___closed__0_once),
        _init_l_Lake_instInhabitedOptionIOTask___closed__0,
    );
    return v___x_434_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Task(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Task(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Task(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Task(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Task(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Task(builtin);
}
