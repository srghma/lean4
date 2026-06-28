// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Insts
// Imports: Lean.Meta.Tactic.Grind.Arith.EvalNum Lean.Meta.Tactic.Grind.SynthInstance Init.Grind.Ring
use crate::r#gen::Init::Grind::Ring::{
    initialize_Init_Grind_Ring, runtime_initialize_Init_Grind_Ring,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_hasMVar, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::EvalNum::{
    initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum, l_Lean_Meta_Grind_Arith_evalNat_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::SynthInstance::{
    initialize_Lean_Meta_Tactic_Grind_SynthInstance,
    runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_11, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
};
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [73, 115, 67, 104, 97, 114, 80, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value)
            as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2_value
            ) as *mut LeanObject,
            5319903737885873089 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [80, 111, 119, 73, 100, 101, 110, 116, 105, 116, 121, 0],
};
static mut l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [67, 111, 109, 109, 83, 101, 109, 105, 114, 105, 110, 103, 0],
    };
static mut l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value
            ) as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0_value)
                as *mut LeanObject,
            15814158821706329669 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [78, 97, 116, 77, 111, 100, 117, 108, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value)
            as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value)
            as *mut LeanObject,
        12969150934523051142 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        78, 111, 78, 97, 116, 90, 101, 114, 111, 68, 105, 118, 105, 115, 111, 114, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value)
            as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value)
            as *mut LeanObject,
        5648161575337860430 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(
    mut v_e_547_: *mut LeanObject,
    mut v___y_548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_564_: u8 = 0;
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_570_: u8 = 0;
    let mut v_unused_571_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_550_ = l_Lean_Expr_hasMVar(v_e_547_);
                if v___x_550_ == 0 {
                    v___x_551_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_551_, 0, v_e_547_);
                    return v___x_551_;
                } else {
                    v___x_552_ = lean_st_ref_get(v___y_548_);
                    v_mctx_553_ = lean_ctor_get(v___x_552_, 0);
                    lean_inc_ref(v_mctx_553_);
                    lean_dec(v___x_552_);
                    v___x_554_ = l_Lean_instantiateMVarsCore(v_mctx_553_, v_e_547_);
                    v_fst_555_ = lean_ctor_get(v___x_554_, 0);
                    lean_inc(v_fst_555_);
                    v_snd_556_ = lean_ctor_get(v___x_554_, 1);
                    lean_inc(v_snd_556_);
                    lean_dec_ref(v___x_554_);
                    v___x_557_ = lean_st_ref_take(v___y_548_);
                    v_cache_558_ = lean_ctor_get(v___x_557_, 1);
                    v_zetaDeltaFVarIds_559_ = lean_ctor_get(v___x_557_, 2);
                    v_postponed_560_ = lean_ctor_get(v___x_557_, 3);
                    v_diag_561_ = lean_ctor_get(v___x_557_, 4);
                    v_isSharedCheck_570_ = (!lean_is_exclusive(v___x_557_)) as u8;
                    if v_isSharedCheck_570_ == 0 {
                        v_unused_571_ = lean_ctor_get(v___x_557_, 0);
                        lean_dec(v_unused_571_);
                        v___x_563_ = v___x_557_;
                        v_isShared_564_ = v_isSharedCheck_570_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_561_);
                        lean_inc(v_postponed_560_);
                        lean_inc(v_zetaDeltaFVarIds_559_);
                        lean_inc(v_cache_558_);
                        lean_dec(v___x_557_);
                        v___x_563_ = lean_box(0);
                        v_isShared_564_ = v_isSharedCheck_570_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_564_ == 0 {
                    lean_ctor_set(v___x_563_, 0, v_snd_556_);
                    v___x_566_ = v___x_563_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_569_, 0, v_snd_556_);
                    lean_ctor_set(v_reuseFailAlloc_569_, 1, v_cache_558_);
                    lean_ctor_set(v_reuseFailAlloc_569_, 2, v_zetaDeltaFVarIds_559_);
                    lean_ctor_set(v_reuseFailAlloc_569_, 3, v_postponed_560_);
                    lean_ctor_set(v_reuseFailAlloc_569_, 4, v_diag_561_);
                    v___x_566_ = v_reuseFailAlloc_569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_567_ = lean_st_ref_set(v___y_548_, v___x_566_);
                v___x_568_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_568_, 0, v_fst_555_);
                return v___x_568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(
    mut v_e_572_: *mut LeanObject,
    mut v___y_573_: *mut LeanObject,
    mut v___y_574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_575_: *mut LeanObject = core::ptr::null_mut();
    v_res_575_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(
            v_e_572_, v___y_573_,
        );
    lean_dec(v___y_573_);
    return v_res_575_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0(
    mut v_e_576_: *mut LeanObject,
    mut v___y_577_: *mut LeanObject,
    mut v___y_578_: *mut LeanObject,
    mut v___y_579_: *mut LeanObject,
    mut v___y_580_: *mut LeanObject,
    mut v___y_581_: *mut LeanObject,
    mut v___y_582_: *mut LeanObject,
    mut v___y_583_: *mut LeanObject,
    mut v___y_584_: *mut LeanObject,
    mut v___y_585_: *mut LeanObject,
    mut v___y_586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    v___x_588_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(
            v_e_576_, v___y_584_,
        );
    return v___x_588_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___boxed(
    mut v_e_589_: *mut LeanObject,
    mut v___y_590_: *mut LeanObject,
    mut v___y_591_: *mut LeanObject,
    mut v___y_592_: *mut LeanObject,
    mut v___y_593_: *mut LeanObject,
    mut v___y_594_: *mut LeanObject,
    mut v___y_595_: *mut LeanObject,
    mut v___y_596_: *mut LeanObject,
    mut v___y_597_: *mut LeanObject,
    mut v___y_598_: *mut LeanObject,
    mut v___y_599_: *mut LeanObject,
    mut v___y_600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_601_: *mut LeanObject = core::ptr::null_mut();
    v_res_601_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0(
        v_e_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_,
        v___y_596_, v___y_597_, v___y_598_, v___y_599_,
    );
    lean_dec(v___y_599_);
    lean_dec_ref(v___y_598_);
    lean_dec(v___y_597_);
    lean_dec_ref(v___y_596_);
    lean_dec(v___y_595_);
    lean_dec_ref(v___y_594_);
    lean_dec(v___y_593_);
    lean_dec_ref(v___y_592_);
    lean_dec(v___y_591_);
    lean_dec(v___y_590_);
    return v_res_601_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(
    mut v_k_602_: *mut LeanObject,
    mut v___y_603_: *mut LeanObject,
    mut v___y_604_: *mut LeanObject,
    mut v___y_605_: *mut LeanObject,
    mut v___y_606_: *mut LeanObject,
    mut v___y_607_: *mut LeanObject,
    mut v___y_608_: *mut LeanObject,
    mut v___y_609_: *mut LeanObject,
    mut v___y_610_: *mut LeanObject,
    mut v___y_611_: *mut LeanObject,
    mut v___y_612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_608_);
    lean_inc_ref(v___y_607_);
    lean_inc(v___y_606_);
    lean_inc_ref(v___y_605_);
    lean_inc(v___y_604_);
    lean_inc(v___y_603_);
    v___x_614_ = lean_apply_11(
        v_k_602_,
        v___y_603_,
        v___y_604_,
        v___y_605_,
        v___y_606_,
        v___y_607_,
        v___y_608_,
        v___y_609_,
        v___y_610_,
        v___y_611_,
        v___y_612_,
        lean_box(0),
    );
    return v___x_614_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(
    mut v_k_615_: *mut LeanObject,
    mut v___y_616_: *mut LeanObject,
    mut v___y_617_: *mut LeanObject,
    mut v___y_618_: *mut LeanObject,
    mut v___y_619_: *mut LeanObject,
    mut v___y_620_: *mut LeanObject,
    mut v___y_621_: *mut LeanObject,
    mut v___y_622_: *mut LeanObject,
    mut v___y_623_: *mut LeanObject,
    mut v___y_624_: *mut LeanObject,
    mut v___y_625_: *mut LeanObject,
    mut v___y_626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_627_: *mut LeanObject = core::ptr::null_mut();
    v_res_627_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(v_k_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
    lean_dec(v___y_621_);
    lean_dec_ref(v___y_620_);
    lean_dec(v___y_619_);
    lean_dec_ref(v___y_618_);
    lean_dec(v___y_617_);
    lean_dec(v___y_616_);
    return v_res_627_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(
    mut v_k_628_: *mut LeanObject,
    mut v_allowLevelAssignments_629_: u8,
    mut v___y_630_: *mut LeanObject,
    mut v___y_631_: *mut LeanObject,
    mut v___y_632_: *mut LeanObject,
    mut v___y_633_: *mut LeanObject,
    mut v___y_634_: *mut LeanObject,
    mut v___y_635_: *mut LeanObject,
    mut v___y_636_: *mut LeanObject,
    mut v___y_637_: *mut LeanObject,
    mut v___y_638_: *mut LeanObject,
    mut v___y_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_646_: u8 = 0;
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_650_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_635_);
                lean_inc_ref(v___y_634_);
                lean_inc(v___y_633_);
                lean_inc_ref(v___y_632_);
                lean_inc(v___y_631_);
                lean_inc(v___y_630_);
                v___f_641_ = lean_alloc_closure(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 7);
                lean_closure_set(v___f_641_, 0, v_k_628_);
                lean_closure_set(v___f_641_, 1, v___y_630_);
                lean_closure_set(v___f_641_, 2, v___y_631_);
                lean_closure_set(v___f_641_, 3, v___y_632_);
                lean_closure_set(v___f_641_, 4, v___y_633_);
                lean_closure_set(v___f_641_, 5, v___y_634_);
                lean_closure_set(v___f_641_, 6, v___y_635_);
                v___x_642_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    lean_box(0),
                    v_allowLevelAssignments_629_,
                    v___f_641_,
                    v___y_636_,
                    v___y_637_,
                    v___y_638_,
                    v___y_639_,
                );
                if lean_obj_tag(v___x_642_) == 0 {
                    return v___x_642_;
                } else {
                    v_a_643_ = lean_ctor_get(v___x_642_, 0);
                    v_isSharedCheck_650_ = (!lean_is_exclusive(v___x_642_)) as u8;
                    if v_isSharedCheck_650_ == 0 {
                        v___x_645_ = v___x_642_;
                        v_isShared_646_ = v_isSharedCheck_650_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_643_);
                        lean_dec(v___x_642_);
                        v___x_645_ = lean_box(0);
                        v_isShared_646_ = v_isSharedCheck_650_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_646_ == 0 {
                    v___x_648_ = v___x_645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
                    v___x_648_ = v_reuseFailAlloc_649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___boxed(
    mut v_k_651_: *mut LeanObject,
    mut v_allowLevelAssignments_652_: *mut LeanObject,
    mut v___y_653_: *mut LeanObject,
    mut v___y_654_: *mut LeanObject,
    mut v___y_655_: *mut LeanObject,
    mut v___y_656_: *mut LeanObject,
    mut v___y_657_: *mut LeanObject,
    mut v___y_658_: *mut LeanObject,
    mut v___y_659_: *mut LeanObject,
    mut v___y_660_: *mut LeanObject,
    mut v___y_661_: *mut LeanObject,
    mut v___y_662_: *mut LeanObject,
    mut v___y_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_664_: u8 = 0;
    let mut v_res_665_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_664_ = (lean_unbox(v_allowLevelAssignments_652_) as u8);
    v_res_665_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_651_, v_allowLevelAssignments_boxed_664_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
    lean_dec(v___y_662_);
    lean_dec_ref(v___y_661_);
    lean_dec(v___y_660_);
    lean_dec_ref(v___y_659_);
    lean_dec(v___y_658_);
    lean_dec_ref(v___y_657_);
    lean_dec(v___y_656_);
    lean_dec_ref(v___y_655_);
    lean_dec(v___y_654_);
    lean_dec(v___y_653_);
    return v_res_665_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1(
    mut v_00_u03b1_666_: *mut LeanObject,
    mut v_k_667_: *mut LeanObject,
    mut v_allowLevelAssignments_668_: u8,
    mut v___y_669_: *mut LeanObject,
    mut v___y_670_: *mut LeanObject,
    mut v___y_671_: *mut LeanObject,
    mut v___y_672_: *mut LeanObject,
    mut v___y_673_: *mut LeanObject,
    mut v___y_674_: *mut LeanObject,
    mut v___y_675_: *mut LeanObject,
    mut v___y_676_: *mut LeanObject,
    mut v___y_677_: *mut LeanObject,
    mut v___y_678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    v___x_680_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_667_, v_allowLevelAssignments_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
    return v___x_680_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___boxed(
    mut v_00_u03b1_681_: *mut LeanObject,
    mut v_k_682_: *mut LeanObject,
    mut v_allowLevelAssignments_683_: *mut LeanObject,
    mut v___y_684_: *mut LeanObject,
    mut v___y_685_: *mut LeanObject,
    mut v___y_686_: *mut LeanObject,
    mut v___y_687_: *mut LeanObject,
    mut v___y_688_: *mut LeanObject,
    mut v___y_689_: *mut LeanObject,
    mut v___y_690_: *mut LeanObject,
    mut v___y_691_: *mut LeanObject,
    mut v___y_692_: *mut LeanObject,
    mut v___y_693_: *mut LeanObject,
    mut v___y_694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_695_: u8 = 0;
    let mut v_res_696_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_695_ = (lean_unbox(v_allowLevelAssignments_683_) as u8);
    v_res_696_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1(
            v_00_u03b1_681_,
            v_k_682_,
            v_allowLevelAssignments_boxed_695_,
            v___y_684_,
            v___y_685_,
            v___y_686_,
            v___y_687_,
            v___y_688_,
            v___y_689_,
            v___y_690_,
            v___y_691_,
            v___y_692_,
            v___y_693_,
        );
    lean_dec(v___y_693_);
    lean_dec_ref(v___y_692_);
    lean_dec(v___y_691_);
    lean_dec_ref(v___y_690_);
    lean_dec(v___y_689_);
    lean_dec_ref(v___y_688_);
    lean_dec(v___y_687_);
    lean_dec_ref(v___y_686_);
    lean_dec(v___y_685_);
    lean_dec(v___y_684_);
    return v_res_696_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(
    mut v___x_704_: *mut LeanObject,
    mut v___x_705_: u8,
    mut v___x_706_: *mut LeanObject,
    mut v_u_707_: *mut LeanObject,
    mut v___x_708_: *mut LeanObject,
    mut v_type_709_: *mut LeanObject,
    mut v_semiringInst_710_: *mut LeanObject,
    mut v___y_711_: *mut LeanObject,
    mut v___y_712_: *mut LeanObject,
    mut v___y_713_: *mut LeanObject,
    mut v___y_714_: *mut LeanObject,
    mut v___y_715_: *mut LeanObject,
    mut v___y_716_: *mut LeanObject,
    mut v___y_717_: *mut LeanObject,
    mut v___y_718_: *mut LeanObject,
    mut v___y_719_: *mut LeanObject,
    mut v___y_720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charType_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_732_: u8 = 0;
    let mut v_val_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_740_: u8 = 0;
    let mut v_val_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_744_: u8 = 0;
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_752_: u8 = 0;
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_757_: u8 = 0;
    let mut v_a_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_761_: u8 = 0;
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_765_: u8 = 0;
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut v_a_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_774_: u8 = 0;
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_778_: u8 = 0;
    let mut v_a_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_782_: u8 = 0;
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_722_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_704_, v___x_705_, v___x_706_, v___y_717_, v___y_718_, v___y_719_,
                    v___y_720_,
                );
                if lean_obj_tag(v___x_722_) == 0 {
                    v_a_723_ = lean_ctor_get(v___x_722_, 0);
                    lean_inc_n(v_a_723_, 2);
                    lean_dec_ref_known(v___x_722_, 1);
                    v___x_724_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3;
                    v___x_725_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_725_, 0, v_u_707_);
                    lean_ctor_set(v___x_725_, 1, v___x_708_);
                    v___x_726_ = l_Lean_mkConst(v___x_724_, v___x_725_);
                    v_charType_727_ =
                        l_Lean_mkApp3(v___x_726_, v_type_709_, v_semiringInst_710_, v_a_723_);
                    v___x_728_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v_charType_727_,
                        v___y_717_,
                        v___y_718_,
                        v___y_719_,
                        v___y_720_,
                    );
                    if lean_obj_tag(v___x_728_) == 0 {
                        v_a_729_ = lean_ctor_get(v___x_728_, 0);
                        v_isSharedCheck_770_ = (!lean_is_exclusive(v___x_728_)) as u8;
                        if v_isSharedCheck_770_ == 0 {
                            v___x_731_ = v___x_728_;
                            v_isShared_732_ = v_isSharedCheck_770_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_729_);
                            lean_dec(v___x_728_);
                            v___x_731_ = lean_box(0);
                            v_isShared_732_ = v_isSharedCheck_770_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_723_);
                        v_a_771_ = lean_ctor_get(v___x_728_, 0);
                        v_isSharedCheck_778_ = (!lean_is_exclusive(v___x_728_)) as u8;
                        if v_isSharedCheck_778_ == 0 {
                            v___x_773_ = v___x_728_;
                            v_isShared_774_ = v_isSharedCheck_778_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_771_);
                            lean_dec(v___x_728_);
                            v___x_773_ = lean_box(0);
                            v_isShared_774_ = v_isSharedCheck_778_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_semiringInst_710_);
                    lean_dec_ref(v_type_709_);
                    lean_dec(v___x_708_);
                    lean_dec(v_u_707_);
                    v_a_779_ = lean_ctor_get(v___x_722_, 0);
                    v_isSharedCheck_786_ = (!lean_is_exclusive(v___x_722_)) as u8;
                    if v_isSharedCheck_786_ == 0 {
                        v___x_781_ = v___x_722_;
                        v_isShared_782_ = v_isSharedCheck_786_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_779_);
                        lean_dec(v___x_722_);
                        v___x_781_ = lean_box(0);
                        v_isShared_782_ = v_isSharedCheck_786_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_729_) == 1 {
                    lean_del_object(v___x_731_);
                    v_val_733_ = lean_ctor_get(v_a_729_, 0);
                    lean_inc(v_val_733_);
                    lean_dec_ref_known(v_a_729_, 1);
                    v___x_734_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_723_, v___y_718_);
                    v_a_735_ = lean_ctor_get(v___x_734_, 0);
                    lean_inc(v_a_735_);
                    lean_dec_ref(v___x_734_);
                    v___x_736_ = l_Lean_Meta_Grind_Arith_evalNat_x3f(
                        v_a_735_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_,
                        v___y_717_, v___y_718_, v___y_719_, v___y_720_,
                    );
                    if lean_obj_tag(v___x_736_) == 0 {
                        v_a_737_ = lean_ctor_get(v___x_736_, 0);
                        v_isSharedCheck_757_ = (!lean_is_exclusive(v___x_736_)) as u8;
                        if v_isSharedCheck_757_ == 0 {
                            v___x_739_ = v___x_736_;
                            v_isShared_740_ = v_isSharedCheck_757_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_737_);
                            lean_dec(v___x_736_);
                            v___x_739_ = lean_box(0);
                            v_isShared_740_ = v_isSharedCheck_757_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_733_);
                        v_a_758_ = lean_ctor_get(v___x_736_, 0);
                        v_isSharedCheck_765_ = (!lean_is_exclusive(v___x_736_)) as u8;
                        if v_isSharedCheck_765_ == 0 {
                            v___x_760_ = v___x_736_;
                            v_isShared_761_ = v_isSharedCheck_765_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_758_);
                            lean_dec(v___x_736_);
                            v___x_760_ = lean_box(0);
                            v_isShared_761_ = v_isSharedCheck_765_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_729_);
                    lean_dec(v_a_723_);
                    v___x_766_ = lean_box(0);
                    if v_isShared_732_ == 0 {
                        lean_ctor_set(v___x_731_, 0, v___x_766_);
                        v___x_768_ = v___x_731_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
                        v___x_768_ = v_reuseFailAlloc_769_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_737_) == 1 {
                    v_val_741_ = lean_ctor_get(v_a_737_, 0);
                    v_isSharedCheck_752_ = (!lean_is_exclusive(v_a_737_)) as u8;
                    if v_isSharedCheck_752_ == 0 {
                        v___x_743_ = v_a_737_;
                        v_isShared_744_ = v_isSharedCheck_752_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_741_);
                        lean_dec(v_a_737_);
                        v___x_743_ = lean_box(0);
                        v_isShared_744_ = v_isSharedCheck_752_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_737_);
                    lean_dec(v_val_733_);
                    v___x_753_ = lean_box(0);
                    if v_isShared_740_ == 0 {
                        lean_ctor_set(v___x_739_, 0, v___x_753_);
                        v___x_755_ = v___x_739_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
                        v___x_755_ = v_reuseFailAlloc_756_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_745_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_745_, 0, v_val_733_);
                lean_ctor_set(v___x_745_, 1, v_val_741_);
                if v_isShared_744_ == 0 {
                    lean_ctor_set(v___x_743_, 0, v___x_745_);
                    v___x_747_ = v___x_743_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_745_);
                    v___x_747_ = v_reuseFailAlloc_751_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_740_ == 0 {
                    lean_ctor_set(v___x_739_, 0, v___x_747_);
                    v___x_749_ = v___x_739_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
                    v___x_749_ = v_reuseFailAlloc_750_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_749_;
            }
            6 => {
                return v___x_755_;
            }
            7 => {
                if v_isShared_761_ == 0 {
                    v___x_763_ = v___x_760_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
                    v___x_763_ = v_reuseFailAlloc_764_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_763_;
            }
            9 => {
                return v___x_768_;
            }
            10 => {
                if v_isShared_774_ == 0 {
                    v___x_776_ = v___x_773_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
                    v___x_776_ = v_reuseFailAlloc_777_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_776_;
            }
            12 => {
                if v_isShared_782_ == 0 {
                    v___x_784_ = v___x_781_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
                    v___x_784_ = v_reuseFailAlloc_785_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_787_: *mut LeanObject = *_args.add(0);
    let mut v___x_788_: *mut LeanObject = *_args.add(1);
    let mut v___x_789_: *mut LeanObject = *_args.add(2);
    let mut v_u_790_: *mut LeanObject = *_args.add(3);
    let mut v___x_791_: *mut LeanObject = *_args.add(4);
    let mut v_type_792_: *mut LeanObject = *_args.add(5);
    let mut v_semiringInst_793_: *mut LeanObject = *_args.add(6);
    let mut v___y_794_: *mut LeanObject = *_args.add(7);
    let mut v___y_795_: *mut LeanObject = *_args.add(8);
    let mut v___y_796_: *mut LeanObject = *_args.add(9);
    let mut v___y_797_: *mut LeanObject = *_args.add(10);
    let mut v___y_798_: *mut LeanObject = *_args.add(11);
    let mut v___y_799_: *mut LeanObject = *_args.add(12);
    let mut v___y_800_: *mut LeanObject = *_args.add(13);
    let mut v___y_801_: *mut LeanObject = *_args.add(14);
    let mut v___y_802_: *mut LeanObject = *_args.add(15);
    let mut v___y_803_: *mut LeanObject = *_args.add(16);
    let mut v___y_804_: *mut LeanObject = *_args.add(17);
    let mut v___x_9036__boxed_805_: u8 = 0;
    let mut v_res_806_: *mut LeanObject = core::ptr::null_mut();
    v___x_9036__boxed_805_ = (lean_unbox(v___x_788_) as u8);
    v_res_806_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(
        v___x_787_,
        v___x_9036__boxed_805_,
        v___x_789_,
        v_u_790_,
        v___x_791_,
        v_type_792_,
        v_semiringInst_793_,
        v___y_794_,
        v___y_795_,
        v___y_796_,
        v___y_797_,
        v___y_798_,
        v___y_799_,
        v___y_800_,
        v___y_801_,
        v___y_802_,
        v___y_803_,
    );
    lean_dec(v___y_803_);
    lean_dec_ref(v___y_802_);
    lean_dec(v___y_801_);
    lean_dec_ref(v___y_800_);
    lean_dec(v___y_799_);
    lean_dec_ref(v___y_798_);
    lean_dec(v___y_797_);
    lean_dec_ref(v___y_796_);
    lean_dec(v___y_795_);
    lean_dec(v___y_794_);
    return v_res_806_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2() -> *mut LeanObject {
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    v___x_810_ = lean_box(0);
    v___x_811_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1;
    v___x_812_ = l_Lean_mkConst(v___x_811_, v___x_810_);
    return v___x_812_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    v___x_813_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2_once),
        _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2,
    );
    v___x_814_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_814_, 0, v___x_813_);
    return v___x_814_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(
    mut v_u_815_: *mut LeanObject,
    mut v_type_816_: *mut LeanObject,
    mut v_semiringInst_817_: *mut LeanObject,
    mut v_a_818_: *mut LeanObject,
    mut v_a_819_: *mut LeanObject,
    mut v_a_820_: *mut LeanObject,
    mut v_a_821_: *mut LeanObject,
    mut v_a_822_: *mut LeanObject,
    mut v_a_823_: *mut LeanObject,
    mut v_a_824_: *mut LeanObject,
    mut v_a_825_: *mut LeanObject,
    mut v_a_826_: *mut LeanObject,
    mut v_a_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: u8 = 0;
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: u8 = 0;
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    v___x_829_ = lean_box(0);
    v___x_830_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3_once),
        _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3,
    );
    v___x_831_ = 0;
    v___x_832_ = lean_box(0);
    v___x_833_ = lean_box((v___x_831_) as usize);
    v___f_834_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed as *mut core::ffi::c_void,
        18,
        7,
    );
    lean_closure_set(v___f_834_, 0, v___x_830_);
    lean_closure_set(v___f_834_, 1, v___x_833_);
    lean_closure_set(v___f_834_, 2, v___x_832_);
    lean_closure_set(v___f_834_, 3, v_u_815_);
    lean_closure_set(v___f_834_, 4, v___x_829_);
    lean_closure_set(v___f_834_, 5, v_type_816_);
    lean_closure_set(v___f_834_, 6, v_semiringInst_817_);
    v___x_835_ = 0;
    v___x_836_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_834_, v___x_835_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
    return v___x_836_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___boxed(
    mut v_u_837_: *mut LeanObject,
    mut v_type_838_: *mut LeanObject,
    mut v_semiringInst_839_: *mut LeanObject,
    mut v_a_840_: *mut LeanObject,
    mut v_a_841_: *mut LeanObject,
    mut v_a_842_: *mut LeanObject,
    mut v_a_843_: *mut LeanObject,
    mut v_a_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
    mut v_a_846_: *mut LeanObject,
    mut v_a_847_: *mut LeanObject,
    mut v_a_848_: *mut LeanObject,
    mut v_a_849_: *mut LeanObject,
    mut v_a_850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_851_: *mut LeanObject = core::ptr::null_mut();
    v_res_851_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(
        v_u_837_,
        v_type_838_,
        v_semiringInst_839_,
        v_a_840_,
        v_a_841_,
        v_a_842_,
        v_a_843_,
        v_a_844_,
        v_a_845_,
        v_a_846_,
        v_a_847_,
        v_a_848_,
        v_a_849_,
    );
    lean_dec(v_a_849_);
    lean_dec_ref(v_a_848_);
    lean_dec(v_a_847_);
    lean_dec_ref(v_a_846_);
    lean_dec(v_a_845_);
    lean_dec_ref(v_a_844_);
    lean_dec(v_a_843_);
    lean_dec_ref(v_a_842_);
    lean_dec(v_a_841_);
    lean_dec(v_a_840_);
    return v_res_851_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0(
    mut v___x_853_: *mut LeanObject,
    mut v___x_854_: u8,
    mut v___x_855_: *mut LeanObject,
    mut v___x_856_: *mut LeanObject,
    mut v___x_857_: *mut LeanObject,
    mut v___x_858_: *mut LeanObject,
    mut v___x_859_: *mut LeanObject,
    mut v_type_860_: *mut LeanObject,
    mut v___y_861_: *mut LeanObject,
    mut v___y_862_: *mut LeanObject,
    mut v___y_863_: *mut LeanObject,
    mut v___y_864_: *mut LeanObject,
    mut v___y_865_: *mut LeanObject,
    mut v___y_866_: *mut LeanObject,
    mut v___y_867_: *mut LeanObject,
    mut v___y_868_: *mut LeanObject,
    mut v___y_869_: *mut LeanObject,
    mut v___y_870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v_val_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v_val_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_901_: u8 = 0;
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_910_: u8 = 0;
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_915_: u8 = 0;
    let mut v_a_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_919_: u8 = 0;
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_923_: u8 = 0;
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_928_: u8 = 0;
    let mut v_a_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_932_: u8 = 0;
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_936_: u8 = 0;
    let mut v_a_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_940_: u8 = 0;
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_944_: u8 = 0;
    let mut v_a_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___x_855_);
                v___x_872_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_853_, v___x_854_, v___x_855_, v___y_867_, v___y_868_, v___y_869_,
                    v___y_870_,
                );
                if lean_obj_tag(v___x_872_) == 0 {
                    v_a_873_ = lean_ctor_get(v___x_872_, 0);
                    lean_inc(v_a_873_);
                    lean_dec_ref_known(v___x_872_, 1);
                    v___x_874_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1;
                    v___x_875_ = l_Lean_mkConst(v___x_874_, v___x_856_);
                    v___x_876_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_876_, 0, v___x_875_);
                    v___x_877_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_876_, v___x_854_, v___x_855_, v___y_867_, v___y_868_, v___y_869_,
                        v___y_870_,
                    );
                    if lean_obj_tag(v___x_877_) == 0 {
                        v_a_878_ = lean_ctor_get(v___x_877_, 0);
                        lean_inc_n(v_a_878_, 2);
                        lean_dec_ref_known(v___x_877_, 1);
                        v___x_879_ =
                            l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0;
                        v___x_880_ = l_Lean_Name_mkStr3(v___x_857_, v___x_858_, v___x_879_);
                        v___x_881_ = l_Lean_mkConst(v___x_880_, v___x_859_);
                        lean_inc(v_a_873_);
                        v___x_882_ = l_Lean_mkApp3(v___x_881_, v_type_860_, v_a_873_, v_a_878_);
                        v___x_883_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                            v___x_882_, v___y_867_, v___y_868_, v___y_869_, v___y_870_,
                        );
                        if lean_obj_tag(v___x_883_) == 0 {
                            v_a_884_ = lean_ctor_get(v___x_883_, 0);
                            v_isSharedCheck_928_ = (!lean_is_exclusive(v___x_883_)) as u8;
                            if v_isSharedCheck_928_ == 0 {
                                v___x_886_ = v___x_883_;
                                v_isShared_887_ = v_isSharedCheck_928_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_884_);
                                lean_dec(v___x_883_);
                                v___x_886_ = lean_box(0);
                                v_isShared_887_ = v_isSharedCheck_928_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_878_);
                            lean_dec(v_a_873_);
                            v_a_929_ = lean_ctor_get(v___x_883_, 0);
                            v_isSharedCheck_936_ = (!lean_is_exclusive(v___x_883_)) as u8;
                            if v_isSharedCheck_936_ == 0 {
                                v___x_931_ = v___x_883_;
                                v_isShared_932_ = v_isSharedCheck_936_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_929_);
                                lean_dec(v___x_883_);
                                v___x_931_ = lean_box(0);
                                v_isShared_932_ = v_isSharedCheck_936_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_873_);
                        lean_dec_ref(v_type_860_);
                        lean_dec(v___x_859_);
                        lean_dec_ref(v___x_858_);
                        lean_dec_ref(v___x_857_);
                        v_a_937_ = lean_ctor_get(v___x_877_, 0);
                        v_isSharedCheck_944_ = (!lean_is_exclusive(v___x_877_)) as u8;
                        if v_isSharedCheck_944_ == 0 {
                            v___x_939_ = v___x_877_;
                            v_isShared_940_ = v_isSharedCheck_944_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_937_);
                            lean_dec(v___x_877_);
                            v___x_939_ = lean_box(0);
                            v_isShared_940_ = v_isSharedCheck_944_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_860_);
                    lean_dec(v___x_859_);
                    lean_dec_ref(v___x_858_);
                    lean_dec_ref(v___x_857_);
                    lean_dec(v___x_856_);
                    lean_dec(v___x_855_);
                    v_a_945_ = lean_ctor_get(v___x_872_, 0);
                    v_isSharedCheck_952_ = (!lean_is_exclusive(v___x_872_)) as u8;
                    if v_isSharedCheck_952_ == 0 {
                        v___x_947_ = v___x_872_;
                        v_isShared_948_ = v_isSharedCheck_952_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_945_);
                        lean_dec(v___x_872_);
                        v___x_947_ = lean_box(0);
                        v_isShared_948_ = v_isSharedCheck_952_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_884_) == 1 {
                    lean_del_object(v___x_886_);
                    v_val_888_ = lean_ctor_get(v_a_884_, 0);
                    lean_inc(v_val_888_);
                    lean_dec_ref_known(v_a_884_, 1);
                    v___x_889_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_873_, v___y_868_);
                    v_a_890_ = lean_ctor_get(v___x_889_, 0);
                    lean_inc(v_a_890_);
                    lean_dec_ref(v___x_889_);
                    v___x_891_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_878_, v___y_868_);
                    v_a_892_ = lean_ctor_get(v___x_891_, 0);
                    lean_inc(v_a_892_);
                    lean_dec_ref(v___x_891_);
                    v___x_893_ = l_Lean_Meta_Grind_Arith_evalNat_x3f(
                        v_a_892_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_,
                        v___y_867_, v___y_868_, v___y_869_, v___y_870_,
                    );
                    if lean_obj_tag(v___x_893_) == 0 {
                        v_a_894_ = lean_ctor_get(v___x_893_, 0);
                        v_isSharedCheck_915_ = (!lean_is_exclusive(v___x_893_)) as u8;
                        if v_isSharedCheck_915_ == 0 {
                            v___x_896_ = v___x_893_;
                            v_isShared_897_ = v_isSharedCheck_915_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_894_);
                            lean_dec(v___x_893_);
                            v___x_896_ = lean_box(0);
                            v_isShared_897_ = v_isSharedCheck_915_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_890_);
                        lean_dec(v_val_888_);
                        v_a_916_ = lean_ctor_get(v___x_893_, 0);
                        v_isSharedCheck_923_ = (!lean_is_exclusive(v___x_893_)) as u8;
                        if v_isSharedCheck_923_ == 0 {
                            v___x_918_ = v___x_893_;
                            v_isShared_919_ = v_isSharedCheck_923_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_916_);
                            lean_dec(v___x_893_);
                            v___x_918_ = lean_box(0);
                            v_isShared_919_ = v_isSharedCheck_923_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_884_);
                    lean_dec(v_a_878_);
                    lean_dec(v_a_873_);
                    v___x_924_ = lean_box(0);
                    if v_isShared_887_ == 0 {
                        lean_ctor_set(v___x_886_, 0, v___x_924_);
                        v___x_926_ = v___x_886_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
                        v___x_926_ = v_reuseFailAlloc_927_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_894_) == 1 {
                    v_val_898_ = lean_ctor_get(v_a_894_, 0);
                    v_isSharedCheck_910_ = (!lean_is_exclusive(v_a_894_)) as u8;
                    if v_isSharedCheck_910_ == 0 {
                        v___x_900_ = v_a_894_;
                        v_isShared_901_ = v_isSharedCheck_910_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_898_);
                        lean_dec(v_a_894_);
                        v___x_900_ = lean_box(0);
                        v_isShared_901_ = v_isSharedCheck_910_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_894_);
                    lean_dec(v_a_890_);
                    lean_dec(v_val_888_);
                    v___x_911_ = lean_box(0);
                    if v_isShared_897_ == 0 {
                        lean_ctor_set(v___x_896_, 0, v___x_911_);
                        v___x_913_ = v___x_896_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
                        v___x_913_ = v_reuseFailAlloc_914_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_902_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_902_, 0, v_a_890_);
                lean_ctor_set(v___x_902_, 1, v_val_898_);
                v___x_903_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_903_, 0, v_val_888_);
                lean_ctor_set(v___x_903_, 1, v___x_902_);
                if v_isShared_901_ == 0 {
                    lean_ctor_set(v___x_900_, 0, v___x_903_);
                    v___x_905_ = v___x_900_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_903_);
                    v___x_905_ = v_reuseFailAlloc_909_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_897_ == 0 {
                    lean_ctor_set(v___x_896_, 0, v___x_905_);
                    v___x_907_ = v___x_896_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
                    v___x_907_ = v_reuseFailAlloc_908_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_907_;
            }
            6 => {
                return v___x_913_;
            }
            7 => {
                if v_isShared_919_ == 0 {
                    v___x_921_ = v___x_918_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
                    v___x_921_ = v_reuseFailAlloc_922_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_921_;
            }
            9 => {
                return v___x_926_;
            }
            10 => {
                if v_isShared_932_ == 0 {
                    v___x_934_ = v___x_931_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
                    v___x_934_ = v_reuseFailAlloc_935_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_934_;
            }
            12 => {
                if v_isShared_940_ == 0 {
                    v___x_942_ = v___x_939_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
                    v___x_942_ = v_reuseFailAlloc_943_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_942_;
            }
            14 => {
                if v_isShared_948_ == 0 {
                    v___x_950_ = v___x_947_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
                    v___x_950_ = v_reuseFailAlloc_951_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_953_: *mut LeanObject = *_args.add(0);
    let mut v___x_954_: *mut LeanObject = *_args.add(1);
    let mut v___x_955_: *mut LeanObject = *_args.add(2);
    let mut v___x_956_: *mut LeanObject = *_args.add(3);
    let mut v___x_957_: *mut LeanObject = *_args.add(4);
    let mut v___x_958_: *mut LeanObject = *_args.add(5);
    let mut v___x_959_: *mut LeanObject = *_args.add(6);
    let mut v_type_960_: *mut LeanObject = *_args.add(7);
    let mut v___y_961_: *mut LeanObject = *_args.add(8);
    let mut v___y_962_: *mut LeanObject = *_args.add(9);
    let mut v___y_963_: *mut LeanObject = *_args.add(10);
    let mut v___y_964_: *mut LeanObject = *_args.add(11);
    let mut v___y_965_: *mut LeanObject = *_args.add(12);
    let mut v___y_966_: *mut LeanObject = *_args.add(13);
    let mut v___y_967_: *mut LeanObject = *_args.add(14);
    let mut v___y_968_: *mut LeanObject = *_args.add(15);
    let mut v___y_969_: *mut LeanObject = *_args.add(16);
    let mut v___y_970_: *mut LeanObject = *_args.add(17);
    let mut v___y_971_: *mut LeanObject = *_args.add(18);
    let mut v___x_6988__boxed_972_: u8 = 0;
    let mut v_res_973_: *mut LeanObject = core::ptr::null_mut();
    v___x_6988__boxed_972_ = (lean_unbox(v___x_954_) as u8);
    v_res_973_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0(
        v___x_953_,
        v___x_6988__boxed_972_,
        v___x_955_,
        v___x_956_,
        v___x_957_,
        v___x_958_,
        v___x_959_,
        v_type_960_,
        v___y_961_,
        v___y_962_,
        v___y_963_,
        v___y_964_,
        v___y_965_,
        v___y_966_,
        v___y_967_,
        v___y_968_,
        v___y_969_,
        v___y_970_,
    );
    lean_dec(v___y_970_);
    lean_dec_ref(v___y_969_);
    lean_dec(v___y_968_);
    lean_dec_ref(v___y_967_);
    lean_dec(v___y_966_);
    lean_dec_ref(v___y_965_);
    lean_dec(v___y_964_);
    lean_dec_ref(v___y_963_);
    lean_dec(v___y_962_);
    lean_dec(v___y_961_);
    return v_res_973_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(
    mut v_u_979_: *mut LeanObject,
    mut v_type_980_: *mut LeanObject,
    mut v_a_981_: *mut LeanObject,
    mut v_a_982_: *mut LeanObject,
    mut v_a_983_: *mut LeanObject,
    mut v_a_984_: *mut LeanObject,
    mut v_a_985_: *mut LeanObject,
    mut v_a_986_: *mut LeanObject,
    mut v_a_987_: *mut LeanObject,
    mut v_a_988_: *mut LeanObject,
    mut v_a_989_: *mut LeanObject,
    mut v_a_990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u8 = 0;
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    v___x_992_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0;
    v___x_993_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1;
    v___x_994_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1;
    v___x_995_ = lean_box(0);
    v___x_996_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_996_, 0, v_u_979_);
    lean_ctor_set(v___x_996_, 1, v___x_995_);
    lean_inc_ref(v___x_996_);
    v___x_997_ = l_Lean_mkConst(v___x_994_, v___x_996_);
    lean_inc_ref(v_type_980_);
    v___x_998_ = l_Lean_Expr_app___override(v___x_997_, v_type_980_);
    v___x_999_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_999_, 0, v___x_998_);
    v___x_1000_ = 0;
    v___x_1001_ = lean_box(0);
    v___x_1002_ = lean_box((v___x_1000_) as usize);
    v___f_1003_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___boxed as *mut core::ffi::c_void,
        19,
        8,
    );
    lean_closure_set(v___f_1003_, 0, v___x_999_);
    lean_closure_set(v___f_1003_, 1, v___x_1002_);
    lean_closure_set(v___f_1003_, 2, v___x_1001_);
    lean_closure_set(v___f_1003_, 3, v___x_995_);
    lean_closure_set(v___f_1003_, 4, v___x_992_);
    lean_closure_set(v___f_1003_, 5, v___x_993_);
    lean_closure_set(v___f_1003_, 6, v___x_996_);
    lean_closure_set(v___f_1003_, 7, v_type_980_);
    v___x_1004_ = 0;
    v___x_1005_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_1003_, v___x_1004_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
    return v___x_1005_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___boxed(
    mut v_u_1006_: *mut LeanObject,
    mut v_type_1007_: *mut LeanObject,
    mut v_a_1008_: *mut LeanObject,
    mut v_a_1009_: *mut LeanObject,
    mut v_a_1010_: *mut LeanObject,
    mut v_a_1011_: *mut LeanObject,
    mut v_a_1012_: *mut LeanObject,
    mut v_a_1013_: *mut LeanObject,
    mut v_a_1014_: *mut LeanObject,
    mut v_a_1015_: *mut LeanObject,
    mut v_a_1016_: *mut LeanObject,
    mut v_a_1017_: *mut LeanObject,
    mut v_a_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1019_: *mut LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(
        v_u_1006_,
        v_type_1007_,
        v_a_1008_,
        v_a_1009_,
        v_a_1010_,
        v_a_1011_,
        v_a_1012_,
        v_a_1013_,
        v_a_1014_,
        v_a_1015_,
        v_a_1016_,
        v_a_1017_,
    );
    lean_dec(v_a_1017_);
    lean_dec_ref(v_a_1016_);
    lean_dec(v_a_1015_);
    lean_dec_ref(v_a_1014_);
    lean_dec(v_a_1013_);
    lean_dec_ref(v_a_1012_);
    lean_dec(v_a_1011_);
    lean_dec_ref(v_a_1010_);
    lean_dec(v_a_1009_);
    lean_dec(v_a_1008_);
    return v_res_1019_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(
    mut v_u_1030_: *mut LeanObject,
    mut v_type_1031_: *mut LeanObject,
    mut v_a_1032_: *mut LeanObject,
    mut v_a_1033_: *mut LeanObject,
    mut v_a_1034_: *mut LeanObject,
    mut v_a_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natModuleType_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1046_: u8 = 0;
    let mut v_val_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1037_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1;
                v___x_1038_ = lean_box(0);
                v___x_1039_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1039_, 0, v_u_1030_);
                lean_ctor_set(v___x_1039_, 1, v___x_1038_);
                lean_inc_ref(v___x_1039_);
                v___x_1040_ = l_Lean_mkConst(v___x_1037_, v___x_1039_);
                lean_inc_ref(v_type_1031_);
                v_natModuleType_1041_ = l_Lean_Expr_app___override(v___x_1040_, v_type_1031_);
                v___x_1042_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_natModuleType_1041_,
                    v_a_1032_,
                    v_a_1033_,
                    v_a_1034_,
                    v_a_1035_,
                );
                if lean_obj_tag(v___x_1042_) == 0 {
                    v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
                    v_isSharedCheck_1056_ = (!lean_is_exclusive(v___x_1042_)) as u8;
                    if v_isSharedCheck_1056_ == 0 {
                        v___x_1045_ = v___x_1042_;
                        v_isShared_1046_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1043_);
                        lean_dec(v___x_1042_);
                        v___x_1045_ = lean_box(0);
                        v_isShared_1046_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_1039_, 2);
                    lean_dec_ref(v_type_1031_);
                    return v___x_1042_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_1043_) == 1 {
                    lean_del_object(v___x_1045_);
                    v_val_1047_ = lean_ctor_get(v_a_1043_, 0);
                    lean_inc(v_val_1047_);
                    lean_dec_ref_known(v_a_1043_, 1);
                    v___x_1048_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3;
                    v___x_1049_ = l_Lean_mkConst(v___x_1048_, v___x_1039_);
                    v___x_1050_ = l_Lean_mkAppB(v___x_1049_, v_type_1031_, v_val_1047_);
                    v___x_1051_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_1050_,
                        v_a_1032_,
                        v_a_1033_,
                        v_a_1034_,
                        v_a_1035_,
                    );
                    return v___x_1051_;
                } else {
                    lean_dec(v_a_1043_);
                    lean_dec_ref_known(v___x_1039_, 2);
                    lean_dec_ref(v_type_1031_);
                    v___x_1052_ = lean_box(0);
                    if v_isShared_1046_ == 0 {
                        lean_ctor_set(v___x_1045_, 0, v___x_1052_);
                        v___x_1054_ = v___x_1045_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
                        v___x_1054_ = v_reuseFailAlloc_1055_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___boxed(
    mut v_u_1057_: *mut LeanObject,
    mut v_type_1058_: *mut LeanObject,
    mut v_a_1059_: *mut LeanObject,
    mut v_a_1060_: *mut LeanObject,
    mut v_a_1061_: *mut LeanObject,
    mut v_a_1062_: *mut LeanObject,
    mut v_a_1063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1064_: *mut LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(
        v_u_1057_,
        v_type_1058_,
        v_a_1059_,
        v_a_1060_,
        v_a_1061_,
        v_a_1062_,
    );
    lean_dec(v_a_1062_);
    lean_dec_ref(v_a_1061_);
    lean_dec(v_a_1060_);
    lean_dec_ref(v_a_1059_);
    return v_res_1064_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(
    mut v_u_1065_: *mut LeanObject,
    mut v_type_1066_: *mut LeanObject,
    mut v_a_1067_: *mut LeanObject,
    mut v_a_1068_: *mut LeanObject,
    mut v_a_1069_: *mut LeanObject,
    mut v_a_1070_: *mut LeanObject,
    mut v_a_1071_: *mut LeanObject,
    mut v_a_1072_: *mut LeanObject,
    mut v_a_1073_: *mut LeanObject,
    mut v_a_1074_: *mut LeanObject,
    mut v_a_1075_: *mut LeanObject,
    mut v_a_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    v___x_1078_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(
        v_u_1065_,
        v_type_1066_,
        v_a_1073_,
        v_a_1074_,
        v_a_1075_,
        v_a_1076_,
    );
    return v___x_1078_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___boxed(
    mut v_u_1079_: *mut LeanObject,
    mut v_type_1080_: *mut LeanObject,
    mut v_a_1081_: *mut LeanObject,
    mut v_a_1082_: *mut LeanObject,
    mut v_a_1083_: *mut LeanObject,
    mut v_a_1084_: *mut LeanObject,
    mut v_a_1085_: *mut LeanObject,
    mut v_a_1086_: *mut LeanObject,
    mut v_a_1087_: *mut LeanObject,
    mut v_a_1088_: *mut LeanObject,
    mut v_a_1089_: *mut LeanObject,
    mut v_a_1090_: *mut LeanObject,
    mut v_a_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1092_: *mut LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(
        v_u_1079_,
        v_type_1080_,
        v_a_1081_,
        v_a_1082_,
        v_a_1083_,
        v_a_1084_,
        v_a_1085_,
        v_a_1086_,
        v_a_1087_,
        v_a_1088_,
        v_a_1089_,
        v_a_1090_,
    );
    lean_dec(v_a_1090_);
    lean_dec_ref(v_a_1089_);
    lean_dec(v_a_1088_);
    lean_dec_ref(v_a_1087_);
    lean_dec(v_a_1086_);
    lean_dec_ref(v_a_1085_);
    lean_dec(v_a_1084_);
    lean_dec_ref(v_a_1083_);
    lean_dec(v_a_1082_);
    lean_dec(v_a_1081_);
    return v_res_1092_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
}
