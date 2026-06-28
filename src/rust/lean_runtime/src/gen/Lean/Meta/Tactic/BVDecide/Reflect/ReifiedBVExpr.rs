// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVExpr
// Imports: Lean.Meta.Tactic.BVDecide.Reflect.Basic Std.Tactic.BVDecide.Reflect Lean.Meta.LitValues
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr5};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::LitValues::{
    initialize_Lean_Meta_LitValues, l_Lean_Meta_getBitVecValue_x3f, l_Lean_Meta_getNatValue_x3f,
    runtime_initialize_Lean_Meta_LitValues,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Basic::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic,
    l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment, l_Lean_Meta_Tactic_BVDecide_M_lookup,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    l_Std_Tactic_BVDecide_BVExpr_const___override, l_Std_Tactic_BVDecide_BVExpr_var___override,
};
use crate::r#gen::Std::Tactic::BVDecide::Reflect::{
    initialize_Std_Tactic_BVDecide_Reflect, runtime_initialize_Std_Tactic_BVDecide_Reflect,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [66, 86, 69, 120, 112, 114, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__4_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [101, 118, 97, 108, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1_value)
            as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2_value)
            as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3_value)
            as *mut LeanObject,
        14410340039599863083 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value: LeanCtorObject<
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__4_value)
            as *mut LeanObject,
        4945347208705483836 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__0_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [69, 113, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__1_value: LeanStringObject<
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
    m_data: [114, 101, 102, 108, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__0_value)
            as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__1_value
            ) as *mut LeanObject,
            13480818501600609864 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__6_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [66, 105, 116, 86, 101, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__6_value
            ) as *mut LeanObject,
            5394957827732845164 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__0_value: LeanStringObject<4> =
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
        m_data: [118, 97, 114, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_0: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0_value
            ) as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1_value
            ) as *mut LeanObject,
            5139300886809190733 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2_value
            ) as *mut LeanObject,
            17363264175708149920 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_3: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3_value
            ) as *mut LeanObject,
            14410340039599863083 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__0_value)
                as *mut LeanObject,
            10402728041249638302 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__3_value: LeanClosureObject<
    1,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 111, 110, 115, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__0_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1_value)
            as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2_value)
            as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3_value)
            as *mut LeanObject,
        14410340039599863083 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__0_value
        ) as *mut LeanObject,
        11927932611098301909 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__3_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [111, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__3_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__6_value)
            as *mut LeanObject,
        5394957827732845164 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4_value:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__3_value
        ) as *mut LeanObject,
        7578295756008745317 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6()
-> *mut LeanObject {
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    v___x_435_ = lean_box(0);
    v___x_436_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5;
    v___x_437_ = l_Lean_mkConst(v___x_436_, v___x_435_);
    return v___x_437_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
    mut v_w_438_: *mut LeanObject,
    mut v_expr_439_: *mut LeanObject,
    mut v_a_440_: *mut LeanObject,
    mut v_a_441_: *mut LeanObject,
    mut v_a_442_: *mut LeanObject,
    mut v_a_443_: *mut LeanObject,
    mut v_a_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_450_: u8 = 0;
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_446_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(
                    v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_,
                );
                if lean_obj_tag(v___x_446_) == 0 {
                    v_a_447_ = lean_ctor_get(v___x_446_, 0);
                    v_isSharedCheck_457_ = (!lean_is_exclusive(v___x_446_)) as u8;
                    if v_isSharedCheck_457_ == 0 {
                        v___x_449_ = v___x_446_;
                        v_isShared_450_ = v_isSharedCheck_457_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_447_);
                        lean_dec(v___x_446_);
                        v___x_449_ = lean_box(0);
                        v_isShared_450_ = v_isSharedCheck_457_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_expr_439_);
                    lean_dec(v_w_438_);
                    return v___x_446_;
                }
            }
            1 => {
                v___x_451_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6,
                );
                v___x_452_ = l_Lean_mkNatLit(v_w_438_);
                v___x_453_ = l_Lean_mkApp3(v___x_451_, v___x_452_, v_a_447_, v_expr_439_);
                if v_isShared_450_ == 0 {
                    lean_ctor_set(v___x_449_, 0, v___x_453_);
                    v___x_455_ = v___x_449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
                    v___x_455_ = v_reuseFailAlloc_456_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___boxed(
    mut v_w_458_: *mut LeanObject,
    mut v_expr_459_: *mut LeanObject,
    mut v_a_460_: *mut LeanObject,
    mut v_a_461_: *mut LeanObject,
    mut v_a_462_: *mut LeanObject,
    mut v_a_463_: *mut LeanObject,
    mut v_a_464_: *mut LeanObject,
    mut v_a_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_466_: *mut LeanObject = core::ptr::null_mut();
    v_res_466_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
        v_w_458_,
        v_expr_459_,
        v_a_460_,
        v_a_461_,
        v_a_462_,
        v_a_463_,
        v_a_464_,
    );
    lean_dec(v_a_464_);
    lean_dec_ref(v_a_463_);
    lean_dec(v_a_462_);
    lean_dec_ref(v_a_461_);
    lean_dec(v_a_460_);
    return v_res_466_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3()
-> *mut LeanObject {
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    v___x_472_ = lean_unsigned_to_nat(1);
    v___x_473_ = l_Lean_Level_ofNat(v___x_472_);
    return v___x_473_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4()
-> *mut LeanObject {
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    v___x_474_ = lean_box(0);
    v___x_475_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3,
    );
    v___x_476_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_476_, 0, v___x_475_);
    lean_ctor_set(v___x_476_, 1, v___x_474_);
    return v___x_476_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5()
-> *mut LeanObject {
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    v___x_477_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4,
    );
    v___x_478_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2;
    v___x_479_ = l_Lean_mkConst(v___x_478_, v___x_477_);
    return v___x_479_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8()
-> *mut LeanObject {
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    v___x_483_ = lean_box(0);
    v___x_484_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7;
    v___x_485_ = l_Lean_mkConst(v___x_484_, v___x_483_);
    return v___x_485_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(
    mut v_w_486_: *mut LeanObject,
    mut v_expr_487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    v___x_488_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5,
    );
    v___x_489_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8,
    );
    v___x_490_ = l_Lean_mkNatLit(v_w_486_);
    v___x_491_ = l_Lean_Expr_app___override(v___x_489_, v___x_490_);
    v___x_492_ = l_Lean_mkAppB(v___x_488_, v___x_491_, v_expr_487_);
    return v___x_492_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___lam__0(
    mut v___x_493_: *mut LeanObject,
    mut v___y_494_: *mut LeanObject,
    mut v___y_495_: *mut LeanObject,
    mut v___y_496_: *mut LeanObject,
    mut v___y_497_: *mut LeanObject,
    mut v___y_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    v___x_500_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_500_, 0, v___x_493_);
    return v___x_500_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___lam__0___boxed(
    mut v___x_501_: *mut LeanObject,
    mut v___y_502_: *mut LeanObject,
    mut v___y_503_: *mut LeanObject,
    mut v___y_504_: *mut LeanObject,
    mut v___y_505_: *mut LeanObject,
    mut v___y_506_: *mut LeanObject,
    mut v___y_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_508_: *mut LeanObject = core::ptr::null_mut();
    v_res_508_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___lam__0(
        v___x_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_,
    );
    lean_dec(v___y_506_);
    lean_dec_ref(v___y_505_);
    lean_dec(v___y_504_);
    lean_dec_ref(v___y_503_);
    lean_dec(v___y_502_);
    return v_res_508_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2() -> *mut LeanObject
{
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    v___x_516_ = lean_box(0);
    v___x_517_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1;
    v___x_518_ = l_Lean_mkConst(v___x_517_, v___x_516_);
    return v___x_518_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom(
    mut v_e_521_: *mut LeanObject,
    mut v_width_522_: *mut LeanObject,
    mut v_synthetic_523_: u8,
    mut v_a_524_: *mut LeanObject,
    mut v_a_525_: *mut LeanObject,
    mut v_a_526_: *mut LeanObject,
    mut v_a_527_: *mut LeanObject,
    mut v_a_528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_534_: u8 = 0;
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_545_: u8 = 0;
    let mut v_a_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_549_: u8 = 0;
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_553_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_width_522_);
                v___x_530_ = l_Lean_Meta_Tactic_BVDecide_M_lookup(
                    v_e_521_,
                    v_width_522_,
                    v_synthetic_523_,
                    v_a_524_,
                    v_a_525_,
                    v_a_526_,
                    v_a_527_,
                    v_a_528_,
                );
                if lean_obj_tag(v___x_530_) == 0 {
                    v_a_531_ = lean_ctor_get(v___x_530_, 0);
                    v_isSharedCheck_545_ = (!lean_is_exclusive(v___x_530_)) as u8;
                    if v_isSharedCheck_545_ == 0 {
                        v___x_533_ = v___x_530_;
                        v_isShared_534_ = v_isSharedCheck_545_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_531_);
                        lean_dec(v___x_530_);
                        v___x_533_ = lean_box(0);
                        v_isShared_534_ = v_isSharedCheck_545_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_width_522_);
                    v_a_546_ = lean_ctor_get(v___x_530_, 0);
                    v_isSharedCheck_553_ = (!lean_is_exclusive(v___x_530_)) as u8;
                    if v_isSharedCheck_553_ == 0 {
                        v___x_548_ = v___x_530_;
                        v_isShared_549_ = v_isSharedCheck_553_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_546_);
                        lean_dec(v___x_530_);
                        v___x_548_ = lean_box(0);
                        v_isShared_549_ = v_isSharedCheck_553_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_535_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2,
                );
                lean_inc_n(v_width_522_, 2);
                v___x_536_ = l_Lean_mkNatLit(v_width_522_);
                lean_inc(v_a_531_);
                v___x_537_ = l_Lean_mkNatLit(v_a_531_);
                v___x_538_ = l_Lean_mkAppB(v___x_535_, v___x_536_, v___x_537_);
                v___f_539_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__3;
                v___x_540_ = l_Std_Tactic_BVDecide_BVExpr_var___override(v_width_522_, v_a_531_);
                lean_inc_ref(v___x_538_);
                v___x_541_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_541_, 0, v_width_522_);
                lean_ctor_set(v___x_541_, 1, v___x_540_);
                lean_ctor_set(v___x_541_, 2, v___x_538_);
                lean_ctor_set(v___x_541_, 3, v___f_539_);
                lean_ctor_set(v___x_541_, 4, v___x_538_);
                if v_isShared_534_ == 0 {
                    lean_ctor_set(v___x_533_, 0, v___x_541_);
                    v___x_543_ = v___x_533_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
                    v___x_543_ = v_reuseFailAlloc_544_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_543_;
            }
            3 => {
                if v_isShared_549_ == 0 {
                    v___x_551_ = v___x_548_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
                    v___x_551_ = v_reuseFailAlloc_552_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_551_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___boxed(
    mut v_e_554_: *mut LeanObject,
    mut v_width_555_: *mut LeanObject,
    mut v_synthetic_556_: *mut LeanObject,
    mut v_a_557_: *mut LeanObject,
    mut v_a_558_: *mut LeanObject,
    mut v_a_559_: *mut LeanObject,
    mut v_a_560_: *mut LeanObject,
    mut v_a_561_: *mut LeanObject,
    mut v_a_562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthetic_boxed_563_: u8 = 0;
    let mut v_res_564_: *mut LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_563_ = (lean_unbox(v_synthetic_556_) as u8);
    v_res_564_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom(
        v_e_554_,
        v_width_555_,
        v_synthetic_boxed_563_,
        v_a_557_,
        v_a_558_,
        v_a_559_,
        v_a_560_,
        v_a_561_,
    );
    lean_dec(v_a_561_);
    lean_dec_ref(v_a_560_);
    lean_dec(v_a_559_);
    lean_dec_ref(v_a_558_);
    lean_dec(v_a_557_);
    return v_res_564_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(
    mut v_ty_568_: *mut LeanObject,
    mut v_expr_569_: *mut LeanObject,
    mut v_a_570_: *mut LeanObject,
    mut v_a_571_: *mut LeanObject,
    mut v_a_572_: *mut LeanObject,
    mut v_a_573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: u8 = 0;
    let mut v___x_583_: u8 = 0;
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_591_: u8 = 0;
    let mut v_val_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_595_: u8 = 0;
    let mut v_snd_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_603_: u8 = 0;
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_608_: u8 = 0;
    let mut v_a_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_612_: u8 = 0;
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_616_: u8 = 0;
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_621_: u8 = 0;
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_625_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_578_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_ty_568_, v_a_571_);
                if lean_obj_tag(v___x_578_) == 0 {
                    v_a_579_ = lean_ctor_get(v___x_578_, 0);
                    lean_inc(v_a_579_);
                    lean_dec_ref_known(v___x_578_, 1);
                    v___x_580_ = l_Lean_Expr_cleanupAnnotations(v_a_579_);
                    v___x_581_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1;
                    v___x_582_ = l_Lean_Expr_isConstOf(v___x_580_, v___x_581_);
                    if v___x_582_ == 0 {
                        v___x_583_ = l_Lean_Expr_isApp(v___x_580_);
                        if v___x_583_ == 0 {
                            lean_dec_ref(v___x_580_);
                            lean_dec_ref(v_expr_569_);
                            state = 1;
                            continue;
                        } else {
                            v___x_584_ = l_Lean_Expr_appFnCleanup___redArg(v___x_580_);
                            v___x_585_ =
                                l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7;
                            v___x_586_ = l_Lean_Expr_isConstOf(v___x_584_, v___x_585_);
                            lean_dec_ref(v___x_584_);
                            if v___x_586_ == 0 {
                                lean_dec_ref(v_expr_569_);
                                state = 1;
                                continue;
                            } else {
                                v___x_587_ = l_Lean_Meta_getBitVecValue_x3f(
                                    v_expr_569_,
                                    v_a_570_,
                                    v_a_571_,
                                    v_a_572_,
                                    v_a_573_,
                                );
                                if lean_obj_tag(v___x_587_) == 0 {
                                    v_a_588_ = lean_ctor_get(v___x_587_, 0);
                                    v_isSharedCheck_608_ = (!lean_is_exclusive(v___x_587_)) as u8;
                                    if v_isSharedCheck_608_ == 0 {
                                        v___x_590_ = v___x_587_;
                                        v_isShared_591_ = v_isSharedCheck_608_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_588_);
                                        lean_dec(v___x_587_);
                                        v___x_590_ = lean_box(0);
                                        v_isShared_591_ = v_isSharedCheck_608_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_a_609_ = lean_ctor_get(v___x_587_, 0);
                                    v_isSharedCheck_616_ = (!lean_is_exclusive(v___x_587_)) as u8;
                                    if v_isSharedCheck_616_ == 0 {
                                        v___x_611_ = v___x_587_;
                                        v_isShared_612_ = v_isSharedCheck_616_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_inc(v_a_609_);
                                        lean_dec(v___x_587_);
                                        v___x_611_ = lean_box(0);
                                        v_isShared_612_ = v_isSharedCheck_616_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_580_);
                        v___x_617_ = l_Lean_Meta_getNatValue_x3f(
                            v_expr_569_,
                            v_a_570_,
                            v_a_571_,
                            v_a_572_,
                            v_a_573_,
                        );
                        lean_dec_ref(v_expr_569_);
                        return v___x_617_;
                    }
                } else {
                    lean_dec_ref(v_expr_569_);
                    v_a_618_ = lean_ctor_get(v___x_578_, 0);
                    v_isSharedCheck_625_ = (!lean_is_exclusive(v___x_578_)) as u8;
                    if v_isSharedCheck_625_ == 0 {
                        v___x_620_ = v___x_578_;
                        v_isShared_621_ = v_isSharedCheck_625_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_618_);
                        lean_dec(v___x_578_);
                        v___x_620_ = lean_box(0);
                        v_isShared_621_ = v_isSharedCheck_625_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_576_ = lean_box(0);
                v___x_577_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_577_, 0, v___x_576_);
                return v___x_577_;
            }
            2 => {
                if lean_obj_tag(v_a_588_) == 1 {
                    v_val_592_ = lean_ctor_get(v_a_588_, 0);
                    v_isSharedCheck_603_ = (!lean_is_exclusive(v_a_588_)) as u8;
                    if v_isSharedCheck_603_ == 0 {
                        v___x_594_ = v_a_588_;
                        v_isShared_595_ = v_isSharedCheck_603_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_592_);
                        lean_dec(v_a_588_);
                        v___x_594_ = lean_box(0);
                        v_isShared_595_ = v_isSharedCheck_603_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_588_);
                    v___x_604_ = lean_box(0);
                    if v_isShared_591_ == 0 {
                        lean_ctor_set(v___x_590_, 0, v___x_604_);
                        v___x_606_ = v___x_590_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
                        v___x_606_ = v_reuseFailAlloc_607_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v_snd_596_ = lean_ctor_get(v_val_592_, 1);
                lean_inc(v_snd_596_);
                lean_dec(v_val_592_);
                if v_isShared_595_ == 0 {
                    lean_ctor_set(v___x_594_, 0, v_snd_596_);
                    v___x_598_ = v___x_594_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_602_, 0, v_snd_596_);
                    v___x_598_ = v_reuseFailAlloc_602_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_591_ == 0 {
                    lean_ctor_set(v___x_590_, 0, v___x_598_);
                    v___x_600_ = v___x_590_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
                    v___x_600_ = v_reuseFailAlloc_601_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_600_;
            }
            6 => {
                return v___x_606_;
            }
            7 => {
                if v_isShared_612_ == 0 {
                    v___x_614_ = v___x_611_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
                    v___x_614_ = v_reuseFailAlloc_615_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_614_;
            }
            9 => {
                if v_isShared_621_ == 0 {
                    v___x_623_ = v___x_620_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
                    v___x_623_ = v_reuseFailAlloc_624_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_623_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___boxed(
    mut v_ty_626_: *mut LeanObject,
    mut v_expr_627_: *mut LeanObject,
    mut v_a_628_: *mut LeanObject,
    mut v_a_629_: *mut LeanObject,
    mut v_a_630_: *mut LeanObject,
    mut v_a_631_: *mut LeanObject,
    mut v_a_632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_633_: *mut LeanObject = core::ptr::null_mut();
    v_res_633_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(
        v_ty_626_,
        v_expr_627_,
        v_a_628_,
        v_a_629_,
        v_a_630_,
        v_a_631_,
    );
    lean_dec(v_a_631_);
    lean_dec_ref(v_a_630_);
    lean_dec(v_a_629_);
    lean_dec_ref(v_a_628_);
    return v_res_633_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f(
    mut v_ty_634_: *mut LeanObject,
    mut v_expr_635_: *mut LeanObject,
    mut v_a_636_: *mut LeanObject,
    mut v_a_637_: *mut LeanObject,
    mut v_a_638_: *mut LeanObject,
    mut v_a_639_: *mut LeanObject,
    mut v_a_640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    v___x_642_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(
        v_ty_634_,
        v_expr_635_,
        v_a_637_,
        v_a_638_,
        v_a_639_,
        v_a_640_,
    );
    return v___x_642_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___boxed(
    mut v_ty_643_: *mut LeanObject,
    mut v_expr_644_: *mut LeanObject,
    mut v_a_645_: *mut LeanObject,
    mut v_a_646_: *mut LeanObject,
    mut v_a_647_: *mut LeanObject,
    mut v_a_648_: *mut LeanObject,
    mut v_a_649_: *mut LeanObject,
    mut v_a_650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_651_: *mut LeanObject = core::ptr::null_mut();
    v_res_651_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f(
        v_ty_643_,
        v_expr_644_,
        v_a_645_,
        v_a_646_,
        v_a_647_,
        v_a_648_,
        v_a_649_,
    );
    lean_dec(v_a_649_);
    lean_dec_ref(v_a_648_);
    lean_dec(v_a_647_);
    lean_dec_ref(v_a_646_);
    lean_dec(v_a_645_);
    return v_res_651_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom_spec__0___redArg(
    mut v_e_652_: *mut LeanObject,
    mut v___y_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_655_: u8 = 0;
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_669_: u8 = 0;
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_675_: u8 = 0;
    let mut v_unused_676_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_655_ = l_Lean_Expr_hasMVar(v_e_652_);
                if v___x_655_ == 0 {
                    v___x_656_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_656_, 0, v_e_652_);
                    return v___x_656_;
                } else {
                    v___x_657_ = lean_st_ref_get(v___y_653_);
                    v_mctx_658_ = lean_ctor_get(v___x_657_, 0);
                    lean_inc_ref(v_mctx_658_);
                    lean_dec(v___x_657_);
                    v___x_659_ = l_Lean_instantiateMVarsCore(v_mctx_658_, v_e_652_);
                    v_fst_660_ = lean_ctor_get(v___x_659_, 0);
                    lean_inc(v_fst_660_);
                    v_snd_661_ = lean_ctor_get(v___x_659_, 1);
                    lean_inc(v_snd_661_);
                    lean_dec_ref(v___x_659_);
                    v___x_662_ = lean_st_ref_take(v___y_653_);
                    v_cache_663_ = lean_ctor_get(v___x_662_, 1);
                    v_zetaDeltaFVarIds_664_ = lean_ctor_get(v___x_662_, 2);
                    v_postponed_665_ = lean_ctor_get(v___x_662_, 3);
                    v_diag_666_ = lean_ctor_get(v___x_662_, 4);
                    v_isSharedCheck_675_ = (!lean_is_exclusive(v___x_662_)) as u8;
                    if v_isSharedCheck_675_ == 0 {
                        v_unused_676_ = lean_ctor_get(v___x_662_, 0);
                        lean_dec(v_unused_676_);
                        v___x_668_ = v___x_662_;
                        v_isShared_669_ = v_isSharedCheck_675_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_666_);
                        lean_inc(v_postponed_665_);
                        lean_inc(v_zetaDeltaFVarIds_664_);
                        lean_inc(v_cache_663_);
                        lean_dec(v___x_662_);
                        v___x_668_ = lean_box(0);
                        v_isShared_669_ = v_isSharedCheck_675_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_669_ == 0 {
                    lean_ctor_set(v___x_668_, 0, v_snd_661_);
                    v___x_671_ = v___x_668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_674_, 0, v_snd_661_);
                    lean_ctor_set(v_reuseFailAlloc_674_, 1, v_cache_663_);
                    lean_ctor_set(v_reuseFailAlloc_674_, 2, v_zetaDeltaFVarIds_664_);
                    lean_ctor_set(v_reuseFailAlloc_674_, 3, v_postponed_665_);
                    lean_ctor_set(v_reuseFailAlloc_674_, 4, v_diag_666_);
                    v___x_671_ = v_reuseFailAlloc_674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_672_ = lean_st_ref_set(v___y_653_, v___x_671_);
                v___x_673_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_673_, 0, v_fst_660_);
                return v___x_673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom_spec__0___redArg___boxed(
    mut v_e_677_: *mut LeanObject,
    mut v___y_678_: *mut LeanObject,
    mut v___y_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_680_: *mut LeanObject = core::ptr::null_mut();
    v_res_680_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom_spec__0___redArg(v_e_677_, v___y_678_);
    lean_dec(v___y_678_);
    return v_res_680_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom_spec__0(
    mut v_e_681_: *mut LeanObject,
    mut v___y_682_: *mut LeanObject,
    mut v___y_683_: *mut LeanObject,
    mut v___y_684_: *mut LeanObject,
    mut v___y_685_: *mut LeanObject,
    mut v___y_686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    v___x_688_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom_spec__0___redArg(v_e_681_, v___y_684_);
    return v___x_688_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom_spec__0___boxed(
    mut v_e_689_: *mut LeanObject,
    mut v___y_690_: *mut LeanObject,
    mut v___y_691_: *mut LeanObject,
    mut v___y_692_: *mut LeanObject,
    mut v___y_693_: *mut LeanObject,
    mut v___y_694_: *mut LeanObject,
    mut v___y_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_696_: *mut LeanObject = core::ptr::null_mut();
    v_res_696_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom_spec__0(
            v_e_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_,
        );
    lean_dec(v___y_694_);
    lean_dec_ref(v___y_693_);
    lean_dec(v___y_692_);
    lean_dec_ref(v___y_691_);
    lean_dec(v___y_690_);
    return v_res_696_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(
    mut v_x_697_: *mut LeanObject,
    mut v_synthetic_698_: u8,
    mut v_a_699_: *mut LeanObject,
    mut v_a_700_: *mut LeanObject,
    mut v_a_701_: *mut LeanObject,
    mut v_a_702_: *mut LeanObject,
    mut v_a_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_713_: u8 = 0;
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: u8 = 0;
    let mut v_arg_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: u8 = 0;
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_729_: u8 = 0;
    let mut v_val_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_733_: u8 = 0;
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_738_: u8 = 0;
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_745_: u8 = 0;
    let mut v_a_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_749_: u8 = 0;
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_753_: u8 = 0;
    let mut v_isSharedCheck_754_: u8 = 0;
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_759_: u8 = 0;
    let mut v_a_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_763_: u8 = 0;
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_767_: u8 = 0;
    let mut v_isSharedCheck_768_: u8 = 0;
    let mut v_a_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_772_: u8 = 0;
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_776_: u8 = 0;
    let mut v_a_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_780_: u8 = 0;
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_703_);
                lean_inc_ref(v_a_702_);
                lean_inc(v_a_701_);
                lean_inc_ref(v_a_700_);
                lean_inc_ref(v_x_697_);
                v___x_705_ = lean_infer_type(v_x_697_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
                if lean_obj_tag(v___x_705_) == 0 {
                    v_a_706_ = lean_ctor_get(v___x_705_, 0);
                    lean_inc(v_a_706_);
                    lean_dec_ref_known(v___x_705_, 1);
                    v___x_707_ =
                        l_Lean_Meta_whnfR(v_a_706_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
                    if lean_obj_tag(v___x_707_) == 0 {
                        v_a_708_ = lean_ctor_get(v___x_707_, 0);
                        lean_inc(v_a_708_);
                        lean_dec_ref_known(v___x_707_, 1);
                        v___x_709_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom_spec__0___redArg(v_a_708_, v_a_701_);
                        v_a_710_ = lean_ctor_get(v___x_709_, 0);
                        v_isSharedCheck_768_ = (!lean_is_exclusive(v___x_709_)) as u8;
                        if v_isSharedCheck_768_ == 0 {
                            v___x_712_ = v___x_709_;
                            v_isShared_713_ = v_isSharedCheck_768_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_710_);
                            lean_dec(v___x_709_);
                            v___x_712_ = lean_box(0);
                            v_isShared_713_ = v_isSharedCheck_768_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_x_697_);
                        v_a_769_ = lean_ctor_get(v___x_707_, 0);
                        v_isSharedCheck_776_ = (!lean_is_exclusive(v___x_707_)) as u8;
                        if v_isSharedCheck_776_ == 0 {
                            v___x_771_ = v___x_707_;
                            v_isShared_772_ = v_isSharedCheck_776_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_769_);
                            lean_dec(v___x_707_);
                            v___x_771_ = lean_box(0);
                            v_isShared_772_ = v_isSharedCheck_776_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_697_);
                    v_a_777_ = lean_ctor_get(v___x_705_, 0);
                    v_isSharedCheck_784_ = (!lean_is_exclusive(v___x_705_)) as u8;
                    if v_isSharedCheck_784_ == 0 {
                        v___x_779_ = v___x_705_;
                        v_isShared_780_ = v_isSharedCheck_784_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_777_);
                        lean_dec(v___x_705_);
                        v___x_779_ = lean_box(0);
                        v_isShared_780_ = v_isSharedCheck_784_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_719_ = l_Lean_Expr_cleanupAnnotations(v_a_710_);
                v___x_720_ = l_Lean_Expr_isApp(v___x_719_);
                if v___x_720_ == 0 {
                    lean_dec_ref(v___x_719_);
                    lean_dec_ref(v_x_697_);
                    state = 2;
                    continue;
                } else {
                    v_arg_721_ = lean_ctor_get(v___x_719_, 1);
                    lean_inc_ref(v_arg_721_);
                    v___x_722_ = l_Lean_Expr_appFnCleanup___redArg(v___x_719_);
                    v___x_723_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7;
                    v___x_724_ = l_Lean_Expr_isConstOf(v___x_722_, v___x_723_);
                    lean_dec_ref(v___x_722_);
                    if v___x_724_ == 0 {
                        lean_dec_ref(v_arg_721_);
                        lean_dec_ref(v_x_697_);
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_712_);
                        v___x_725_ = l_Lean_Meta_getNatValue_x3f(
                            v_arg_721_, v_a_700_, v_a_701_, v_a_702_, v_a_703_,
                        );
                        lean_dec_ref(v_arg_721_);
                        if lean_obj_tag(v___x_725_) == 0 {
                            v_a_726_ = lean_ctor_get(v___x_725_, 0);
                            v_isSharedCheck_759_ = (!lean_is_exclusive(v___x_725_)) as u8;
                            if v_isSharedCheck_759_ == 0 {
                                v___x_728_ = v___x_725_;
                                v_isShared_729_ = v_isSharedCheck_759_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_726_);
                                lean_dec(v___x_725_);
                                v___x_728_ = lean_box(0);
                                v_isShared_729_ = v_isSharedCheck_759_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_x_697_);
                            v_a_760_ = lean_ctor_get(v___x_725_, 0);
                            v_isSharedCheck_767_ = (!lean_is_exclusive(v___x_725_)) as u8;
                            if v_isSharedCheck_767_ == 0 {
                                v___x_762_ = v___x_725_;
                                v_isShared_763_ = v_isSharedCheck_767_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_760_);
                                lean_dec(v___x_725_);
                                v___x_762_ = lean_box(0);
                                v_isShared_763_ = v_isSharedCheck_767_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_715_ = lean_box(0);
                if v_isShared_713_ == 0 {
                    lean_ctor_set(v___x_712_, 0, v___x_715_);
                    v___x_717_ = v___x_712_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
                    v___x_717_ = v_reuseFailAlloc_718_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_717_;
            }
            4 => {
                if lean_obj_tag(v_a_726_) == 1 {
                    lean_del_object(v___x_728_);
                    v_val_730_ = lean_ctor_get(v_a_726_, 0);
                    v_isSharedCheck_754_ = (!lean_is_exclusive(v_a_726_)) as u8;
                    if v_isSharedCheck_754_ == 0 {
                        v___x_732_ = v_a_726_;
                        v_isShared_733_ = v_isSharedCheck_754_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_730_);
                        lean_dec(v_a_726_);
                        v___x_732_ = lean_box(0);
                        v_isShared_733_ = v_isSharedCheck_754_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_a_726_);
                    lean_dec_ref(v_x_697_);
                    v___x_755_ = lean_box(0);
                    if v_isShared_729_ == 0 {
                        lean_ctor_set(v___x_728_, 0, v___x_755_);
                        v___x_757_ = v___x_728_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
                        v___x_757_ = v_reuseFailAlloc_758_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v___x_734_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom(
                    v_x_697_,
                    v_val_730_,
                    v_synthetic_698_,
                    v_a_699_,
                    v_a_700_,
                    v_a_701_,
                    v_a_702_,
                    v_a_703_,
                );
                if lean_obj_tag(v___x_734_) == 0 {
                    v_a_735_ = lean_ctor_get(v___x_734_, 0);
                    v_isSharedCheck_745_ = (!lean_is_exclusive(v___x_734_)) as u8;
                    if v_isSharedCheck_745_ == 0 {
                        v___x_737_ = v___x_734_;
                        v_isShared_738_ = v_isSharedCheck_745_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_735_);
                        lean_dec(v___x_734_);
                        v___x_737_ = lean_box(0);
                        v_isShared_738_ = v_isSharedCheck_745_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_732_);
                    v_a_746_ = lean_ctor_get(v___x_734_, 0);
                    v_isSharedCheck_753_ = (!lean_is_exclusive(v___x_734_)) as u8;
                    if v_isSharedCheck_753_ == 0 {
                        v___x_748_ = v___x_734_;
                        v_isShared_749_ = v_isSharedCheck_753_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_746_);
                        lean_dec(v___x_734_);
                        v___x_748_ = lean_box(0);
                        v_isShared_749_ = v_isSharedCheck_753_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_733_ == 0 {
                    lean_ctor_set(v___x_732_, 0, v_a_735_);
                    v___x_740_ = v___x_732_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_735_);
                    v___x_740_ = v_reuseFailAlloc_744_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_738_ == 0 {
                    lean_ctor_set(v___x_737_, 0, v___x_740_);
                    v___x_742_ = v___x_737_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
                    v___x_742_ = v_reuseFailAlloc_743_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_742_;
            }
            9 => {
                if v_isShared_749_ == 0 {
                    v___x_751_ = v___x_748_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
                    v___x_751_ = v_reuseFailAlloc_752_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_751_;
            }
            11 => {
                return v___x_757_;
            }
            12 => {
                if v_isShared_763_ == 0 {
                    v___x_765_ = v___x_762_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
                    v___x_765_ = v_reuseFailAlloc_766_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_765_;
            }
            14 => {
                if v_isShared_772_ == 0 {
                    v___x_774_ = v___x_771_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
                    v___x_774_ = v_reuseFailAlloc_775_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_774_;
            }
            16 => {
                if v_isShared_780_ == 0 {
                    v___x_782_ = v___x_779_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
                    v___x_782_ = v_reuseFailAlloc_783_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom___boxed(
    mut v_x_785_: *mut LeanObject,
    mut v_synthetic_786_: *mut LeanObject,
    mut v_a_787_: *mut LeanObject,
    mut v_a_788_: *mut LeanObject,
    mut v_a_789_: *mut LeanObject,
    mut v_a_790_: *mut LeanObject,
    mut v_a_791_: *mut LeanObject,
    mut v_a_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthetic_boxed_793_: u8 = 0;
    let mut v_res_794_: *mut LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_793_ = (lean_unbox(v_synthetic_786_) as u8);
    v_res_794_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(
        v_x_785_,
        v_synthetic_boxed_793_,
        v_a_787_,
        v_a_788_,
        v_a_789_,
        v_a_790_,
        v_a_791_,
    );
    lean_dec(v_a_791_);
    lean_dec_ref(v_a_790_);
    lean_dec(v_a_789_);
    lean_dec_ref(v_a_788_);
    lean_dec(v_a_787_);
    return v_res_794_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    v___x_802_ = lean_box(0);
    v___x_803_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1;
    v___x_804_ = l_Lean_mkConst(v___x_803_, v___x_802_);
    return v___x_804_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    v___x_809_ = lean_box(0);
    v___x_810_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4;
    v___x_811_ = l_Lean_Expr_const___override(v___x_810_, v___x_809_);
    return v___x_811_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(
    mut v_w_812_: *mut LeanObject,
    mut v_val_813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bvExpr_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_val_813_);
    lean_inc_n(v_w_812_, 2);
    v_bvExpr_815_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_812_, v_val_813_);
    v___x_816_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2,
    );
    v___x_817_ = l_Lean_mkNatLit(v_w_812_);
    v___x_818_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5,
    );
    v___x_819_ = l_Lean_mkNatLit(v_val_813_);
    lean_inc_ref(v___x_817_);
    v___x_820_ = l_Lean_mkAppB(v___x_818_, v___x_817_, v___x_819_);
    lean_inc_ref(v___x_820_);
    v_expr_821_ = l_Lean_mkAppB(v___x_816_, v___x_817_, v___x_820_);
    v_proof_822_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__3;
    v___x_823_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_823_, 0, v_w_812_);
    lean_ctor_set(v___x_823_, 1, v_bvExpr_815_);
    lean_ctor_set(v___x_823_, 2, v___x_820_);
    lean_ctor_set(v___x_823_, 3, v_proof_822_);
    lean_ctor_set(v___x_823_, 4, v_expr_821_);
    v___x_824_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_824_, 0, v___x_823_);
    return v___x_824_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___boxed(
    mut v_w_825_: *mut LeanObject,
    mut v_val_826_: *mut LeanObject,
    mut v_a_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_828_: *mut LeanObject = core::ptr::null_mut();
    v_res_828_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(v_w_825_, v_val_826_);
    return v_res_828_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst(
    mut v_w_829_: *mut LeanObject,
    mut v_val_830_: *mut LeanObject,
    mut v_a_831_: *mut LeanObject,
    mut v_a_832_: *mut LeanObject,
    mut v_a_833_: *mut LeanObject,
    mut v_a_834_: *mut LeanObject,
    mut v_a_835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    v___x_837_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(v_w_829_, v_val_830_);
    return v___x_837_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___boxed(
    mut v_w_838_: *mut LeanObject,
    mut v_val_839_: *mut LeanObject,
    mut v_a_840_: *mut LeanObject,
    mut v_a_841_: *mut LeanObject,
    mut v_a_842_: *mut LeanObject,
    mut v_a_843_: *mut LeanObject,
    mut v_a_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_846_: *mut LeanObject = core::ptr::null_mut();
    v_res_846_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst(
        v_w_838_, v_val_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_,
    );
    lean_dec(v_a_844_);
    lean_dec_ref(v_a_843_);
    lean_dec(v_a_842_);
    lean_dec_ref(v_a_841_);
    lean_dec(v_a_840_);
    return v_res_846_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Reflect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LitValues(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Reflect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_LitValues(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
}
