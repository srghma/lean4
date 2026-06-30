// Lean compiler output
// Module: Lean.Elab.Tactic.FalseOrByContra
// Imports: Lean.Elab.Tactic.Basic Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Intro
use crate::ffi::{
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_uint64_lor, lean_uint64_shift_left,
    lean_uint64_shift_right,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Syntax_isOfKind};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
    l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Tactic::Apply::{
    initialize_Lean_Meta_Tactic_Apply, l_Lean_MVarId_applyConst,
    runtime_initialize_Lean_Meta_Tactic_Apply,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::{
    initialize_Lean_Meta_Tactic_Intro, l_Lean_Meta_intro1Core,
    runtime_initialize_Lean_Meta_Tactic_Intro,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
pub static l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_falseOrByContra___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [70, 97, 108, 115, 101, 0],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_falseOrByContra___closed__1_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [101, 108, 105, 109, 0],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_MVarId_falseOrByContra___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__0_value)
                as *mut leanh::LeanObject,
            907667957179513571 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_falseOrByContra___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__1_value)
                as *mut leanh::LeanObject,
            3404330064793727539 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_falseOrByContra___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [16777472 as *mut leanh::LeanObject],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_falseOrByContra___closed__4_value: leanh::LeanStringObject<33> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 70, 97, 108,
            115, 101, 79, 114, 66, 121, 67, 111, 110, 116, 114, 97, 0,
        ],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_falseOrByContra___closed__5_value: leanh::LeanStringObject<28> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 101, 97, 110, 46, 77, 86, 97, 114, 73, 100, 46, 102, 97, 108, 115, 101, 79, 114,
            66, 121, 67, 111, 110, 116, 114, 97, 0,
        ],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_falseOrByContra___closed__6_value: leanh::LeanStringObject<28> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 116, 32, 109, 111, 115, 116, 32, 111,
            110, 101, 32, 115, 117, 103, 111, 97, 108, 0,
        ],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_falseOrByContra___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_falseOrByContra___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_falseOrByContra___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_falseOrByContra___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_falseOrByContra___closed__9_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [67, 108, 97, 115, 115, 105, 99, 97, 108, 0],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_falseOrByContra___closed__10_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_falseOrByContra___closed__11_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            98, 121, 67, 111, 110, 116, 114, 97, 100, 105, 99, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lean_MVarId_falseOrByContra___closed__12_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__10_value)
                as *mut leanh::LeanObject,
            4342836574150310743 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_falseOrByContra___closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__12_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__11_value)
                as *mut leanh::LeanObject,
            12625095907856970332 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__12_value)
        as *mut leanh::LeanObject;
static l_Lean_MVarId_falseOrByContra___closed__13_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__9_value)
                as *mut leanh::LeanObject,
            10854111772627758120 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_falseOrByContra___closed__13_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__13_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__11_value)
                as *mut leanh::LeanObject,
            3628558105408452239 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_falseOrByContra___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_falseOrByContra___closed__14: u64 = 0;
pub static l_Lean_MVarId_falseOrByContra___closed__15_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 111, 116, 0],
    };
static mut l_Lean_MVarId_falseOrByContra___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_falseOrByContra___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_elabFalseOrByContra___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_MVarId_elabFalseOrByContra___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_elabFalseOrByContra___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_MVarId_elabFalseOrByContra___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_elabFalseOrByContra___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_MVarId_elabFalseOrByContra___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_elabFalseOrByContra___closed__3_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            102, 97, 108, 115, 101, 79, 114, 66, 121, 67, 111, 110, 116, 114, 97, 0,
        ],
    };
static mut l_Lean_MVarId_elabFalseOrByContra___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_elabFalseOrByContra___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__3_value)
                as *mut leanh::LeanObject,
            9131313649144347253 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_elabFalseOrByContra___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_elabFalseOrByContra___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_elabFalseOrByContra___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [77, 86, 97, 114, 73, 100, 0]};
static mut l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 108, 97, 98, 70, 97, 108, 115, 101, 79, 114, 66, 121, 67, 111, 110, 116, 114, 97, 0]};
static mut l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_MVarId_elabFalseOrByContra___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value) as *mut leanh::LeanObject,5356933541775719089 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value) as *mut leanh::LeanObject,14939747291578792208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 62 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 64 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 62 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 62 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(
    mut v_msg_530_: *mut leanh::LeanObject,
    mut v___y_531_: *mut leanh::LeanObject,
    mut v___y_532_: *mut leanh::LeanObject,
    mut v___y_533_: *mut leanh::LeanObject,
    mut v___y_534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190__overap_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_536_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0;
    v___x_6190__overap_537_ = lean_panic_fn_borrowed(v___f_536_, v_msg_530_);
    leanh::lean_inc(v___y_534_);
    leanh::lean_inc_ref(v___y_533_);
    leanh::lean_inc(v___y_532_);
    leanh::lean_inc_ref(v___y_531_);
    v___x_538_ = leanh::lean_apply_5(
        v___x_6190__overap_537_,
        v___y_531_,
        v___y_532_,
        v___y_533_,
        v___y_534_,
        leanh::lean_box(0),
    );
    return v___x_538_;
}
pub unsafe fn l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___boxed(
    mut v_msg_539_: *mut leanh::LeanObject,
    mut v___y_540_: *mut leanh::LeanObject,
    mut v___y_541_: *mut leanh::LeanObject,
    mut v___y_542_: *mut leanh::LeanObject,
    mut v___y_543_: *mut leanh::LeanObject,
    mut v___y_544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_545_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(
        v_msg_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_,
    );
    leanh::lean_dec(v___y_543_);
    leanh::lean_dec_ref(v___y_542_);
    leanh::lean_dec(v___y_541_);
    leanh::lean_dec_ref(v___y_540_);
    return v_res_545_;
}
pub unsafe fn _init_l_Lean_MVarId_falseOrByContra___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_558_ = l_Lean_MVarId_falseOrByContra___closed__6;
    v___x_559_ = leanh::lean_unsigned_to_nat(13);
    v___x_560_ = leanh::lean_unsigned_to_nat(66);
    v___x_561_ = l_Lean_MVarId_falseOrByContra___closed__5;
    v___x_562_ = l_Lean_MVarId_falseOrByContra___closed__4;
    v___x_563_ =
        l_mkPanicMessageWithDecl(v___x_562_, v___x_561_, v___x_560_, v___x_559_, v___x_558_);
    return v___x_563_;
}
pub unsafe fn _init_l_Lean_MVarId_falseOrByContra___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = l_Lean_MVarId_falseOrByContra___closed__6;
    v___x_565_ = leanh::lean_unsigned_to_nat(16);
    v___x_566_ = leanh::lean_unsigned_to_nat(61);
    v___x_567_ = l_Lean_MVarId_falseOrByContra___closed__5;
    v___x_568_ = l_Lean_MVarId_falseOrByContra___closed__4;
    v___x_569_ =
        l_mkPanicMessageWithDecl(v___x_568_, v___x_567_, v___x_566_, v___x_565_, v___x_564_);
    return v___x_569_;
}
pub unsafe fn _init_l_Lean_MVarId_falseOrByContra___closed__14() -> u64 {
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: u64 = 0;
    v___x_579_ = 0;
    v___x_580_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_579_);
    return v___x_580_;
}
pub unsafe fn l_Lean_MVarId_falseOrByContra(
    mut v_g_582_: *mut leanh::LeanObject,
    mut v_useClassical_583_: *mut leanh::LeanObject,
    mut v_a_584_: *mut leanh::LeanObject,
    mut v_a_585_: *mut leanh::LeanObject,
    mut v_a_586_: *mut leanh::LeanObject,
    mut v_a_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v_tail_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_612_: u8 = 0;
    let mut v_a_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_616_: u8 = 0;
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_620_: u8 = 0;
    let mut v___y_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_627_: u8 = 0;
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: u8 = 0;
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_642_: u8 = 0;
    let mut v_snd_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_648_: u8 = 0;
    let mut v_a_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_652_: u8 = 0;
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_667_: u8 = 0;
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_675_: u8 = 0;
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_679_: u8 = 0;
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_687_: u8 = 0;
    let mut v___y_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: u8 = 0;
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: u8 = 0;
    let mut v___x_699_: u8 = 0;
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: u8 = 0;
    let mut v___x_702_: u8 = 0;
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: u8 = 0;
    let mut v___x_707_: u8 = 0;
    let mut v_val_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: u8 = 0;
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: u8 = 0;
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: u8 = 0;
    let mut v___x_714_: u8 = 0;
    let mut v___x_715_: u8 = 0;
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: u8 = 0;
    let mut v___x_720_: u8 = 0;
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: u8 = 0;
    let mut v___x_723_: u8 = 0;
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: u8 = 0;
    let mut v___x_726_: u8 = 0;
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_732_: u8 = 0;
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_736_: u8 = 0;
    let mut v_a_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_740_: u8 = 0;
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_744_: u8 = 0;
    let mut v_declName_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: u8 = 0;
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_755_: u8 = 0;
    let mut v_ctxApprox_756_: u8 = 0;
    let mut v_quasiPatternApprox_757_: u8 = 0;
    let mut v_constApprox_758_: u8 = 0;
    let mut v_isDefEqStuckEx_759_: u8 = 0;
    let mut v_unificationHints_760_: u8 = 0;
    let mut v_proofIrrelevance_761_: u8 = 0;
    let mut v_assignSyntheticOpaque_762_: u8 = 0;
    let mut v_offsetCnstrs_763_: u8 = 0;
    let mut v_etaStruct_764_: u8 = 0;
    let mut v_univApprox_765_: u8 = 0;
    let mut v_iota_766_: u8 = 0;
    let mut v_beta_767_: u8 = 0;
    let mut v_proj_768_: u8 = 0;
    let mut v_zeta_769_: u8 = 0;
    let mut v_zetaDelta_770_: u8 = 0;
    let mut v_zetaUnused_771_: u8 = 0;
    let mut v_zetaHave_772_: u8 = 0;
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_775_: u8 = 0;
    let mut v_trackZetaDelta_776_: u8 = 0;
    let mut v_zetaDeltaSet_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_783_: u8 = 0;
    let mut v_inTypeClassResolution_784_: u8 = 0;
    let mut v_cacheInferType_785_: u8 = 0;
    let mut v___x_786_: u8 = 0;
    let mut v_config_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: u64 = 0;
    let mut v___x_790_: u64 = 0;
    let mut v___x_791_: u64 = 0;
    let mut v___x_792_: u64 = 0;
    let mut v___x_793_: u64 = 0;
    let mut v_key_794_: u64 = 0;
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: u8 = 0;
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_805_: u8 = 0;
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_809_: u8 = 0;
    let mut v_reuseFailAlloc_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_811_: u8 = 0;
    let mut v_fn_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: u8 = 0;
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_819_: u8 = 0;
    let mut v_ctxApprox_820_: u8 = 0;
    let mut v_quasiPatternApprox_821_: u8 = 0;
    let mut v_constApprox_822_: u8 = 0;
    let mut v_isDefEqStuckEx_823_: u8 = 0;
    let mut v_unificationHints_824_: u8 = 0;
    let mut v_proofIrrelevance_825_: u8 = 0;
    let mut v_assignSyntheticOpaque_826_: u8 = 0;
    let mut v_offsetCnstrs_827_: u8 = 0;
    let mut v_etaStruct_828_: u8 = 0;
    let mut v_univApprox_829_: u8 = 0;
    let mut v_iota_830_: u8 = 0;
    let mut v_beta_831_: u8 = 0;
    let mut v_proj_832_: u8 = 0;
    let mut v_zeta_833_: u8 = 0;
    let mut v_zetaDelta_834_: u8 = 0;
    let mut v_zetaUnused_835_: u8 = 0;
    let mut v_zetaHave_836_: u8 = 0;
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_839_: u8 = 0;
    let mut v_trackZetaDelta_840_: u8 = 0;
    let mut v_zetaDeltaSet_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_847_: u8 = 0;
    let mut v_inTypeClassResolution_848_: u8 = 0;
    let mut v_cacheInferType_849_: u8 = 0;
    let mut v___x_850_: u8 = 0;
    let mut v_config_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: u64 = 0;
    let mut v___x_854_: u64 = 0;
    let mut v___x_855_: u64 = 0;
    let mut v___x_856_: u64 = 0;
    let mut v___x_857_: u64 = 0;
    let mut v_key_858_: u64 = 0;
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_868_: u8 = 0;
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut v_reuseFailAlloc_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut v_isSharedCheck_875_: u8 = 0;
    let mut v_a_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_879_: u8 = 0;
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_883_: u8 = 0;
    let mut v_a_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_g_582_);
                v___x_681_ =
                    l_Lean_MVarId_getType(v_g_582_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
                if leanh::lean_obj_tag(v___x_681_) == 0 {
                    v_a_682_ = leanh::lean_ctor_get(v___x_681_, 0);
                    leanh::lean_inc(v_a_682_);
                    leanh::lean_dec_ref_known(v___x_681_, 1);
                    v___x_683_ =
                        l_Lean_Meta_whnfR(v_a_682_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
                    if leanh::lean_obj_tag(v___x_683_) == 0 {
                        v_a_684_ = leanh::lean_ctor_get(v___x_683_, 0);
                        v_isSharedCheck_875_ = (!leanh::lean_is_exclusive(v___x_683_)) as u8;
                        if v_isSharedCheck_875_ == 0 {
                            v___x_686_ = v___x_683_;
                            v_isShared_687_ = v_isSharedCheck_875_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_684_);
                            leanh::lean_dec(v___x_683_);
                            v___x_686_ = leanh::lean_box(0);
                            v_isShared_687_ = v_isSharedCheck_875_;
                            state = 16;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_g_582_);
                        v_a_876_ = leanh::lean_ctor_get(v___x_683_, 0);
                        v_isSharedCheck_883_ = (!leanh::lean_is_exclusive(v___x_683_)) as u8;
                        if v_isSharedCheck_883_ == 0 {
                            v___x_878_ = v___x_683_;
                            v_isShared_879_ = v_isSharedCheck_883_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_876_);
                            leanh::lean_dec(v___x_683_);
                            v___x_878_ = leanh::lean_box(0);
                            v_isShared_879_ = v_isSharedCheck_883_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_g_582_);
                    v_a_884_ = leanh::lean_ctor_get(v___x_681_, 0);
                    v_isSharedCheck_891_ = (!leanh::lean_is_exclusive(v___x_681_)) as u8;
                    if v_isSharedCheck_891_ == 0 {
                        v___x_886_ = v___x_681_;
                        v_isShared_887_ = v_isSharedCheck_891_;
                        state = 33;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_884_);
                        leanh::lean_dec(v___x_681_);
                        v___x_886_ = leanh::lean_box(0);
                        v_isShared_887_ = v_isSharedCheck_891_;
                        state = 33;
                        continue;
                    }
                }
            }
            1 => {
                v___x_590_ = leanh::lean_box(0);
                v___x_591_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_591_, 0, v___x_590_);
                return v___x_591_;
            }
            2 => {
                v___x_597_ = l_Lean_MVarId_falseOrByContra___closed__2;
                v___x_598_ = l_Lean_MVarId_falseOrByContra___closed__3;
                v___x_599_ = l_Lean_MVarId_applyConst(
                    v_g_582_, v___x_597_, v___x_598_, v___y_593_, v___y_594_, v___y_595_,
                    v___y_596_,
                );
                if leanh::lean_obj_tag(v___x_599_) == 0 {
                    v_a_600_ = leanh::lean_ctor_get(v___x_599_, 0);
                    v_isSharedCheck_612_ = (!leanh::lean_is_exclusive(v___x_599_)) as u8;
                    if v_isSharedCheck_612_ == 0 {
                        v___x_602_ = v___x_599_;
                        v_isShared_603_ = v_isSharedCheck_612_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_600_);
                        leanh::lean_dec(v___x_599_);
                        v___x_602_ = leanh::lean_box(0);
                        v_isShared_603_ = v_isSharedCheck_612_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_613_ = leanh::lean_ctor_get(v___x_599_, 0);
                    v_isSharedCheck_620_ = (!leanh::lean_is_exclusive(v___x_599_)) as u8;
                    if v_isSharedCheck_620_ == 0 {
                        v___x_615_ = v___x_599_;
                        v_isShared_616_ = v_isSharedCheck_620_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_613_);
                        leanh::lean_dec(v___x_599_);
                        v___x_615_ = leanh::lean_box(0);
                        v_isShared_616_ = v_isSharedCheck_620_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_600_) == 0 {
                    leanh::lean_del_object(v___x_602_);
                    state = 1;
                    continue;
                } else {
                    v_tail_604_ = leanh::lean_ctor_get(v_a_600_, 1);
                    if leanh::lean_obj_tag(v_tail_604_) == 0 {
                        v_head_605_ = leanh::lean_ctor_get(v_a_600_, 0);
                        leanh::lean_inc(v_head_605_);
                        leanh::lean_dec_ref_known(v_a_600_, 2);
                        v___x_606_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_606_, 0, v_head_605_);
                        if v_isShared_603_ == 0 {
                            leanh::lean_ctor_set(v___x_602_, 0, v___x_606_);
                            v___x_608_ = v___x_602_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_609_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
                            v___x_608_ = v_reuseFailAlloc_609_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_600_, 2);
                        leanh::lean_del_object(v___x_602_);
                        v___x_610_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_falseOrByContra___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_falseOrByContra___closed__7_once),
                            _init_l_Lean_MVarId_falseOrByContra___closed__7,
                        );
                        v___x_611_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(
                            v___x_610_, v___y_593_, v___y_594_, v___y_595_, v___y_596_,
                        );
                        return v___x_611_;
                    }
                }
            }
            4 => {
                return v___x_608_;
            }
            5 => {
                if v_isShared_616_ == 0 {
                    v___x_618_ = v___x_615_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_619_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
                    v___x_618_ = v_reuseFailAlloc_619_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_618_;
            }
            7 => {
                if v___y_627_ == 0 {
                    leanh::lean_dec_ref(v___y_622_);
                    v___y_593_ = v___y_625_;
                    v___y_594_ = v___y_626_;
                    v___y_595_ = v___y_623_;
                    v___y_596_ = v___y_624_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_g_582_);
                    v___x_628_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_628_, 0, v___y_622_);
                    return v___x_628_;
                }
            }
            8 => {
                if leanh::lean_obj_tag(v_val_630_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_tail_635_ = leanh::lean_ctor_get(v_val_630_, 1);
                    if leanh::lean_obj_tag(v_tail_635_) == 0 {
                        v_head_636_ = leanh::lean_ctor_get(v_val_630_, 0);
                        leanh::lean_inc(v_head_636_);
                        leanh::lean_dec_ref_known(v_val_630_, 2);
                        v___x_637_ = 0;
                        v___x_638_ = l_Lean_Meta_intro1Core(
                            v_head_636_,
                            v___x_637_,
                            v___y_631_,
                            v___y_632_,
                            v___y_633_,
                            v___y_634_,
                        );
                        if leanh::lean_obj_tag(v___x_638_) == 0 {
                            v_a_639_ = leanh::lean_ctor_get(v___x_638_, 0);
                            v_isSharedCheck_648_ =
                                (!leanh::lean_is_exclusive(v___x_638_)) as u8;
                            if v_isSharedCheck_648_ == 0 {
                                v___x_641_ = v___x_638_;
                                v_isShared_642_ = v_isSharedCheck_648_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_639_);
                                leanh::lean_dec(v___x_638_);
                                v___x_641_ = leanh::lean_box(0);
                                v_isShared_642_ = v_isSharedCheck_648_;
                                state = 9;
                                continue;
                            }
                        } else {
                            v_a_649_ = leanh::lean_ctor_get(v___x_638_, 0);
                            v_isSharedCheck_656_ =
                                (!leanh::lean_is_exclusive(v___x_638_)) as u8;
                            if v_isSharedCheck_656_ == 0 {
                                v___x_651_ = v___x_638_;
                                v_isShared_652_ = v_isSharedCheck_656_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_649_);
                                leanh::lean_dec(v___x_638_);
                                v___x_651_ = leanh::lean_box(0);
                                v_isShared_652_ = v_isSharedCheck_656_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_val_630_, 2);
                        v___x_657_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_falseOrByContra___closed__8),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_falseOrByContra___closed__8_once),
                            _init_l_Lean_MVarId_falseOrByContra___closed__8,
                        );
                        v___x_658_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(
                            v___x_657_, v___y_631_, v___y_632_, v___y_633_, v___y_634_,
                        );
                        return v___x_658_;
                    }
                }
            }
            9 => {
                v_snd_643_ = leanh::lean_ctor_get(v_a_639_, 1);
                leanh::lean_inc(v_snd_643_);
                leanh::lean_dec(v_a_639_);
                v___x_644_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_644_, 0, v_snd_643_);
                if v_isShared_642_ == 0 {
                    leanh::lean_ctor_set(v___x_641_, 0, v___x_644_);
                    v___x_646_ = v___x_641_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_647_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
                    v___x_646_ = v_reuseFailAlloc_647_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_646_;
            }
            11 => {
                if v_isShared_652_ == 0 {
                    v___x_654_ = v___x_651_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_655_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
                    v___x_654_ = v_reuseFailAlloc_655_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_654_;
            }
            13 => {
                if v___y_667_ == 0 {
                    leanh::lean_dec_ref(v___y_665_);
                    v___x_668_ = l_Lean_MVarId_falseOrByContra___closed__9;
                    leanh::lean_inc_ref(v___y_666_);
                    v___x_669_ = l_Lean_Name_mkStr2(v___x_668_, v___y_666_);
                    v___x_670_ = l_Lean_MVarId_applyConst(
                        v_g_582_, v___x_669_, v___y_661_, v___y_663_, v___y_664_, v___y_660_,
                        v___y_662_,
                    );
                    if leanh::lean_obj_tag(v___x_670_) == 0 {
                        v_a_671_ = leanh::lean_ctor_get(v___x_670_, 0);
                        leanh::lean_inc(v_a_671_);
                        leanh::lean_dec_ref_known(v___x_670_, 1);
                        v_val_630_ = v_a_671_;
                        v___y_631_ = v___y_663_;
                        v___y_632_ = v___y_664_;
                        v___y_633_ = v___y_660_;
                        v___y_634_ = v___y_662_;
                        state = 8;
                        continue;
                    } else {
                        v_a_672_ = leanh::lean_ctor_get(v___x_670_, 0);
                        v_isSharedCheck_679_ = (!leanh::lean_is_exclusive(v___x_670_)) as u8;
                        if v_isSharedCheck_679_ == 0 {
                            v___x_674_ = v___x_670_;
                            v_isShared_675_ = v_isSharedCheck_679_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_672_);
                            leanh::lean_dec(v___x_670_);
                            v___x_674_ = leanh::lean_box(0);
                            v_isShared_675_ = v_isSharedCheck_679_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_661_);
                    leanh::lean_dec(v_g_582_);
                    v___x_680_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_680_, 0, v___y_665_);
                    return v___x_680_;
                }
            }
            14 => {
                if v_isShared_675_ == 0 {
                    v___x_677_ = v___x_674_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_678_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
                    v___x_677_ = v_reuseFailAlloc_678_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_677_;
            }
            16 => match leanh::lean_obj_tag(v_a_684_) {
                4 => {
                    v_declName_745_ = leanh::lean_ctor_get(v_a_684_, 0);
                    if leanh::lean_obj_tag(v_declName_745_) == 1 {
                        v_pre_746_ = leanh::lean_ctor_get(v_declName_745_, 0);
                        if leanh::lean_obj_tag(v_pre_746_) == 0 {
                            v_str_747_ = leanh::lean_ctor_get(v_declName_745_, 1);
                            v___x_748_ = l_Lean_MVarId_falseOrByContra___closed__0;
                            v___x_749_ = lean_string_dec_eq(v_str_747_, v___x_748_);
                            if v___x_749_ == 0 {
                                leanh::lean_del_object(v___x_686_);
                                v___y_689_ = v_a_584_;
                                v___y_690_ = v_a_585_;
                                v___y_691_ = v_a_586_;
                                v___y_692_ = v_a_587_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_a_684_, 2);
                                v___x_750_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_750_, 0, v_g_582_);
                                if v_isShared_687_ == 0 {
                                    leanh::lean_ctor_set(v___x_686_, 0, v___x_750_);
                                    v___x_752_ = v___x_686_;
                                    state = 22;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_753_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_753_,
                                        0,
                                        v___x_750_,
                                    );
                                    v___x_752_ = v_reuseFailAlloc_753_;
                                    state = 22;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_686_);
                            v___y_689_ = v_a_584_;
                            v___y_690_ = v_a_585_;
                            v___y_691_ = v_a_586_;
                            v___y_692_ = v_a_587_;
                            state = 17;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_686_);
                        v___y_689_ = v_a_584_;
                        v___y_690_ = v_a_585_;
                        v___y_691_ = v_a_586_;
                        v___y_692_ = v_a_587_;
                        state = 17;
                        continue;
                    }
                }
                7 => {
                    leanh::lean_dec_ref_known(v_a_684_, 3);
                    leanh::lean_del_object(v___x_686_);
                    v___x_754_ = l_Lean_Meta_Context_config(v_a_584_);
                    v_foApprox_755_ = leanh::lean_ctor_get_uint8(v___x_754_, 0 as u32);
                    v_ctxApprox_756_ = leanh::lean_ctor_get_uint8(v___x_754_, 1 as u32);
                    v_quasiPatternApprox_757_ =
                        leanh::lean_ctor_get_uint8(v___x_754_, 2 as u32);
                    v_constApprox_758_ = leanh::lean_ctor_get_uint8(v___x_754_, 3 as u32);
                    v_isDefEqStuckEx_759_ = leanh::lean_ctor_get_uint8(v___x_754_, 4 as u32);
                    v_unificationHints_760_ =
                        leanh::lean_ctor_get_uint8(v___x_754_, 5 as u32);
                    v_proofIrrelevance_761_ =
                        leanh::lean_ctor_get_uint8(v___x_754_, 6 as u32);
                    v_assignSyntheticOpaque_762_ =
                        leanh::lean_ctor_get_uint8(v___x_754_, 7 as u32);
                    v_offsetCnstrs_763_ = leanh::lean_ctor_get_uint8(v___x_754_, 8 as u32);
                    v_etaStruct_764_ = leanh::lean_ctor_get_uint8(v___x_754_, 10 as u32);
                    v_univApprox_765_ = leanh::lean_ctor_get_uint8(v___x_754_, 11 as u32);
                    v_iota_766_ = leanh::lean_ctor_get_uint8(v___x_754_, 12 as u32);
                    v_beta_767_ = leanh::lean_ctor_get_uint8(v___x_754_, 13 as u32);
                    v_proj_768_ = leanh::lean_ctor_get_uint8(v___x_754_, 14 as u32);
                    v_zeta_769_ = leanh::lean_ctor_get_uint8(v___x_754_, 15 as u32);
                    v_zetaDelta_770_ = leanh::lean_ctor_get_uint8(v___x_754_, 16 as u32);
                    v_zetaUnused_771_ = leanh::lean_ctor_get_uint8(v___x_754_, 17 as u32);
                    v_zetaHave_772_ = leanh::lean_ctor_get_uint8(v___x_754_, 18 as u32);
                    v_isSharedCheck_811_ = (!leanh::lean_is_exclusive(v___x_754_)) as u8;
                    if v_isSharedCheck_811_ == 0 {
                        v___x_774_ = v___x_754_;
                        v_isShared_775_ = v_isSharedCheck_811_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_754_);
                        v___x_774_ = leanh::lean_box(0);
                        v_isShared_775_ = v_isSharedCheck_811_;
                        state = 23;
                        continue;
                    }
                }
                5 => {
                    leanh::lean_del_object(v___x_686_);
                    v_fn_812_ = leanh::lean_ctor_get(v_a_684_, 0);
                    if leanh::lean_obj_tag(v_fn_812_) == 4 {
                        v_declName_813_ = leanh::lean_ctor_get(v_fn_812_, 0);
                        if leanh::lean_obj_tag(v_declName_813_) == 1 {
                            v_pre_814_ = leanh::lean_ctor_get(v_declName_813_, 0);
                            if leanh::lean_obj_tag(v_pre_814_) == 0 {
                                v_str_815_ = leanh::lean_ctor_get(v_declName_813_, 1);
                                v___x_816_ = l_Lean_MVarId_falseOrByContra___closed__15;
                                v___x_817_ = lean_string_dec_eq(v_str_815_, v___x_816_);
                                if v___x_817_ == 0 {
                                    v___y_689_ = v_a_584_;
                                    v___y_690_ = v_a_585_;
                                    v___y_691_ = v_a_586_;
                                    v___y_692_ = v_a_587_;
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref_known(v_a_684_, 2);
                                    v___x_818_ = l_Lean_Meta_Context_config(v_a_584_);
                                    v_foApprox_819_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 0 as u32);
                                    v_ctxApprox_820_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 1 as u32);
                                    v_quasiPatternApprox_821_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 2 as u32);
                                    v_constApprox_822_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 3 as u32);
                                    v_isDefEqStuckEx_823_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 4 as u32);
                                    v_unificationHints_824_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 5 as u32);
                                    v_proofIrrelevance_825_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 6 as u32);
                                    v_assignSyntheticOpaque_826_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 7 as u32);
                                    v_offsetCnstrs_827_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 8 as u32);
                                    v_etaStruct_828_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 10 as u32);
                                    v_univApprox_829_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 11 as u32);
                                    v_iota_830_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 12 as u32);
                                    v_beta_831_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 13 as u32);
                                    v_proj_832_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 14 as u32);
                                    v_zeta_833_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 15 as u32);
                                    v_zetaDelta_834_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 16 as u32);
                                    v_zetaUnused_835_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 17 as u32);
                                    v_zetaHave_836_ =
                                        leanh::lean_ctor_get_uint8(v___x_818_, 18 as u32);
                                    v_isSharedCheck_874_ =
                                        (!leanh::lean_is_exclusive(v___x_818_)) as u8;
                                    if v_isSharedCheck_874_ == 0 {
                                        v___x_838_ = v___x_818_;
                                        v_isShared_839_ = v_isSharedCheck_874_;
                                        state = 27;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_818_);
                                        v___x_838_ = leanh::lean_box(0);
                                        v_isShared_839_ = v_isSharedCheck_874_;
                                        state = 27;
                                        continue;
                                    }
                                }
                            } else {
                                v___y_689_ = v_a_584_;
                                v___y_690_ = v_a_585_;
                                v___y_691_ = v_a_586_;
                                v___y_692_ = v_a_587_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v___y_689_ = v_a_584_;
                            v___y_690_ = v_a_585_;
                            v___y_691_ = v_a_586_;
                            v___y_692_ = v_a_587_;
                            state = 17;
                            continue;
                        }
                    } else {
                        v___y_689_ = v_a_584_;
                        v___y_690_ = v_a_585_;
                        v___y_691_ = v_a_586_;
                        v___y_692_ = v_a_587_;
                        state = 17;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_del_object(v___x_686_);
                    v___y_689_ = v_a_584_;
                    v___y_690_ = v_a_585_;
                    v___y_691_ = v_a_586_;
                    v___y_692_ = v_a_587_;
                    state = 17;
                    continue;
                }
            },
            17 => {
                v___x_693_ =
                    l_Lean_Meta_isProp(v_a_684_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
                if leanh::lean_obj_tag(v___x_693_) == 0 {
                    v_a_694_ = leanh::lean_ctor_get(v___x_693_, 0);
                    leanh::lean_inc(v_a_694_);
                    leanh::lean_dec_ref_known(v___x_693_, 1);
                    v___x_695_ = (leanh::lean_unbox(v_a_694_) as u8);
                    if v___x_695_ == 0 {
                        leanh::lean_dec(v_a_694_);
                        v___y_593_ = v___y_689_;
                        v___y_594_ = v___y_690_;
                        v___y_595_ = v___y_691_;
                        v___y_596_ = v___y_692_;
                        state = 2;
                        continue;
                    } else {
                        if leanh::lean_obj_tag(v_useClassical_583_) == 0 {
                            v___x_696_ = l_Lean_MVarId_falseOrByContra___closed__11;
                            v___x_697_ = l_Lean_MVarId_falseOrByContra___closed__12;
                            v___x_698_ = 0;
                            v___x_699_ = 0;
                            v___x_700_ = leanh::lean_alloc_ctor(0, 0, (4) as u32);
                            leanh::lean_ctor_set_uint8(v___x_700_, 0 as u32, v___x_698_);
                            v___x_701_ = (leanh::lean_unbox(v_a_694_) as u8);
                            leanh::lean_ctor_set_uint8(v___x_700_, 1 as u32, v___x_701_);
                            leanh::lean_ctor_set_uint8(v___x_700_, 2 as u32, v___x_699_);
                            v___x_702_ = (leanh::lean_unbox(v_a_694_) as u8);
                            leanh::lean_dec(v_a_694_);
                            leanh::lean_ctor_set_uint8(v___x_700_, 3 as u32, v___x_702_);
                            leanh::lean_inc_ref(v___x_700_);
                            leanh::lean_inc(v_g_582_);
                            v___x_703_ = l_Lean_MVarId_applyConst(
                                v_g_582_, v___x_697_, v___x_700_, v___y_689_, v___y_690_,
                                v___y_691_, v___y_692_,
                            );
                            if leanh::lean_obj_tag(v___x_703_) == 0 {
                                leanh::lean_dec_ref_known(v___x_700_, 0);
                                leanh::lean_dec(v_g_582_);
                                v_a_704_ = leanh::lean_ctor_get(v___x_703_, 0);
                                leanh::lean_inc(v_a_704_);
                                leanh::lean_dec_ref_known(v___x_703_, 1);
                                v_val_630_ = v_a_704_;
                                v___y_631_ = v___y_689_;
                                v___y_632_ = v___y_690_;
                                v___y_633_ = v___y_691_;
                                v___y_634_ = v___y_692_;
                                state = 8;
                                continue;
                            } else {
                                v_a_705_ = leanh::lean_ctor_get(v___x_703_, 0);
                                leanh::lean_inc(v_a_705_);
                                leanh::lean_dec_ref_known(v___x_703_, 1);
                                v___x_706_ = l_Lean_Exception_isInterrupt(v_a_705_);
                                if v___x_706_ == 0 {
                                    leanh::lean_inc(v_a_705_);
                                    v___x_707_ = l_Lean_Exception_isRuntime(v_a_705_);
                                    v___y_660_ = v___y_691_;
                                    v___y_661_ = v___x_700_;
                                    v___y_662_ = v___y_692_;
                                    v___y_663_ = v___y_689_;
                                    v___y_664_ = v___y_690_;
                                    v___y_665_ = v_a_705_;
                                    v___y_666_ = v___x_696_;
                                    v___y_667_ = v___x_707_;
                                    state = 13;
                                    continue;
                                } else {
                                    v___y_660_ = v___y_691_;
                                    v___y_661_ = v___x_700_;
                                    v___y_662_ = v___y_692_;
                                    v___y_663_ = v___y_689_;
                                    v___y_664_ = v___y_690_;
                                    v___y_665_ = v_a_705_;
                                    v___y_666_ = v___x_696_;
                                    v___y_667_ = v___x_706_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            v_val_708_ = leanh::lean_ctor_get(v_useClassical_583_, 0);
                            v___x_709_ = (leanh::lean_unbox(v_val_708_) as u8);
                            if v___x_709_ == 0 {
                                v___x_710_ = l_Lean_MVarId_falseOrByContra___closed__12;
                                v___x_711_ = 0;
                                v___x_712_ = leanh::lean_alloc_ctor(0, 0, (4) as u32);
                                leanh::lean_ctor_set_uint8(v___x_712_, 0 as u32, v___x_711_);
                                v___x_713_ = (leanh::lean_unbox(v_a_694_) as u8);
                                leanh::lean_ctor_set_uint8(v___x_712_, 1 as u32, v___x_713_);
                                v___x_714_ = (leanh::lean_unbox(v_val_708_) as u8);
                                leanh::lean_ctor_set_uint8(v___x_712_, 2 as u32, v___x_714_);
                                v___x_715_ = (leanh::lean_unbox(v_a_694_) as u8);
                                leanh::lean_dec(v_a_694_);
                                leanh::lean_ctor_set_uint8(v___x_712_, 3 as u32, v___x_715_);
                                leanh::lean_inc(v_g_582_);
                                v___x_716_ = l_Lean_MVarId_applyConst(
                                    v_g_582_, v___x_710_, v___x_712_, v___y_689_, v___y_690_,
                                    v___y_691_, v___y_692_,
                                );
                                if leanh::lean_obj_tag(v___x_716_) == 0 {
                                    leanh::lean_dec(v_g_582_);
                                    v_a_717_ = leanh::lean_ctor_get(v___x_716_, 0);
                                    leanh::lean_inc(v_a_717_);
                                    leanh::lean_dec_ref_known(v___x_716_, 1);
                                    v_val_630_ = v_a_717_;
                                    v___y_631_ = v___y_689_;
                                    v___y_632_ = v___y_690_;
                                    v___y_633_ = v___y_691_;
                                    v___y_634_ = v___y_692_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_a_718_ = leanh::lean_ctor_get(v___x_716_, 0);
                                    leanh::lean_inc(v_a_718_);
                                    leanh::lean_dec_ref_known(v___x_716_, 1);
                                    v___x_719_ = l_Lean_Exception_isInterrupt(v_a_718_);
                                    if v___x_719_ == 0 {
                                        leanh::lean_inc(v_a_718_);
                                        v___x_720_ = l_Lean_Exception_isRuntime(v_a_718_);
                                        v___y_622_ = v_a_718_;
                                        v___y_623_ = v___y_691_;
                                        v___y_624_ = v___y_692_;
                                        v___y_625_ = v___y_689_;
                                        v___y_626_ = v___y_690_;
                                        v___y_627_ = v___x_720_;
                                        state = 7;
                                        continue;
                                    } else {
                                        v___y_622_ = v_a_718_;
                                        v___y_623_ = v___y_691_;
                                        v___y_624_ = v___y_692_;
                                        v___y_625_ = v___y_689_;
                                        v___y_626_ = v___y_690_;
                                        v___y_627_ = v___x_719_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_721_ = l_Lean_MVarId_falseOrByContra___closed__13;
                                v___x_722_ = 0;
                                v___x_723_ = 0;
                                v___x_724_ = leanh::lean_alloc_ctor(0, 0, (4) as u32);
                                leanh::lean_ctor_set_uint8(v___x_724_, 0 as u32, v___x_722_);
                                v___x_725_ = (leanh::lean_unbox(v_a_694_) as u8);
                                leanh::lean_ctor_set_uint8(v___x_724_, 1 as u32, v___x_725_);
                                leanh::lean_ctor_set_uint8(v___x_724_, 2 as u32, v___x_723_);
                                v___x_726_ = (leanh::lean_unbox(v_a_694_) as u8);
                                leanh::lean_dec(v_a_694_);
                                leanh::lean_ctor_set_uint8(v___x_724_, 3 as u32, v___x_726_);
                                v___x_727_ = l_Lean_MVarId_applyConst(
                                    v_g_582_, v___x_721_, v___x_724_, v___y_689_, v___y_690_,
                                    v___y_691_, v___y_692_,
                                );
                                if leanh::lean_obj_tag(v___x_727_) == 0 {
                                    v_a_728_ = leanh::lean_ctor_get(v___x_727_, 0);
                                    leanh::lean_inc(v_a_728_);
                                    leanh::lean_dec_ref_known(v___x_727_, 1);
                                    v_val_630_ = v_a_728_;
                                    v___y_631_ = v___y_689_;
                                    v___y_632_ = v___y_690_;
                                    v___y_633_ = v___y_691_;
                                    v___y_634_ = v___y_692_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_a_729_ = leanh::lean_ctor_get(v___x_727_, 0);
                                    v_isSharedCheck_736_ =
                                        (!leanh::lean_is_exclusive(v___x_727_)) as u8;
                                    if v_isSharedCheck_736_ == 0 {
                                        v___x_731_ = v___x_727_;
                                        v_isShared_732_ = v_isSharedCheck_736_;
                                        state = 18;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_729_);
                                        leanh::lean_dec(v___x_727_);
                                        v___x_731_ = leanh::lean_box(0);
                                        v_isShared_732_ = v_isSharedCheck_736_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_g_582_);
                    v_a_737_ = leanh::lean_ctor_get(v___x_693_, 0);
                    v_isSharedCheck_744_ = (!leanh::lean_is_exclusive(v___x_693_)) as u8;
                    if v_isSharedCheck_744_ == 0 {
                        v___x_739_ = v___x_693_;
                        v_isShared_740_ = v_isSharedCheck_744_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_737_);
                        leanh::lean_dec(v___x_693_);
                        v___x_739_ = leanh::lean_box(0);
                        v_isShared_740_ = v_isSharedCheck_744_;
                        state = 20;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_732_ == 0 {
                    v___x_734_ = v___x_731_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
                    v___x_734_ = v_reuseFailAlloc_735_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_734_;
            }
            20 => {
                if v_isShared_740_ == 0 {
                    v___x_742_ = v___x_739_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_743_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
                    v___x_742_ = v_reuseFailAlloc_743_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_742_;
            }
            22 => {
                return v___x_752_;
            }
            23 => {
                v_trackZetaDelta_776_ = leanh::lean_ctor_get_uint8(
                    v_a_584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_777_ = leanh::lean_ctor_get(v_a_584_, 1);
                v_lctx_778_ = leanh::lean_ctor_get(v_a_584_, 2);
                v_localInstances_779_ = leanh::lean_ctor_get(v_a_584_, 3);
                v_defEqCtx_x3f_780_ = leanh::lean_ctor_get(v_a_584_, 4);
                v_synthPendingDepth_781_ = leanh::lean_ctor_get(v_a_584_, 5);
                v_canUnfold_x3f_782_ = leanh::lean_ctor_get(v_a_584_, 6);
                v_univApprox_783_ = leanh::lean_ctor_get_uint8(
                    v_a_584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_784_ = leanh::lean_ctor_get_uint8(
                    v_a_584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_785_ = leanh::lean_ctor_get_uint8(
                    v_a_584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_786_ = 0;
                if v_isShared_775_ == 0 {
                    v_config_788_ = v___x_774_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_810_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        0 as u32,
                        v_foApprox_755_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        1 as u32,
                        v_ctxApprox_756_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        2 as u32,
                        v_quasiPatternApprox_757_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        3 as u32,
                        v_constApprox_758_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        4 as u32,
                        v_isDefEqStuckEx_759_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        5 as u32,
                        v_unificationHints_760_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        6 as u32,
                        v_proofIrrelevance_761_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        7 as u32,
                        v_assignSyntheticOpaque_762_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        8 as u32,
                        v_offsetCnstrs_763_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        10 as u32,
                        v_etaStruct_764_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        11 as u32,
                        v_univApprox_765_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        12 as u32,
                        v_iota_766_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        13 as u32,
                        v_beta_767_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        14 as u32,
                        v_proj_768_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        15 as u32,
                        v_zeta_769_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        16 as u32,
                        v_zetaDelta_770_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        17 as u32,
                        v_zetaUnused_771_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_810_,
                        18 as u32,
                        v_zetaHave_772_,
                    );
                    v_config_788_ = v_reuseFailAlloc_810_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                leanh::lean_ctor_set_uint8(v_config_788_, 9 as u32, v___x_786_);
                v___x_789_ = l_Lean_Meta_Context_configKey(v_a_584_);
                v___x_790_ = 3u64;
                v___x_791_ = lean_uint64_shift_right(v___x_789_, v___x_790_);
                v___x_792_ = lean_uint64_shift_left(v___x_791_, v___x_790_);
                v___x_793_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_falseOrByContra___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_falseOrByContra___closed__14_once),
                    _init_l_Lean_MVarId_falseOrByContra___closed__14,
                );
                v_key_794_ = lean_uint64_lor(v___x_792_, v___x_793_);
                v___x_795_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_795_, 0, v_config_788_);
                leanh::lean_ctor_set_uint64(
                    v___x_795_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_794_,
                );
                leanh::lean_inc(v_canUnfold_x3f_782_);
                leanh::lean_inc(v_synthPendingDepth_781_);
                leanh::lean_inc(v_defEqCtx_x3f_780_);
                leanh::lean_inc_ref(v_localInstances_779_);
                leanh::lean_inc_ref(v_lctx_778_);
                leanh::lean_inc(v_zetaDeltaSet_777_);
                v___x_796_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_796_, 0, v___x_795_);
                leanh::lean_ctor_set(v___x_796_, 1, v_zetaDeltaSet_777_);
                leanh::lean_ctor_set(v___x_796_, 2, v_lctx_778_);
                leanh::lean_ctor_set(v___x_796_, 3, v_localInstances_779_);
                leanh::lean_ctor_set(v___x_796_, 4, v_defEqCtx_x3f_780_);
                leanh::lean_ctor_set(v___x_796_, 5, v_synthPendingDepth_781_);
                leanh::lean_ctor_set(v___x_796_, 6, v_canUnfold_x3f_782_);
                leanh::lean_ctor_set_uint8(
                    v___x_796_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_776_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_796_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_783_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_796_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_784_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_796_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_785_,
                );
                v___x_797_ = 1;
                v___x_798_ = l_Lean_Meta_intro1Core(
                    v_g_582_, v___x_797_, v___x_796_, v_a_585_, v_a_586_, v_a_587_,
                );
                leanh::lean_dec_ref_known(v___x_796_, 7);
                if leanh::lean_obj_tag(v___x_798_) == 0 {
                    v_a_799_ = leanh::lean_ctor_get(v___x_798_, 0);
                    leanh::lean_inc(v_a_799_);
                    leanh::lean_dec_ref_known(v___x_798_, 1);
                    v_snd_800_ = leanh::lean_ctor_get(v_a_799_, 1);
                    leanh::lean_inc(v_snd_800_);
                    leanh::lean_dec(v_a_799_);
                    v_g_582_ = v_snd_800_;
                    state = 0;
                    continue;
                } else {
                    v_a_802_ = leanh::lean_ctor_get(v___x_798_, 0);
                    v_isSharedCheck_809_ = (!leanh::lean_is_exclusive(v___x_798_)) as u8;
                    if v_isSharedCheck_809_ == 0 {
                        v___x_804_ = v___x_798_;
                        v_isShared_805_ = v_isSharedCheck_809_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_802_);
                        leanh::lean_dec(v___x_798_);
                        v___x_804_ = leanh::lean_box(0);
                        v_isShared_805_ = v_isSharedCheck_809_;
                        state = 25;
                        continue;
                    }
                }
            }
            25 => {
                if v_isShared_805_ == 0 {
                    v___x_807_ = v___x_804_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_808_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
                    v___x_807_ = v_reuseFailAlloc_808_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_807_;
            }
            27 => {
                v_trackZetaDelta_840_ = leanh::lean_ctor_get_uint8(
                    v_a_584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_841_ = leanh::lean_ctor_get(v_a_584_, 1);
                v_lctx_842_ = leanh::lean_ctor_get(v_a_584_, 2);
                v_localInstances_843_ = leanh::lean_ctor_get(v_a_584_, 3);
                v_defEqCtx_x3f_844_ = leanh::lean_ctor_get(v_a_584_, 4);
                v_synthPendingDepth_845_ = leanh::lean_ctor_get(v_a_584_, 5);
                v_canUnfold_x3f_846_ = leanh::lean_ctor_get(v_a_584_, 6);
                v_univApprox_847_ = leanh::lean_ctor_get_uint8(
                    v_a_584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_848_ = leanh::lean_ctor_get_uint8(
                    v_a_584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_849_ = leanh::lean_ctor_get_uint8(
                    v_a_584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_850_ = 0;
                if v_isShared_839_ == 0 {
                    v_config_852_ = v___x_838_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_873_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        0 as u32,
                        v_foApprox_819_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        1 as u32,
                        v_ctxApprox_820_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        2 as u32,
                        v_quasiPatternApprox_821_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        3 as u32,
                        v_constApprox_822_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        4 as u32,
                        v_isDefEqStuckEx_823_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        5 as u32,
                        v_unificationHints_824_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        6 as u32,
                        v_proofIrrelevance_825_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        7 as u32,
                        v_assignSyntheticOpaque_826_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        8 as u32,
                        v_offsetCnstrs_827_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        10 as u32,
                        v_etaStruct_828_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        11 as u32,
                        v_univApprox_829_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        12 as u32,
                        v_iota_830_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        13 as u32,
                        v_beta_831_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        14 as u32,
                        v_proj_832_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        15 as u32,
                        v_zeta_833_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        16 as u32,
                        v_zetaDelta_834_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        17 as u32,
                        v_zetaUnused_835_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_873_,
                        18 as u32,
                        v_zetaHave_836_,
                    );
                    v_config_852_ = v_reuseFailAlloc_873_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                leanh::lean_ctor_set_uint8(v_config_852_, 9 as u32, v___x_850_);
                v___x_853_ = l_Lean_Meta_Context_configKey(v_a_584_);
                v___x_854_ = 3u64;
                v___x_855_ = lean_uint64_shift_right(v___x_853_, v___x_854_);
                v___x_856_ = lean_uint64_shift_left(v___x_855_, v___x_854_);
                v___x_857_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_falseOrByContra___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_falseOrByContra___closed__14_once),
                    _init_l_Lean_MVarId_falseOrByContra___closed__14,
                );
                v_key_858_ = lean_uint64_lor(v___x_856_, v___x_857_);
                v___x_859_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_859_, 0, v_config_852_);
                leanh::lean_ctor_set_uint64(
                    v___x_859_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_858_,
                );
                leanh::lean_inc(v_canUnfold_x3f_846_);
                leanh::lean_inc(v_synthPendingDepth_845_);
                leanh::lean_inc(v_defEqCtx_x3f_844_);
                leanh::lean_inc_ref(v_localInstances_843_);
                leanh::lean_inc_ref(v_lctx_842_);
                leanh::lean_inc(v_zetaDeltaSet_841_);
                v___x_860_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_860_, 0, v___x_859_);
                leanh::lean_ctor_set(v___x_860_, 1, v_zetaDeltaSet_841_);
                leanh::lean_ctor_set(v___x_860_, 2, v_lctx_842_);
                leanh::lean_ctor_set(v___x_860_, 3, v_localInstances_843_);
                leanh::lean_ctor_set(v___x_860_, 4, v_defEqCtx_x3f_844_);
                leanh::lean_ctor_set(v___x_860_, 5, v_synthPendingDepth_845_);
                leanh::lean_ctor_set(v___x_860_, 6, v_canUnfold_x3f_846_);
                leanh::lean_ctor_set_uint8(
                    v___x_860_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_840_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_860_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_847_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_860_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_848_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_860_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_849_,
                );
                v___x_861_ = l_Lean_Meta_intro1Core(
                    v_g_582_, v___x_817_, v___x_860_, v_a_585_, v_a_586_, v_a_587_,
                );
                leanh::lean_dec_ref_known(v___x_860_, 7);
                if leanh::lean_obj_tag(v___x_861_) == 0 {
                    v_a_862_ = leanh::lean_ctor_get(v___x_861_, 0);
                    leanh::lean_inc(v_a_862_);
                    leanh::lean_dec_ref_known(v___x_861_, 1);
                    v_snd_863_ = leanh::lean_ctor_get(v_a_862_, 1);
                    leanh::lean_inc(v_snd_863_);
                    leanh::lean_dec(v_a_862_);
                    v_g_582_ = v_snd_863_;
                    state = 0;
                    continue;
                } else {
                    v_a_865_ = leanh::lean_ctor_get(v___x_861_, 0);
                    v_isSharedCheck_872_ = (!leanh::lean_is_exclusive(v___x_861_)) as u8;
                    if v_isSharedCheck_872_ == 0 {
                        v___x_867_ = v___x_861_;
                        v_isShared_868_ = v_isSharedCheck_872_;
                        state = 29;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_865_);
                        leanh::lean_dec(v___x_861_);
                        v___x_867_ = leanh::lean_box(0);
                        v_isShared_868_ = v_isSharedCheck_872_;
                        state = 29;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_868_ == 0 {
                    v___x_870_ = v___x_867_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_871_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
                    v___x_870_ = v_reuseFailAlloc_871_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_870_;
            }
            31 => {
                if v_isShared_879_ == 0 {
                    v___x_881_ = v___x_878_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_882_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
                    v___x_881_ = v_reuseFailAlloc_882_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_881_;
            }
            33 => {
                if v_isShared_887_ == 0 {
                    v___x_889_ = v___x_886_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_890_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
                    v___x_889_ = v_reuseFailAlloc_890_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_falseOrByContra___boxed(
    mut v_g_892_: *mut leanh::LeanObject,
    mut v_useClassical_893_: *mut leanh::LeanObject,
    mut v_a_894_: *mut leanh::LeanObject,
    mut v_a_895_: *mut leanh::LeanObject,
    mut v_a_896_: *mut leanh::LeanObject,
    mut v_a_897_: *mut leanh::LeanObject,
    mut v_a_898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_899_ = l_Lean_MVarId_falseOrByContra(
        v_g_892_,
        v_useClassical_893_,
        v_a_894_,
        v_a_895_,
        v_a_896_,
        v_a_897_,
    );
    leanh::lean_dec(v_a_897_);
    leanh::lean_dec_ref(v_a_896_);
    leanh::lean_dec(v_a_895_);
    leanh::lean_dec_ref(v_a_894_);
    leanh::lean_dec(v_useClassical_893_);
    return v_res_899_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_900_ = leanh::lean_box(0);
    v___x_901_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_902_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_902_, 0, v___x_901_);
    leanh::lean_ctor_set(v___x_902_, 1, v___x_900_);
    return v___x_902_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_904_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0);
    v___x_905_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_905_, 0, v___x_904_);
    return v___x_905_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___boxed(
    mut v___y_906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_907_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
    return v_res_907_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(
    mut v_00_u03b1_908_: *mut leanh::LeanObject,
    mut v___y_909_: *mut leanh::LeanObject,
    mut v___y_910_: *mut leanh::LeanObject,
    mut v___y_911_: *mut leanh::LeanObject,
    mut v___y_912_: *mut leanh::LeanObject,
    mut v___y_913_: *mut leanh::LeanObject,
    mut v___y_914_: *mut leanh::LeanObject,
    mut v___y_915_: *mut leanh::LeanObject,
    mut v___y_916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
    return v___x_918_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___boxed(
    mut v_00_u03b1_919_: *mut leanh::LeanObject,
    mut v___y_920_: *mut leanh::LeanObject,
    mut v___y_921_: *mut leanh::LeanObject,
    mut v___y_922_: *mut leanh::LeanObject,
    mut v___y_923_: *mut leanh::LeanObject,
    mut v___y_924_: *mut leanh::LeanObject,
    mut v___y_925_: *mut leanh::LeanObject,
    mut v___y_926_: *mut leanh::LeanObject,
    mut v___y_927_: *mut leanh::LeanObject,
    mut v___y_928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_929_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(
            v_00_u03b1_919_,
            v___y_920_,
            v___y_921_,
            v___y_922_,
            v___y_923_,
            v___y_924_,
            v___y_925_,
            v___y_926_,
            v___y_927_,
        );
    leanh::lean_dec(v___y_927_);
    leanh::lean_dec_ref(v___y_926_);
    leanh::lean_dec(v___y_925_);
    leanh::lean_dec_ref(v___y_924_);
    leanh::lean_dec(v___y_923_);
    leanh::lean_dec_ref(v___y_922_);
    leanh::lean_dec(v___y_921_);
    leanh::lean_dec_ref(v___y_920_);
    return v_res_929_;
}
pub unsafe fn l_Lean_MVarId_elabFalseOrByContra___lam__0(
    mut v___y_930_: *mut leanh::LeanObject,
    mut v___y_931_: *mut leanh::LeanObject,
    mut v___y_932_: *mut leanh::LeanObject,
    mut v___y_933_: *mut leanh::LeanObject,
    mut v___y_934_: *mut leanh::LeanObject,
    mut v___y_935_: *mut leanh::LeanObject,
    mut v___y_936_: *mut leanh::LeanObject,
    mut v___y_937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_953_: u8 = 0;
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut v_a_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_965_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_939_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_931_, v___y_934_, v___y_935_, v___y_936_, v___y_937_,
                );
                if leanh::lean_obj_tag(v___x_939_) == 0 {
                    v_a_940_ = leanh::lean_ctor_get(v___x_939_, 0);
                    leanh::lean_inc(v_a_940_);
                    leanh::lean_dec_ref_known(v___x_939_, 1);
                    v___x_941_ = leanh::lean_box(0);
                    v___x_942_ = l_Lean_MVarId_falseOrByContra(
                        v_a_940_, v___x_941_, v___y_934_, v___y_935_, v___y_936_, v___y_937_,
                    );
                    if leanh::lean_obj_tag(v___x_942_) == 0 {
                        v_a_943_ = leanh::lean_ctor_get(v___x_942_, 0);
                        leanh::lean_inc(v_a_943_);
                        leanh::lean_dec_ref_known(v___x_942_, 1);
                        if leanh::lean_obj_tag(v_a_943_) == 1 {
                            v_val_944_ = leanh::lean_ctor_get(v_a_943_, 0);
                            leanh::lean_inc(v_val_944_);
                            leanh::lean_dec_ref_known(v_a_943_, 1);
                            v___x_945_ = leanh::lean_box(0);
                            v___x_946_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_946_, 0, v_val_944_);
                            leanh::lean_ctor_set(v___x_946_, 1, v___x_945_);
                            v___x_947_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v___x_946_, v___y_931_, v___y_934_, v___y_935_, v___y_936_,
                                v___y_937_,
                            );
                            return v___x_947_;
                        } else {
                            leanh::lean_dec(v_a_943_);
                            v___x_948_ = leanh::lean_box(0);
                            v___x_949_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v___x_948_, v___y_931_, v___y_934_, v___y_935_, v___y_936_,
                                v___y_937_,
                            );
                            return v___x_949_;
                        }
                    } else {
                        v_a_950_ = leanh::lean_ctor_get(v___x_942_, 0);
                        v_isSharedCheck_957_ = (!leanh::lean_is_exclusive(v___x_942_)) as u8;
                        if v_isSharedCheck_957_ == 0 {
                            v___x_952_ = v___x_942_;
                            v_isShared_953_ = v_isSharedCheck_957_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_950_);
                            leanh::lean_dec(v___x_942_);
                            v___x_952_ = leanh::lean_box(0);
                            v_isShared_953_ = v_isSharedCheck_957_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_958_ = leanh::lean_ctor_get(v___x_939_, 0);
                    v_isSharedCheck_965_ = (!leanh::lean_is_exclusive(v___x_939_)) as u8;
                    if v_isSharedCheck_965_ == 0 {
                        v___x_960_ = v___x_939_;
                        v_isShared_961_ = v_isSharedCheck_965_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_958_);
                        leanh::lean_dec(v___x_939_);
                        v___x_960_ = leanh::lean_box(0);
                        v_isShared_961_ = v_isSharedCheck_965_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_953_ == 0 {
                    v___x_955_ = v___x_952_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_956_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
                    v___x_955_ = v_reuseFailAlloc_956_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_955_;
            }
            3 => {
                if v_isShared_961_ == 0 {
                    v___x_963_ = v___x_960_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_964_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
                    v___x_963_ = v_reuseFailAlloc_964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_963_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed(
    mut v___y_966_: *mut leanh::LeanObject,
    mut v___y_967_: *mut leanh::LeanObject,
    mut v___y_968_: *mut leanh::LeanObject,
    mut v___y_969_: *mut leanh::LeanObject,
    mut v___y_970_: *mut leanh::LeanObject,
    mut v___y_971_: *mut leanh::LeanObject,
    mut v___y_972_: *mut leanh::LeanObject,
    mut v___y_973_: *mut leanh::LeanObject,
    mut v___y_974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_975_ = l_Lean_MVarId_elabFalseOrByContra___lam__0(
        v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_,
        v___y_973_,
    );
    leanh::lean_dec(v___y_973_);
    leanh::lean_dec_ref(v___y_972_);
    leanh::lean_dec(v___y_971_);
    leanh::lean_dec_ref(v___y_970_);
    leanh::lean_dec(v___y_969_);
    leanh::lean_dec_ref(v___y_968_);
    leanh::lean_dec(v___y_967_);
    leanh::lean_dec_ref(v___y_966_);
    return v_res_975_;
}
pub unsafe fn l_Lean_MVarId_elabFalseOrByContra(
    mut v_x_986_: *mut leanh::LeanObject,
    mut v_a_987_: *mut leanh::LeanObject,
    mut v_a_988_: *mut leanh::LeanObject,
    mut v_a_989_: *mut leanh::LeanObject,
    mut v_a_990_: *mut leanh::LeanObject,
    mut v_a_991_: *mut leanh::LeanObject,
    mut v_a_992_: *mut leanh::LeanObject,
    mut v_a_993_: *mut leanh::LeanObject,
    mut v_a_994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: u8 = 0;
    v___x_996_ = l_Lean_MVarId_elabFalseOrByContra___closed__4;
    v___x_997_ = l_Lean_Syntax_isOfKind(v_x_986_, v___x_996_);
    if v___x_997_ == 0 {
        let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_998_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
        return v___x_998_;
    } else {
        let mut v___f_999_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_999_ = l_Lean_MVarId_elabFalseOrByContra___closed__5;
        v___x_1000_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_999_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_,
            v_a_994_,
        );
        return v___x_1000_;
    }
}
pub unsafe fn l_Lean_MVarId_elabFalseOrByContra___boxed(
    mut v_x_1001_: *mut leanh::LeanObject,
    mut v_a_1002_: *mut leanh::LeanObject,
    mut v_a_1003_: *mut leanh::LeanObject,
    mut v_a_1004_: *mut leanh::LeanObject,
    mut v_a_1005_: *mut leanh::LeanObject,
    mut v_a_1006_: *mut leanh::LeanObject,
    mut v_a_1007_: *mut leanh::LeanObject,
    mut v_a_1008_: *mut leanh::LeanObject,
    mut v_a_1009_: *mut leanh::LeanObject,
    mut v_a_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1011_ = l_Lean_MVarId_elabFalseOrByContra(
        v_x_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_,
        v_a_1009_,
    );
    leanh::lean_dec(v_a_1009_);
    leanh::lean_dec_ref(v_a_1008_);
    leanh::lean_dec(v_a_1007_);
    leanh::lean_dec_ref(v_a_1006_);
    leanh::lean_dec(v_a_1005_);
    leanh::lean_dec_ref(v_a_1004_);
    leanh::lean_dec(v_a_1003_);
    leanh::lean_dec_ref(v_a_1002_);
    return v_res_1011_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1()
-> *mut leanh::LeanObject {
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1019_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1020_ = l_Lean_MVarId_elabFalseOrByContra___closed__4;
    v___x_1021_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2;
    v___x_1022_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_elabFalseOrByContra___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1023_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1019_,
        v___x_1020_,
        v___x_1021_,
        v___x_1022_,
    );
    return v___x_1023_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___boxed(
    mut v_a_1024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1025_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
    return v_res_1025_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2;
    v___x_1053_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6;
    v___x_1054_ = l_Lean_addBuiltinDeclarationRanges(v___x_1052_, v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___boxed(
    mut v_a_1055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
    return v_res_1056_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_FalseOrByContra(
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
pub unsafe fn initialize_Lean_Elab_Tactic_FalseOrByContra(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Apply(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Intro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
}