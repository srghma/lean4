// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Simp
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.MarkNestedSubsingletons Lean.Meta.Sym.Util
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Grind::Lemmas::{
    initialize_Init_Grind_Lemmas, runtime_initialize_Init_Grind_Lemmas,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_mkApp4, l_Lean_mkConst};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::Canon::l_Lean_Meta_Sym_canon;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_normalizeLevels,
    l_Lean_Meta_Sym_unfoldReducible, runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MarkNestedSubsingletons::{
    initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons,
    l_Lean_Meta_Grind_markNestedSubsingletons,
    runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MatchDiscrOnly::{
    initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly, l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly,
    runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_abstractNestedProofs___redArg,
    l_Lean_Meta_Grind_updateLastTag, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Util::{
    initialize_Lean_Meta_Tactic_Grind_Util, l_Lean_Meta_Grind_eraseIrrelevantMData,
    l_Lean_Meta_Grind_foldProjs, l_Lean_Meta_Grind_replacePreMatchCond,
    runtime_initialize_Lean_Meta_Tactic_Grind_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    initialize_Lean_Meta_Tactic_Simp_Main, l_Lean_Meta_Simp_dsimpMainCore,
    l_Lean_Meta_Simp_mainCore, runtime_initialize_Lean_Meta_Tactic_Simp_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_Result_mkEqTrans;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Profile::l_Lean_profileitIOUnsafe___redArg;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpCore___lam__0___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpCore___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [103, 114, 105, 110, 100, 32, 115, 105, 109, 112, 0],
    };
static mut l_Lean_Meta_Grind_simpCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_dsimpCore___closed__0_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [103, 114, 105, 110, 100, 32, 100, 115, 105, 109, 112, 0],
    };
static mut l_Lean_Meta_Grind_dsimpCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_dsimpCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0:
    f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_preprocessImpl___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [103, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_preprocessImpl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_preprocessImpl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_preprocessImpl___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [115, 105, 109, 112, 0],
    };
static mut l_Lean_Meta_Grind_preprocessImpl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_preprocessImpl___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_preprocessImpl___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_preprocessImpl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15947788021050471391 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_preprocessImpl___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_preprocessImpl___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_preprocessImpl___closed__1_value)
                as *mut crate::leanh::LeanObject,
            16551112126483115663 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_preprocessImpl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_preprocessImpl___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_preprocessImpl___closed__3_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Meta_Grind_preprocessImpl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_preprocessImpl___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_preprocessImpl___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_preprocessImpl___closed__3_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_preprocessImpl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_preprocessImpl___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_preprocessImpl___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_preprocessImpl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_preprocessImpl___closed__6_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [10, 61, 61, 61, 62, 10, 0],
    };
static mut l_Lean_Meta_Grind_preprocessImpl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_preprocessImpl___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_preprocessImpl___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_preprocessImpl___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNewFact_x27___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [100, 101, 98, 117, 103, 0],
    };
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNewFact_x27___closed__1_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [112, 117, 115, 104, 78, 101, 119, 70, 97, 99, 116, 0],
    };
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_preprocessImpl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15947788021050471391 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5637236024813792860 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__1_value)
                as *mut crate::leanh::LeanObject,
            7666958742445354398 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNewFact_x27___closed__4_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [32, 61, 61, 62, 32, 0],
    };
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNewFact_x27___closed__6_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNewFact_x27___closed__7_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [109, 112, 0],
    };
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNewFact_x27___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__6_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNewFact_x27___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__8_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__7_value)
                as *mut crate::leanh::LeanObject,
            5647098122476602039 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNewFact_x27___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNewFact_x27___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNewFact_x27___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(
    mut v_category_922_: *mut crate::leanh::LeanObject,
    mut v_opts_923_: *mut crate::leanh::LeanObject,
    mut v_act_924_: *mut crate::leanh::LeanObject,
    mut v_decl_925_: *mut crate::leanh::LeanObject,
    mut v___y_926_: *mut crate::leanh::LeanObject,
    mut v___y_927_: *mut crate::leanh::LeanObject,
    mut v___y_928_: *mut crate::leanh::LeanObject,
    mut v___y_929_: *mut crate::leanh::LeanObject,
    mut v___y_930_: *mut crate::leanh::LeanObject,
    mut v___y_931_: *mut crate::leanh::LeanObject,
    mut v___y_932_: *mut crate::leanh::LeanObject,
    mut v___y_933_: *mut crate::leanh::LeanObject,
    mut v___y_934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_934_);
    crate::leanh::lean_inc_ref(v___y_933_);
    crate::leanh::lean_inc(v___y_932_);
    crate::leanh::lean_inc_ref(v___y_931_);
    crate::leanh::lean_inc(v___y_930_);
    crate::leanh::lean_inc_ref(v___y_929_);
    crate::leanh::lean_inc(v___y_928_);
    crate::leanh::lean_inc_ref(v___y_927_);
    crate::leanh::lean_inc(v___y_926_);
    v___x_936_ = crate::leanh::lean_apply_9(
        v_act_924_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_,
        v___y_932_, v___y_933_, v___y_934_,
    );
    v___x_937_ =
        l_Lean_profileitIOUnsafe___redArg(v_category_922_, v_opts_923_, v___x_936_, v_decl_925_);
    return v___x_937_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg___boxed(
    mut v_category_938_: *mut crate::leanh::LeanObject,
    mut v_opts_939_: *mut crate::leanh::LeanObject,
    mut v_act_940_: *mut crate::leanh::LeanObject,
    mut v_decl_941_: *mut crate::leanh::LeanObject,
    mut v___y_942_: *mut crate::leanh::LeanObject,
    mut v___y_943_: *mut crate::leanh::LeanObject,
    mut v___y_944_: *mut crate::leanh::LeanObject,
    mut v___y_945_: *mut crate::leanh::LeanObject,
    mut v___y_946_: *mut crate::leanh::LeanObject,
    mut v___y_947_: *mut crate::leanh::LeanObject,
    mut v___y_948_: *mut crate::leanh::LeanObject,
    mut v___y_949_: *mut crate::leanh::LeanObject,
    mut v___y_950_: *mut crate::leanh::LeanObject,
    mut v___y_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_952_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(
        v_category_938_,
        v_opts_939_,
        v_act_940_,
        v_decl_941_,
        v___y_942_,
        v___y_943_,
        v___y_944_,
        v___y_945_,
        v___y_946_,
        v___y_947_,
        v___y_948_,
        v___y_949_,
        v___y_950_,
    );
    crate::leanh::lean_dec(v___y_950_);
    crate::leanh::lean_dec_ref(v___y_949_);
    crate::leanh::lean_dec(v___y_948_);
    crate::leanh::lean_dec_ref(v___y_947_);
    crate::leanh::lean_dec(v___y_946_);
    crate::leanh::lean_dec_ref(v___y_945_);
    crate::leanh::lean_dec(v___y_944_);
    crate::leanh::lean_dec_ref(v___y_943_);
    crate::leanh::lean_dec(v___y_942_);
    crate::leanh::lean_dec_ref(v_opts_939_);
    crate::leanh::lean_dec_ref(v_category_938_);
    return v_res_952_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0(
    mut v_00_u03b1_953_: *mut crate::leanh::LeanObject,
    mut v_category_954_: *mut crate::leanh::LeanObject,
    mut v_opts_955_: *mut crate::leanh::LeanObject,
    mut v_act_956_: *mut crate::leanh::LeanObject,
    mut v_decl_957_: *mut crate::leanh::LeanObject,
    mut v___y_958_: *mut crate::leanh::LeanObject,
    mut v___y_959_: *mut crate::leanh::LeanObject,
    mut v___y_960_: *mut crate::leanh::LeanObject,
    mut v___y_961_: *mut crate::leanh::LeanObject,
    mut v___y_962_: *mut crate::leanh::LeanObject,
    mut v___y_963_: *mut crate::leanh::LeanObject,
    mut v___y_964_: *mut crate::leanh::LeanObject,
    mut v___y_965_: *mut crate::leanh::LeanObject,
    mut v___y_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_968_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(
        v_category_954_,
        v_opts_955_,
        v_act_956_,
        v_decl_957_,
        v___y_958_,
        v___y_959_,
        v___y_960_,
        v___y_961_,
        v___y_962_,
        v___y_963_,
        v___y_964_,
        v___y_965_,
        v___y_966_,
    );
    return v___x_968_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___boxed(
    mut v_00_u03b1_969_: *mut crate::leanh::LeanObject,
    mut v_category_970_: *mut crate::leanh::LeanObject,
    mut v_opts_971_: *mut crate::leanh::LeanObject,
    mut v_act_972_: *mut crate::leanh::LeanObject,
    mut v_decl_973_: *mut crate::leanh::LeanObject,
    mut v___y_974_: *mut crate::leanh::LeanObject,
    mut v___y_975_: *mut crate::leanh::LeanObject,
    mut v___y_976_: *mut crate::leanh::LeanObject,
    mut v___y_977_: *mut crate::leanh::LeanObject,
    mut v___y_978_: *mut crate::leanh::LeanObject,
    mut v___y_979_: *mut crate::leanh::LeanObject,
    mut v___y_980_: *mut crate::leanh::LeanObject,
    mut v___y_981_: *mut crate::leanh::LeanObject,
    mut v___y_982_: *mut crate::leanh::LeanObject,
    mut v___y_983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0(
        v_00_u03b1_969_,
        v_category_970_,
        v_opts_971_,
        v_act_972_,
        v_decl_973_,
        v___y_974_,
        v___y_975_,
        v___y_976_,
        v___y_977_,
        v___y_978_,
        v___y_979_,
        v___y_980_,
        v___y_981_,
        v___y_982_,
    );
    crate::leanh::lean_dec(v___y_982_);
    crate::leanh::lean_dec_ref(v___y_981_);
    crate::leanh::lean_dec(v___y_980_);
    crate::leanh::lean_dec_ref(v___y_979_);
    crate::leanh::lean_dec(v___y_978_);
    crate::leanh::lean_dec_ref(v___y_977_);
    crate::leanh::lean_dec(v___y_976_);
    crate::leanh::lean_dec_ref(v___y_975_);
    crate::leanh::lean_dec(v___y_974_);
    crate::leanh::lean_dec_ref(v_opts_971_);
    crate::leanh::lean_dec_ref(v_category_970_);
    return v_res_984_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = crate::leanh::lean_box(0);
    v___x_986_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_987_ = lean_mk_array(v___x_986_, v___x_985_);
    return v___x_987_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__0_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__0,
    );
    v___x_989_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_990_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_990_, 0, v___x_989_);
    crate::leanh::lean_ctor_set(v___x_990_, 1, v___x_988_);
    return v___x_990_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_991_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_991_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__2_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__2,
    );
    v___x_993_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_993_, 0, v___x_992_);
    return v___x_993_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: u8 = 0;
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_994_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__3_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3,
    );
    v___x_995_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__1_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__1,
    );
    v___x_996_ = 1;
    v___x_997_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_997_, 0, v___x_995_);
    crate::leanh::lean_ctor_set(v___x_997_, 1, v___x_994_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_997_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_996_,
    );
    return v___x_997_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_999_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__3_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3,
    );
    v___x_1000_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1000_, 0, v___x_999_);
    crate::leanh::lean_ctor_set(v___x_1000_, 1, v___x_998_);
    return v___x_1000_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1001_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1002_ = lean_mk_empty_array_with_capacity(v___x_1001_);
    v___x_1003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1003_, 0, v___x_1002_);
    return v___x_1003_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1004_: usize = 0;
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = 5usize;
    v___x_1005_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1006_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1007_ = lean_mk_empty_array_with_capacity(v___x_1006_);
    v___x_1008_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__6_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__6,
    );
    v___x_1009_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1009_, 0, v___x_1008_);
    crate::leanh::lean_ctor_set(v___x_1009_, 1, v___x_1007_);
    crate::leanh::lean_ctor_set(v___x_1009_, 2, v___x_1005_);
    crate::leanh::lean_ctor_set(v___x_1009_, 3, v___x_1005_);
    crate::leanh::lean_ctor_set_usize(v___x_1009_, 4, v___x_1004_);
    return v___x_1009_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1010_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__7_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__7,
    );
    v___x_1011_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__3_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3,
    );
    v___x_1012_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1012_, 0, v___x_1011_);
    crate::leanh::lean_ctor_set(v___x_1012_, 1, v___x_1011_);
    crate::leanh::lean_ctor_set(v___x_1012_, 2, v___x_1011_);
    crate::leanh::lean_ctor_set(v___x_1012_, 3, v___x_1010_);
    return v___x_1012_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1013_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__8_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__8,
    );
    v___x_1014_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1015_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__5_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__5,
    );
    v___x_1016_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__1_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__1,
    );
    v___x_1017_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__4_once),
        _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__4,
    );
    v___x_1018_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1018_, 0, v___x_1017_);
    crate::leanh::lean_ctor_set(v___x_1018_, 1, v___x_1016_);
    crate::leanh::lean_ctor_set(v___x_1018_, 2, v___x_1016_);
    crate::leanh::lean_ctor_set(v___x_1018_, 3, v___x_1015_);
    crate::leanh::lean_ctor_set(v___x_1018_, 4, v___x_1014_);
    crate::leanh::lean_ctor_set(v___x_1018_, 5, v___x_1013_);
    return v___x_1018_;
}
pub unsafe fn l_Lean_Meta_Grind_simpCore___lam__0(
    mut v_e_1019_: *mut crate::leanh::LeanObject,
    mut v___y_1020_: *mut crate::leanh::LeanObject,
    mut v___y_1021_: *mut crate::leanh::LeanObject,
    mut v___y_1022_: *mut crate::leanh::LeanObject,
    mut v___y_1023_: *mut crate::leanh::LeanObject,
    mut v___y_1024_: *mut crate::leanh::LeanObject,
    mut v___y_1025_: *mut crate::leanh::LeanObject,
    mut v___y_1026_: *mut crate::leanh::LeanObject,
    mut v___y_1027_: *mut crate::leanh::LeanObject,
    mut v___y_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrThms_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simp_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastTag_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_counters_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitDiags_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematchDiags_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulEqCmpMap_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reflCmpMap_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instanceMap_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1043_: u8 = 0;
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simp_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpMethods_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1054_: u8 = 0;
    let mut v_fst_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrThms_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastTag_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_counters_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitDiags_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematchDiags_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulEqCmpMap_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reflCmpMap_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instanceMap_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1069_: u8 = 0;
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1077_: u8 = 0;
    let mut v_unused_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut v_a_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1083_: u8 = 0;
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1087_: u8 = 0;
    let mut v_reuseFailAlloc_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1030_ = lean_st_ref_take(v___y_1022_);
                v_congrThms_1031_ = crate::leanh::lean_ctor_get(v___x_1030_, 0);
                v_simp_1032_ = crate::leanh::lean_ctor_get(v___x_1030_, 1);
                v_lastTag_1033_ = crate::leanh::lean_ctor_get(v___x_1030_, 2);
                v_counters_1034_ = crate::leanh::lean_ctor_get(v___x_1030_, 3);
                v_splitDiags_1035_ = crate::leanh::lean_ctor_get(v___x_1030_, 4);
                v_ematchDiags_1036_ = crate::leanh::lean_ctor_get(v___x_1030_, 5);
                v_lawfulEqCmpMap_1037_ = crate::leanh::lean_ctor_get(v___x_1030_, 6);
                v_reflCmpMap_1038_ = crate::leanh::lean_ctor_get(v___x_1030_, 7);
                v_anchors_1039_ = crate::leanh::lean_ctor_get(v___x_1030_, 8);
                v_instanceMap_1040_ = crate::leanh::lean_ctor_get(v___x_1030_, 9);
                v_isSharedCheck_1089_ = (!crate::leanh::lean_is_exclusive(v___x_1030_)) as u8;
                if v_isSharedCheck_1089_ == 0 {
                    v___x_1042_ = v___x_1030_;
                    v_isShared_1043_ = v_isSharedCheck_1089_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_instanceMap_1040_);
                    crate::leanh::lean_inc(v_anchors_1039_);
                    crate::leanh::lean_inc(v_reflCmpMap_1038_);
                    crate::leanh::lean_inc(v_lawfulEqCmpMap_1037_);
                    crate::leanh::lean_inc(v_ematchDiags_1036_);
                    crate::leanh::lean_inc(v_splitDiags_1035_);
                    crate::leanh::lean_inc(v_counters_1034_);
                    crate::leanh::lean_inc(v_lastTag_1033_);
                    crate::leanh::lean_inc(v_simp_1032_);
                    crate::leanh::lean_inc(v_congrThms_1031_);
                    crate::leanh::lean_dec(v___x_1030_);
                    v___x_1042_ = crate::leanh::lean_box(0);
                    v_isShared_1043_ = v_isSharedCheck_1089_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1044_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__9_once),
                    _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9,
                );
                if v_isShared_1043_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1042_, 1, v___x_1044_);
                    v___x_1046_ = v___x_1042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1088_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_congrThms_1031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_lastTag_1033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_counters_1034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_splitDiags_1035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 5, v_ematchDiags_1036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 6, v_lawfulEqCmpMap_1037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 7, v_reflCmpMap_1038_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 8, v_anchors_1039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 9, v_instanceMap_1040_);
                    v___x_1046_ = v_reuseFailAlloc_1088_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1047_ = lean_st_ref_set(v___y_1022_, v___x_1046_);
                v_simp_1048_ = crate::leanh::lean_ctor_get(v___y_1021_, 0);
                v_simpMethods_1049_ = crate::leanh::lean_ctor_get(v___y_1021_, 1);
                crate::leanh::lean_inc_ref(v_simpMethods_1049_);
                crate::leanh::lean_inc_ref(v_simp_1048_);
                v___x_1050_ = l_Lean_Meta_Simp_mainCore(
                    v_e_1019_,
                    v_simp_1048_,
                    v_simp_1032_,
                    v_simpMethods_1049_,
                    v___y_1025_,
                    v___y_1026_,
                    v___y_1027_,
                    v___y_1028_,
                );
                if crate::leanh::lean_obj_tag(v___x_1050_) == 0 {
                    v_a_1051_ = crate::leanh::lean_ctor_get(v___x_1050_, 0);
                    v_isSharedCheck_1079_ = (!crate::leanh::lean_is_exclusive(v___x_1050_)) as u8;
                    if v_isSharedCheck_1079_ == 0 {
                        v___x_1053_ = v___x_1050_;
                        v_isShared_1054_ = v_isSharedCheck_1079_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1051_);
                        crate::leanh::lean_dec(v___x_1050_);
                        v___x_1053_ = crate::leanh::lean_box(0);
                        v_isShared_1054_ = v_isSharedCheck_1079_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1080_ = crate::leanh::lean_ctor_get(v___x_1050_, 0);
                    v_isSharedCheck_1087_ = (!crate::leanh::lean_is_exclusive(v___x_1050_)) as u8;
                    if v_isSharedCheck_1087_ == 0 {
                        v___x_1082_ = v___x_1050_;
                        v_isShared_1083_ = v_isSharedCheck_1087_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1080_);
                        crate::leanh::lean_dec(v___x_1050_);
                        v___x_1082_ = crate::leanh::lean_box(0);
                        v_isShared_1083_ = v_isSharedCheck_1087_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_1055_ = crate::leanh::lean_ctor_get(v_a_1051_, 0);
                crate::leanh::lean_inc(v_fst_1055_);
                v_snd_1056_ = crate::leanh::lean_ctor_get(v_a_1051_, 1);
                crate::leanh::lean_inc(v_snd_1056_);
                crate::leanh::lean_dec(v_a_1051_);
                v___x_1057_ = lean_st_ref_take(v___y_1022_);
                v_congrThms_1058_ = crate::leanh::lean_ctor_get(v___x_1057_, 0);
                v_lastTag_1059_ = crate::leanh::lean_ctor_get(v___x_1057_, 2);
                v_counters_1060_ = crate::leanh::lean_ctor_get(v___x_1057_, 3);
                v_splitDiags_1061_ = crate::leanh::lean_ctor_get(v___x_1057_, 4);
                v_ematchDiags_1062_ = crate::leanh::lean_ctor_get(v___x_1057_, 5);
                v_lawfulEqCmpMap_1063_ = crate::leanh::lean_ctor_get(v___x_1057_, 6);
                v_reflCmpMap_1064_ = crate::leanh::lean_ctor_get(v___x_1057_, 7);
                v_anchors_1065_ = crate::leanh::lean_ctor_get(v___x_1057_, 8);
                v_instanceMap_1066_ = crate::leanh::lean_ctor_get(v___x_1057_, 9);
                v_isSharedCheck_1077_ = (!crate::leanh::lean_is_exclusive(v___x_1057_)) as u8;
                if v_isSharedCheck_1077_ == 0 {
                    v_unused_1078_ = crate::leanh::lean_ctor_get(v___x_1057_, 1);
                    crate::leanh::lean_dec(v_unused_1078_);
                    v___x_1068_ = v___x_1057_;
                    v_isShared_1069_ = v_isSharedCheck_1077_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_instanceMap_1066_);
                    crate::leanh::lean_inc(v_anchors_1065_);
                    crate::leanh::lean_inc(v_reflCmpMap_1064_);
                    crate::leanh::lean_inc(v_lawfulEqCmpMap_1063_);
                    crate::leanh::lean_inc(v_ematchDiags_1062_);
                    crate::leanh::lean_inc(v_splitDiags_1061_);
                    crate::leanh::lean_inc(v_counters_1060_);
                    crate::leanh::lean_inc(v_lastTag_1059_);
                    crate::leanh::lean_inc(v_congrThms_1058_);
                    crate::leanh::lean_dec(v___x_1057_);
                    v___x_1068_ = crate::leanh::lean_box(0);
                    v_isShared_1069_ = v_isSharedCheck_1077_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1069_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1068_, 1, v_snd_1056_);
                    v___x_1071_ = v___x_1068_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1076_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_congrThms_1058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_snd_1056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_lastTag_1059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_counters_1060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 4, v_splitDiags_1061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 5, v_ematchDiags_1062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 6, v_lawfulEqCmpMap_1063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 7, v_reflCmpMap_1064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 8, v_anchors_1065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 9, v_instanceMap_1066_);
                    v___x_1071_ = v_reuseFailAlloc_1076_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1072_ = lean_st_ref_set(v___y_1022_, v___x_1071_);
                if v_isShared_1054_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1053_, 0, v_fst_1055_);
                    v___x_1074_ = v___x_1053_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1075_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_fst_1055_);
                    v___x_1074_ = v_reuseFailAlloc_1075_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1074_;
            }
            7 => {
                if v_isShared_1083_ == 0 {
                    v___x_1085_ = v___x_1082_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1086_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
                    v___x_1085_ = v_reuseFailAlloc_1086_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_simpCore___lam__0___boxed(
    mut v_e_1090_: *mut crate::leanh::LeanObject,
    mut v___y_1091_: *mut crate::leanh::LeanObject,
    mut v___y_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
    mut v___y_1096_: *mut crate::leanh::LeanObject,
    mut v___y_1097_: *mut crate::leanh::LeanObject,
    mut v___y_1098_: *mut crate::leanh::LeanObject,
    mut v___y_1099_: *mut crate::leanh::LeanObject,
    mut v___y_1100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1101_ = l_Lean_Meta_Grind_simpCore___lam__0(
        v_e_1090_,
        v___y_1091_,
        v___y_1092_,
        v___y_1093_,
        v___y_1094_,
        v___y_1095_,
        v___y_1096_,
        v___y_1097_,
        v___y_1098_,
        v___y_1099_,
    );
    crate::leanh::lean_dec(v___y_1099_);
    crate::leanh::lean_dec_ref(v___y_1098_);
    crate::leanh::lean_dec(v___y_1097_);
    crate::leanh::lean_dec_ref(v___y_1096_);
    crate::leanh::lean_dec(v___y_1095_);
    crate::leanh::lean_dec_ref(v___y_1094_);
    crate::leanh::lean_dec(v___y_1093_);
    crate::leanh::lean_dec_ref(v___y_1092_);
    crate::leanh::lean_dec(v___y_1091_);
    return v_res_1101_;
}
pub unsafe fn l_Lean_Meta_Grind_simpCore(
    mut v_e_1103_: *mut crate::leanh::LeanObject,
    mut v_a_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
    mut v_a_1106_: *mut crate::leanh::LeanObject,
    mut v_a_1107_: *mut crate::leanh::LeanObject,
    mut v_a_1108_: *mut crate::leanh::LeanObject,
    mut v_a_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
    mut v_a_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_1114_ = crate::leanh::lean_ctor_get(v_a_1111_, 2);
    v___f_1115_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_simpCore___lam__0___boxed as *mut core::ffi::c_void,
        11,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1115_, 0, v_e_1103_);
    v___x_1116_ = l_Lean_Meta_Grind_simpCore___closed__0;
    v___x_1117_ = crate::leanh::lean_box(0);
    v___x_1118_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(
        v___x_1116_,
        v_options_1114_,
        v___f_1115_,
        v___x_1117_,
        v_a_1104_,
        v_a_1105_,
        v_a_1106_,
        v_a_1107_,
        v_a_1108_,
        v_a_1109_,
        v_a_1110_,
        v_a_1111_,
        v_a_1112_,
    );
    return v___x_1118_;
}
pub unsafe fn l_Lean_Meta_Grind_simpCore___boxed(
    mut v_e_1119_: *mut crate::leanh::LeanObject,
    mut v_a_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v_a_1122_: *mut crate::leanh::LeanObject,
    mut v_a_1123_: *mut crate::leanh::LeanObject,
    mut v_a_1124_: *mut crate::leanh::LeanObject,
    mut v_a_1125_: *mut crate::leanh::LeanObject,
    mut v_a_1126_: *mut crate::leanh::LeanObject,
    mut v_a_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_a_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_Lean_Meta_Grind_simpCore(
        v_e_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_,
        v_a_1127_, v_a_1128_,
    );
    crate::leanh::lean_dec(v_a_1128_);
    crate::leanh::lean_dec_ref(v_a_1127_);
    crate::leanh::lean_dec(v_a_1126_);
    crate::leanh::lean_dec_ref(v_a_1125_);
    crate::leanh::lean_dec(v_a_1124_);
    crate::leanh::lean_dec_ref(v_a_1123_);
    crate::leanh::lean_dec(v_a_1122_);
    crate::leanh::lean_dec_ref(v_a_1121_);
    crate::leanh::lean_dec(v_a_1120_);
    return v_res_1130_;
}
pub unsafe fn l_Lean_Meta_Grind_dsimpCore___lam__0(
    mut v_e_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrThms_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simp_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastTag_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_counters_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitDiags_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematchDiags_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulEqCmpMap_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reflCmpMap_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instanceMap_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1155_: u8 = 0;
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simp_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpMethods_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1168_: u8 = 0;
    let mut v_fst_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrThms_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastTag_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_counters_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitDiags_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematchDiags_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulEqCmpMap_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reflCmpMap_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instanceMap_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1183_: u8 = 0;
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1191_: u8 = 0;
    let mut v_unused_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1193_: u8 = 0;
    let mut v_a_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1197_: u8 = 0;
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1201_: u8 = 0;
    let mut v_reuseFailAlloc_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1142_ = lean_st_ref_take(v___y_1134_);
                v_congrThms_1143_ = crate::leanh::lean_ctor_get(v___x_1142_, 0);
                v_simp_1144_ = crate::leanh::lean_ctor_get(v___x_1142_, 1);
                v_lastTag_1145_ = crate::leanh::lean_ctor_get(v___x_1142_, 2);
                v_counters_1146_ = crate::leanh::lean_ctor_get(v___x_1142_, 3);
                v_splitDiags_1147_ = crate::leanh::lean_ctor_get(v___x_1142_, 4);
                v_ematchDiags_1148_ = crate::leanh::lean_ctor_get(v___x_1142_, 5);
                v_lawfulEqCmpMap_1149_ = crate::leanh::lean_ctor_get(v___x_1142_, 6);
                v_reflCmpMap_1150_ = crate::leanh::lean_ctor_get(v___x_1142_, 7);
                v_anchors_1151_ = crate::leanh::lean_ctor_get(v___x_1142_, 8);
                v_instanceMap_1152_ = crate::leanh::lean_ctor_get(v___x_1142_, 9);
                v_isSharedCheck_1203_ = (!crate::leanh::lean_is_exclusive(v___x_1142_)) as u8;
                if v_isSharedCheck_1203_ == 0 {
                    v___x_1154_ = v___x_1142_;
                    v_isShared_1155_ = v_isSharedCheck_1203_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_instanceMap_1152_);
                    crate::leanh::lean_inc(v_anchors_1151_);
                    crate::leanh::lean_inc(v_reflCmpMap_1150_);
                    crate::leanh::lean_inc(v_lawfulEqCmpMap_1149_);
                    crate::leanh::lean_inc(v_ematchDiags_1148_);
                    crate::leanh::lean_inc(v_splitDiags_1147_);
                    crate::leanh::lean_inc(v_counters_1146_);
                    crate::leanh::lean_inc(v_lastTag_1145_);
                    crate::leanh::lean_inc(v_simp_1144_);
                    crate::leanh::lean_inc(v_congrThms_1143_);
                    crate::leanh::lean_dec(v___x_1142_);
                    v___x_1154_ = crate::leanh::lean_box(0);
                    v_isShared_1155_ = v_isSharedCheck_1203_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1156_ = crate::leanh::lean_unsigned_to_nat(32);
                v___x_1157_ = lean_mk_empty_array_with_capacity(v___x_1156_);
                crate::leanh::lean_dec_ref(v___x_1157_);
                v___x_1158_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpCore___lam__0___closed__9_once),
                    _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9,
                );
                if v_isShared_1155_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1154_, 1, v___x_1158_);
                    v___x_1160_ = v___x_1154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1202_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_congrThms_1143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_lastTag_1145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_counters_1146_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 4, v_splitDiags_1147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 5, v_ematchDiags_1148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 6, v_lawfulEqCmpMap_1149_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 7, v_reflCmpMap_1150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 8, v_anchors_1151_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 9, v_instanceMap_1152_);
                    v___x_1160_ = v_reuseFailAlloc_1202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1161_ = lean_st_ref_set(v___y_1134_, v___x_1160_);
                v_simp_1162_ = crate::leanh::lean_ctor_get(v___y_1133_, 0);
                v_simpMethods_1163_ = crate::leanh::lean_ctor_get(v___y_1133_, 1);
                crate::leanh::lean_inc_ref(v_simpMethods_1163_);
                crate::leanh::lean_inc_ref(v_simp_1162_);
                v___x_1164_ = l_Lean_Meta_Simp_dsimpMainCore(
                    v_e_1131_,
                    v_simp_1162_,
                    v_simp_1144_,
                    v_simpMethods_1163_,
                    v___y_1137_,
                    v___y_1138_,
                    v___y_1139_,
                    v___y_1140_,
                );
                if crate::leanh::lean_obj_tag(v___x_1164_) == 0 {
                    v_a_1165_ = crate::leanh::lean_ctor_get(v___x_1164_, 0);
                    v_isSharedCheck_1193_ = (!crate::leanh::lean_is_exclusive(v___x_1164_)) as u8;
                    if v_isSharedCheck_1193_ == 0 {
                        v___x_1167_ = v___x_1164_;
                        v_isShared_1168_ = v_isSharedCheck_1193_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1165_);
                        crate::leanh::lean_dec(v___x_1164_);
                        v___x_1167_ = crate::leanh::lean_box(0);
                        v_isShared_1168_ = v_isSharedCheck_1193_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1194_ = crate::leanh::lean_ctor_get(v___x_1164_, 0);
                    v_isSharedCheck_1201_ = (!crate::leanh::lean_is_exclusive(v___x_1164_)) as u8;
                    if v_isSharedCheck_1201_ == 0 {
                        v___x_1196_ = v___x_1164_;
                        v_isShared_1197_ = v_isSharedCheck_1201_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1194_);
                        crate::leanh::lean_dec(v___x_1164_);
                        v___x_1196_ = crate::leanh::lean_box(0);
                        v_isShared_1197_ = v_isSharedCheck_1201_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_1169_ = crate::leanh::lean_ctor_get(v_a_1165_, 0);
                crate::leanh::lean_inc(v_fst_1169_);
                v_snd_1170_ = crate::leanh::lean_ctor_get(v_a_1165_, 1);
                crate::leanh::lean_inc(v_snd_1170_);
                crate::leanh::lean_dec(v_a_1165_);
                v___x_1171_ = lean_st_ref_take(v___y_1134_);
                v_congrThms_1172_ = crate::leanh::lean_ctor_get(v___x_1171_, 0);
                v_lastTag_1173_ = crate::leanh::lean_ctor_get(v___x_1171_, 2);
                v_counters_1174_ = crate::leanh::lean_ctor_get(v___x_1171_, 3);
                v_splitDiags_1175_ = crate::leanh::lean_ctor_get(v___x_1171_, 4);
                v_ematchDiags_1176_ = crate::leanh::lean_ctor_get(v___x_1171_, 5);
                v_lawfulEqCmpMap_1177_ = crate::leanh::lean_ctor_get(v___x_1171_, 6);
                v_reflCmpMap_1178_ = crate::leanh::lean_ctor_get(v___x_1171_, 7);
                v_anchors_1179_ = crate::leanh::lean_ctor_get(v___x_1171_, 8);
                v_instanceMap_1180_ = crate::leanh::lean_ctor_get(v___x_1171_, 9);
                v_isSharedCheck_1191_ = (!crate::leanh::lean_is_exclusive(v___x_1171_)) as u8;
                if v_isSharedCheck_1191_ == 0 {
                    v_unused_1192_ = crate::leanh::lean_ctor_get(v___x_1171_, 1);
                    crate::leanh::lean_dec(v_unused_1192_);
                    v___x_1182_ = v___x_1171_;
                    v_isShared_1183_ = v_isSharedCheck_1191_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_instanceMap_1180_);
                    crate::leanh::lean_inc(v_anchors_1179_);
                    crate::leanh::lean_inc(v_reflCmpMap_1178_);
                    crate::leanh::lean_inc(v_lawfulEqCmpMap_1177_);
                    crate::leanh::lean_inc(v_ematchDiags_1176_);
                    crate::leanh::lean_inc(v_splitDiags_1175_);
                    crate::leanh::lean_inc(v_counters_1174_);
                    crate::leanh::lean_inc(v_lastTag_1173_);
                    crate::leanh::lean_inc(v_congrThms_1172_);
                    crate::leanh::lean_dec(v___x_1171_);
                    v___x_1182_ = crate::leanh::lean_box(0);
                    v_isShared_1183_ = v_isSharedCheck_1191_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1183_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1182_, 1, v_snd_1170_);
                    v___x_1185_ = v___x_1182_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1190_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_congrThms_1172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_snd_1170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_lastTag_1173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_counters_1174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 4, v_splitDiags_1175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 5, v_ematchDiags_1176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 6, v_lawfulEqCmpMap_1177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 7, v_reflCmpMap_1178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 8, v_anchors_1179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1190_, 9, v_instanceMap_1180_);
                    v___x_1185_ = v_reuseFailAlloc_1190_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1186_ = lean_st_ref_set(v___y_1134_, v___x_1185_);
                if v_isShared_1168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1167_, 0, v_fst_1169_);
                    v___x_1188_ = v___x_1167_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1189_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_fst_1169_);
                    v___x_1188_ = v_reuseFailAlloc_1189_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1188_;
            }
            7 => {
                if v_isShared_1197_ == 0 {
                    v___x_1199_ = v___x_1196_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1200_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
                    v___x_1199_ = v_reuseFailAlloc_1200_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_dsimpCore___lam__0___boxed(
    mut v_e_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
    mut v___y_1208_: *mut crate::leanh::LeanObject,
    mut v___y_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1215_ = l_Lean_Meta_Grind_dsimpCore___lam__0(
        v_e_1204_,
        v___y_1205_,
        v___y_1206_,
        v___y_1207_,
        v___y_1208_,
        v___y_1209_,
        v___y_1210_,
        v___y_1211_,
        v___y_1212_,
        v___y_1213_,
    );
    crate::leanh::lean_dec(v___y_1213_);
    crate::leanh::lean_dec_ref(v___y_1212_);
    crate::leanh::lean_dec(v___y_1211_);
    crate::leanh::lean_dec_ref(v___y_1210_);
    crate::leanh::lean_dec(v___y_1209_);
    crate::leanh::lean_dec_ref(v___y_1208_);
    crate::leanh::lean_dec(v___y_1207_);
    crate::leanh::lean_dec_ref(v___y_1206_);
    crate::leanh::lean_dec(v___y_1205_);
    return v_res_1215_;
}
pub unsafe fn l_Lean_Meta_Grind_dsimpCore(
    mut v_e_1217_: *mut crate::leanh::LeanObject,
    mut v_a_1218_: *mut crate::leanh::LeanObject,
    mut v_a_1219_: *mut crate::leanh::LeanObject,
    mut v_a_1220_: *mut crate::leanh::LeanObject,
    mut v_a_1221_: *mut crate::leanh::LeanObject,
    mut v_a_1222_: *mut crate::leanh::LeanObject,
    mut v_a_1223_: *mut crate::leanh::LeanObject,
    mut v_a_1224_: *mut crate::leanh::LeanObject,
    mut v_a_1225_: *mut crate::leanh::LeanObject,
    mut v_a_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_1228_ = crate::leanh::lean_ctor_get(v_a_1225_, 2);
    v___f_1229_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_dsimpCore___lam__0___boxed as *mut core::ffi::c_void,
        11,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1229_, 0, v_e_1217_);
    v___x_1230_ = l_Lean_Meta_Grind_dsimpCore___closed__0;
    v___x_1231_ = crate::leanh::lean_box(0);
    v___x_1232_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(
        v___x_1230_,
        v_options_1228_,
        v___f_1229_,
        v___x_1231_,
        v_a_1218_,
        v_a_1219_,
        v_a_1220_,
        v_a_1221_,
        v_a_1222_,
        v_a_1223_,
        v_a_1224_,
        v_a_1225_,
        v_a_1226_,
    );
    return v___x_1232_;
}
pub unsafe fn l_Lean_Meta_Grind_dsimpCore___boxed(
    mut v_e_1233_: *mut crate::leanh::LeanObject,
    mut v_a_1234_: *mut crate::leanh::LeanObject,
    mut v_a_1235_: *mut crate::leanh::LeanObject,
    mut v_a_1236_: *mut crate::leanh::LeanObject,
    mut v_a_1237_: *mut crate::leanh::LeanObject,
    mut v_a_1238_: *mut crate::leanh::LeanObject,
    mut v_a_1239_: *mut crate::leanh::LeanObject,
    mut v_a_1240_: *mut crate::leanh::LeanObject,
    mut v_a_1241_: *mut crate::leanh::LeanObject,
    mut v_a_1242_: *mut crate::leanh::LeanObject,
    mut v_a_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1244_ = l_Lean_Meta_Grind_dsimpCore(
        v_e_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_,
        v_a_1241_, v_a_1242_,
    );
    crate::leanh::lean_dec(v_a_1242_);
    crate::leanh::lean_dec_ref(v_a_1241_);
    crate::leanh::lean_dec(v_a_1240_);
    crate::leanh::lean_dec_ref(v_a_1239_);
    crate::leanh::lean_dec(v_a_1238_);
    crate::leanh::lean_dec_ref(v_a_1237_);
    crate::leanh::lean_dec(v_a_1236_);
    crate::leanh::lean_dec_ref(v_a_1235_);
    crate::leanh::lean_dec(v_a_1234_);
    return v_res_1244_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(
    mut v_e_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1248_: u8 = 0;
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1262_: u8 = 0;
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1268_: u8 = 0;
    let mut v_unused_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1248_ = l_Lean_Expr_hasMVar(v_e_1245_);
                if v___x_1248_ == 0 {
                    v___x_1249_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1249_, 0, v_e_1245_);
                    return v___x_1249_;
                } else {
                    v___x_1250_ = lean_st_ref_get(v___y_1246_);
                    v_mctx_1251_ = crate::leanh::lean_ctor_get(v___x_1250_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1251_);
                    crate::leanh::lean_dec(v___x_1250_);
                    v___x_1252_ = l_Lean_instantiateMVarsCore(v_mctx_1251_, v_e_1245_);
                    v_fst_1253_ = crate::leanh::lean_ctor_get(v___x_1252_, 0);
                    crate::leanh::lean_inc(v_fst_1253_);
                    v_snd_1254_ = crate::leanh::lean_ctor_get(v___x_1252_, 1);
                    crate::leanh::lean_inc(v_snd_1254_);
                    crate::leanh::lean_dec_ref(v___x_1252_);
                    v___x_1255_ = lean_st_ref_take(v___y_1246_);
                    v_cache_1256_ = crate::leanh::lean_ctor_get(v___x_1255_, 1);
                    v_zetaDeltaFVarIds_1257_ = crate::leanh::lean_ctor_get(v___x_1255_, 2);
                    v_postponed_1258_ = crate::leanh::lean_ctor_get(v___x_1255_, 3);
                    v_diag_1259_ = crate::leanh::lean_ctor_get(v___x_1255_, 4);
                    v_isSharedCheck_1268_ = (!crate::leanh::lean_is_exclusive(v___x_1255_)) as u8;
                    if v_isSharedCheck_1268_ == 0 {
                        v_unused_1269_ = crate::leanh::lean_ctor_get(v___x_1255_, 0);
                        crate::leanh::lean_dec(v_unused_1269_);
                        v___x_1261_ = v___x_1255_;
                        v_isShared_1262_ = v_isSharedCheck_1268_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1259_);
                        crate::leanh::lean_inc(v_postponed_1258_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1257_);
                        crate::leanh::lean_inc(v_cache_1256_);
                        crate::leanh::lean_dec(v___x_1255_);
                        v___x_1261_ = crate::leanh::lean_box(0);
                        v_isShared_1262_ = v_isSharedCheck_1268_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1261_, 0, v_snd_1254_);
                    v___x_1264_ = v___x_1261_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1267_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_snd_1254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_cache_1256_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1267_,
                        2,
                        v_zetaDeltaFVarIds_1257_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_postponed_1258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_diag_1259_);
                    v___x_1264_ = v_reuseFailAlloc_1267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1265_ = lean_st_ref_set(v___y_1246_, v___x_1264_);
                v___x_1266_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1266_, 0, v_fst_1253_);
                return v___x_1266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg___boxed(
    mut v_e_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1273_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(
        v_e_1270_,
        v___y_1271_,
    );
    crate::leanh::lean_dec(v___y_1271_);
    return v_res_1273_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(
    mut v_e_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
    mut v___y_1276_: *mut crate::leanh::LeanObject,
    mut v___y_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
    mut v___y_1280_: *mut crate::leanh::LeanObject,
    mut v___y_1281_: *mut crate::leanh::LeanObject,
    mut v___y_1282_: *mut crate::leanh::LeanObject,
    mut v___y_1283_: *mut crate::leanh::LeanObject,
    mut v___y_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1286_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(
        v_e_1274_,
        v___y_1282_,
    );
    return v___x_1286_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___boxed(
    mut v_e_1287_: *mut crate::leanh::LeanObject,
    mut v___y_1288_: *mut crate::leanh::LeanObject,
    mut v___y_1289_: *mut crate::leanh::LeanObject,
    mut v___y_1290_: *mut crate::leanh::LeanObject,
    mut v___y_1291_: *mut crate::leanh::LeanObject,
    mut v___y_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1299_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(
        v_e_1287_,
        v___y_1288_,
        v___y_1289_,
        v___y_1290_,
        v___y_1291_,
        v___y_1292_,
        v___y_1293_,
        v___y_1294_,
        v___y_1295_,
        v___y_1296_,
        v___y_1297_,
    );
    crate::leanh::lean_dec(v___y_1297_);
    crate::leanh::lean_dec_ref(v___y_1296_);
    crate::leanh::lean_dec(v___y_1295_);
    crate::leanh::lean_dec_ref(v___y_1294_);
    crate::leanh::lean_dec(v___y_1293_);
    crate::leanh::lean_dec_ref(v___y_1292_);
    crate::leanh::lean_dec(v___y_1291_);
    crate::leanh::lean_dec_ref(v___y_1290_);
    crate::leanh::lean_dec(v___y_1289_);
    crate::leanh::lean_dec(v___y_1288_);
    return v_res_1299_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(
    mut v_msgData_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1306_ = lean_st_ref_get(v___y_1304_);
    v_env_1307_ = crate::leanh::lean_ctor_get(v___x_1306_, 0);
    crate::leanh::lean_inc_ref(v_env_1307_);
    crate::leanh::lean_dec(v___x_1306_);
    v___x_1308_ = lean_st_ref_get(v___y_1302_);
    v_mctx_1309_ = crate::leanh::lean_ctor_get(v___x_1308_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1309_);
    crate::leanh::lean_dec(v___x_1308_);
    v_lctx_1310_ = crate::leanh::lean_ctor_get(v___y_1301_, 2);
    v_options_1311_ = crate::leanh::lean_ctor_get(v___y_1303_, 2);
    crate::leanh::lean_inc_ref(v_options_1311_);
    crate::leanh::lean_inc_ref(v_lctx_1310_);
    v___x_1312_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1312_, 0, v_env_1307_);
    crate::leanh::lean_ctor_set(v___x_1312_, 1, v_mctx_1309_);
    crate::leanh::lean_ctor_set(v___x_1312_, 2, v_lctx_1310_);
    crate::leanh::lean_ctor_set(v___x_1312_, 3, v_options_1311_);
    v___x_1313_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1313_, 0, v___x_1312_);
    crate::leanh::lean_ctor_set(v___x_1313_, 1, v_msgData_1300_);
    v___x_1314_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1314_, 0, v___x_1313_);
    return v___x_1314_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1___boxed(
    mut v_msgData_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msgData_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
    crate::leanh::lean_dec(v___y_1319_);
    crate::leanh::lean_dec_ref(v___y_1318_);
    crate::leanh::lean_dec(v___y_1317_);
    crate::leanh::lean_dec_ref(v___y_1316_);
    return v_res_1321_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: f64 = 0.0;
    v___x_1322_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1323_ = lean_float_of_nat(v___x_1322_);
    return v___x_1323_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(
    mut v_cls_1327_: *mut crate::leanh::LeanObject,
    mut v_msg_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
    mut v___y_1331_: *mut crate::leanh::LeanObject,
    mut v___y_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1352_: u8 = 0;
    let mut v_tid_1353_: u64 = 0;
    let mut v_traces_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: f64 = 0.0;
    let mut v___x_1360_: u8 = 0;
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut v_isSharedCheck_1379_: u8 = 0;
    let mut v_isSharedCheck_1380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1334_ = crate::leanh::lean_ctor_get(v___y_1331_, 5);
                v___x_1335_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msg_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
                v_a_1336_ = crate::leanh::lean_ctor_get(v___x_1335_, 0);
                v_isSharedCheck_1380_ = (!crate::leanh::lean_is_exclusive(v___x_1335_)) as u8;
                if v_isSharedCheck_1380_ == 0 {
                    v___x_1338_ = v___x_1335_;
                    v_isShared_1339_ = v_isSharedCheck_1380_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1336_);
                    crate::leanh::lean_dec(v___x_1335_);
                    v___x_1338_ = crate::leanh::lean_box(0);
                    v_isShared_1339_ = v_isSharedCheck_1380_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1340_ = lean_st_ref_take(v___y_1332_);
                v_traceState_1341_ = crate::leanh::lean_ctor_get(v___x_1340_, 4);
                v_env_1342_ = crate::leanh::lean_ctor_get(v___x_1340_, 0);
                v_nextMacroScope_1343_ = crate::leanh::lean_ctor_get(v___x_1340_, 1);
                v_ngen_1344_ = crate::leanh::lean_ctor_get(v___x_1340_, 2);
                v_auxDeclNGen_1345_ = crate::leanh::lean_ctor_get(v___x_1340_, 3);
                v_cache_1346_ = crate::leanh::lean_ctor_get(v___x_1340_, 5);
                v_messages_1347_ = crate::leanh::lean_ctor_get(v___x_1340_, 6);
                v_infoState_1348_ = crate::leanh::lean_ctor_get(v___x_1340_, 7);
                v_snapshotTasks_1349_ = crate::leanh::lean_ctor_get(v___x_1340_, 8);
                v_isSharedCheck_1379_ = (!crate::leanh::lean_is_exclusive(v___x_1340_)) as u8;
                if v_isSharedCheck_1379_ == 0 {
                    v___x_1351_ = v___x_1340_;
                    v_isShared_1352_ = v_isSharedCheck_1379_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1349_);
                    crate::leanh::lean_inc(v_infoState_1348_);
                    crate::leanh::lean_inc(v_messages_1347_);
                    crate::leanh::lean_inc(v_cache_1346_);
                    crate::leanh::lean_inc(v_traceState_1341_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1345_);
                    crate::leanh::lean_inc(v_ngen_1344_);
                    crate::leanh::lean_inc(v_nextMacroScope_1343_);
                    crate::leanh::lean_inc(v_env_1342_);
                    crate::leanh::lean_dec(v___x_1340_);
                    v___x_1351_ = crate::leanh::lean_box(0);
                    v_isShared_1352_ = v_isSharedCheck_1379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1353_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1341_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1354_ = crate::leanh::lean_ctor_get(v_traceState_1341_, 0);
                v_isSharedCheck_1378_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1341_)) as u8;
                if v_isSharedCheck_1378_ == 0 {
                    v___x_1356_ = v_traceState_1341_;
                    v_isShared_1357_ = v_isSharedCheck_1378_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1354_);
                    crate::leanh::lean_dec(v_traceState_1341_);
                    v___x_1356_ = crate::leanh::lean_box(0);
                    v_isShared_1357_ = v_isSharedCheck_1378_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1358_ = crate::leanh::lean_box(0);
                v___x_1359_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0);
                v___x_1360_ = 0;
                v___x_1361_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1;
                v___x_1362_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_1362_, 0, v_cls_1327_);
                crate::leanh::lean_ctor_set(v___x_1362_, 1, v___x_1358_);
                crate::leanh::lean_ctor_set(v___x_1362_, 2, v___x_1361_);
                crate::leanh::lean_ctor_set_float(
                    v___x_1362_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1359_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_1362_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1359_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1362_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1360_,
                );
                v___x_1363_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2;
                v___x_1364_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1364_, 0, v___x_1362_);
                crate::leanh::lean_ctor_set(v___x_1364_, 1, v_a_1336_);
                crate::leanh::lean_ctor_set(v___x_1364_, 2, v___x_1363_);
                crate::leanh::lean_inc(v_ref_1334_);
                v___x_1365_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1365_, 0, v_ref_1334_);
                crate::leanh::lean_ctor_set(v___x_1365_, 1, v___x_1364_);
                v___x_1366_ = l_Lean_PersistentArray_push___redArg(v_traces_1354_, v___x_1365_);
                if v_isShared_1357_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1356_, 0, v___x_1366_);
                    v___x_1368_ = v___x_1356_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1366_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1377_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1353_,
                    );
                    v___x_1368_ = v_reuseFailAlloc_1377_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1352_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1351_, 4, v___x_1368_);
                    v___x_1370_ = v___x_1351_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_env_1342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_nextMacroScope_1343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_ngen_1344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 3, v_auxDeclNGen_1345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 4, v___x_1368_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 5, v_cache_1346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 6, v_messages_1347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 7, v_infoState_1348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 8, v_snapshotTasks_1349_);
                    v___x_1370_ = v_reuseFailAlloc_1376_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1371_ = lean_st_ref_set(v___y_1332_, v___x_1370_);
                v___x_1372_ = crate::leanh::lean_box(0);
                if v_isShared_1339_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1338_, 0, v___x_1372_);
                    v___x_1374_ = v___x_1338_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1375_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
                    v___x_1374_ = v_reuseFailAlloc_1375_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(
    mut v_cls_1381_: *mut crate::leanh::LeanObject,
    mut v_msg_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___y_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1388_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(
        v_cls_1381_,
        v_msg_1382_,
        v___y_1383_,
        v___y_1384_,
        v___y_1385_,
        v___y_1386_,
    );
    crate::leanh::lean_dec(v___y_1386_);
    crate::leanh::lean_dec_ref(v___y_1385_);
    crate::leanh::lean_dec(v___y_1384_);
    crate::leanh::lean_dec_ref(v___y_1383_);
    return v_res_1388_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_preprocessImpl___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1397_ = l_Lean_Meta_Grind_preprocessImpl___closed__2;
    v___x_1398_ = l_Lean_Meta_Grind_preprocessImpl___closed__4;
    v___x_1399_ = l_Lean_Name_append(v___x_1398_, v___x_1397_);
    return v___x_1399_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_preprocessImpl___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = l_Lean_Meta_Grind_preprocessImpl___closed__6;
    v___x_1402_ = l_Lean_stringToMessageData(v___x_1401_);
    return v___x_1402_;
}
pub unsafe fn lean_grind_preprocess(
    mut v_e_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
    mut v_a_1408_: *mut crate::leanh::LeanObject,
    mut v_a_1409_: *mut crate::leanh::LeanObject,
    mut v_a_1410_: *mut crate::leanh::LeanObject,
    mut v_a_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
    mut v_a_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1450_: u8 = 0;
    let mut v_proof_x3f_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1453_: u8 = 0;
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1456_: u8 = 0;
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1463_: u8 = 0;
    let mut v_unused_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1466_: u8 = 0;
    let mut v_inheritedTraceOptions_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: u8 = 0;
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1481_: u8 = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1485_: u8 = 0;
    let mut v_a_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1489_: u8 = 0;
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1493_: u8 = 0;
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut v_a_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1502_: u8 = 0;
    let mut v_a_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1506_: u8 = 0;
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1510_: u8 = 0;
    let mut v_a_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1514_: u8 = 0;
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1518_: u8 = 0;
    let mut v_a_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1522_: u8 = 0;
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1526_: u8 = 0;
    let mut v_a_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut v_a_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1538_: u8 = 0;
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1542_: u8 = 0;
    let mut v_a_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1546_: u8 = 0;
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1550_: u8 = 0;
    let mut v_a_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1554_: u8 = 0;
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1415_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_1403_, v_a_1411_);
                v_a_1416_ = crate::leanh::lean_ctor_get(v___x_1415_, 0);
                crate::leanh::lean_inc_n(v_a_1416_, 2);
                crate::leanh::lean_dec_ref(v___x_1415_);
                v___x_1417_ = l_Lean_Meta_Grind_simpCore(
                    v_a_1416_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_,
                    v_a_1411_, v_a_1412_, v_a_1413_,
                );
                if crate::leanh::lean_obj_tag(v___x_1417_) == 0 {
                    v_a_1418_ = crate::leanh::lean_ctor_get(v___x_1417_, 0);
                    crate::leanh::lean_inc(v_a_1418_);
                    crate::leanh::lean_dec_ref_known(v___x_1417_, 1);
                    v_expr_1419_ = crate::leanh::lean_ctor_get(v_a_1418_, 0);
                    crate::leanh::lean_inc_ref(v_expr_1419_);
                    v___x_1420_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_expr_1419_, v_a_1411_);
                    v_a_1421_ = crate::leanh::lean_ctor_get(v___x_1420_, 0);
                    crate::leanh::lean_inc(v_a_1421_);
                    crate::leanh::lean_dec_ref(v___x_1420_);
                    v___x_1422_ = l_Lean_Meta_Sym_unfoldReducible(
                        v_a_1421_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1422_) == 0 {
                        v_a_1423_ = crate::leanh::lean_ctor_get(v___x_1422_, 0);
                        crate::leanh::lean_inc(v_a_1423_);
                        crate::leanh::lean_dec_ref_known(v___x_1422_, 1);
                        v___x_1424_ = l_Lean_Meta_Grind_abstractNestedProofs___redArg(
                            v_a_1423_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1424_) == 0 {
                            v_a_1425_ = crate::leanh::lean_ctor_get(v___x_1424_, 0);
                            crate::leanh::lean_inc(v_a_1425_);
                            crate::leanh::lean_dec_ref_known(v___x_1424_, 1);
                            v___x_1426_ = l_Lean_Meta_Grind_markNestedSubsingletons(
                                v_a_1425_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_,
                                v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1426_) == 0 {
                                v_a_1427_ = crate::leanh::lean_ctor_get(v___x_1426_, 0);
                                crate::leanh::lean_inc(v_a_1427_);
                                crate::leanh::lean_dec_ref_known(v___x_1426_, 1);
                                v___x_1428_ = l_Lean_Meta_Grind_eraseIrrelevantMData(
                                    v_a_1427_, v_a_1412_, v_a_1413_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1428_) == 0 {
                                    v_a_1429_ = crate::leanh::lean_ctor_get(v___x_1428_, 0);
                                    crate::leanh::lean_inc(v_a_1429_);
                                    crate::leanh::lean_dec_ref_known(v___x_1428_, 1);
                                    v___x_1430_ = l_Lean_Meta_Grind_foldProjs(
                                        v_a_1429_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_1430_) == 0 {
                                        v_a_1431_ = crate::leanh::lean_ctor_get(v___x_1430_, 0);
                                        crate::leanh::lean_inc(v_a_1431_);
                                        crate::leanh::lean_dec_ref_known(v___x_1430_, 1);
                                        v___x_1432_ = l_Lean_Meta_Sym_normalizeLevels(
                                            v_a_1431_, v_a_1412_, v_a_1413_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_1432_) == 0 {
                                            v_a_1433_ = crate::leanh::lean_ctor_get(v___x_1432_, 0);
                                            crate::leanh::lean_inc(v_a_1433_);
                                            crate::leanh::lean_dec_ref_known(v___x_1432_, 1);
                                            v___x_1434_ =
                                                l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(
                                                    v_a_1433_, v_a_1410_, v_a_1411_, v_a_1412_,
                                                    v_a_1413_,
                                                );
                                            if crate::leanh::lean_obj_tag(v___x_1434_) == 0 {
                                                v_a_1435_ =
                                                    crate::leanh::lean_ctor_get(v___x_1434_, 0);
                                                crate::leanh::lean_inc_n(v_a_1435_, 2);
                                                crate::leanh::lean_dec_ref_known(v___x_1434_, 1);
                                                v___x_1436_ = l_Lean_Meta_Simp_Result_mkEqTrans(
                                                    v_a_1418_, v_a_1435_, v_a_1410_, v_a_1411_,
                                                    v_a_1412_, v_a_1413_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_1436_) == 0 {
                                                    v_a_1437_ =
                                                        crate::leanh::lean_ctor_get(v___x_1436_, 0);
                                                    crate::leanh::lean_inc(v_a_1437_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1436_,
                                                        1,
                                                    );
                                                    v_expr_1438_ =
                                                        crate::leanh::lean_ctor_get(v_a_1435_, 0);
                                                    crate::leanh::lean_inc_ref(v_expr_1438_);
                                                    crate::leanh::lean_dec(v_a_1435_);
                                                    v___x_1439_ =
                                                        l_Lean_Meta_Grind_replacePreMatchCond(
                                                            v_expr_1438_,
                                                            v_a_1410_,
                                                            v_a_1411_,
                                                            v_a_1412_,
                                                            v_a_1413_,
                                                        );
                                                    if crate::leanh::lean_obj_tag(v___x_1439_) == 0
                                                    {
                                                        v_a_1440_ = crate::leanh::lean_ctor_get(
                                                            v___x_1439_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc_n(v_a_1440_, 2);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_1439_,
                                                            1,
                                                        );
                                                        v___x_1441_ =
                                                            l_Lean_Meta_Simp_Result_mkEqTrans(
                                                                v_a_1437_, v_a_1440_, v_a_1410_,
                                                                v_a_1411_, v_a_1412_, v_a_1413_,
                                                            );
                                                        if crate::leanh::lean_obj_tag(v___x_1441_)
                                                            == 0
                                                        {
                                                            v_a_1442_ = crate::leanh::lean_ctor_get(
                                                                v___x_1441_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_1442_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_1441_,
                                                                1,
                                                            );
                                                            v_expr_1443_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_a_1440_, 0,
                                                                );
                                                            crate::leanh::lean_inc_ref(
                                                                v_expr_1443_,
                                                            );
                                                            crate::leanh::lean_dec(v_a_1440_);
                                                            v___x_1444_ = l_Lean_Meta_Sym_canon(
                                                                v_expr_1443_,
                                                                v_a_1408_,
                                                                v_a_1409_,
                                                                v_a_1410_,
                                                                v_a_1411_,
                                                                v_a_1412_,
                                                                v_a_1413_,
                                                            );
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_1444_,
                                                            ) == 0
                                                            {
                                                                v_a_1445_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_1444_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_1445_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_1444_,
                                                                    1,
                                                                );
                                                                v___x_1446_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1445_, v_a_1409_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_1446_,
                                                                ) == 0
                                                                {
                                                                    v_a_1447_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1446_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1494_ = (!crate::leanh::lean_is_exclusive(v___x_1446_)) as u8;
                                                                    if v_isSharedCheck_1494_ == 0 {
                                                                        v___x_1449_ = v___x_1446_;
                                                                        v_isShared_1450_ =
                                                                            v_isSharedCheck_1494_;
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1447_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1446_,
                                                                        );
                                                                        v___x_1449_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1450_ =
                                                                            v_isSharedCheck_1494_;
                                                                        state = 1;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v_a_1442_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_1416_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_1413_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_a_1412_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_1411_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_a_1410_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_1409_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_a_1408_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_1407_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_a_1406_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_1405_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_1404_,
                                                                    );
                                                                    v_a_1495_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1446_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1502_ = (!crate::leanh::lean_is_exclusive(v___x_1446_)) as u8;
                                                                    if v_isSharedCheck_1502_ == 0 {
                                                                        v___x_1497_ = v___x_1446_;
                                                                        v_isShared_1498_ =
                                                                            v_isSharedCheck_1502_;
                                                                        state = 10;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1495_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1446_,
                                                                        );
                                                                        v___x_1497_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1498_ =
                                                                            v_isSharedCheck_1502_;
                                                                        state = 10;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec(v_a_1442_);
                                                                crate::leanh::lean_dec(v_a_1416_);
                                                                crate::leanh::lean_dec(v_a_1413_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_a_1412_,
                                                                );
                                                                crate::leanh::lean_dec(v_a_1411_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_a_1410_,
                                                                );
                                                                crate::leanh::lean_dec(v_a_1409_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_a_1408_,
                                                                );
                                                                crate::leanh::lean_dec(v_a_1407_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_a_1406_,
                                                                );
                                                                crate::leanh::lean_dec(v_a_1405_);
                                                                crate::leanh::lean_dec(v_a_1404_);
                                                                v_a_1503_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_1444_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_1510_ = (!crate::leanh::lean_is_exclusive(v___x_1444_)) as u8;
                                                                if v_isSharedCheck_1510_ == 0 {
                                                                    v___x_1505_ = v___x_1444_;
                                                                    v_isShared_1506_ =
                                                                        v_isSharedCheck_1510_;
                                                                    state = 12;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_1503_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_1444_,
                                                                    );
                                                                    v___x_1505_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_1506_ =
                                                                        v_isSharedCheck_1510_;
                                                                    state = 12;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_a_1440_);
                                                            crate::leanh::lean_dec(v_a_1416_);
                                                            crate::leanh::lean_dec(v_a_1413_);
                                                            crate::leanh::lean_dec_ref(v_a_1412_);
                                                            crate::leanh::lean_dec(v_a_1411_);
                                                            crate::leanh::lean_dec_ref(v_a_1410_);
                                                            crate::leanh::lean_dec(v_a_1409_);
                                                            crate::leanh::lean_dec_ref(v_a_1408_);
                                                            crate::leanh::lean_dec(v_a_1407_);
                                                            crate::leanh::lean_dec_ref(v_a_1406_);
                                                            crate::leanh::lean_dec(v_a_1405_);
                                                            crate::leanh::lean_dec(v_a_1404_);
                                                            return v___x_1441_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_1437_);
                                                        crate::leanh::lean_dec(v_a_1416_);
                                                        crate::leanh::lean_dec(v_a_1413_);
                                                        crate::leanh::lean_dec_ref(v_a_1412_);
                                                        crate::leanh::lean_dec(v_a_1411_);
                                                        crate::leanh::lean_dec_ref(v_a_1410_);
                                                        crate::leanh::lean_dec(v_a_1409_);
                                                        crate::leanh::lean_dec_ref(v_a_1408_);
                                                        crate::leanh::lean_dec(v_a_1407_);
                                                        crate::leanh::lean_dec_ref(v_a_1406_);
                                                        crate::leanh::lean_dec(v_a_1405_);
                                                        crate::leanh::lean_dec(v_a_1404_);
                                                        return v___x_1439_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_1435_);
                                                    crate::leanh::lean_dec(v_a_1416_);
                                                    crate::leanh::lean_dec(v_a_1413_);
                                                    crate::leanh::lean_dec_ref(v_a_1412_);
                                                    crate::leanh::lean_dec(v_a_1411_);
                                                    crate::leanh::lean_dec_ref(v_a_1410_);
                                                    crate::leanh::lean_dec(v_a_1409_);
                                                    crate::leanh::lean_dec_ref(v_a_1408_);
                                                    crate::leanh::lean_dec(v_a_1407_);
                                                    crate::leanh::lean_dec_ref(v_a_1406_);
                                                    crate::leanh::lean_dec(v_a_1405_);
                                                    crate::leanh::lean_dec(v_a_1404_);
                                                    return v___x_1436_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_1418_);
                                                crate::leanh::lean_dec(v_a_1416_);
                                                crate::leanh::lean_dec(v_a_1413_);
                                                crate::leanh::lean_dec_ref(v_a_1412_);
                                                crate::leanh::lean_dec(v_a_1411_);
                                                crate::leanh::lean_dec_ref(v_a_1410_);
                                                crate::leanh::lean_dec(v_a_1409_);
                                                crate::leanh::lean_dec_ref(v_a_1408_);
                                                crate::leanh::lean_dec(v_a_1407_);
                                                crate::leanh::lean_dec_ref(v_a_1406_);
                                                crate::leanh::lean_dec(v_a_1405_);
                                                crate::leanh::lean_dec(v_a_1404_);
                                                return v___x_1434_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_1418_);
                                            crate::leanh::lean_dec(v_a_1416_);
                                            crate::leanh::lean_dec(v_a_1413_);
                                            crate::leanh::lean_dec_ref(v_a_1412_);
                                            crate::leanh::lean_dec(v_a_1411_);
                                            crate::leanh::lean_dec_ref(v_a_1410_);
                                            crate::leanh::lean_dec(v_a_1409_);
                                            crate::leanh::lean_dec_ref(v_a_1408_);
                                            crate::leanh::lean_dec(v_a_1407_);
                                            crate::leanh::lean_dec_ref(v_a_1406_);
                                            crate::leanh::lean_dec(v_a_1405_);
                                            crate::leanh::lean_dec(v_a_1404_);
                                            v_a_1511_ = crate::leanh::lean_ctor_get(v___x_1432_, 0);
                                            v_isSharedCheck_1518_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1432_))
                                                    as u8;
                                            if v_isSharedCheck_1518_ == 0 {
                                                v___x_1513_ = v___x_1432_;
                                                v_isShared_1514_ = v_isSharedCheck_1518_;
                                                state = 14;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1511_);
                                                crate::leanh::lean_dec(v___x_1432_);
                                                v___x_1513_ = crate::leanh::lean_box(0);
                                                v_isShared_1514_ = v_isSharedCheck_1518_;
                                                state = 14;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1418_);
                                        crate::leanh::lean_dec(v_a_1416_);
                                        crate::leanh::lean_dec(v_a_1413_);
                                        crate::leanh::lean_dec_ref(v_a_1412_);
                                        crate::leanh::lean_dec(v_a_1411_);
                                        crate::leanh::lean_dec_ref(v_a_1410_);
                                        crate::leanh::lean_dec(v_a_1409_);
                                        crate::leanh::lean_dec_ref(v_a_1408_);
                                        crate::leanh::lean_dec(v_a_1407_);
                                        crate::leanh::lean_dec_ref(v_a_1406_);
                                        crate::leanh::lean_dec(v_a_1405_);
                                        crate::leanh::lean_dec(v_a_1404_);
                                        v_a_1519_ = crate::leanh::lean_ctor_get(v___x_1430_, 0);
                                        v_isSharedCheck_1526_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1430_)) as u8;
                                        if v_isSharedCheck_1526_ == 0 {
                                            v___x_1521_ = v___x_1430_;
                                            v_isShared_1522_ = v_isSharedCheck_1526_;
                                            state = 16;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1519_);
                                            crate::leanh::lean_dec(v___x_1430_);
                                            v___x_1521_ = crate::leanh::lean_box(0);
                                            v_isShared_1522_ = v_isSharedCheck_1526_;
                                            state = 16;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1418_);
                                    crate::leanh::lean_dec(v_a_1416_);
                                    crate::leanh::lean_dec(v_a_1413_);
                                    crate::leanh::lean_dec_ref(v_a_1412_);
                                    crate::leanh::lean_dec(v_a_1411_);
                                    crate::leanh::lean_dec_ref(v_a_1410_);
                                    crate::leanh::lean_dec(v_a_1409_);
                                    crate::leanh::lean_dec_ref(v_a_1408_);
                                    crate::leanh::lean_dec(v_a_1407_);
                                    crate::leanh::lean_dec_ref(v_a_1406_);
                                    crate::leanh::lean_dec(v_a_1405_);
                                    crate::leanh::lean_dec(v_a_1404_);
                                    v_a_1527_ = crate::leanh::lean_ctor_get(v___x_1428_, 0);
                                    v_isSharedCheck_1534_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1428_)) as u8;
                                    if v_isSharedCheck_1534_ == 0 {
                                        v___x_1529_ = v___x_1428_;
                                        v_isShared_1530_ = v_isSharedCheck_1534_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1527_);
                                        crate::leanh::lean_dec(v___x_1428_);
                                        v___x_1529_ = crate::leanh::lean_box(0);
                                        v_isShared_1530_ = v_isSharedCheck_1534_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1418_);
                                crate::leanh::lean_dec(v_a_1416_);
                                crate::leanh::lean_dec(v_a_1413_);
                                crate::leanh::lean_dec_ref(v_a_1412_);
                                crate::leanh::lean_dec(v_a_1411_);
                                crate::leanh::lean_dec_ref(v_a_1410_);
                                crate::leanh::lean_dec(v_a_1409_);
                                crate::leanh::lean_dec_ref(v_a_1408_);
                                crate::leanh::lean_dec(v_a_1407_);
                                crate::leanh::lean_dec_ref(v_a_1406_);
                                crate::leanh::lean_dec(v_a_1405_);
                                crate::leanh::lean_dec(v_a_1404_);
                                v_a_1535_ = crate::leanh::lean_ctor_get(v___x_1426_, 0);
                                v_isSharedCheck_1542_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1426_)) as u8;
                                if v_isSharedCheck_1542_ == 0 {
                                    v___x_1537_ = v___x_1426_;
                                    v_isShared_1538_ = v_isSharedCheck_1542_;
                                    state = 20;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1535_);
                                    crate::leanh::lean_dec(v___x_1426_);
                                    v___x_1537_ = crate::leanh::lean_box(0);
                                    v_isShared_1538_ = v_isSharedCheck_1542_;
                                    state = 20;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1418_);
                            crate::leanh::lean_dec(v_a_1416_);
                            crate::leanh::lean_dec(v_a_1413_);
                            crate::leanh::lean_dec_ref(v_a_1412_);
                            crate::leanh::lean_dec(v_a_1411_);
                            crate::leanh::lean_dec_ref(v_a_1410_);
                            crate::leanh::lean_dec(v_a_1409_);
                            crate::leanh::lean_dec_ref(v_a_1408_);
                            crate::leanh::lean_dec(v_a_1407_);
                            crate::leanh::lean_dec_ref(v_a_1406_);
                            crate::leanh::lean_dec(v_a_1405_);
                            crate::leanh::lean_dec(v_a_1404_);
                            v_a_1543_ = crate::leanh::lean_ctor_get(v___x_1424_, 0);
                            v_isSharedCheck_1550_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1424_)) as u8;
                            if v_isSharedCheck_1550_ == 0 {
                                v___x_1545_ = v___x_1424_;
                                v_isShared_1546_ = v_isSharedCheck_1550_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1543_);
                                crate::leanh::lean_dec(v___x_1424_);
                                v___x_1545_ = crate::leanh::lean_box(0);
                                v_isShared_1546_ = v_isSharedCheck_1550_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1418_);
                        crate::leanh::lean_dec(v_a_1416_);
                        crate::leanh::lean_dec(v_a_1413_);
                        crate::leanh::lean_dec_ref(v_a_1412_);
                        crate::leanh::lean_dec(v_a_1411_);
                        crate::leanh::lean_dec_ref(v_a_1410_);
                        crate::leanh::lean_dec(v_a_1409_);
                        crate::leanh::lean_dec_ref(v_a_1408_);
                        crate::leanh::lean_dec(v_a_1407_);
                        crate::leanh::lean_dec_ref(v_a_1406_);
                        crate::leanh::lean_dec(v_a_1405_);
                        crate::leanh::lean_dec(v_a_1404_);
                        v_a_1551_ = crate::leanh::lean_ctor_get(v___x_1422_, 0);
                        v_isSharedCheck_1558_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1422_)) as u8;
                        if v_isSharedCheck_1558_ == 0 {
                            v___x_1553_ = v___x_1422_;
                            v_isShared_1554_ = v_isSharedCheck_1558_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1551_);
                            crate::leanh::lean_dec(v___x_1422_);
                            v___x_1553_ = crate::leanh::lean_box(0);
                            v_isShared_1554_ = v_isSharedCheck_1558_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1416_);
                    crate::leanh::lean_dec(v_a_1413_);
                    crate::leanh::lean_dec_ref(v_a_1412_);
                    crate::leanh::lean_dec(v_a_1411_);
                    crate::leanh::lean_dec_ref(v_a_1410_);
                    crate::leanh::lean_dec(v_a_1409_);
                    crate::leanh::lean_dec_ref(v_a_1408_);
                    crate::leanh::lean_dec(v_a_1407_);
                    crate::leanh::lean_dec_ref(v_a_1406_);
                    crate::leanh::lean_dec(v_a_1405_);
                    crate::leanh::lean_dec(v_a_1404_);
                    return v___x_1417_;
                }
            }
            1 => {
                v_options_1465_ = crate::leanh::lean_ctor_get(v_a_1412_, 2);
                v_hasTrace_1466_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_1465_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_1466_ == 0 {
                    crate::leanh::lean_dec(v_a_1416_);
                    crate::leanh::lean_dec(v_a_1413_);
                    crate::leanh::lean_dec_ref(v_a_1412_);
                    crate::leanh::lean_dec(v_a_1411_);
                    crate::leanh::lean_dec_ref(v_a_1410_);
                    crate::leanh::lean_dec(v_a_1409_);
                    crate::leanh::lean_dec_ref(v_a_1408_);
                    crate::leanh::lean_dec(v_a_1407_);
                    crate::leanh::lean_dec_ref(v_a_1406_);
                    crate::leanh::lean_dec(v_a_1405_);
                    crate::leanh::lean_dec(v_a_1404_);
                    state = 2;
                    continue;
                } else {
                    v_inheritedTraceOptions_1467_ = crate::leanh::lean_ctor_get(v_a_1412_, 13);
                    v___x_1468_ = l_Lean_Meta_Grind_preprocessImpl___closed__2;
                    v___x_1469_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_preprocessImpl___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_preprocessImpl___closed__5_once),
                        _init_l_Lean_Meta_Grind_preprocessImpl___closed__5,
                    );
                    v___x_1470_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_1467_,
                        v_options_1465_,
                        v___x_1469_,
                    );
                    if v___x_1470_ == 0 {
                        crate::leanh::lean_dec(v_a_1416_);
                        crate::leanh::lean_dec(v_a_1413_);
                        crate::leanh::lean_dec_ref(v_a_1412_);
                        crate::leanh::lean_dec(v_a_1411_);
                        crate::leanh::lean_dec_ref(v_a_1410_);
                        crate::leanh::lean_dec(v_a_1409_);
                        crate::leanh::lean_dec_ref(v_a_1408_);
                        crate::leanh::lean_dec(v_a_1407_);
                        crate::leanh::lean_dec_ref(v_a_1406_);
                        crate::leanh::lean_dec(v_a_1405_);
                        crate::leanh::lean_dec(v_a_1404_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1471_ = l_Lean_Meta_Grind_updateLastTag(
                            v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_,
                            v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_,
                        );
                        crate::leanh::lean_dec(v_a_1409_);
                        crate::leanh::lean_dec_ref(v_a_1408_);
                        crate::leanh::lean_dec(v_a_1407_);
                        crate::leanh::lean_dec_ref(v_a_1406_);
                        crate::leanh::lean_dec(v_a_1405_);
                        crate::leanh::lean_dec(v_a_1404_);
                        if crate::leanh::lean_obj_tag(v___x_1471_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1471_, 1);
                            v___x_1472_ = l_Lean_MessageData_ofExpr(v_a_1416_);
                            v___x_1473_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_preprocessImpl___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_preprocessImpl___closed__7_once
                                ),
                                _init_l_Lean_Meta_Grind_preprocessImpl___closed__7,
                            );
                            v___x_1474_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1474_, 0, v___x_1472_);
                            crate::leanh::lean_ctor_set(v___x_1474_, 1, v___x_1473_);
                            crate::leanh::lean_inc(v_a_1447_);
                            v___x_1475_ = l_Lean_MessageData_ofExpr(v_a_1447_);
                            v___x_1476_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1476_, 0, v___x_1474_);
                            crate::leanh::lean_ctor_set(v___x_1476_, 1, v___x_1475_);
                            v___x_1477_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1468_, v___x_1476_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
                            crate::leanh::lean_dec(v_a_1413_);
                            crate::leanh::lean_dec_ref(v_a_1412_);
                            crate::leanh::lean_dec(v_a_1411_);
                            crate::leanh::lean_dec_ref(v_a_1410_);
                            if crate::leanh::lean_obj_tag(v___x_1477_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1477_, 1);
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_1449_);
                                crate::leanh::lean_dec(v_a_1447_);
                                crate::leanh::lean_dec(v_a_1442_);
                                v_a_1478_ = crate::leanh::lean_ctor_get(v___x_1477_, 0);
                                v_isSharedCheck_1485_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1477_)) as u8;
                                if v_isSharedCheck_1485_ == 0 {
                                    v___x_1480_ = v___x_1477_;
                                    v_isShared_1481_ = v_isSharedCheck_1485_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1478_);
                                    crate::leanh::lean_dec(v___x_1477_);
                                    v___x_1480_ = crate::leanh::lean_box(0);
                                    v_isShared_1481_ = v_isSharedCheck_1485_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1449_);
                            crate::leanh::lean_dec(v_a_1447_);
                            crate::leanh::lean_dec(v_a_1442_);
                            crate::leanh::lean_dec(v_a_1416_);
                            crate::leanh::lean_dec(v_a_1413_);
                            crate::leanh::lean_dec_ref(v_a_1412_);
                            crate::leanh::lean_dec(v_a_1411_);
                            crate::leanh::lean_dec_ref(v_a_1410_);
                            v_a_1486_ = crate::leanh::lean_ctor_get(v___x_1471_, 0);
                            v_isSharedCheck_1493_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1471_)) as u8;
                            if v_isSharedCheck_1493_ == 0 {
                                v___x_1488_ = v___x_1471_;
                                v_isShared_1489_ = v_isSharedCheck_1493_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1486_);
                                crate::leanh::lean_dec(v___x_1471_);
                                v___x_1488_ = crate::leanh::lean_box(0);
                                v_isShared_1489_ = v_isSharedCheck_1493_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v_proof_x3f_1452_ = crate::leanh::lean_ctor_get(v_a_1442_, 1);
                v_cache_1453_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1442_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_1463_ = (!crate::leanh::lean_is_exclusive(v_a_1442_)) as u8;
                if v_isSharedCheck_1463_ == 0 {
                    v_unused_1464_ = crate::leanh::lean_ctor_get(v_a_1442_, 0);
                    crate::leanh::lean_dec(v_unused_1464_);
                    v___x_1455_ = v_a_1442_;
                    v_isShared_1456_ = v_isSharedCheck_1463_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_proof_x3f_1452_);
                    crate::leanh::lean_dec(v_a_1442_);
                    v___x_1455_ = crate::leanh::lean_box(0);
                    v_isShared_1456_ = v_isSharedCheck_1463_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1456_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1455_, 0, v_a_1447_);
                    v___x_1458_ = v___x_1455_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1462_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1447_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_proof_x3f_1452_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1462_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_cache_1453_,
                    );
                    v___x_1458_ = v_reuseFailAlloc_1462_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1449_, 0, v___x_1458_);
                    v___x_1460_ = v___x_1449_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
                    v___x_1460_ = v_reuseFailAlloc_1461_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1460_;
            }
            6 => {
                if v_isShared_1481_ == 0 {
                    v___x_1483_ = v___x_1480_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1484_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
                    v___x_1483_ = v_reuseFailAlloc_1484_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1483_;
            }
            8 => {
                if v_isShared_1489_ == 0 {
                    v___x_1491_ = v___x_1488_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
                    v___x_1491_ = v_reuseFailAlloc_1492_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1491_;
            }
            10 => {
                if v_isShared_1498_ == 0 {
                    v___x_1500_ = v___x_1497_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
                    v___x_1500_ = v_reuseFailAlloc_1501_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1500_;
            }
            12 => {
                if v_isShared_1506_ == 0 {
                    v___x_1508_ = v___x_1505_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1509_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
                    v___x_1508_ = v_reuseFailAlloc_1509_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1508_;
            }
            14 => {
                if v_isShared_1514_ == 0 {
                    v___x_1516_ = v___x_1513_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1517_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
                    v___x_1516_ = v_reuseFailAlloc_1517_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1516_;
            }
            16 => {
                if v_isShared_1522_ == 0 {
                    v___x_1524_ = v___x_1521_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
                    v___x_1524_ = v_reuseFailAlloc_1525_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1524_;
            }
            18 => {
                if v_isShared_1530_ == 0 {
                    v___x_1532_ = v___x_1529_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1533_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
                    v___x_1532_ = v_reuseFailAlloc_1533_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1532_;
            }
            20 => {
                if v_isShared_1538_ == 0 {
                    v___x_1540_ = v___x_1537_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
                    v___x_1540_ = v_reuseFailAlloc_1541_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1540_;
            }
            22 => {
                if v_isShared_1546_ == 0 {
                    v___x_1548_ = v___x_1545_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
                    v___x_1548_ = v_reuseFailAlloc_1549_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1548_;
            }
            24 => {
                if v_isShared_1554_ == 0 {
                    v___x_1556_ = v___x_1553_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1557_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
                    v___x_1556_ = v_reuseFailAlloc_1557_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_preprocessImpl___boxed(
    mut v_e_1559_: *mut crate::leanh::LeanObject,
    mut v_a_1560_: *mut crate::leanh::LeanObject,
    mut v_a_1561_: *mut crate::leanh::LeanObject,
    mut v_a_1562_: *mut crate::leanh::LeanObject,
    mut v_a_1563_: *mut crate::leanh::LeanObject,
    mut v_a_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
    mut v_a_1566_: *mut crate::leanh::LeanObject,
    mut v_a_1567_: *mut crate::leanh::LeanObject,
    mut v_a_1568_: *mut crate::leanh::LeanObject,
    mut v_a_1569_: *mut crate::leanh::LeanObject,
    mut v_a_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = lean_grind_preprocess(
        v_e_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_,
        v_a_1567_, v_a_1568_, v_a_1569_,
    );
    return v_res_1571_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(
    mut v_cls_1572_: *mut crate::leanh::LeanObject,
    mut v_msg_1573_: *mut crate::leanh::LeanObject,
    mut v___y_1574_: *mut crate::leanh::LeanObject,
    mut v___y_1575_: *mut crate::leanh::LeanObject,
    mut v___y_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
    mut v___y_1578_: *mut crate::leanh::LeanObject,
    mut v___y_1579_: *mut crate::leanh::LeanObject,
    mut v___y_1580_: *mut crate::leanh::LeanObject,
    mut v___y_1581_: *mut crate::leanh::LeanObject,
    mut v___y_1582_: *mut crate::leanh::LeanObject,
    mut v___y_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(
        v_cls_1572_,
        v_msg_1573_,
        v___y_1580_,
        v___y_1581_,
        v___y_1582_,
        v___y_1583_,
    );
    return v___x_1585_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(
    mut v_cls_1586_: *mut crate::leanh::LeanObject,
    mut v_msg_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
    mut v___y_1591_: *mut crate::leanh::LeanObject,
    mut v___y_1592_: *mut crate::leanh::LeanObject,
    mut v___y_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1599_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(
        v_cls_1586_,
        v_msg_1587_,
        v___y_1588_,
        v___y_1589_,
        v___y_1590_,
        v___y_1591_,
        v___y_1592_,
        v___y_1593_,
        v___y_1594_,
        v___y_1595_,
        v___y_1596_,
        v___y_1597_,
    );
    crate::leanh::lean_dec(v___y_1597_);
    crate::leanh::lean_dec_ref(v___y_1596_);
    crate::leanh::lean_dec(v___y_1595_);
    crate::leanh::lean_dec_ref(v___y_1594_);
    crate::leanh::lean_dec(v___y_1593_);
    crate::leanh::lean_dec_ref(v___y_1592_);
    crate::leanh::lean_dec(v___y_1591_);
    crate::leanh::lean_dec_ref(v___y_1590_);
    crate::leanh::lean_dec(v___y_1589_);
    crate::leanh::lean_dec(v___y_1588_);
    return v_res_1599_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_Meta_Grind_pushNewFact_x27___closed__2;
    v___x_1607_ = l_Lean_Meta_Grind_preprocessImpl___closed__4;
    v___x_1608_ = l_Lean_Name_append(v___x_1607_, v___x_1606_);
    return v___x_1608_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1610_ = l_Lean_Meta_Grind_pushNewFact_x27___closed__4;
    v___x_1611_ = l_Lean_stringToMessageData(v___x_1610_);
    return v___x_1611_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Lean_Meta_Grind_pushNewFact_x27___closed__9;
    v___x_1621_ = l_Lean_Meta_Grind_pushNewFact_x27___closed__8;
    v___x_1622_ = l_Lean_mkConst(v___x_1621_, v___x_1620_);
    return v___x_1622_;
}
pub unsafe fn l_Lean_Meta_Grind_pushNewFact_x27(
    mut v_prop_1623_: *mut crate::leanh::LeanObject,
    mut v_proof_1624_: *mut crate::leanh::LeanObject,
    mut v_generation_1625_: *mut crate::leanh::LeanObject,
    mut v_a_1626_: *mut crate::leanh::LeanObject,
    mut v_a_1627_: *mut crate::leanh::LeanObject,
    mut v_a_1628_: *mut crate::leanh::LeanObject,
    mut v_a_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: *mut crate::leanh::LeanObject,
    mut v_a_1631_: *mut crate::leanh::LeanObject,
    mut v_a_1632_: *mut crate::leanh::LeanObject,
    mut v_a_1633_: *mut crate::leanh::LeanObject,
    mut v_a_1634_: *mut crate::leanh::LeanObject,
    mut v_a_1635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v_expr_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_x3f_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1652_: u8 = 0;
    let mut v_nextDeclIdx_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appMap_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newFacts_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_1661_: u8 = 0;
    let mut v_nextIdx_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facts_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sstates_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1673_: u8 = 0;
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut v___y_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1692_: u8 = 0;
    let mut v_inheritedTraceOptions_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1706_: u8 = 0;
    let mut v_a_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1710_: u8 = 0;
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1635_);
                crate::leanh::lean_inc_ref(v_a_1634_);
                crate::leanh::lean_inc(v_a_1633_);
                crate::leanh::lean_inc_ref(v_a_1632_);
                crate::leanh::lean_inc(v_a_1631_);
                crate::leanh::lean_inc_ref(v_a_1630_);
                crate::leanh::lean_inc(v_a_1629_);
                crate::leanh::lean_inc_ref(v_a_1628_);
                crate::leanh::lean_inc(v_a_1627_);
                crate::leanh::lean_inc(v_a_1626_);
                crate::leanh::lean_inc_ref(v_prop_1623_);
                v___x_1637_ = lean_grind_preprocess(
                    v_prop_1623_,
                    v_a_1626_,
                    v_a_1627_,
                    v_a_1628_,
                    v_a_1629_,
                    v_a_1630_,
                    v_a_1631_,
                    v_a_1632_,
                    v_a_1633_,
                    v_a_1634_,
                    v_a_1635_,
                );
                if crate::leanh::lean_obj_tag(v___x_1637_) == 0 {
                    v_a_1638_ = crate::leanh::lean_ctor_get(v___x_1637_, 0);
                    v_isSharedCheck_1706_ = (!crate::leanh::lean_is_exclusive(v___x_1637_)) as u8;
                    if v_isSharedCheck_1706_ == 0 {
                        v___x_1640_ = v___x_1637_;
                        v_isShared_1641_ = v_isSharedCheck_1706_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1638_);
                        crate::leanh::lean_dec(v___x_1637_);
                        v___x_1640_ = crate::leanh::lean_box(0);
                        v_isShared_1641_ = v_isSharedCheck_1706_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_generation_1625_);
                    crate::leanh::lean_dec_ref(v_proof_1624_);
                    crate::leanh::lean_dec_ref(v_prop_1623_);
                    v_a_1707_ = crate::leanh::lean_ctor_get(v___x_1637_, 0);
                    v_isSharedCheck_1714_ = (!crate::leanh::lean_is_exclusive(v___x_1637_)) as u8;
                    if v_isSharedCheck_1714_ == 0 {
                        v___x_1709_ = v___x_1637_;
                        v_isShared_1710_ = v_isSharedCheck_1714_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1707_);
                        crate::leanh::lean_dec(v___x_1637_);
                        v___x_1709_ = crate::leanh::lean_box(0);
                        v_isShared_1710_ = v_isSharedCheck_1714_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_expr_1642_ = crate::leanh::lean_ctor_get(v_a_1638_, 0);
                crate::leanh::lean_inc_ref(v_expr_1642_);
                v_proof_x3f_1643_ = crate::leanh::lean_ctor_get(v_a_1638_, 1);
                crate::leanh::lean_inc(v_proof_x3f_1643_);
                crate::leanh::lean_dec(v_a_1638_);
                if crate::leanh::lean_obj_tag(v_proof_x3f_1643_) == 1 {
                    v_val_1703_ = crate::leanh::lean_ctor_get(v_proof_x3f_1643_, 0);
                    crate::leanh::lean_inc(v_val_1703_);
                    crate::leanh::lean_dec_ref_known(v_proof_x3f_1643_, 1);
                    v___x_1704_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNewFact_x27___closed__10),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNewFact_x27___closed__10_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10,
                    );
                    crate::leanh::lean_inc_ref(v_expr_1642_);
                    crate::leanh::lean_inc_ref(v_prop_1623_);
                    v___x_1705_ = l_Lean_mkApp4(
                        v___x_1704_,
                        v_prop_1623_,
                        v_expr_1642_,
                        v_val_1703_,
                        v_proof_1624_,
                    );
                    v___y_1690_ = v___x_1705_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_proof_x3f_1643_);
                    v___y_1690_ = v_proof_1624_;
                    state = 8;
                    continue;
                }
            }
            2 => {
                v___x_1647_ = lean_st_ref_take(v___y_1646_);
                v_toGoalState_1648_ = crate::leanh::lean_ctor_get(v___x_1647_, 0);
                v_mvarId_1649_ = crate::leanh::lean_ctor_get(v___x_1647_, 1);
                v_isSharedCheck_1688_ = (!crate::leanh::lean_is_exclusive(v___x_1647_)) as u8;
                if v_isSharedCheck_1688_ == 0 {
                    v___x_1651_ = v___x_1647_;
                    v_isShared_1652_ = v_isSharedCheck_1688_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_1649_);
                    crate::leanh::lean_inc(v_toGoalState_1648_);
                    crate::leanh::lean_dec(v___x_1647_);
                    v___x_1651_ = crate::leanh::lean_box(0);
                    v_isShared_1652_ = v_isSharedCheck_1688_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_nextDeclIdx_1653_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 0);
                v_enodeMap_1654_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 1);
                v_exprs_1655_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 2);
                v_parents_1656_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 3);
                v_congrTable_1657_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 4);
                v_appMap_1658_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 5);
                v_indicesFound_1659_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 6);
                v_newFacts_1660_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 7);
                v_inconsistent_1661_ = crate::leanh::lean_ctor_get_uint8(
                    v_toGoalState_1648_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_nextIdx_1662_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 8);
                v_newRawFacts_1663_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 9);
                v_facts_1664_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 10);
                v_extThms_1665_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 11);
                v_ematch_1666_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 12);
                v_inj_1667_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 13);
                v_split_1668_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 14);
                v_clean_1669_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 15);
                v_sstates_1670_ = crate::leanh::lean_ctor_get(v_toGoalState_1648_, 16);
                v_isSharedCheck_1687_ =
                    (!crate::leanh::lean_is_exclusive(v_toGoalState_1648_)) as u8;
                if v_isSharedCheck_1687_ == 0 {
                    v___x_1672_ = v_toGoalState_1648_;
                    v_isShared_1673_ = v_isSharedCheck_1687_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_sstates_1670_);
                    crate::leanh::lean_inc(v_clean_1669_);
                    crate::leanh::lean_inc(v_split_1668_);
                    crate::leanh::lean_inc(v_inj_1667_);
                    crate::leanh::lean_inc(v_ematch_1666_);
                    crate::leanh::lean_inc(v_extThms_1665_);
                    crate::leanh::lean_inc(v_facts_1664_);
                    crate::leanh::lean_inc(v_newRawFacts_1663_);
                    crate::leanh::lean_inc(v_nextIdx_1662_);
                    crate::leanh::lean_inc(v_newFacts_1660_);
                    crate::leanh::lean_inc(v_indicesFound_1659_);
                    crate::leanh::lean_inc(v_appMap_1658_);
                    crate::leanh::lean_inc(v_congrTable_1657_);
                    crate::leanh::lean_inc(v_parents_1656_);
                    crate::leanh::lean_inc(v_exprs_1655_);
                    crate::leanh::lean_inc(v_enodeMap_1654_);
                    crate::leanh::lean_inc(v_nextDeclIdx_1653_);
                    crate::leanh::lean_dec(v_toGoalState_1648_);
                    v___x_1672_ = crate::leanh::lean_box(0);
                    v_isShared_1673_ = v_isSharedCheck_1687_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1674_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1674_, 0, v_expr_1642_);
                crate::leanh::lean_ctor_set(v___x_1674_, 1, v___y_1645_);
                crate::leanh::lean_ctor_set(v___x_1674_, 2, v_generation_1625_);
                v___x_1675_ = lean_array_push(v_newFacts_1660_, v___x_1674_);
                if v_isShared_1673_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1672_, 7, v___x_1675_);
                    v___x_1677_ = v___x_1672_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = crate::leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_nextDeclIdx_1653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_enodeMap_1654_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_exprs_1655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_parents_1656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_congrTable_1657_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 5, v_appMap_1658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 6, v_indicesFound_1659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 7, v___x_1675_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 8, v_nextIdx_1662_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 9, v_newRawFacts_1663_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 10, v_facts_1664_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 11, v_extThms_1665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 12, v_ematch_1666_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 13, v_inj_1667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 14, v_split_1668_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 15, v_clean_1669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 16, v_sstates_1670_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1686_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_inconsistent_1661_,
                    );
                    v___x_1677_ = v_reuseFailAlloc_1686_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1652_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1651_, 0, v___x_1677_);
                    v___x_1679_ = v___x_1651_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1685_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1677_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_mvarId_1649_);
                    v___x_1679_ = v_reuseFailAlloc_1685_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1680_ = lean_st_ref_set(v___y_1646_, v___x_1679_);
                v___x_1681_ = crate::leanh::lean_box(0);
                if v_isShared_1641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1640_, 0, v___x_1681_);
                    v___x_1683_ = v___x_1640_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
                    v___x_1683_ = v_reuseFailAlloc_1684_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1683_;
            }
            8 => {
                v_options_1691_ = crate::leanh::lean_ctor_get(v_a_1634_, 2);
                v_hasTrace_1692_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_1691_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_1692_ == 0 {
                    crate::leanh::lean_dec_ref(v_prop_1623_);
                    v___y_1645_ = v___y_1690_;
                    v___y_1646_ = v_a_1626_;
                    state = 2;
                    continue;
                } else {
                    v_inheritedTraceOptions_1693_ = crate::leanh::lean_ctor_get(v_a_1634_, 13);
                    v___x_1694_ = l_Lean_Meta_Grind_pushNewFact_x27___closed__2;
                    v___x_1695_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNewFact_x27___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once),
                        _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3,
                    );
                    v___x_1696_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_1693_,
                        v_options_1691_,
                        v___x_1695_,
                    );
                    if v___x_1696_ == 0 {
                        crate::leanh::lean_dec_ref(v_prop_1623_);
                        v___y_1645_ = v___y_1690_;
                        v___y_1646_ = v_a_1626_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1697_ = l_Lean_MessageData_ofExpr(v_prop_1623_);
                        v___x_1698_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNewFact_x27___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNewFact_x27___closed__5_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5,
                        );
                        v___x_1699_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1699_, 0, v___x_1697_);
                        crate::leanh::lean_ctor_set(v___x_1699_, 1, v___x_1698_);
                        crate::leanh::lean_inc_ref(v_expr_1642_);
                        v___x_1700_ = l_Lean_MessageData_ofExpr(v_expr_1642_);
                        v___x_1701_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1701_, 0, v___x_1699_);
                        crate::leanh::lean_ctor_set(v___x_1701_, 1, v___x_1700_);
                        v___x_1702_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1694_, v___x_1701_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
                        if crate::leanh::lean_obj_tag(v___x_1702_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1702_, 1);
                            v___y_1645_ = v___y_1690_;
                            v___y_1646_ = v_a_1626_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_1690_);
                            crate::leanh::lean_dec_ref(v_expr_1642_);
                            crate::leanh::lean_del_object(v___x_1640_);
                            crate::leanh::lean_dec(v_generation_1625_);
                            return v___x_1702_;
                        }
                    }
                }
            }
            9 => {
                if v_isShared_1710_ == 0 {
                    v___x_1712_ = v___x_1709_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
                    v___x_1712_ = v_reuseFailAlloc_1713_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_pushNewFact_x27___boxed(
    mut v_prop_1715_: *mut crate::leanh::LeanObject,
    mut v_proof_1716_: *mut crate::leanh::LeanObject,
    mut v_generation_1717_: *mut crate::leanh::LeanObject,
    mut v_a_1718_: *mut crate::leanh::LeanObject,
    mut v_a_1719_: *mut crate::leanh::LeanObject,
    mut v_a_1720_: *mut crate::leanh::LeanObject,
    mut v_a_1721_: *mut crate::leanh::LeanObject,
    mut v_a_1722_: *mut crate::leanh::LeanObject,
    mut v_a_1723_: *mut crate::leanh::LeanObject,
    mut v_a_1724_: *mut crate::leanh::LeanObject,
    mut v_a_1725_: *mut crate::leanh::LeanObject,
    mut v_a_1726_: *mut crate::leanh::LeanObject,
    mut v_a_1727_: *mut crate::leanh::LeanObject,
    mut v_a_1728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1729_ = l_Lean_Meta_Grind_pushNewFact_x27(
        v_prop_1715_,
        v_proof_1716_,
        v_generation_1717_,
        v_a_1718_,
        v_a_1719_,
        v_a_1720_,
        v_a_1721_,
        v_a_1722_,
        v_a_1723_,
        v_a_1724_,
        v_a_1725_,
        v_a_1726_,
        v_a_1727_,
    );
    crate::leanh::lean_dec(v_a_1727_);
    crate::leanh::lean_dec_ref(v_a_1726_);
    crate::leanh::lean_dec(v_a_1725_);
    crate::leanh::lean_dec_ref(v_a_1724_);
    crate::leanh::lean_dec(v_a_1723_);
    crate::leanh::lean_dec_ref(v_a_1722_);
    crate::leanh::lean_dec(v_a_1721_);
    crate::leanh::lean_dec_ref(v_a_1720_);
    crate::leanh::lean_dec(v_a_1719_);
    crate::leanh::lean_dec(v_a_1718_);
    return v_res_1729_;
}
pub unsafe fn l_Lean_Meta_Grind_pushNewFact(
    mut v_proof_1730_: *mut crate::leanh::LeanObject,
    mut v_generation_1731_: *mut crate::leanh::LeanObject,
    mut v_a_1732_: *mut crate::leanh::LeanObject,
    mut v_a_1733_: *mut crate::leanh::LeanObject,
    mut v_a_1734_: *mut crate::leanh::LeanObject,
    mut v_a_1735_: *mut crate::leanh::LeanObject,
    mut v_a_1736_: *mut crate::leanh::LeanObject,
    mut v_a_1737_: *mut crate::leanh::LeanObject,
    mut v_a_1738_: *mut crate::leanh::LeanObject,
    mut v_a_1739_: *mut crate::leanh::LeanObject,
    mut v_a_1740_: *mut crate::leanh::LeanObject,
    mut v_a_1741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1745_: u8 = 0;
    let mut v_a_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: u8 = 0;
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1760_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1741_);
                crate::leanh::lean_inc_ref(v_a_1740_);
                crate::leanh::lean_inc(v_a_1739_);
                crate::leanh::lean_inc_ref(v_a_1738_);
                crate::leanh::lean_inc_ref(v_proof_1730_);
                v___x_1743_ =
                    lean_infer_type(v_proof_1730_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
                if crate::leanh::lean_obj_tag(v___x_1743_) == 0 {
                    v_options_1744_ = crate::leanh::lean_ctor_get(v_a_1740_, 2);
                    v_hasTrace_1745_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_1744_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_1745_ == 0 {
                        v_a_1746_ = crate::leanh::lean_ctor_get(v___x_1743_, 0);
                        crate::leanh::lean_inc(v_a_1746_);
                        crate::leanh::lean_dec_ref_known(v___x_1743_, 1);
                        v___x_1747_ = l_Lean_Meta_Grind_pushNewFact_x27(
                            v_a_1746_,
                            v_proof_1730_,
                            v_generation_1731_,
                            v_a_1732_,
                            v_a_1733_,
                            v_a_1734_,
                            v_a_1735_,
                            v_a_1736_,
                            v_a_1737_,
                            v_a_1738_,
                            v_a_1739_,
                            v_a_1740_,
                            v_a_1741_,
                        );
                        return v___x_1747_;
                    } else {
                        v_a_1748_ = crate::leanh::lean_ctor_get(v___x_1743_, 0);
                        crate::leanh::lean_inc(v_a_1748_);
                        crate::leanh::lean_dec_ref_known(v___x_1743_, 1);
                        v_inheritedTraceOptions_1749_ = crate::leanh::lean_ctor_get(v_a_1740_, 13);
                        v___x_1750_ = l_Lean_Meta_Grind_pushNewFact_x27___closed__2;
                        v___x_1751_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNewFact_x27___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3,
                        );
                        v___x_1752_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_1749_,
                            v_options_1744_,
                            v___x_1751_,
                        );
                        if v___x_1752_ == 0 {
                            v___x_1753_ = l_Lean_Meta_Grind_pushNewFact_x27(
                                v_a_1748_,
                                v_proof_1730_,
                                v_generation_1731_,
                                v_a_1732_,
                                v_a_1733_,
                                v_a_1734_,
                                v_a_1735_,
                                v_a_1736_,
                                v_a_1737_,
                                v_a_1738_,
                                v_a_1739_,
                                v_a_1740_,
                                v_a_1741_,
                            );
                            return v___x_1753_;
                        } else {
                            crate::leanh::lean_inc(v_a_1748_);
                            v___x_1754_ = l_Lean_MessageData_ofExpr(v_a_1748_);
                            v___x_1755_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1750_, v___x_1754_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
                            if crate::leanh::lean_obj_tag(v___x_1755_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1755_, 1);
                                v___x_1756_ = l_Lean_Meta_Grind_pushNewFact_x27(
                                    v_a_1748_,
                                    v_proof_1730_,
                                    v_generation_1731_,
                                    v_a_1732_,
                                    v_a_1733_,
                                    v_a_1734_,
                                    v_a_1735_,
                                    v_a_1736_,
                                    v_a_1737_,
                                    v_a_1738_,
                                    v_a_1739_,
                                    v_a_1740_,
                                    v_a_1741_,
                                );
                                return v___x_1756_;
                            } else {
                                crate::leanh::lean_dec(v_a_1748_);
                                crate::leanh::lean_dec(v_generation_1731_);
                                crate::leanh::lean_dec_ref(v_proof_1730_);
                                return v___x_1755_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_generation_1731_);
                    crate::leanh::lean_dec_ref(v_proof_1730_);
                    v_a_1757_ = crate::leanh::lean_ctor_get(v___x_1743_, 0);
                    v_isSharedCheck_1764_ = (!crate::leanh::lean_is_exclusive(v___x_1743_)) as u8;
                    if v_isSharedCheck_1764_ == 0 {
                        v___x_1759_ = v___x_1743_;
                        v_isShared_1760_ = v_isSharedCheck_1764_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1757_);
                        crate::leanh::lean_dec(v___x_1743_);
                        v___x_1759_ = crate::leanh::lean_box(0);
                        v_isShared_1760_ = v_isSharedCheck_1764_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1760_ == 0 {
                    v___x_1762_ = v___x_1759_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
                    v___x_1762_ = v_reuseFailAlloc_1763_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1762_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_pushNewFact___boxed(
    mut v_proof_1765_: *mut crate::leanh::LeanObject,
    mut v_generation_1766_: *mut crate::leanh::LeanObject,
    mut v_a_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
    mut v_a_1769_: *mut crate::leanh::LeanObject,
    mut v_a_1770_: *mut crate::leanh::LeanObject,
    mut v_a_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
    mut v_a_1773_: *mut crate::leanh::LeanObject,
    mut v_a_1774_: *mut crate::leanh::LeanObject,
    mut v_a_1775_: *mut crate::leanh::LeanObject,
    mut v_a_1776_: *mut crate::leanh::LeanObject,
    mut v_a_1777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1778_ = l_Lean_Meta_Grind_pushNewFact(
        v_proof_1765_,
        v_generation_1766_,
        v_a_1767_,
        v_a_1768_,
        v_a_1769_,
        v_a_1770_,
        v_a_1771_,
        v_a_1772_,
        v_a_1773_,
        v_a_1774_,
        v_a_1775_,
        v_a_1776_,
    );
    crate::leanh::lean_dec(v_a_1776_);
    crate::leanh::lean_dec_ref(v_a_1775_);
    crate::leanh::lean_dec(v_a_1774_);
    crate::leanh::lean_dec_ref(v_a_1773_);
    crate::leanh::lean_dec(v_a_1772_);
    crate::leanh::lean_dec_ref(v_a_1771_);
    crate::leanh::lean_dec(v_a_1770_);
    crate::leanh::lean_dec_ref(v_a_1769_);
    crate::leanh::lean_dec(v_a_1768_);
    crate::leanh::lean_dec(v_a_1767_);
    return v_res_1778_;
}
pub unsafe fn l_Lean_Meta_Grind_preprocessLight___redArg(
    mut v_e_1779_: *mut crate::leanh::LeanObject,
    mut v_a_1780_: *mut crate::leanh::LeanObject,
    mut v_a_1781_: *mut crate::leanh::LeanObject,
    mut v_a_1782_: *mut crate::leanh::LeanObject,
    mut v_a_1783_: *mut crate::leanh::LeanObject,
    mut v_a_1784_: *mut crate::leanh::LeanObject,
    mut v_a_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
    mut v_a_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1790_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(
        v_e_1779_, v_a_1786_,
    );
    v_a_1791_ = crate::leanh::lean_ctor_get(v___x_1790_, 0);
    crate::leanh::lean_inc(v_a_1791_);
    crate::leanh::lean_dec_ref(v___x_1790_);
    v___x_1792_ =
        l_Lean_Meta_Sym_unfoldReducible(v_a_1791_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
    if crate::leanh::lean_obj_tag(v___x_1792_) == 0 {
        let mut v_a_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1793_ = crate::leanh::lean_ctor_get(v___x_1792_, 0);
        crate::leanh::lean_inc(v_a_1793_);
        crate::leanh::lean_dec_ref_known(v___x_1792_, 1);
        v___x_1794_ = l_Lean_Meta_Grind_markNestedSubsingletons(
            v_a_1793_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_,
            v_a_1787_, v_a_1788_,
        );
        if crate::leanh::lean_obj_tag(v___x_1794_) == 0 {
            let mut v_a_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1795_ = crate::leanh::lean_ctor_get(v___x_1794_, 0);
            crate::leanh::lean_inc(v_a_1795_);
            crate::leanh::lean_dec_ref_known(v___x_1794_, 1);
            v___x_1796_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_1795_, v_a_1787_, v_a_1788_);
            if crate::leanh::lean_obj_tag(v___x_1796_) == 0 {
                let mut v_a_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_1797_ = crate::leanh::lean_ctor_get(v___x_1796_, 0);
                crate::leanh::lean_inc(v_a_1797_);
                crate::leanh::lean_dec_ref_known(v___x_1796_, 1);
                v___x_1798_ = l_Lean_Meta_Grind_foldProjs(
                    v_a_1797_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_,
                );
                if crate::leanh::lean_obj_tag(v___x_1798_) == 0 {
                    let mut v_a_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_a_1799_ = crate::leanh::lean_ctor_get(v___x_1798_, 0);
                    crate::leanh::lean_inc(v_a_1799_);
                    crate::leanh::lean_dec_ref_known(v___x_1798_, 1);
                    v___x_1800_ = l_Lean_Meta_Sym_normalizeLevels(v_a_1799_, v_a_1787_, v_a_1788_);
                    if crate::leanh::lean_obj_tag(v___x_1800_) == 0 {
                        let mut v_a_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_a_1801_ = crate::leanh::lean_ctor_get(v___x_1800_, 0);
                        crate::leanh::lean_inc(v_a_1801_);
                        crate::leanh::lean_dec_ref_known(v___x_1800_, 1);
                        v___x_1802_ = l_Lean_Meta_Sym_canon(
                            v_a_1801_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_,
                            v_a_1788_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1802_) == 0 {
                            let mut v_a_1803_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1804_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v_a_1803_ = crate::leanh::lean_ctor_get(v___x_1802_, 0);
                            crate::leanh::lean_inc(v_a_1803_);
                            crate::leanh::lean_dec_ref_known(v___x_1802_, 1);
                            v___x_1804_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_1803_, v_a_1784_);
                            return v___x_1804_;
                        } else {
                            return v___x_1802_;
                        }
                    } else {
                        return v___x_1800_;
                    }
                } else {
                    return v___x_1798_;
                }
            } else {
                return v___x_1796_;
            }
        } else {
            return v___x_1794_;
        }
    } else {
        return v___x_1792_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_preprocessLight___redArg___boxed(
    mut v_e_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
    mut v_a_1807_: *mut crate::leanh::LeanObject,
    mut v_a_1808_: *mut crate::leanh::LeanObject,
    mut v_a_1809_: *mut crate::leanh::LeanObject,
    mut v_a_1810_: *mut crate::leanh::LeanObject,
    mut v_a_1811_: *mut crate::leanh::LeanObject,
    mut v_a_1812_: *mut crate::leanh::LeanObject,
    mut v_a_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
    mut v_a_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1816_ = l_Lean_Meta_Grind_preprocessLight___redArg(
        v_e_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_,
        v_a_1813_, v_a_1814_,
    );
    crate::leanh::lean_dec(v_a_1814_);
    crate::leanh::lean_dec_ref(v_a_1813_);
    crate::leanh::lean_dec(v_a_1812_);
    crate::leanh::lean_dec_ref(v_a_1811_);
    crate::leanh::lean_dec(v_a_1810_);
    crate::leanh::lean_dec_ref(v_a_1809_);
    crate::leanh::lean_dec(v_a_1808_);
    crate::leanh::lean_dec_ref(v_a_1807_);
    crate::leanh::lean_dec(v_a_1806_);
    return v_res_1816_;
}
pub unsafe fn l_Lean_Meta_Grind_preprocessLight(
    mut v_e_1817_: *mut crate::leanh::LeanObject,
    mut v_a_1818_: *mut crate::leanh::LeanObject,
    mut v_a_1819_: *mut crate::leanh::LeanObject,
    mut v_a_1820_: *mut crate::leanh::LeanObject,
    mut v_a_1821_: *mut crate::leanh::LeanObject,
    mut v_a_1822_: *mut crate::leanh::LeanObject,
    mut v_a_1823_: *mut crate::leanh::LeanObject,
    mut v_a_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1829_ = l_Lean_Meta_Grind_preprocessLight___redArg(
        v_e_1817_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_,
        v_a_1826_, v_a_1827_,
    );
    return v___x_1829_;
}
pub unsafe fn l_Lean_Meta_Grind_preprocessLight___boxed(
    mut v_e_1830_: *mut crate::leanh::LeanObject,
    mut v_a_1831_: *mut crate::leanh::LeanObject,
    mut v_a_1832_: *mut crate::leanh::LeanObject,
    mut v_a_1833_: *mut crate::leanh::LeanObject,
    mut v_a_1834_: *mut crate::leanh::LeanObject,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
    mut v_a_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
    mut v_a_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1842_ = l_Lean_Meta_Grind_preprocessLight(
        v_e_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_,
        v_a_1838_, v_a_1839_, v_a_1840_,
    );
    crate::leanh::lean_dec(v_a_1840_);
    crate::leanh::lean_dec_ref(v_a_1839_);
    crate::leanh::lean_dec(v_a_1838_);
    crate::leanh::lean_dec_ref(v_a_1837_);
    crate::leanh::lean_dec(v_a_1836_);
    crate::leanh::lean_dec_ref(v_a_1835_);
    crate::leanh::lean_dec(v_a_1834_);
    crate::leanh::lean_dec_ref(v_a_1833_);
    crate::leanh::lean_dec(v_a_1832_);
    crate::leanh::lean_dec(v_a_1831_);
    return v_res_1842_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Simp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Simp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Simp(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
}
