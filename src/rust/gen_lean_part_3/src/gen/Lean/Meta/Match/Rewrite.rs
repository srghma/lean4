// Lean compiler output
// Module: Lean.Meta.Match.Rewrite
// Imports: Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.Refl Lean.Meta.Tactic.Simp.Rewrite
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_float_decLt, lean_float_div,
    lean_float_sub, lean_get_congr_match_equations_for, lean_infer_type,
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land,
    lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_replaceRef};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_appArg_x21,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_beta,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_constLevels_x21, l_Lean_Expr_constName_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar, l_Lean_Expr_headBeta,
    l_Lean_Expr_isApp, l_Lean_Expr_isAppOf, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf,
    l_Lean_Expr_mvarId_x21, l_Lean_Expr_sort___override, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkNot,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofList, l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkEq, l_Lean_Meta_mkEqOfHEq};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_forallMetaTelescope,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::Match::MatcherInfo::l_Lean_Meta_isMatcherAppCore;
use crate::r#gen::Lean::Meta::Tactic::Assumption::{
    initialize_Lean_Meta_Tactic_Assumption, l_Lean_MVarId_assumption,
    runtime_initialize_Lean_Meta_Tactic_Assumption,
};
use crate::r#gen::Lean::Meta::Tactic::Refl::{
    initialize_Lean_Meta_Tactic_Refl, l_Lean_MVarId_hrefl, l_Lean_MVarId_refl,
    runtime_initialize_Lean_Meta_Tactic_Refl,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Rewrite::{
    initialize_Lean_Meta_Tactic_Simp_Rewrite, l_Lean_Meta_Simp_isEqnThmHypothesis,
    runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    initialize_Lean_Meta_Tactic_Simp_Types, runtime_initialize_Lean_Meta_Tactic_Simp_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::Meta::WHNF::l_Lean_Meta_reduceRecMatcher_x3f;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Recognizers::{l_Lean_Expr_isEq, l_Lean_Expr_isHEq};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_trace_profiler, l_Lean_trace_profiler_threshold, l_Lean_trace_profiler_useHeartbeats,
};
pub static l_Lean_Meta_rwIfWith___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [99, 111, 110, 100, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__0_value)
                as *mut leanh::LeanObject,
            105488867511536770 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwIfWith___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__2_value: leanh::LeanStringObject<5> =
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
        m_data: [100, 105, 116, 101, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__2_value)
                as *mut leanh::LeanObject,
            8391571994004792969 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwIfWith___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__4_value: leanh::LeanStringObject<4> =
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
        m_data: [105, 116, 101, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__4_value)
                as *mut leanh::LeanObject,
            18356704233129443855 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwIfWith___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__6_value: leanh::LeanStringObject<7> =
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
        m_data: [105, 102, 95, 110, 101, 103, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__6_value)
                as *mut leanh::LeanObject,
            16244458485308795742 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwIfWith___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__8_value: leanh::LeanStringObject<7> =
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
        m_data: [105, 102, 95, 112, 111, 115, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__8_value)
                as *mut leanh::LeanObject,
            7709702948238413810 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwIfWith___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__10_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [100, 105, 102, 95, 110, 101, 103, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__10_value)
                as *mut leanh::LeanObject,
            8042454805655286456 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwIfWith___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__12_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [100, 105, 102, 95, 112, 111, 115, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__13_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__12_value)
                as *mut leanh::LeanObject,
            5766869440961418022 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwIfWith___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__14_value: leanh::LeanStringObject<5> =
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
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__15_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__15_value) as *mut leanh::LeanObject;
static l_Lean_Meta_rwIfWith___closed__16_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__14_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_rwIfWith___closed__16_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__16_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__15_value)
                as *mut leanh::LeanObject,
            9255189395584251158 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwIfWith___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwIfWith___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwIfWith___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_rwIfWith___closed__18_value: leanh::LeanStringObject<6> =
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
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__18_value) as *mut leanh::LeanObject;
static l_Lean_Meta_rwIfWith___closed__19_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__14_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_rwIfWith___closed__19_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__19_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__18_value)
                as *mut leanh::LeanObject,
            15761733860085307253 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwIfWith___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__19_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwIfWith___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwIfWith___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_rwIfWith___closed__21_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [99, 111, 110, 100, 95, 110, 101, 103, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__21_value) as *mut leanh::LeanObject;
static l_Lean_Meta_rwIfWith___closed__22_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__14_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_rwIfWith___closed__22_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__22_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__21_value)
                as *mut leanh::LeanObject,
            2138448497742974001 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwIfWith___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwIfWith___closed__23_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [99, 111, 110, 100, 95, 112, 111, 115, 0],
    };
static mut l_Lean_Meta_rwIfWith___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__23_value) as *mut leanh::LeanObject;
static l_Lean_Meta_rwIfWith___closed__24_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__14_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_rwIfWith___closed__24_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__24_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__23_value)
                as *mut leanh::LeanObject,
            15335016062029210204 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwIfWith___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwIfWith___closed__24_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__1___closed__0_value: leanh::LeanStringObject<16> =
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
            114, 101, 119, 114, 105, 116, 105, 110, 103, 32, 119, 105, 116, 104, 32, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__1___closed__2_value: leanh::LeanStringObject<4> =
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
        m_data: [32, 105, 110, 0],
    };
static mut l_Lean_Meta_rwMatcher___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1: usize = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 115, 111, 108, 118, 101, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 100, 105, 115, 99, 104, 97, 114, 103, 101, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__2___closed__0_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 117, 110, 45, 72, 69, 113, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__2___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__2___closed__2_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [96, 58, 0],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__2___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__2___closed__4_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [32, 0],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__2___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__2___closed__6_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            78, 111, 116, 32, 97, 108, 108, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115,
            32, 111, 102, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__2___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__2___closed__8_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            96, 32, 99, 111, 117, 108, 100, 32, 98, 101, 32, 100, 105, 115, 99, 104, 97, 114, 103,
            101, 100, 58, 32, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__2___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__2___closed__10_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwMatcher___lam__2___closed__11_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            76, 101, 102, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__2___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__2___closed__13_value: leanh::LeanStringObject<7> =
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
        m_data: [96, 32, 111, 102, 32, 96, 0],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__2___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__2___closed__15_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 97, 112, 112, 108, 121, 32, 116,
            111, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__2___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__2___closed__17_value: leanh::LeanStringObject<4> =
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
        m_data: [72, 69, 113, 0],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwMatcher___lam__2___closed__18_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__17_value)
                as *mut leanh::LeanObject,
            13589827700912665667 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwMatcher___lam__2___closed__19_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_rwMatcher___lam__2___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwMatcher___lam__2___closed__20_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__19_value)
                as *mut leanh::LeanObject,
            16122875713692181903 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwMatcher___lam__2___closed__21_value: leanh::LeanStringObject<10> =
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
        m_data: [84, 121, 112, 101, 32, 111, 102, 32, 96, 0],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__2___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___lam__2___closed__23_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 101, 113, 117, 97, 108, 105, 116,
            121, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___lam__2___closed__23_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___lam__2___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___lam__2___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2: f64 = 0.0;
pub static l_Lean_Meta_rwMatcher___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Meta_rwMatcher___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwMatcher___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__0_value)
                as *mut leanh::LeanObject,
            14231257465488249300 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwMatcher___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwMatcher___closed__2_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___closed__4_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [58, 0],
    };
static mut l_Lean_Meta_rwMatcher___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_rwMatcher___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___closed__6: f64 = 0.0;
pub static l_Lean_Meta_rwMatcher___closed__7_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            101, 113, 80, 114, 111, 111, 102, 32, 104, 97, 115, 32, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__7_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___closed__9_value: leanh::LeanStringObject<5> =
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
        m_data: [77, 101, 116, 97, 0],
    };
static mut l_Lean_Meta_rwMatcher___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwMatcher___closed__10_value: leanh::LeanStringObject<6> =
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
        m_data: [77, 97, 116, 99, 104, 0],
    };
static mut l_Lean_Meta_rwMatcher___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwMatcher___closed__11_value: leanh::LeanStringObject<6> =
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
        m_data: [100, 101, 98, 117, 103, 0],
    };
static mut l_Lean_Meta_rwMatcher___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__11_value) as *mut leanh::LeanObject;
static l_Lean_Meta_rwMatcher___closed__12_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__9_value)
                as *mut leanh::LeanObject,
            142734480563613395 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_rwMatcher___closed__12_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__12_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__10_value)
                as *mut leanh::LeanObject,
            17634115403684839930 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_rwMatcher___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__12_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__11_value)
                as *mut leanh::LeanObject,
            9385099872620329213 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwMatcher___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___closed__14_value: leanh::LeanStringObject<27> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            78, 111, 116, 32, 97, 32, 109, 97, 116, 99, 104, 101, 114, 32, 97, 112, 112, 108, 105,
            99, 97, 116, 105, 111, 110, 58, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___closed__16_value: leanh::LeanStringObject<27> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            87, 104, 101, 110, 32, 116, 114, 121, 105, 110, 103, 32, 116, 111, 32, 114, 101, 100,
            117, 99, 101, 32, 97, 114, 109, 32, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___closed__18_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [44, 32, 111, 110, 108, 121, 32, 0],
    };
static mut l_Lean_Meta_rwMatcher___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___closed__20_value: leanh::LeanStringObject<16> =
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
            32, 101, 113, 117, 97, 116, 105, 111, 110, 115, 32, 102, 111, 114, 32, 0,
        ],
    };
static mut l_Lean_Meta_rwMatcher___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__20_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_rwMatcher___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_rwMatcher___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_rwMatcher___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_rwMatcher___closed__23_value: leanh::LeanStringObject<5> =
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
        m_data: [80, 83, 117, 109, 0],
    };
static mut l_Lean_Meta_rwMatcher___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__23_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwMatcher___closed__24_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [99, 97, 115, 101, 115, 79, 110, 0],
    };
static mut l_Lean_Meta_rwMatcher___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__24_value) as *mut leanh::LeanObject;
static l_Lean_Meta_rwMatcher___closed__25_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__23_value)
                as *mut leanh::LeanObject,
            3874814940683362451 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_rwMatcher___closed__25_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__25_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__24_value)
                as *mut leanh::LeanObject,
            621621110004085670 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwMatcher___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__25_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_rwMatcher___closed__26_value: leanh::LeanStringObject<7> =
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
        m_data: [80, 83, 105, 103, 109, 97, 0],
    };
static mut l_Lean_Meta_rwMatcher___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__26_value) as *mut leanh::LeanObject;
static l_Lean_Meta_rwMatcher___closed__27_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__26_value)
                as *mut leanh::LeanObject,
            16079402598994914048 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_rwMatcher___closed__27_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__27_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__24_value)
                as *mut leanh::LeanObject,
            6028345373435855329 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_rwMatcher___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_rwMatcher___closed__27_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_rwIfWith___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2989_ = leanh::lean_box(0);
    v___x_2990_ = l_Lean_Meta_rwIfWith___closed__16;
    v___x_2991_ = l_Lean_mkConst(v___x_2990_, v___x_2989_);
    return v___x_2991_;
}
pub unsafe fn _init_l_Lean_Meta_rwIfWith___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2996_ = leanh::lean_box(0);
    v___x_2997_ = l_Lean_Meta_rwIfWith___closed__19;
    v___x_2998_ = l_Lean_mkConst(v___x_2997_, v___x_2996_);
    return v___x_2998_;
}
pub unsafe fn l_Lean_Meta_rwIfWith(
    mut v_hc_3007_: *mut leanh::LeanObject,
    mut v_e_3008_: *mut leanh::LeanObject,
    mut v_a_3009_: *mut leanh::LeanObject,
    mut v_a_3010_: *mut leanh::LeanObject,
    mut v_a_3011_: *mut leanh::LeanObject,
    mut v_a_3012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: u8 = 0;
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: u8 = 0;
    let mut v_arg_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: u8 = 0;
    let mut v_arg_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: u8 = 0;
    let mut v_arg_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: u8 = 0;
    let mut v_arg_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: u8 = 0;
    let mut v___x_3036_: u8 = 0;
    let mut v_arg_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: u8 = 0;
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: u8 = 0;
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3049_: u8 = 0;
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: u8 = 0;
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3060_: u8 = 0;
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut v_a_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3081_: u8 = 0;
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut v_a_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3089_: u8 = 0;
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3093_: u8 = 0;
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3110_: u8 = 0;
    let mut v_a_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3114_: u8 = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3118_: u8 = 0;
    let mut v_a_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3133_: u8 = 0;
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3143_: u8 = 0;
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3165_: u8 = 0;
    let mut v_a_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v_a_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_a_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3206_: u8 = 0;
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3210_: u8 = 0;
    let mut v_a_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3214_: u8 = 0;
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3218_: u8 = 0;
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3228_: u8 = 0;
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: u8 = 0;
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3241_: u8 = 0;
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut v_a_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v_a_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_a_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3277_: u8 = 0;
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3281_: u8 = 0;
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut v_a_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3301_: u8 = 0;
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3305_: u8 = 0;
    let mut v_a_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3309_: u8 = 0;
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_a_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3321_: u8 = 0;
    let mut v_a_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_3008_);
                v___x_3019_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3008_, v_a_3010_);
                if leanh::lean_obj_tag(v___x_3019_) == 0 {
                    v_a_3020_ = leanh::lean_ctor_get(v___x_3019_, 0);
                    leanh::lean_inc(v_a_3020_);
                    leanh::lean_dec_ref_known(v___x_3019_, 1);
                    v___x_3021_ = l_Lean_Expr_cleanupAnnotations(v_a_3020_);
                    v___x_3022_ = l_Lean_Expr_isApp(v___x_3021_);
                    if v___x_3022_ == 0 {
                        leanh::lean_dec_ref(v___x_3021_);
                        leanh::lean_dec_ref(v_hc_3007_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_3023_ = leanh::lean_ctor_get(v___x_3021_, 1);
                        leanh::lean_inc_ref(v_arg_3023_);
                        v___x_3024_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3021_);
                        v___x_3025_ = l_Lean_Expr_isApp(v___x_3024_);
                        if v___x_3025_ == 0 {
                            leanh::lean_dec_ref(v___x_3024_);
                            leanh::lean_dec_ref(v_arg_3023_);
                            leanh::lean_dec_ref(v_hc_3007_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_3026_ = leanh::lean_ctor_get(v___x_3024_, 1);
                            leanh::lean_inc_ref(v_arg_3026_);
                            v___x_3027_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3024_);
                            v___x_3028_ = l_Lean_Expr_isApp(v___x_3027_);
                            if v___x_3028_ == 0 {
                                leanh::lean_dec_ref(v___x_3027_);
                                leanh::lean_dec_ref(v_arg_3026_);
                                leanh::lean_dec_ref(v_arg_3023_);
                                leanh::lean_dec_ref(v_hc_3007_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_3029_ = leanh::lean_ctor_get(v___x_3027_, 1);
                                leanh::lean_inc_ref(v_arg_3029_);
                                v___x_3030_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3027_);
                                v___x_3031_ = l_Lean_Expr_isApp(v___x_3030_);
                                if v___x_3031_ == 0 {
                                    leanh::lean_dec_ref(v___x_3030_);
                                    leanh::lean_dec_ref(v_arg_3029_);
                                    leanh::lean_dec_ref(v_arg_3026_);
                                    leanh::lean_dec_ref(v_arg_3023_);
                                    leanh::lean_dec_ref(v_hc_3007_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_3032_ = leanh::lean_ctor_get(v___x_3030_, 1);
                                    leanh::lean_inc_ref(v_arg_3032_);
                                    v___x_3033_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3030_);
                                    v___x_3034_ = l_Lean_Meta_rwIfWith___closed__1;
                                    v___x_3035_ = l_Lean_Expr_isConstOf(v___x_3033_, v___x_3034_);
                                    if v___x_3035_ == 0 {
                                        v___x_3036_ = l_Lean_Expr_isApp(v___x_3033_);
                                        if v___x_3036_ == 0 {
                                            leanh::lean_dec_ref(v___x_3033_);
                                            leanh::lean_dec_ref(v_arg_3032_);
                                            leanh::lean_dec_ref(v_arg_3029_);
                                            leanh::lean_dec_ref(v_arg_3026_);
                                            leanh::lean_dec_ref(v_arg_3023_);
                                            leanh::lean_dec_ref(v_hc_3007_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_arg_3037_ =
                                                leanh::lean_ctor_get(v___x_3033_, 1);
                                            leanh::lean_inc_ref(v_arg_3037_);
                                            v___x_3038_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3033_);
                                            v___x_3039_ = l_Lean_Meta_rwIfWith___closed__3;
                                            v___x_3040_ =
                                                l_Lean_Expr_isConstOf(v___x_3038_, v___x_3039_);
                                            if v___x_3040_ == 0 {
                                                v___x_3041_ = l_Lean_Meta_rwIfWith___closed__5;
                                                v___x_3042_ =
                                                    l_Lean_Expr_isConstOf(v___x_3038_, v___x_3041_);
                                                if v___x_3042_ == 0 {
                                                    leanh::lean_dec_ref(v___x_3038_);
                                                    leanh::lean_dec_ref(v_arg_3037_);
                                                    leanh::lean_dec_ref(v_arg_3032_);
                                                    leanh::lean_dec_ref(v_arg_3029_);
                                                    leanh::lean_dec_ref(v_arg_3026_);
                                                    leanh::lean_dec_ref(v_arg_3023_);
                                                    leanh::lean_dec_ref(v_hc_3007_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_3012_);
                                                    leanh::lean_inc_ref(v_a_3011_);
                                                    leanh::lean_inc(v_a_3010_);
                                                    leanh::lean_inc_ref(v_a_3009_);
                                                    leanh::lean_inc_ref(v_hc_3007_);
                                                    v___x_3043_ = lean_infer_type(
                                                        v_hc_3007_, v_a_3009_, v_a_3010_,
                                                        v_a_3011_, v_a_3012_,
                                                    );
                                                    if leanh::lean_obj_tag(v___x_3043_) == 0
                                                    {
                                                        v_a_3044_ = leanh::lean_ctor_get(
                                                            v___x_3043_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_3044_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_3043_,
                                                            1,
                                                        );
                                                        leanh::lean_inc_ref(v_arg_3032_);
                                                        v___x_3045_ = l_Lean_Meta_isExprDefEq(
                                                            v_arg_3032_,
                                                            v_a_3044_,
                                                            v_a_3009_,
                                                            v_a_3010_,
                                                            v_a_3011_,
                                                            v_a_3012_,
                                                        );
                                                        if leanh::lean_obj_tag(v___x_3045_)
                                                            == 0
                                                        {
                                                            v_a_3046_ = leanh::lean_ctor_get(
                                                                v___x_3045_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_3110_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_3045_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_3110_ == 0 {
                                                                v___x_3048_ = v___x_3045_;
                                                                v_isShared_3049_ =
                                                                    v_isSharedCheck_3110_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_3046_);
                                                                leanh::lean_dec(v___x_3045_);
                                                                v___x_3048_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_3049_ =
                                                                    v_isSharedCheck_3110_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref(v___x_3038_);
                                                            leanh::lean_dec_ref(v_arg_3037_);
                                                            leanh::lean_dec_ref(v_arg_3032_);
                                                            leanh::lean_dec_ref(v_arg_3029_);
                                                            leanh::lean_dec_ref(v_arg_3026_);
                                                            leanh::lean_dec_ref(v_arg_3023_);
                                                            leanh::lean_dec_ref(v_e_3008_);
                                                            leanh::lean_dec_ref(v_hc_3007_);
                                                            v_a_3111_ = leanh::lean_ctor_get(
                                                                v___x_3045_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_3118_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_3045_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_3118_ == 0 {
                                                                v___x_3113_ = v___x_3045_;
                                                                v_isShared_3114_ =
                                                                    v_isSharedCheck_3118_;
                                                                state = 10;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_3111_);
                                                                leanh::lean_dec(v___x_3045_);
                                                                v___x_3113_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_3114_ =
                                                                    v_isSharedCheck_3118_;
                                                                state = 10;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref(v___x_3038_);
                                                        leanh::lean_dec_ref(v_arg_3037_);
                                                        leanh::lean_dec_ref(v_arg_3032_);
                                                        leanh::lean_dec_ref(v_arg_3029_);
                                                        leanh::lean_dec_ref(v_arg_3026_);
                                                        leanh::lean_dec_ref(v_arg_3023_);
                                                        leanh::lean_dec_ref(v_e_3008_);
                                                        leanh::lean_dec_ref(v_hc_3007_);
                                                        v_a_3119_ = leanh::lean_ctor_get(
                                                            v___x_3043_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3126_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_3043_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3126_ == 0 {
                                                            v___x_3121_ = v___x_3043_;
                                                            v_isShared_3122_ =
                                                                v_isSharedCheck_3126_;
                                                            state = 12;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_3119_);
                                                            leanh::lean_dec(v___x_3043_);
                                                            v___x_3121_ = leanh::lean_box(0);
                                                            v_isShared_3122_ =
                                                                v_isSharedCheck_3126_;
                                                            state = 12;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_inc(v_a_3012_);
                                                leanh::lean_inc_ref(v_a_3011_);
                                                leanh::lean_inc(v_a_3010_);
                                                leanh::lean_inc_ref(v_a_3009_);
                                                leanh::lean_inc_ref(v_hc_3007_);
                                                v___x_3127_ = lean_infer_type(
                                                    v_hc_3007_, v_a_3009_, v_a_3010_, v_a_3011_,
                                                    v_a_3012_,
                                                );
                                                if leanh::lean_obj_tag(v___x_3127_) == 0 {
                                                    v_a_3128_ =
                                                        leanh::lean_ctor_get(v___x_3127_, 0);
                                                    leanh::lean_inc(v_a_3128_);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_3127_,
                                                        1,
                                                    );
                                                    leanh::lean_inc_ref(v_arg_3032_);
                                                    v___x_3129_ = l_Lean_Meta_isExprDefEq(
                                                        v_arg_3032_,
                                                        v_a_3128_,
                                                        v_a_3009_,
                                                        v_a_3010_,
                                                        v_a_3011_,
                                                        v_a_3012_,
                                                    );
                                                    if leanh::lean_obj_tag(v___x_3129_) == 0
                                                    {
                                                        v_a_3130_ = leanh::lean_ctor_get(
                                                            v___x_3129_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3202_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_3129_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3202_ == 0 {
                                                            v___x_3132_ = v___x_3129_;
                                                            v_isShared_3133_ =
                                                                v_isSharedCheck_3202_;
                                                            state = 14;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_3130_);
                                                            leanh::lean_dec(v___x_3129_);
                                                            v___x_3132_ = leanh::lean_box(0);
                                                            v_isShared_3133_ =
                                                                v_isSharedCheck_3202_;
                                                            state = 14;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref(v___x_3038_);
                                                        leanh::lean_dec_ref(v_arg_3037_);
                                                        leanh::lean_dec_ref(v_arg_3032_);
                                                        leanh::lean_dec_ref(v_arg_3029_);
                                                        leanh::lean_dec_ref(v_arg_3026_);
                                                        leanh::lean_dec_ref(v_arg_3023_);
                                                        leanh::lean_dec_ref(v_e_3008_);
                                                        leanh::lean_dec_ref(v_hc_3007_);
                                                        v_a_3203_ = leanh::lean_ctor_get(
                                                            v___x_3129_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3210_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_3129_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3210_ == 0 {
                                                            v___x_3205_ = v___x_3129_;
                                                            v_isShared_3206_ =
                                                                v_isSharedCheck_3210_;
                                                            state = 22;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_3203_);
                                                            leanh::lean_dec(v___x_3129_);
                                                            v___x_3205_ = leanh::lean_box(0);
                                                            v_isShared_3206_ =
                                                                v_isSharedCheck_3210_;
                                                            state = 22;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_3038_);
                                                    leanh::lean_dec_ref(v_arg_3037_);
                                                    leanh::lean_dec_ref(v_arg_3032_);
                                                    leanh::lean_dec_ref(v_arg_3029_);
                                                    leanh::lean_dec_ref(v_arg_3026_);
                                                    leanh::lean_dec_ref(v_arg_3023_);
                                                    leanh::lean_dec_ref(v_e_3008_);
                                                    leanh::lean_dec_ref(v_hc_3007_);
                                                    v_a_3211_ =
                                                        leanh::lean_ctor_get(v___x_3127_, 0);
                                                    v_isSharedCheck_3218_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_3127_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3218_ == 0 {
                                                        v___x_3213_ = v___x_3127_;
                                                        v_isShared_3214_ = v_isSharedCheck_3218_;
                                                        state = 24;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_3211_);
                                                        leanh::lean_dec(v___x_3127_);
                                                        v___x_3213_ = leanh::lean_box(0);
                                                        v_isShared_3214_ = v_isSharedCheck_3218_;
                                                        state = 24;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_inc(v_a_3012_);
                                        leanh::lean_inc_ref(v_a_3011_);
                                        leanh::lean_inc(v_a_3010_);
                                        leanh::lean_inc_ref(v_a_3009_);
                                        leanh::lean_inc_ref(v_hc_3007_);
                                        v___x_3219_ = lean_infer_type(
                                            v_hc_3007_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_,
                                        );
                                        if leanh::lean_obj_tag(v___x_3219_) == 0 {
                                            v_a_3220_ = leanh::lean_ctor_get(v___x_3219_, 0);
                                            leanh::lean_inc(v_a_3220_);
                                            leanh::lean_dec_ref_known(v___x_3219_, 1);
                                            v___x_3221_ = leanh::lean_obj_once(
                                                core::ptr::addr_of_mut!(
                                                    l_Lean_Meta_rwIfWith___closed__17
                                                ),
                                                core::ptr::addr_of_mut!(
                                                    l_Lean_Meta_rwIfWith___closed__17_once
                                                ),
                                                _init_l_Lean_Meta_rwIfWith___closed__17,
                                            );
                                            leanh::lean_inc_ref(v_arg_3029_);
                                            v___x_3222_ = l_Lean_Meta_mkEq(
                                                v_arg_3029_,
                                                v___x_3221_,
                                                v_a_3009_,
                                                v_a_3010_,
                                                v_a_3011_,
                                                v_a_3012_,
                                            );
                                            if leanh::lean_obj_tag(v___x_3222_) == 0 {
                                                v_a_3223_ =
                                                    leanh::lean_ctor_get(v___x_3222_, 0);
                                                leanh::lean_inc(v_a_3223_);
                                                leanh::lean_dec_ref_known(v___x_3222_, 1);
                                                v___x_3224_ = l_Lean_Meta_isExprDefEq(
                                                    v_a_3220_, v_a_3223_, v_a_3009_, v_a_3010_,
                                                    v_a_3011_, v_a_3012_,
                                                );
                                                if leanh::lean_obj_tag(v___x_3224_) == 0 {
                                                    v_a_3225_ =
                                                        leanh::lean_ctor_get(v___x_3224_, 0);
                                                    v_isSharedCheck_3297_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_3224_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3297_ == 0 {
                                                        v___x_3227_ = v___x_3224_;
                                                        v_isShared_3228_ = v_isSharedCheck_3297_;
                                                        state = 26;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_3225_);
                                                        leanh::lean_dec(v___x_3224_);
                                                        v___x_3227_ = leanh::lean_box(0);
                                                        v_isShared_3228_ = v_isSharedCheck_3297_;
                                                        state = 26;
                                                        continue;
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_3033_);
                                                    leanh::lean_dec_ref(v_arg_3032_);
                                                    leanh::lean_dec_ref(v_arg_3029_);
                                                    leanh::lean_dec_ref(v_arg_3026_);
                                                    leanh::lean_dec_ref(v_arg_3023_);
                                                    leanh::lean_dec_ref(v_e_3008_);
                                                    leanh::lean_dec_ref(v_hc_3007_);
                                                    v_a_3298_ =
                                                        leanh::lean_ctor_get(v___x_3224_, 0);
                                                    v_isSharedCheck_3305_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_3224_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3305_ == 0 {
                                                        v___x_3300_ = v___x_3224_;
                                                        v_isShared_3301_ = v_isSharedCheck_3305_;
                                                        state = 36;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_3298_);
                                                        leanh::lean_dec(v___x_3224_);
                                                        v___x_3300_ = leanh::lean_box(0);
                                                        v_isShared_3301_ = v_isSharedCheck_3305_;
                                                        state = 36;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec(v_a_3220_);
                                                leanh::lean_dec_ref(v___x_3033_);
                                                leanh::lean_dec_ref(v_arg_3032_);
                                                leanh::lean_dec_ref(v_arg_3029_);
                                                leanh::lean_dec_ref(v_arg_3026_);
                                                leanh::lean_dec_ref(v_arg_3023_);
                                                leanh::lean_dec_ref(v_e_3008_);
                                                leanh::lean_dec_ref(v_hc_3007_);
                                                v_a_3306_ =
                                                    leanh::lean_ctor_get(v___x_3222_, 0);
                                                v_isSharedCheck_3313_ =
                                                    (!leanh::lean_is_exclusive(v___x_3222_))
                                                        as u8;
                                                if v_isSharedCheck_3313_ == 0 {
                                                    v___x_3308_ = v___x_3222_;
                                                    v_isShared_3309_ = v_isSharedCheck_3313_;
                                                    state = 38;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_3306_);
                                                    leanh::lean_dec(v___x_3222_);
                                                    v___x_3308_ = leanh::lean_box(0);
                                                    v_isShared_3309_ = v_isSharedCheck_3313_;
                                                    state = 38;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_3033_);
                                            leanh::lean_dec_ref(v_arg_3032_);
                                            leanh::lean_dec_ref(v_arg_3029_);
                                            leanh::lean_dec_ref(v_arg_3026_);
                                            leanh::lean_dec_ref(v_arg_3023_);
                                            leanh::lean_dec_ref(v_e_3008_);
                                            leanh::lean_dec_ref(v_hc_3007_);
                                            v_a_3314_ = leanh::lean_ctor_get(v___x_3219_, 0);
                                            v_isSharedCheck_3321_ =
                                                (!leanh::lean_is_exclusive(v___x_3219_))
                                                    as u8;
                                            if v_isSharedCheck_3321_ == 0 {
                                                v___x_3316_ = v___x_3219_;
                                                v_isShared_3317_ = v_isSharedCheck_3321_;
                                                state = 40;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3314_);
                                                leanh::lean_dec(v___x_3219_);
                                                v___x_3316_ = leanh::lean_box(0);
                                                v_isShared_3317_ = v_isSharedCheck_3321_;
                                                state = 40;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3008_);
                    leanh::lean_dec_ref(v_hc_3007_);
                    v_a_3322_ = leanh::lean_ctor_get(v___x_3019_, 0);
                    v_isSharedCheck_3329_ = (!leanh::lean_is_exclusive(v___x_3019_)) as u8;
                    if v_isSharedCheck_3329_ == 0 {
                        v___x_3324_ = v___x_3019_;
                        v_isShared_3325_ = v_isSharedCheck_3329_;
                        state = 42;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3322_);
                        leanh::lean_dec(v___x_3019_);
                        v___x_3324_ = leanh::lean_box(0);
                        v_isShared_3325_ = v_isSharedCheck_3329_;
                        state = 42;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3015_ = leanh::lean_box(0);
                v___x_3016_ = 1;
                v___x_3017_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3017_, 0, v_e_3008_);
                leanh::lean_ctor_set(v___x_3017_, 1, v___x_3015_);
                leanh::lean_ctor_set_uint8(
                    v___x_3017_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3016_,
                );
                v___x_3018_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3018_, 0, v___x_3017_);
                return v___x_3018_;
            }
            2 => {
                v___x_3050_ = l_Lean_Expr_constLevels_x21(v___x_3038_);
                leanh::lean_dec_ref(v___x_3038_);
                v___x_3051_ = (leanh::lean_unbox(v_a_3046_) as u8);
                leanh::lean_dec(v_a_3046_);
                if v___x_3051_ == 0 {
                    leanh::lean_del_object(v___x_3048_);
                    leanh::lean_inc(v_a_3012_);
                    leanh::lean_inc_ref(v_a_3011_);
                    leanh::lean_inc(v_a_3010_);
                    leanh::lean_inc_ref(v_a_3009_);
                    leanh::lean_inc_ref(v_hc_3007_);
                    v___x_3052_ =
                        lean_infer_type(v_hc_3007_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
                    if leanh::lean_obj_tag(v___x_3052_) == 0 {
                        v_a_3053_ = leanh::lean_ctor_get(v___x_3052_, 0);
                        leanh::lean_inc(v_a_3053_);
                        leanh::lean_dec_ref_known(v___x_3052_, 1);
                        leanh::lean_inc_ref(v_arg_3032_);
                        v___x_3054_ = l_Lean_mkNot(v_arg_3032_);
                        v___x_3055_ = l_Lean_Meta_isExprDefEq(
                            v___x_3054_,
                            v_a_3053_,
                            v_a_3009_,
                            v_a_3010_,
                            v_a_3011_,
                            v_a_3012_,
                        );
                        if leanh::lean_obj_tag(v___x_3055_) == 0 {
                            v_a_3056_ = leanh::lean_ctor_get(v___x_3055_, 0);
                            v_isSharedCheck_3077_ =
                                (!leanh::lean_is_exclusive(v___x_3055_)) as u8;
                            if v_isSharedCheck_3077_ == 0 {
                                v___x_3058_ = v___x_3055_;
                                v_isShared_3059_ = v_isSharedCheck_3077_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3056_);
                                leanh::lean_dec(v___x_3055_);
                                v___x_3058_ = leanh::lean_box(0);
                                v_isShared_3059_ = v_isSharedCheck_3077_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_3050_);
                            leanh::lean_dec_ref(v_arg_3037_);
                            leanh::lean_dec_ref(v_arg_3032_);
                            leanh::lean_dec_ref(v_arg_3029_);
                            leanh::lean_dec_ref(v_arg_3026_);
                            leanh::lean_dec_ref(v_arg_3023_);
                            leanh::lean_dec_ref(v_e_3008_);
                            leanh::lean_dec_ref(v_hc_3007_);
                            v_a_3078_ = leanh::lean_ctor_get(v___x_3055_, 0);
                            v_isSharedCheck_3085_ =
                                (!leanh::lean_is_exclusive(v___x_3055_)) as u8;
                            if v_isSharedCheck_3085_ == 0 {
                                v___x_3080_ = v___x_3055_;
                                v_isShared_3081_ = v_isSharedCheck_3085_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3078_);
                                leanh::lean_dec(v___x_3055_);
                                v___x_3080_ = leanh::lean_box(0);
                                v_isShared_3081_ = v_isSharedCheck_3085_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3050_);
                        leanh::lean_dec_ref(v_arg_3037_);
                        leanh::lean_dec_ref(v_arg_3032_);
                        leanh::lean_dec_ref(v_arg_3029_);
                        leanh::lean_dec_ref(v_arg_3026_);
                        leanh::lean_dec_ref(v_arg_3023_);
                        leanh::lean_dec_ref(v_e_3008_);
                        leanh::lean_dec_ref(v_hc_3007_);
                        v_a_3086_ = leanh::lean_ctor_get(v___x_3052_, 0);
                        v_isSharedCheck_3093_ =
                            (!leanh::lean_is_exclusive(v___x_3052_)) as u8;
                        if v_isSharedCheck_3093_ == 0 {
                            v___x_3088_ = v___x_3052_;
                            v_isShared_3089_ = v_isSharedCheck_3093_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3086_);
                            leanh::lean_dec(v___x_3052_);
                            v___x_3088_ = leanh::lean_box(0);
                            v_isShared_3089_ = v_isSharedCheck_3093_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3008_);
                    v___x_3094_ = l_Lean_Meta_rwIfWith___closed__9;
                    v___x_3095_ = l_Lean_mkConst(v___x_3094_, v___x_3050_);
                    v___x_3096_ = leanh::lean_unsigned_to_nat(6);
                    v___x_3097_ = lean_mk_empty_array_with_capacity(v___x_3096_);
                    v___x_3098_ = lean_array_push(v___x_3097_, v_arg_3032_);
                    v___x_3099_ = lean_array_push(v___x_3098_, v_arg_3029_);
                    v___x_3100_ = lean_array_push(v___x_3099_, v_hc_3007_);
                    v___x_3101_ = lean_array_push(v___x_3100_, v_arg_3037_);
                    leanh::lean_inc_ref(v_arg_3026_);
                    v___x_3102_ = lean_array_push(v___x_3101_, v_arg_3026_);
                    v___x_3103_ = lean_array_push(v___x_3102_, v_arg_3023_);
                    v___x_3104_ = l_Lean_mkAppN(v___x_3095_, v___x_3103_);
                    leanh::lean_dec_ref(v___x_3103_);
                    v___x_3105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3105_, 0, v___x_3104_);
                    v___x_3106_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3106_, 0, v_arg_3026_);
                    leanh::lean_ctor_set(v___x_3106_, 1, v___x_3105_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3106_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3042_,
                    );
                    if v_isShared_3049_ == 0 {
                        leanh::lean_ctor_set(v___x_3048_, 0, v___x_3106_);
                        v___x_3108_ = v___x_3048_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3109_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3106_);
                        v___x_3108_ = v_reuseFailAlloc_3109_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3060_ = (leanh::lean_unbox(v_a_3056_) as u8);
                leanh::lean_dec(v_a_3056_);
                if v___x_3060_ == 0 {
                    leanh::lean_del_object(v___x_3058_);
                    leanh::lean_dec(v___x_3050_);
                    leanh::lean_dec_ref(v_arg_3037_);
                    leanh::lean_dec_ref(v_arg_3032_);
                    leanh::lean_dec_ref(v_arg_3029_);
                    leanh::lean_dec_ref(v_arg_3026_);
                    leanh::lean_dec_ref(v_arg_3023_);
                    leanh::lean_dec_ref(v_hc_3007_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_3008_);
                    v___x_3061_ = l_Lean_Meta_rwIfWith___closed__7;
                    v___x_3062_ = l_Lean_mkConst(v___x_3061_, v___x_3050_);
                    v___x_3063_ = leanh::lean_unsigned_to_nat(6);
                    v___x_3064_ = lean_mk_empty_array_with_capacity(v___x_3063_);
                    v___x_3065_ = lean_array_push(v___x_3064_, v_arg_3032_);
                    v___x_3066_ = lean_array_push(v___x_3065_, v_arg_3029_);
                    v___x_3067_ = lean_array_push(v___x_3066_, v_hc_3007_);
                    v___x_3068_ = lean_array_push(v___x_3067_, v_arg_3037_);
                    v___x_3069_ = lean_array_push(v___x_3068_, v_arg_3026_);
                    leanh::lean_inc_ref(v_arg_3023_);
                    v___x_3070_ = lean_array_push(v___x_3069_, v_arg_3023_);
                    v___x_3071_ = l_Lean_mkAppN(v___x_3062_, v___x_3070_);
                    leanh::lean_dec_ref(v___x_3070_);
                    v___x_3072_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3072_, 0, v___x_3071_);
                    v___x_3073_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3073_, 0, v_arg_3023_);
                    leanh::lean_ctor_set(v___x_3073_, 1, v___x_3072_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3073_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3042_,
                    );
                    if v_isShared_3059_ == 0 {
                        leanh::lean_ctor_set(v___x_3058_, 0, v___x_3073_);
                        v___x_3075_ = v___x_3058_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3076_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
                        v___x_3075_ = v_reuseFailAlloc_3076_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3075_;
            }
            5 => {
                if v_isShared_3081_ == 0 {
                    v___x_3083_ = v___x_3080_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3084_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
                    v___x_3083_ = v_reuseFailAlloc_3084_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3083_;
            }
            7 => {
                if v_isShared_3089_ == 0 {
                    v___x_3091_ = v___x_3088_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3092_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
                    v___x_3091_ = v_reuseFailAlloc_3092_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3091_;
            }
            9 => {
                return v___x_3108_;
            }
            10 => {
                if v_isShared_3114_ == 0 {
                    v___x_3116_ = v___x_3113_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3117_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
                    v___x_3116_ = v_reuseFailAlloc_3117_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3116_;
            }
            12 => {
                if v_isShared_3122_ == 0 {
                    v___x_3124_ = v___x_3121_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3125_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
                    v___x_3124_ = v_reuseFailAlloc_3125_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3124_;
            }
            14 => {
                v___x_3134_ = l_Lean_Expr_constLevels_x21(v___x_3038_);
                leanh::lean_dec_ref(v___x_3038_);
                v___x_3135_ = (leanh::lean_unbox(v_a_3130_) as u8);
                leanh::lean_dec(v_a_3130_);
                if v___x_3135_ == 0 {
                    leanh::lean_del_object(v___x_3132_);
                    leanh::lean_inc(v_a_3012_);
                    leanh::lean_inc_ref(v_a_3011_);
                    leanh::lean_inc(v_a_3010_);
                    leanh::lean_inc_ref(v_a_3009_);
                    leanh::lean_inc_ref(v_hc_3007_);
                    v___x_3136_ =
                        lean_infer_type(v_hc_3007_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
                    if leanh::lean_obj_tag(v___x_3136_) == 0 {
                        v_a_3137_ = leanh::lean_ctor_get(v___x_3136_, 0);
                        leanh::lean_inc(v_a_3137_);
                        leanh::lean_dec_ref_known(v___x_3136_, 1);
                        leanh::lean_inc_ref(v_arg_3032_);
                        v___x_3138_ = l_Lean_mkNot(v_arg_3032_);
                        v___x_3139_ = l_Lean_Meta_isExprDefEq(
                            v___x_3138_,
                            v_a_3137_,
                            v_a_3009_,
                            v_a_3010_,
                            v_a_3011_,
                            v_a_3012_,
                        );
                        if leanh::lean_obj_tag(v___x_3139_) == 0 {
                            v_a_3140_ = leanh::lean_ctor_get(v___x_3139_, 0);
                            v_isSharedCheck_3165_ =
                                (!leanh::lean_is_exclusive(v___x_3139_)) as u8;
                            if v_isSharedCheck_3165_ == 0 {
                                v___x_3142_ = v___x_3139_;
                                v_isShared_3143_ = v_isSharedCheck_3165_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3140_);
                                leanh::lean_dec(v___x_3139_);
                                v___x_3142_ = leanh::lean_box(0);
                                v_isShared_3143_ = v_isSharedCheck_3165_;
                                state = 15;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_3134_);
                            leanh::lean_dec_ref(v_arg_3037_);
                            leanh::lean_dec_ref(v_arg_3032_);
                            leanh::lean_dec_ref(v_arg_3029_);
                            leanh::lean_dec_ref(v_arg_3026_);
                            leanh::lean_dec_ref(v_arg_3023_);
                            leanh::lean_dec_ref(v_e_3008_);
                            leanh::lean_dec_ref(v_hc_3007_);
                            v_a_3166_ = leanh::lean_ctor_get(v___x_3139_, 0);
                            v_isSharedCheck_3173_ =
                                (!leanh::lean_is_exclusive(v___x_3139_)) as u8;
                            if v_isSharedCheck_3173_ == 0 {
                                v___x_3168_ = v___x_3139_;
                                v_isShared_3169_ = v_isSharedCheck_3173_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3166_);
                                leanh::lean_dec(v___x_3139_);
                                v___x_3168_ = leanh::lean_box(0);
                                v_isShared_3169_ = v_isSharedCheck_3173_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3134_);
                        leanh::lean_dec_ref(v_arg_3037_);
                        leanh::lean_dec_ref(v_arg_3032_);
                        leanh::lean_dec_ref(v_arg_3029_);
                        leanh::lean_dec_ref(v_arg_3026_);
                        leanh::lean_dec_ref(v_arg_3023_);
                        leanh::lean_dec_ref(v_e_3008_);
                        leanh::lean_dec_ref(v_hc_3007_);
                        v_a_3174_ = leanh::lean_ctor_get(v___x_3136_, 0);
                        v_isSharedCheck_3181_ =
                            (!leanh::lean_is_exclusive(v___x_3136_)) as u8;
                        if v_isSharedCheck_3181_ == 0 {
                            v___x_3176_ = v___x_3136_;
                            v_isShared_3177_ = v_isSharedCheck_3181_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3174_);
                            leanh::lean_dec(v___x_3136_);
                            v___x_3176_ = leanh::lean_box(0);
                            v_isShared_3177_ = v_isSharedCheck_3181_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3008_);
                    v___x_3182_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3183_ = lean_mk_empty_array_with_capacity(v___x_3182_);
                    leanh::lean_inc_ref(v_hc_3007_);
                    v___x_3184_ = lean_array_push(v___x_3183_, v_hc_3007_);
                    leanh::lean_inc_ref(v_arg_3026_);
                    v___x_3185_ = l_Lean_Expr_beta(v_arg_3026_, v___x_3184_);
                    v___x_3186_ = l_Lean_Meta_rwIfWith___closed__13;
                    v___x_3187_ = l_Lean_mkConst(v___x_3186_, v___x_3134_);
                    v___x_3188_ = leanh::lean_unsigned_to_nat(6);
                    v___x_3189_ = lean_mk_empty_array_with_capacity(v___x_3188_);
                    v___x_3190_ = lean_array_push(v___x_3189_, v_arg_3032_);
                    v___x_3191_ = lean_array_push(v___x_3190_, v_arg_3029_);
                    v___x_3192_ = lean_array_push(v___x_3191_, v_hc_3007_);
                    v___x_3193_ = lean_array_push(v___x_3192_, v_arg_3037_);
                    v___x_3194_ = lean_array_push(v___x_3193_, v_arg_3026_);
                    v___x_3195_ = lean_array_push(v___x_3194_, v_arg_3023_);
                    v___x_3196_ = l_Lean_mkAppN(v___x_3187_, v___x_3195_);
                    leanh::lean_dec_ref(v___x_3195_);
                    v___x_3197_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3197_, 0, v___x_3196_);
                    v___x_3198_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3198_, 0, v___x_3185_);
                    leanh::lean_ctor_set(v___x_3198_, 1, v___x_3197_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3198_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3040_,
                    );
                    if v_isShared_3133_ == 0 {
                        leanh::lean_ctor_set(v___x_3132_, 0, v___x_3198_);
                        v___x_3200_ = v___x_3132_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_3201_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
                        v___x_3200_ = v_reuseFailAlloc_3201_;
                        state = 21;
                        continue;
                    }
                }
            }
            15 => {
                v___x_3144_ = (leanh::lean_unbox(v_a_3140_) as u8);
                leanh::lean_dec(v_a_3140_);
                if v___x_3144_ == 0 {
                    leanh::lean_del_object(v___x_3142_);
                    leanh::lean_dec(v___x_3134_);
                    leanh::lean_dec_ref(v_arg_3037_);
                    leanh::lean_dec_ref(v_arg_3032_);
                    leanh::lean_dec_ref(v_arg_3029_);
                    leanh::lean_dec_ref(v_arg_3026_);
                    leanh::lean_dec_ref(v_arg_3023_);
                    leanh::lean_dec_ref(v_hc_3007_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_3008_);
                    v___x_3145_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3146_ = lean_mk_empty_array_with_capacity(v___x_3145_);
                    leanh::lean_inc_ref(v_hc_3007_);
                    v___x_3147_ = lean_array_push(v___x_3146_, v_hc_3007_);
                    leanh::lean_inc_ref(v_arg_3023_);
                    v___x_3148_ = l_Lean_Expr_beta(v_arg_3023_, v___x_3147_);
                    v___x_3149_ = l_Lean_Meta_rwIfWith___closed__11;
                    v___x_3150_ = l_Lean_mkConst(v___x_3149_, v___x_3134_);
                    v___x_3151_ = leanh::lean_unsigned_to_nat(6);
                    v___x_3152_ = lean_mk_empty_array_with_capacity(v___x_3151_);
                    v___x_3153_ = lean_array_push(v___x_3152_, v_arg_3032_);
                    v___x_3154_ = lean_array_push(v___x_3153_, v_arg_3029_);
                    v___x_3155_ = lean_array_push(v___x_3154_, v_hc_3007_);
                    v___x_3156_ = lean_array_push(v___x_3155_, v_arg_3037_);
                    v___x_3157_ = lean_array_push(v___x_3156_, v_arg_3026_);
                    v___x_3158_ = lean_array_push(v___x_3157_, v_arg_3023_);
                    v___x_3159_ = l_Lean_mkAppN(v___x_3150_, v___x_3158_);
                    leanh::lean_dec_ref(v___x_3158_);
                    v___x_3160_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3160_, 0, v___x_3159_);
                    v___x_3161_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3161_, 0, v___x_3148_);
                    leanh::lean_ctor_set(v___x_3161_, 1, v___x_3160_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3161_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3040_,
                    );
                    if v_isShared_3143_ == 0 {
                        leanh::lean_ctor_set(v___x_3142_, 0, v___x_3161_);
                        v___x_3163_ = v___x_3142_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_3164_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3161_);
                        v___x_3163_ = v_reuseFailAlloc_3164_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                return v___x_3163_;
            }
            17 => {
                if v_isShared_3169_ == 0 {
                    v___x_3171_ = v___x_3168_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3172_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
                    v___x_3171_ = v_reuseFailAlloc_3172_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3171_;
            }
            19 => {
                if v_isShared_3177_ == 0 {
                    v___x_3179_ = v___x_3176_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
                    v___x_3179_ = v_reuseFailAlloc_3180_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3179_;
            }
            21 => {
                return v___x_3200_;
            }
            22 => {
                if v_isShared_3206_ == 0 {
                    v___x_3208_ = v___x_3205_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
                    v___x_3208_ = v_reuseFailAlloc_3209_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3208_;
            }
            24 => {
                if v_isShared_3214_ == 0 {
                    v___x_3216_ = v___x_3213_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3217_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
                    v___x_3216_ = v_reuseFailAlloc_3217_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3216_;
            }
            26 => {
                v___x_3229_ = l_Lean_Expr_constLevels_x21(v___x_3033_);
                leanh::lean_dec_ref(v___x_3033_);
                v___x_3230_ = (leanh::lean_unbox(v_a_3225_) as u8);
                leanh::lean_dec(v_a_3225_);
                if v___x_3230_ == 0 {
                    leanh::lean_del_object(v___x_3227_);
                    leanh::lean_inc(v_a_3012_);
                    leanh::lean_inc_ref(v_a_3011_);
                    leanh::lean_inc(v_a_3010_);
                    leanh::lean_inc_ref(v_a_3009_);
                    leanh::lean_inc_ref(v_hc_3007_);
                    v___x_3231_ =
                        lean_infer_type(v_hc_3007_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
                    if leanh::lean_obj_tag(v___x_3231_) == 0 {
                        v_a_3232_ = leanh::lean_ctor_get(v___x_3231_, 0);
                        leanh::lean_inc(v_a_3232_);
                        leanh::lean_dec_ref_known(v___x_3231_, 1);
                        v___x_3233_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwIfWith___closed__20),
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwIfWith___closed__20_once),
                            _init_l_Lean_Meta_rwIfWith___closed__20,
                        );
                        leanh::lean_inc_ref(v_arg_3029_);
                        v___x_3234_ = l_Lean_Meta_mkEq(
                            v_arg_3029_,
                            v___x_3233_,
                            v_a_3009_,
                            v_a_3010_,
                            v_a_3011_,
                            v_a_3012_,
                        );
                        if leanh::lean_obj_tag(v___x_3234_) == 0 {
                            v_a_3235_ = leanh::lean_ctor_get(v___x_3234_, 0);
                            leanh::lean_inc(v_a_3235_);
                            leanh::lean_dec_ref_known(v___x_3234_, 1);
                            v___x_3236_ = l_Lean_Meta_isExprDefEq(
                                v_a_3232_, v_a_3235_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_,
                            );
                            if leanh::lean_obj_tag(v___x_3236_) == 0 {
                                v_a_3237_ = leanh::lean_ctor_get(v___x_3236_, 0);
                                v_isSharedCheck_3257_ =
                                    (!leanh::lean_is_exclusive(v___x_3236_)) as u8;
                                if v_isSharedCheck_3257_ == 0 {
                                    v___x_3239_ = v___x_3236_;
                                    v_isShared_3240_ = v_isSharedCheck_3257_;
                                    state = 27;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3237_);
                                    leanh::lean_dec(v___x_3236_);
                                    v___x_3239_ = leanh::lean_box(0);
                                    v_isShared_3240_ = v_isSharedCheck_3257_;
                                    state = 27;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_3229_);
                                leanh::lean_dec_ref(v_arg_3032_);
                                leanh::lean_dec_ref(v_arg_3029_);
                                leanh::lean_dec_ref(v_arg_3026_);
                                leanh::lean_dec_ref(v_arg_3023_);
                                leanh::lean_dec_ref(v_e_3008_);
                                leanh::lean_dec_ref(v_hc_3007_);
                                v_a_3258_ = leanh::lean_ctor_get(v___x_3236_, 0);
                                v_isSharedCheck_3265_ =
                                    (!leanh::lean_is_exclusive(v___x_3236_)) as u8;
                                if v_isSharedCheck_3265_ == 0 {
                                    v___x_3260_ = v___x_3236_;
                                    v_isShared_3261_ = v_isSharedCheck_3265_;
                                    state = 29;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3258_);
                                    leanh::lean_dec(v___x_3236_);
                                    v___x_3260_ = leanh::lean_box(0);
                                    v_isShared_3261_ = v_isSharedCheck_3265_;
                                    state = 29;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_3232_);
                            leanh::lean_dec(v___x_3229_);
                            leanh::lean_dec_ref(v_arg_3032_);
                            leanh::lean_dec_ref(v_arg_3029_);
                            leanh::lean_dec_ref(v_arg_3026_);
                            leanh::lean_dec_ref(v_arg_3023_);
                            leanh::lean_dec_ref(v_e_3008_);
                            leanh::lean_dec_ref(v_hc_3007_);
                            v_a_3266_ = leanh::lean_ctor_get(v___x_3234_, 0);
                            v_isSharedCheck_3273_ =
                                (!leanh::lean_is_exclusive(v___x_3234_)) as u8;
                            if v_isSharedCheck_3273_ == 0 {
                                v___x_3268_ = v___x_3234_;
                                v_isShared_3269_ = v_isSharedCheck_3273_;
                                state = 31;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3266_);
                                leanh::lean_dec(v___x_3234_);
                                v___x_3268_ = leanh::lean_box(0);
                                v_isShared_3269_ = v_isSharedCheck_3273_;
                                state = 31;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3229_);
                        leanh::lean_dec_ref(v_arg_3032_);
                        leanh::lean_dec_ref(v_arg_3029_);
                        leanh::lean_dec_ref(v_arg_3026_);
                        leanh::lean_dec_ref(v_arg_3023_);
                        leanh::lean_dec_ref(v_e_3008_);
                        leanh::lean_dec_ref(v_hc_3007_);
                        v_a_3274_ = leanh::lean_ctor_get(v___x_3231_, 0);
                        v_isSharedCheck_3281_ =
                            (!leanh::lean_is_exclusive(v___x_3231_)) as u8;
                        if v_isSharedCheck_3281_ == 0 {
                            v___x_3276_ = v___x_3231_;
                            v_isShared_3277_ = v_isSharedCheck_3281_;
                            state = 33;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3274_);
                            leanh::lean_dec(v___x_3231_);
                            v___x_3276_ = leanh::lean_box(0);
                            v_isShared_3277_ = v_isSharedCheck_3281_;
                            state = 33;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3008_);
                    v___x_3282_ = l_Lean_Meta_rwIfWith___closed__24;
                    v___x_3283_ = l_Lean_mkConst(v___x_3282_, v___x_3229_);
                    v___x_3284_ = leanh::lean_unsigned_to_nat(5);
                    v___x_3285_ = lean_mk_empty_array_with_capacity(v___x_3284_);
                    v___x_3286_ = lean_array_push(v___x_3285_, v_arg_3032_);
                    v___x_3287_ = lean_array_push(v___x_3286_, v_arg_3029_);
                    leanh::lean_inc_ref(v_arg_3026_);
                    v___x_3288_ = lean_array_push(v___x_3287_, v_arg_3026_);
                    v___x_3289_ = lean_array_push(v___x_3288_, v_arg_3023_);
                    v___x_3290_ = lean_array_push(v___x_3289_, v_hc_3007_);
                    v___x_3291_ = l_Lean_mkAppN(v___x_3283_, v___x_3290_);
                    leanh::lean_dec_ref(v___x_3290_);
                    v___x_3292_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3292_, 0, v___x_3291_);
                    v___x_3293_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3293_, 0, v_arg_3026_);
                    leanh::lean_ctor_set(v___x_3293_, 1, v___x_3292_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3293_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3035_,
                    );
                    if v_isShared_3228_ == 0 {
                        leanh::lean_ctor_set(v___x_3227_, 0, v___x_3293_);
                        v___x_3295_ = v___x_3227_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_3296_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
                        v___x_3295_ = v_reuseFailAlloc_3296_;
                        state = 35;
                        continue;
                    }
                }
            }
            27 => {
                v___x_3241_ = (leanh::lean_unbox(v_a_3237_) as u8);
                leanh::lean_dec(v_a_3237_);
                if v___x_3241_ == 0 {
                    leanh::lean_del_object(v___x_3239_);
                    leanh::lean_dec(v___x_3229_);
                    leanh::lean_dec_ref(v_arg_3032_);
                    leanh::lean_dec_ref(v_arg_3029_);
                    leanh::lean_dec_ref(v_arg_3026_);
                    leanh::lean_dec_ref(v_arg_3023_);
                    leanh::lean_dec_ref(v_hc_3007_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_3008_);
                    v___x_3242_ = l_Lean_Meta_rwIfWith___closed__22;
                    v___x_3243_ = l_Lean_mkConst(v___x_3242_, v___x_3229_);
                    v___x_3244_ = leanh::lean_unsigned_to_nat(5);
                    v___x_3245_ = lean_mk_empty_array_with_capacity(v___x_3244_);
                    v___x_3246_ = lean_array_push(v___x_3245_, v_arg_3032_);
                    v___x_3247_ = lean_array_push(v___x_3246_, v_arg_3029_);
                    v___x_3248_ = lean_array_push(v___x_3247_, v_arg_3026_);
                    leanh::lean_inc_ref(v_arg_3023_);
                    v___x_3249_ = lean_array_push(v___x_3248_, v_arg_3023_);
                    v___x_3250_ = lean_array_push(v___x_3249_, v_hc_3007_);
                    v___x_3251_ = l_Lean_mkAppN(v___x_3243_, v___x_3250_);
                    leanh::lean_dec_ref(v___x_3250_);
                    v___x_3252_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3252_, 0, v___x_3251_);
                    v___x_3253_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3253_, 0, v_arg_3023_);
                    leanh::lean_ctor_set(v___x_3253_, 1, v___x_3252_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3253_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3035_,
                    );
                    if v_isShared_3240_ == 0 {
                        leanh::lean_ctor_set(v___x_3239_, 0, v___x_3253_);
                        v___x_3255_ = v___x_3239_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_3256_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
                        v___x_3255_ = v_reuseFailAlloc_3256_;
                        state = 28;
                        continue;
                    }
                }
            }
            28 => {
                return v___x_3255_;
            }
            29 => {
                if v_isShared_3261_ == 0 {
                    v___x_3263_ = v___x_3260_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3264_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
                    v___x_3263_ = v_reuseFailAlloc_3264_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3263_;
            }
            31 => {
                if v_isShared_3269_ == 0 {
                    v___x_3271_ = v___x_3268_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3272_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
                    v___x_3271_ = v_reuseFailAlloc_3272_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3271_;
            }
            33 => {
                if v_isShared_3277_ == 0 {
                    v___x_3279_ = v___x_3276_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3280_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
                    v___x_3279_ = v_reuseFailAlloc_3280_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3279_;
            }
            35 => {
                return v___x_3295_;
            }
            36 => {
                if v_isShared_3301_ == 0 {
                    v___x_3303_ = v___x_3300_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3304_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
                    v___x_3303_ = v_reuseFailAlloc_3304_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3303_;
            }
            38 => {
                if v_isShared_3309_ == 0 {
                    v___x_3311_ = v___x_3308_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3312_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
                    v___x_3311_ = v_reuseFailAlloc_3312_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_3311_;
            }
            40 => {
                if v_isShared_3317_ == 0 {
                    v___x_3319_ = v___x_3316_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3320_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
                    v___x_3319_ = v_reuseFailAlloc_3320_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3319_;
            }
            42 => {
                if v_isShared_3325_ == 0 {
                    v___x_3327_ = v___x_3324_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
                    v___x_3327_ = v_reuseFailAlloc_3328_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_3327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_rwIfWith___boxed(
    mut v_hc_3330_: *mut leanh::LeanObject,
    mut v_e_3331_: *mut leanh::LeanObject,
    mut v_a_3332_: *mut leanh::LeanObject,
    mut v_a_3333_: *mut leanh::LeanObject,
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
    mut v_a_3336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3337_ = l_Lean_Meta_rwIfWith(
        v_hc_3330_, v_e_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_,
    );
    leanh::lean_dec(v_a_3335_);
    leanh::lean_dec_ref(v_a_3334_);
    leanh::lean_dec(v_a_3333_);
    leanh::lean_dec_ref(v_a_3332_);
    return v_res_3337_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(
    mut v_e_3338_: *mut leanh::LeanObject,
    mut v___y_3339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = lean_st_ref_get(v___y_3339_);
    v_env_3342_ = leanh::lean_ctor_get(v___x_3341_, 0);
    leanh::lean_inc_ref(v_env_3342_);
    leanh::lean_dec(v___x_3341_);
    v___x_3343_ = l_Lean_Meta_isMatcherAppCore(v_env_3342_, v_e_3338_);
    v___x_3344_ = leanh::lean_box((v___x_3343_) as usize);
    v___x_3345_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3345_, 0, v___x_3344_);
    return v___x_3345_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg___boxed(
    mut v_e_3346_: *mut leanh::LeanObject,
    mut v___y_3347_: *mut leanh::LeanObject,
    mut v___y_3348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3349_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(
        v_e_3346_,
        v___y_3347_,
    );
    leanh::lean_dec(v___y_3347_);
    leanh::lean_dec_ref(v_e_3346_);
    return v_res_3349_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1(
    mut v_e_3350_: *mut leanh::LeanObject,
    mut v___y_3351_: *mut leanh::LeanObject,
    mut v___y_3352_: *mut leanh::LeanObject,
    mut v___y_3353_: *mut leanh::LeanObject,
    mut v___y_3354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3356_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(
        v_e_3350_,
        v___y_3354_,
    );
    return v___x_3356_;
}
pub unsafe fn l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___boxed(
    mut v_e_3357_: *mut leanh::LeanObject,
    mut v___y_3358_: *mut leanh::LeanObject,
    mut v___y_3359_: *mut leanh::LeanObject,
    mut v___y_3360_: *mut leanh::LeanObject,
    mut v___y_3361_: *mut leanh::LeanObject,
    mut v___y_3362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3363_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1(
        v_e_3357_,
        v___y_3358_,
        v___y_3359_,
        v___y_3360_,
        v___y_3361_,
    );
    leanh::lean_dec(v___y_3361_);
    leanh::lean_dec_ref(v___y_3360_);
    leanh::lean_dec(v___y_3359_);
    leanh::lean_dec_ref(v___y_3358_);
    leanh::lean_dec_ref(v_e_3357_);
    return v_res_3363_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(
    mut v_e_3364_: *mut leanh::LeanObject,
    mut v___y_3365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3367_: u8 = 0;
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3381_: u8 = 0;
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3387_: u8 = 0;
    let mut v_unused_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3367_ = l_Lean_Expr_hasMVar(v_e_3364_);
                if v___x_3367_ == 0 {
                    v___x_3368_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3368_, 0, v_e_3364_);
                    return v___x_3368_;
                } else {
                    v___x_3369_ = lean_st_ref_get(v___y_3365_);
                    v_mctx_3370_ = leanh::lean_ctor_get(v___x_3369_, 0);
                    leanh::lean_inc_ref(v_mctx_3370_);
                    leanh::lean_dec(v___x_3369_);
                    v___x_3371_ = l_Lean_instantiateMVarsCore(v_mctx_3370_, v_e_3364_);
                    v_fst_3372_ = leanh::lean_ctor_get(v___x_3371_, 0);
                    leanh::lean_inc(v_fst_3372_);
                    v_snd_3373_ = leanh::lean_ctor_get(v___x_3371_, 1);
                    leanh::lean_inc(v_snd_3373_);
                    leanh::lean_dec_ref(v___x_3371_);
                    v___x_3374_ = lean_st_ref_take(v___y_3365_);
                    v_cache_3375_ = leanh::lean_ctor_get(v___x_3374_, 1);
                    v_zetaDeltaFVarIds_3376_ = leanh::lean_ctor_get(v___x_3374_, 2);
                    v_postponed_3377_ = leanh::lean_ctor_get(v___x_3374_, 3);
                    v_diag_3378_ = leanh::lean_ctor_get(v___x_3374_, 4);
                    v_isSharedCheck_3387_ = (!leanh::lean_is_exclusive(v___x_3374_)) as u8;
                    if v_isSharedCheck_3387_ == 0 {
                        v_unused_3388_ = leanh::lean_ctor_get(v___x_3374_, 0);
                        leanh::lean_dec(v_unused_3388_);
                        v___x_3380_ = v___x_3374_;
                        v_isShared_3381_ = v_isSharedCheck_3387_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_3378_);
                        leanh::lean_inc(v_postponed_3377_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_3376_);
                        leanh::lean_inc(v_cache_3375_);
                        leanh::lean_dec(v___x_3374_);
                        v___x_3380_ = leanh::lean_box(0);
                        v_isShared_3381_ = v_isSharedCheck_3387_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3381_ == 0 {
                    leanh::lean_ctor_set(v___x_3380_, 0, v_snd_3373_);
                    v___x_3383_ = v___x_3380_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3386_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_snd_3373_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_cache_3375_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3386_,
                        2,
                        v_zetaDeltaFVarIds_3376_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 3, v_postponed_3377_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 4, v_diag_3378_);
                    v___x_3383_ = v_reuseFailAlloc_3386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3384_ = lean_st_ref_set(v___y_3365_, v___x_3383_);
                v___x_3385_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3385_, 0, v_fst_3372_);
                return v___x_3385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg___boxed(
    mut v_e_3389_: *mut leanh::LeanObject,
    mut v___y_3390_: *mut leanh::LeanObject,
    mut v___y_3391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3392_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(
        v_e_3389_,
        v___y_3390_,
    );
    leanh::lean_dec(v___y_3390_);
    return v_res_3392_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4(
    mut v_e_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
    mut v___y_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
    mut v___y_3397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(
        v_e_3393_,
        v___y_3395_,
    );
    return v___x_3399_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___boxed(
    mut v_e_3400_: *mut leanh::LeanObject,
    mut v___y_3401_: *mut leanh::LeanObject,
    mut v___y_3402_: *mut leanh::LeanObject,
    mut v___y_3403_: *mut leanh::LeanObject,
    mut v___y_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3406_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4(
        v_e_3400_,
        v___y_3401_,
        v___y_3402_,
        v___y_3403_,
        v___y_3404_,
    );
    leanh::lean_dec(v___y_3404_);
    leanh::lean_dec_ref(v___y_3403_);
    leanh::lean_dec(v___y_3402_);
    leanh::lean_dec_ref(v___y_3401_);
    return v_res_3406_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3407_ = leanh::lean_unsigned_to_nat(32);
    v___x_3408_ = lean_mk_empty_array_with_capacity(v___x_3407_);
    v___x_3409_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3409_, 0, v___x_3408_);
    return v___x_3409_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3410_: usize = 0;
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3410_ = 5usize;
    v___x_3411_ = leanh::lean_unsigned_to_nat(0);
    v___x_3412_ = leanh::lean_unsigned_to_nat(32);
    v___x_3413_ = lean_mk_empty_array_with_capacity(v___x_3412_);
    v___x_3414_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0);
    v___x_3415_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3415_, 0, v___x_3414_);
    leanh::lean_ctor_set(v___x_3415_, 1, v___x_3413_);
    leanh::lean_ctor_set(v___x_3415_, 2, v___x_3411_);
    leanh::lean_ctor_set(v___x_3415_, 3, v___x_3411_);
    leanh::lean_ctor_set_usize(v___x_3415_, 4, v___x_3410_);
    return v___x_3415_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(
    mut v___y_3416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v_tid_3434_: u64 = 0;
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3437_: u8 = 0;
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut v_unused_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3449_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3418_ = lean_st_ref_get(v___y_3416_);
                v_traceState_3419_ = leanh::lean_ctor_get(v___x_3418_, 4);
                leanh::lean_inc_ref(v_traceState_3419_);
                leanh::lean_dec(v___x_3418_);
                v_traces_3420_ = leanh::lean_ctor_get(v_traceState_3419_, 0);
                leanh::lean_inc_ref(v_traces_3420_);
                leanh::lean_dec_ref(v_traceState_3419_);
                v___x_3421_ = lean_st_ref_take(v___y_3416_);
                v_traceState_3422_ = leanh::lean_ctor_get(v___x_3421_, 4);
                v_env_3423_ = leanh::lean_ctor_get(v___x_3421_, 0);
                v_nextMacroScope_3424_ = leanh::lean_ctor_get(v___x_3421_, 1);
                v_ngen_3425_ = leanh::lean_ctor_get(v___x_3421_, 2);
                v_auxDeclNGen_3426_ = leanh::lean_ctor_get(v___x_3421_, 3);
                v_cache_3427_ = leanh::lean_ctor_get(v___x_3421_, 5);
                v_messages_3428_ = leanh::lean_ctor_get(v___x_3421_, 6);
                v_infoState_3429_ = leanh::lean_ctor_get(v___x_3421_, 7);
                v_snapshotTasks_3430_ = leanh::lean_ctor_get(v___x_3421_, 8);
                v_isSharedCheck_3449_ = (!leanh::lean_is_exclusive(v___x_3421_)) as u8;
                if v_isSharedCheck_3449_ == 0 {
                    v___x_3432_ = v___x_3421_;
                    v_isShared_3433_ = v_isSharedCheck_3449_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3430_);
                    leanh::lean_inc(v_infoState_3429_);
                    leanh::lean_inc(v_messages_3428_);
                    leanh::lean_inc(v_cache_3427_);
                    leanh::lean_inc(v_traceState_3422_);
                    leanh::lean_inc(v_auxDeclNGen_3426_);
                    leanh::lean_inc(v_ngen_3425_);
                    leanh::lean_inc(v_nextMacroScope_3424_);
                    leanh::lean_inc(v_env_3423_);
                    leanh::lean_dec(v___x_3421_);
                    v___x_3432_ = leanh::lean_box(0);
                    v_isShared_3433_ = v_isSharedCheck_3449_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_3434_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3422_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3447_ =
                    (!leanh::lean_is_exclusive(v_traceState_3422_)) as u8;
                if v_isSharedCheck_3447_ == 0 {
                    v_unused_3448_ = leanh::lean_ctor_get(v_traceState_3422_, 0);
                    leanh::lean_dec(v_unused_3448_);
                    v___x_3436_ = v_traceState_3422_;
                    v_isShared_3437_ = v_isSharedCheck_3447_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_3422_);
                    v___x_3436_ = leanh::lean_box(0);
                    v_isShared_3437_ = v_isSharedCheck_3447_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3438_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1);
                if v_isShared_3437_ == 0 {
                    leanh::lean_ctor_set(v___x_3436_, 0, v___x_3438_);
                    v___x_3440_ = v___x_3436_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3438_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3446_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3434_,
                    );
                    v___x_3440_ = v_reuseFailAlloc_3446_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3433_ == 0 {
                    leanh::lean_ctor_set(v___x_3432_, 4, v___x_3440_);
                    v___x_3442_ = v___x_3432_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3445_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_env_3423_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 1, v_nextMacroScope_3424_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 2, v_ngen_3425_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 3, v_auxDeclNGen_3426_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 4, v___x_3440_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 5, v_cache_3427_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 6, v_messages_3428_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 7, v_infoState_3429_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 8, v_snapshotTasks_3430_);
                    v___x_3442_ = v_reuseFailAlloc_3445_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3443_ = lean_st_ref_set(v___y_3416_, v___x_3442_);
                v___x_3444_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3444_, 0, v_traces_3420_);
                return v___x_3444_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___boxed(
    mut v___y_3450_: *mut leanh::LeanObject,
    mut v___y_3451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3452_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v___y_3450_);
    leanh::lean_dec(v___y_3450_);
    return v_res_3452_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9(
    mut v___y_3453_: *mut leanh::LeanObject,
    mut v___y_3454_: *mut leanh::LeanObject,
    mut v___y_3455_: *mut leanh::LeanObject,
    mut v___y_3456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3458_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v___y_3456_);
    return v___x_3458_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___boxed(
    mut v___y_3459_: *mut leanh::LeanObject,
    mut v___y_3460_: *mut leanh::LeanObject,
    mut v___y_3461_: *mut leanh::LeanObject,
    mut v___y_3462_: *mut leanh::LeanObject,
    mut v___y_3463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3464_ =
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9(
            v___y_3459_,
            v___y_3460_,
            v___y_3461_,
            v___y_3462_,
        );
    leanh::lean_dec(v___y_3462_);
    leanh::lean_dec_ref(v___y_3461_);
    leanh::lean_dec(v___y_3460_);
    leanh::lean_dec_ref(v___y_3459_);
    return v_res_3464_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(
    mut v_opts_3465_: *mut leanh::LeanObject,
    mut v_opt_3466_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3467_ = leanh::lean_ctor_get(v_opt_3466_, 0);
    v_defValue_3468_ = leanh::lean_ctor_get(v_opt_3466_, 1);
    v_map_3469_ = leanh::lean_ctor_get(v_opts_3465_, 0);
    v___x_3470_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3469_,
            v_name_3467_,
        );
    if leanh::lean_obj_tag(v___x_3470_) == 0 {
        let mut v___x_3471_: u8 = 0;
        v___x_3471_ = (leanh::lean_unbox(v_defValue_3468_) as u8);
        return v___x_3471_;
    } else {
        let mut v_val_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3472_ = leanh::lean_ctor_get(v___x_3470_, 0);
        leanh::lean_inc(v_val_3472_);
        leanh::lean_dec_ref_known(v___x_3470_, 1);
        if leanh::lean_obj_tag(v_val_3472_) == 1 {
            let mut v_v_3473_: u8 = 0;
            v_v_3473_ = leanh::lean_ctor_get_uint8(v_val_3472_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3472_, 0);
            return v_v_3473_;
        } else {
            let mut v___x_3474_: u8 = 0;
            leanh::lean_dec(v_val_3472_);
            v___x_3474_ = (leanh::lean_unbox(v_defValue_3468_) as u8);
            return v___x_3474_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10___boxed(
    mut v_opts_3475_: *mut leanh::LeanObject,
    mut v_opt_3476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3477_: u8 = 0;
    let mut v_r_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3477_ =
        l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_3475_, v_opt_3476_);
    leanh::lean_dec_ref(v_opt_3476_);
    leanh::lean_dec_ref(v_opts_3475_);
    v_r_3478_ = leanh::lean_box((v_res_3477_) as usize);
    return v_r_3478_;
}
pub unsafe fn l_Lean_Meta_rwMatcher___lam__0(
    mut v_e_3479_: *mut leanh::LeanObject,
    mut v___x_3480_: u8,
    mut v_____r_3481_: *mut leanh::LeanObject,
    mut v___y_3482_: *mut leanh::LeanObject,
    mut v___y_3483_: *mut leanh::LeanObject,
    mut v___y_3484_: *mut leanh::LeanObject,
    mut v___y_3485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3487_ = leanh::lean_box(0);
    v___x_3488_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_3488_, 0, v_e_3479_);
    leanh::lean_ctor_set(v___x_3488_, 1, v___x_3487_);
    leanh::lean_ctor_set_uint8(
        v___x_3488_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_3480_,
    );
    v___x_3489_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3489_, 0, v___x_3488_);
    v___x_3490_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3490_, 0, v___x_3489_);
    return v___x_3490_;
}
pub unsafe fn l_Lean_Meta_rwMatcher___lam__0___boxed(
    mut v_e_3491_: *mut leanh::LeanObject,
    mut v___x_3492_: *mut leanh::LeanObject,
    mut v_____r_3493_: *mut leanh::LeanObject,
    mut v___y_3494_: *mut leanh::LeanObject,
    mut v___y_3495_: *mut leanh::LeanObject,
    mut v___y_3496_: *mut leanh::LeanObject,
    mut v___y_3497_: *mut leanh::LeanObject,
    mut v___y_3498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_107860__boxed_3499_: u8 = 0;
    let mut v_res_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_107860__boxed_3499_ = (leanh::lean_unbox(v___x_3492_) as u8);
    v_res_3500_ = l_Lean_Meta_rwMatcher___lam__0(
        v_e_3491_,
        v___x_107860__boxed_3499_,
        v_____r_3493_,
        v___y_3494_,
        v___y_3495_,
        v___y_3496_,
        v___y_3497_,
    );
    leanh::lean_dec(v___y_3497_);
    leanh::lean_dec_ref(v___y_3496_);
    leanh::lean_dec(v___y_3495_);
    leanh::lean_dec_ref(v___y_3494_);
    return v_res_3500_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__1___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3502_ = l_Lean_Meta_rwMatcher___lam__1___closed__0;
    v___x_3503_ = l_Lean_stringToMessageData(v___x_3502_);
    return v___x_3503_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__1___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3505_ = l_Lean_Meta_rwMatcher___lam__1___closed__2;
    v___x_3506_ = l_Lean_stringToMessageData(v___x_3505_);
    return v___x_3506_;
}
pub unsafe fn l_Lean_Meta_rwMatcher___lam__1(
    mut v___x_3507_: *mut leanh::LeanObject,
    mut v___y_3508_: u8,
    mut v_e_3509_: *mut leanh::LeanObject,
    mut v_x_3510_: *mut leanh::LeanObject,
    mut v___y_3511_: *mut leanh::LeanObject,
    mut v___y_3512_: *mut leanh::LeanObject,
    mut v___y_3513_: *mut leanh::LeanObject,
    mut v___y_3514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3516_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__1___closed__1_once),
        _init_l_Lean_Meta_rwMatcher___lam__1___closed__1,
    );
    v___x_3517_ = l_Lean_MessageData_ofConstName(v___x_3507_, v___y_3508_);
    v___x_3518_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3518_, 0, v___x_3516_);
    leanh::lean_ctor_set(v___x_3518_, 1, v___x_3517_);
    v___x_3519_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__1___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__1___closed__3_once),
        _init_l_Lean_Meta_rwMatcher___lam__1___closed__3,
    );
    v___x_3520_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3520_, 0, v___x_3518_);
    leanh::lean_ctor_set(v___x_3520_, 1, v___x_3519_);
    v___x_3521_ = l_Lean_indentExpr(v_e_3509_);
    v___x_3522_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3522_, 0, v___x_3520_);
    leanh::lean_ctor_set(v___x_3522_, 1, v___x_3521_);
    v___x_3523_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3523_, 0, v___x_3522_);
    return v___x_3523_;
}
pub unsafe fn l_Lean_Meta_rwMatcher___lam__1___boxed(
    mut v___x_3524_: *mut leanh::LeanObject,
    mut v___y_3525_: *mut leanh::LeanObject,
    mut v_e_3526_: *mut leanh::LeanObject,
    mut v_x_3527_: *mut leanh::LeanObject,
    mut v___y_3528_: *mut leanh::LeanObject,
    mut v___y_3529_: *mut leanh::LeanObject,
    mut v___y_3530_: *mut leanh::LeanObject,
    mut v___y_3531_: *mut leanh::LeanObject,
    mut v___y_3532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_107902__boxed_3533_: u8 = 0;
    let mut v_res_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_107902__boxed_3533_ = (leanh::lean_unbox(v___y_3525_) as u8);
    v_res_3534_ = l_Lean_Meta_rwMatcher___lam__1(
        v___x_3524_,
        v___y_107902__boxed_3533_,
        v_e_3526_,
        v_x_3527_,
        v___y_3528_,
        v___y_3529_,
        v___y_3530_,
        v___y_3531_,
    );
    leanh::lean_dec(v___y_3531_);
    leanh::lean_dec_ref(v___y_3530_);
    leanh::lean_dec(v___y_3529_);
    leanh::lean_dec_ref(v___y_3528_);
    leanh::lean_dec_ref(v_x_3527_);
    return v_res_3534_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(
    mut v_sz_3535_: usize,
    mut v_i_3536_: usize,
    mut v_bs_3537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3538_: u8 = 0;
    let mut v_v_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: usize = 0;
    let mut v___x_3544_: usize = 0;
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3538_ = lean_usize_dec_lt(v_i_3536_, v_sz_3535_);
                if v___x_3538_ == 0 {
                    return v_bs_3537_;
                } else {
                    v_v_3539_ = lean_array_uget(v_bs_3537_, v_i_3536_);
                    v___x_3540_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3541_ = lean_array_uset(v_bs_3537_, v_i_3536_, v___x_3540_);
                    v___x_3542_ = l_Lean_Expr_mvarId_x21(v_v_3539_);
                    leanh::lean_dec(v_v_3539_);
                    v___x_3543_ = 1usize;
                    v___x_3544_ = lean_usize_add(v_i_3536_, v___x_3543_);
                    v___x_3545_ = lean_array_uset(v_bs_x27_3541_, v_i_3536_, v___x_3542_);
                    v_i_3536_ = v___x_3544_;
                    v_bs_3537_ = v___x_3545_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3___boxed(
    mut v_sz_3547_: *mut leanh::LeanObject,
    mut v_i_3548_: *mut leanh::LeanObject,
    mut v_bs_3549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3550_: usize = 0;
    let mut v_i_boxed_3551_: usize = 0;
    let mut v_res_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3550_ = leanh::lean_unbox_usize(v_sz_3547_);
    leanh::lean_dec(v_sz_3547_);
    v_i_boxed_3551_ = leanh::lean_unbox_usize(v_i_3548_);
    leanh::lean_dec(v_i_3548_);
    v_res_3552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_boxed_3550_, v_i_boxed_3551_, v_bs_3549_);
    return v_res_3552_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(
    mut v_msgData_3553_: *mut leanh::LeanObject,
    mut v___y_3554_: *mut leanh::LeanObject,
    mut v___y_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3559_ = lean_st_ref_get(v___y_3557_);
    v_env_3560_ = leanh::lean_ctor_get(v___x_3559_, 0);
    leanh::lean_inc_ref(v_env_3560_);
    leanh::lean_dec(v___x_3559_);
    v___x_3561_ = lean_st_ref_get(v___y_3555_);
    v_mctx_3562_ = leanh::lean_ctor_get(v___x_3561_, 0);
    leanh::lean_inc_ref(v_mctx_3562_);
    leanh::lean_dec(v___x_3561_);
    v_lctx_3563_ = leanh::lean_ctor_get(v___y_3554_, 2);
    v_options_3564_ = leanh::lean_ctor_get(v___y_3556_, 2);
    leanh::lean_inc_ref(v_options_3564_);
    leanh::lean_inc_ref(v_lctx_3563_);
    v___x_3565_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3565_, 0, v_env_3560_);
    leanh::lean_ctor_set(v___x_3565_, 1, v_mctx_3562_);
    leanh::lean_ctor_set(v___x_3565_, 2, v_lctx_3563_);
    leanh::lean_ctor_set(v___x_3565_, 3, v_options_3564_);
    v___x_3566_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3566_, 0, v___x_3565_);
    leanh::lean_ctor_set(v___x_3566_, 1, v_msgData_3553_);
    v___x_3567_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3567_, 0, v___x_3566_);
    return v___x_3567_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3___boxed(
    mut v_msgData_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
    mut v___y_3571_: *mut leanh::LeanObject,
    mut v___y_3572_: *mut leanh::LeanObject,
    mut v___y_3573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3574_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msgData_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
    leanh::lean_dec(v___y_3572_);
    leanh::lean_dec_ref(v___y_3571_);
    leanh::lean_dec(v___y_3570_);
    leanh::lean_dec_ref(v___y_3569_);
    return v_res_3574_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
    mut v_msg_3575_: *mut leanh::LeanObject,
    mut v___y_3576_: *mut leanh::LeanObject,
    mut v___y_3577_: *mut leanh::LeanObject,
    mut v___y_3578_: *mut leanh::LeanObject,
    mut v___y_3579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3586_: u8 = 0;
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3581_ = leanh::lean_ctor_get(v___y_3578_, 5);
                v___x_3582_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
                v_a_3583_ = leanh::lean_ctor_get(v___x_3582_, 0);
                v_isSharedCheck_3591_ = (!leanh::lean_is_exclusive(v___x_3582_)) as u8;
                if v_isSharedCheck_3591_ == 0 {
                    v___x_3585_ = v___x_3582_;
                    v_isShared_3586_ = v_isSharedCheck_3591_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3583_);
                    leanh::lean_dec(v___x_3582_);
                    v___x_3585_ = leanh::lean_box(0);
                    v_isShared_3586_ = v_isSharedCheck_3591_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3581_);
                v___x_3587_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3587_, 0, v_ref_3581_);
                leanh::lean_ctor_set(v___x_3587_, 1, v_a_3583_);
                if v_isShared_3586_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3585_, 1);
                    leanh::lean_ctor_set(v___x_3585_, 0, v___x_3587_);
                    v___x_3589_ = v___x_3585_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3590_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
                    v___x_3589_ = v_reuseFailAlloc_3590_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg___boxed(
    mut v_msg_3592_: *mut leanh::LeanObject,
    mut v___y_3593_: *mut leanh::LeanObject,
    mut v___y_3594_: *mut leanh::LeanObject,
    mut v___y_3595_: *mut leanh::LeanObject,
    mut v___y_3596_: *mut leanh::LeanObject,
    mut v___y_3597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3598_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
        v_msg_3592_,
        v___y_3593_,
        v___y_3594_,
        v___y_3595_,
        v___y_3596_,
    );
    leanh::lean_dec(v___y_3596_);
    leanh::lean_dec_ref(v___y_3595_);
    leanh::lean_dec(v___y_3594_);
    leanh::lean_dec_ref(v___y_3593_);
    return v_res_3598_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(
    mut v_keys_3599_: *mut leanh::LeanObject,
    mut v_i_3600_: *mut leanh::LeanObject,
    mut v_k_3601_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: u8 = 0;
    let mut v_k_x27_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: u8 = 0;
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3602_ = lean_array_get_size(v_keys_3599_);
                v___x_3603_ = lean_nat_dec_lt(v_i_3600_, v___x_3602_);
                if v___x_3603_ == 0 {
                    leanh::lean_dec(v_i_3600_);
                    return v___x_3603_;
                } else {
                    v_k_x27_3604_ = lean_array_fget_borrowed(v_keys_3599_, v_i_3600_);
                    v___x_3605_ = l_Lean_instBEqMVarId_beq(v_k_3601_, v_k_x27_3604_);
                    if v___x_3605_ == 0 {
                        v___x_3606_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3607_ = lean_nat_add(v_i_3600_, v___x_3606_);
                        leanh::lean_dec(v_i_3600_);
                        v_i_3600_ = v___x_3607_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_3600_);
                        return v___x_3605_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg___boxed(
    mut v_keys_3609_: *mut leanh::LeanObject,
    mut v_i_3610_: *mut leanh::LeanObject,
    mut v_k_3611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3612_: u8 = 0;
    let mut v_r_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3612_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(v_keys_3609_, v_i_3610_, v_k_3611_);
    leanh::lean_dec(v_k_3611_);
    leanh::lean_dec_ref(v_keys_3609_);
    v_r_3613_ = leanh::lean_box((v_res_3612_) as usize);
    return v_r_3613_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0()
-> usize {
    let mut v___x_3614_: usize = 0;
    let mut v___x_3615_: usize = 0;
    let mut v___x_3616_: usize = 0;
    v___x_3614_ = 5usize;
    v___x_3615_ = 1usize;
    v___x_3616_ = lean_usize_shift_left(v___x_3615_, v___x_3614_);
    return v___x_3616_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1()
-> usize {
    let mut v___x_3617_: usize = 0;
    let mut v___x_3618_: usize = 0;
    let mut v___x_3619_: usize = 0;
    v___x_3617_ = 1usize;
    v___x_3618_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0);
    v___x_3619_ = lean_usize_sub(v___x_3618_, v___x_3617_);
    return v___x_3619_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(
    mut v_x_3620_: *mut leanh::LeanObject,
    mut v_x_3621_: usize,
    mut v_x_3622_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: usize = 0;
    let mut v___x_3626_: usize = 0;
    let mut v___x_3627_: usize = 0;
    let mut v_j_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: u8 = 0;
    let mut v_node_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: usize = 0;
    let mut v___x_3635_: u8 = 0;
    let mut v_ks_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3620_) == 0 {
                    v_es_3623_ = leanh::lean_ctor_get(v_x_3620_, 0);
                    v___x_3624_ = leanh::lean_box(2);
                    v___x_3625_ = 5usize;
                    v___x_3626_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1);
                    v___x_3627_ = lean_usize_land(v_x_3621_, v___x_3626_);
                    v_j_3628_ = lean_usize_to_nat(v___x_3627_);
                    v___x_3629_ = lean_array_get_borrowed(v___x_3624_, v_es_3623_, v_j_3628_);
                    leanh::lean_dec(v_j_3628_);
                    match leanh::lean_obj_tag(v___x_3629_) {
                        0 => {
                            v_key_3630_ = leanh::lean_ctor_get(v___x_3629_, 0);
                            v___x_3631_ = l_Lean_instBEqMVarId_beq(v_x_3622_, v_key_3630_);
                            return v___x_3631_;
                        }
                        1 => {
                            v_node_3632_ = leanh::lean_ctor_get(v___x_3629_, 0);
                            v___x_3633_ = lean_usize_shift_right(v_x_3621_, v___x_3625_);
                            v_x_3620_ = v_node_3632_;
                            v_x_3621_ = v___x_3633_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3635_ = 0;
                            return v___x_3635_;
                        }
                    }
                } else {
                    v_ks_3636_ = leanh::lean_ctor_get(v_x_3620_, 0);
                    v___x_3637_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3638_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(v_ks_3636_, v___x_3637_, v_x_3622_);
                    return v___x_3638_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(
    mut v_x_3639_: *mut leanh::LeanObject,
    mut v_x_3640_: *mut leanh::LeanObject,
    mut v_x_3641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_108047__boxed_3642_: usize = 0;
    let mut v_res_3643_: u8 = 0;
    let mut v_r_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_108047__boxed_3642_ = leanh::lean_unbox_usize(v_x_3640_);
    leanh::lean_dec(v_x_3640_);
    v_res_3643_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_3639_, v_x_108047__boxed_3642_, v_x_3641_);
    leanh::lean_dec(v_x_3641_);
    leanh::lean_dec_ref(v_x_3639_);
    v_r_3644_ = leanh::lean_box((v_res_3643_) as usize);
    return v_r_3644_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(
    mut v_x_3645_: *mut leanh::LeanObject,
    mut v_x_3646_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3647_: u64 = 0;
    let mut v___x_3648_: usize = 0;
    let mut v___x_3649_: u8 = 0;
    v___x_3647_ = l_Lean_instHashableMVarId_hash(v_x_3646_);
    v___x_3648_ = lean_uint64_to_usize(v___x_3647_);
    v___x_3649_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_3645_, v___x_3648_, v_x_3646_);
    return v___x_3649_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(
    mut v_x_3650_: *mut leanh::LeanObject,
    mut v_x_3651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3652_: u8 = 0;
    let mut v_r_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3652_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_3650_, v_x_3651_);
    leanh::lean_dec(v_x_3651_);
    leanh::lean_dec_ref(v_x_3650_);
    v_r_3653_ = leanh::lean_box((v_res_3652_) as usize);
    return v_r_3653_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(
    mut v_mvarId_3654_: *mut leanh::LeanObject,
    mut v___y_3655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: u8 = 0;
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3657_ = lean_st_ref_get(v___y_3655_);
    v_mctx_3658_ = leanh::lean_ctor_get(v___x_3657_, 0);
    leanh::lean_inc_ref(v_mctx_3658_);
    leanh::lean_dec(v___x_3657_);
    v_eAssignment_3659_ = leanh::lean_ctor_get(v_mctx_3658_, 8);
    leanh::lean_inc_ref(v_eAssignment_3659_);
    leanh::lean_dec_ref(v_mctx_3658_);
    v___x_3660_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_eAssignment_3659_, v_mvarId_3654_);
    leanh::lean_dec_ref(v_eAssignment_3659_);
    v___x_3661_ = leanh::lean_box((v___x_3660_) as usize);
    v___x_3662_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3662_, 0, v___x_3661_);
    return v___x_3662_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(
    mut v_mvarId_3663_: *mut leanh::LeanObject,
    mut v___y_3664_: *mut leanh::LeanObject,
    mut v___y_3665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3666_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(
        v_mvarId_3663_,
        v___y_3664_,
    );
    leanh::lean_dec(v___y_3664_);
    leanh::lean_dec(v_mvarId_3663_);
    return v_res_3666_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(
    mut v___x_3667_: u8,
    mut v_as_3668_: *mut leanh::LeanObject,
    mut v_i_3669_: usize,
    mut v_stop_3670_: usize,
    mut v_b_3671_: *mut leanh::LeanObject,
    mut v___y_3672_: *mut leanh::LeanObject,
    mut v___y_3673_: *mut leanh::LeanObject,
    mut v___y_3674_: *mut leanh::LeanObject,
    mut v___y_3675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: usize = 0;
    let mut v___x_3680_: usize = 0;
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3687_: u8 = 0;
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: u8 = 0;
    let mut v_a_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: u8 = 0;
    let mut v_a_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3696_: u8 = 0;
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3700_: u8 = 0;
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3682_ = lean_usize_dec_eq(v_i_3669_, v_stop_3670_);
                if v___x_3682_ == 0 {
                    v___x_3683_ = lean_array_uget_borrowed(v_as_3668_, v_i_3669_);
                    v___x_3688_ =
                        l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(
                            v___x_3683_,
                            v___y_3673_,
                        );
                    if leanh::lean_obj_tag(v___x_3688_) == 0 {
                        v_a_3689_ = leanh::lean_ctor_get(v___x_3688_, 0);
                        leanh::lean_inc(v_a_3689_);
                        leanh::lean_dec_ref_known(v___x_3688_, 1);
                        v___x_3690_ = (leanh::lean_unbox(v_a_3689_) as u8);
                        leanh::lean_dec(v_a_3689_);
                        if v___x_3690_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_3687_ = v___x_3667_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_3688_) == 0 {
                            v_a_3691_ = leanh::lean_ctor_get(v___x_3688_, 0);
                            leanh::lean_inc(v_a_3691_);
                            leanh::lean_dec_ref_known(v___x_3688_, 1);
                            v___x_3692_ = (leanh::lean_unbox(v_a_3691_) as u8);
                            leanh::lean_dec(v_a_3691_);
                            v_a_3687_ = v___x_3692_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_3671_);
                            v_a_3693_ = leanh::lean_ctor_get(v___x_3688_, 0);
                            v_isSharedCheck_3700_ =
                                (!leanh::lean_is_exclusive(v___x_3688_)) as u8;
                            if v_isSharedCheck_3700_ == 0 {
                                v___x_3695_ = v___x_3688_;
                                v_isShared_3696_ = v_isSharedCheck_3700_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3693_);
                                leanh::lean_dec(v___x_3688_);
                                v___x_3695_ = leanh::lean_box(0);
                                v_isShared_3696_ = v_isSharedCheck_3700_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_3701_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3701_, 0, v_b_3671_);
                    return v___x_3701_;
                }
            }
            1 => {
                v___x_3679_ = 1usize;
                v___x_3680_ = lean_usize_add(v_i_3669_, v___x_3679_);
                v_i_3669_ = v___x_3680_;
                v_b_3671_ = v_a_3678_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v___x_3683_);
                v___x_3685_ = lean_array_push(v_b_3671_, v___x_3683_);
                v_a_3678_ = v___x_3685_;
                state = 1;
                continue;
            }
            3 => {
                if v_a_3687_ == 0 {
                    v_a_3678_ = v_b_3671_;
                    state = 1;
                    continue;
                } else {
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_3696_ == 0 {
                    v___x_3698_ = v___x_3695_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3699_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
                    v___x_3698_ = v_reuseFailAlloc_3699_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12___boxed(
    mut v___x_3702_: *mut leanh::LeanObject,
    mut v_as_3703_: *mut leanh::LeanObject,
    mut v_i_3704_: *mut leanh::LeanObject,
    mut v_stop_3705_: *mut leanh::LeanObject,
    mut v_b_3706_: *mut leanh::LeanObject,
    mut v___y_3707_: *mut leanh::LeanObject,
    mut v___y_3708_: *mut leanh::LeanObject,
    mut v___y_3709_: *mut leanh::LeanObject,
    mut v___y_3710_: *mut leanh::LeanObject,
    mut v___y_3711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_108119__boxed_3712_: u8 = 0;
    let mut v_i_boxed_3713_: usize = 0;
    let mut v_stop_boxed_3714_: usize = 0;
    let mut v_res_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_108119__boxed_3712_ = (leanh::lean_unbox(v___x_3702_) as u8);
    v_i_boxed_3713_ = leanh::lean_unbox_usize(v_i_3704_);
    leanh::lean_dec(v_i_3704_);
    v_stop_boxed_3714_ = leanh::lean_unbox_usize(v_stop_3705_);
    leanh::lean_dec(v_stop_3705_);
    v_res_3715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_108119__boxed_3712_, v_as_3703_, v_i_boxed_3713_, v_stop_boxed_3714_, v_b_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_);
    leanh::lean_dec(v___y_3710_);
    leanh::lean_dec_ref(v___y_3709_);
    leanh::lean_dec(v___y_3708_);
    leanh::lean_dec_ref(v___y_3707_);
    leanh::lean_dec_ref(v_as_3703_);
    return v_res_3715_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0;
    v___x_3718_ = l_Lean_stringToMessageData(v___x_3717_);
    return v___x_3718_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2;
    v___x_3721_ = l_Lean_stringToMessageData(v___x_3720_);
    return v___x_3721_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4;
    v___x_3724_ = l_Lean_stringToMessageData(v___x_3723_);
    return v___x_3724_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(
    mut v_as_3725_: *mut leanh::LeanObject,
    mut v_sz_3726_: usize,
    mut v_i_3727_: usize,
    mut v_b_3728_: *mut leanh::LeanObject,
    mut v___y_3729_: *mut leanh::LeanObject,
    mut v___y_3730_: *mut leanh::LeanObject,
    mut v___y_3731_: *mut leanh::LeanObject,
    mut v___y_3732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: usize = 0;
    let mut v___x_3737_: usize = 0;
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3750_: u8 = 0;
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3754_: u8 = 0;
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3763_: u8 = 0;
    let mut v_unused_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3770_: u8 = 0;
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3774_: u8 = 0;
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3783_: u8 = 0;
    let mut v_unused_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: u8 = 0;
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: u8 = 0;
    let mut v___x_3791_: u8 = 0;
    let mut v___x_3792_: u8 = 0;
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3798_: u8 = 0;
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: u8 = 0;
    let mut v___x_3805_: u8 = 0;
    let mut v_a_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3809_: u8 = 0;
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3813_: u8 = 0;
    let mut v___x_3814_: u8 = 0;
    let mut v___x_3815_: u8 = 0;
    let mut v_a_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3819_: u8 = 0;
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3823_: u8 = 0;
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3829_: u8 = 0;
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: u8 = 0;
    let mut v___x_3836_: u8 = 0;
    let mut v_a_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3840_: u8 = 0;
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut v___x_3845_: u8 = 0;
    let mut v___x_3846_: u8 = 0;
    let mut v_a_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3854_: u8 = 0;
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3860_: u8 = 0;
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3864_: u8 = 0;
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut v_unused_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: u8 = 0;
    let mut v___x_3876_: u8 = 0;
    let mut v_a_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3880_: u8 = 0;
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3884_: u8 = 0;
    let mut v_a_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3888_: u8 = 0;
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3892_: u8 = 0;
    let mut v_a_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3896_: u8 = 0;
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3739_ = lean_usize_dec_lt(v_i_3727_, v_sz_3726_);
                if v___x_3739_ == 0 {
                    v___x_3740_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3740_, 0, v_b_3728_);
                    return v___x_3740_;
                } else {
                    v_a_3741_ = lean_array_uget_borrowed(v_as_3725_, v_i_3727_);
                    v___x_3742_ =
                        l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(
                            v_a_3741_,
                            v___y_3730_,
                        );
                    if leanh::lean_obj_tag(v___x_3742_) == 0 {
                        v_a_3743_ = leanh::lean_ctor_get(v___x_3742_, 0);
                        leanh::lean_inc(v_a_3743_);
                        leanh::lean_dec_ref_known(v___x_3742_, 1);
                        v___x_3744_ = leanh::lean_box(0);
                        v___x_3787_ = (leanh::lean_unbox(v_a_3743_) as u8);
                        leanh::lean_dec(v_a_3743_);
                        if v___x_3787_ == 0 {
                            leanh::lean_inc(v_a_3741_);
                            v___x_3788_ = l_Lean_MVarId_getType(
                                v_a_3741_,
                                v___y_3729_,
                                v___y_3730_,
                                v___y_3731_,
                                v___y_3732_,
                            );
                            if leanh::lean_obj_tag(v___x_3788_) == 0 {
                                v_a_3789_ = leanh::lean_ctor_get(v___x_3788_, 0);
                                leanh::lean_inc_n(v_a_3789_, 2);
                                leanh::lean_dec_ref_known(v___x_3788_, 1);
                                v___x_3790_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_3789_);
                                if v___x_3790_ == 0 {
                                    v___x_3791_ = l_Lean_Expr_isEq(v_a_3789_);
                                    if v___x_3791_ == 0 {
                                        v___x_3792_ = l_Lean_Expr_isHEq(v_a_3789_);
                                        leanh::lean_dec(v_a_3789_);
                                        if v___x_3792_ == 0 {
                                            v_a_3735_ = v___x_3744_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_3793_ = l_Lean_Meta_saveState___redArg(
                                                v___y_3730_,
                                                v___y_3732_,
                                            );
                                            if leanh::lean_obj_tag(v___x_3793_) == 0 {
                                                v_a_3794_ =
                                                    leanh::lean_ctor_get(v___x_3793_, 0);
                                                leanh::lean_inc(v_a_3794_);
                                                leanh::lean_dec_ref_known(v___x_3793_, 1);
                                                leanh::lean_inc(v_a_3741_);
                                                v___x_3795_ = l_Lean_MVarId_assumption(
                                                    v_a_3741_,
                                                    v___y_3729_,
                                                    v___y_3730_,
                                                    v___y_3731_,
                                                    v___y_3732_,
                                                );
                                                if leanh::lean_obj_tag(v___x_3795_) == 0 {
                                                    leanh::lean_dec(v_a_3794_);
                                                    v___y_3766_ = v___x_3795_;
                                                    state = 6;
                                                    continue;
                                                } else {
                                                    v_a_3796_ =
                                                        leanh::lean_ctor_get(v___x_3795_, 0);
                                                    leanh::lean_inc(v_a_3796_);
                                                    v___x_3814_ =
                                                        l_Lean_Exception_isInterrupt(v_a_3796_);
                                                    if v___x_3814_ == 0 {
                                                        v___x_3815_ =
                                                            l_Lean_Exception_isRuntime(v_a_3796_);
                                                        v___y_3798_ = v___x_3815_;
                                                        state = 11;
                                                        continue;
                                                    } else {
                                                        leanh::lean_dec(v_a_3796_);
                                                        v___y_3798_ = v___x_3814_;
                                                        state = 11;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                v_a_3816_ =
                                                    leanh::lean_ctor_get(v___x_3793_, 0);
                                                v_isSharedCheck_3823_ =
                                                    (!leanh::lean_is_exclusive(v___x_3793_))
                                                        as u8;
                                                if v_isSharedCheck_3823_ == 0 {
                                                    v___x_3818_ = v___x_3793_;
                                                    v_isShared_3819_ = v_isSharedCheck_3823_;
                                                    state = 14;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_3816_);
                                                    leanh::lean_dec(v___x_3793_);
                                                    v___x_3818_ = leanh::lean_box(0);
                                                    v_isShared_3819_ = v_isSharedCheck_3823_;
                                                    state = 14;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_3789_);
                                        v___x_3824_ = l_Lean_Meta_saveState___redArg(
                                            v___y_3730_,
                                            v___y_3732_,
                                        );
                                        if leanh::lean_obj_tag(v___x_3824_) == 0 {
                                            v_a_3825_ = leanh::lean_ctor_get(v___x_3824_, 0);
                                            leanh::lean_inc(v_a_3825_);
                                            leanh::lean_dec_ref_known(v___x_3824_, 1);
                                            leanh::lean_inc(v_a_3741_);
                                            v___x_3826_ = l_Lean_MVarId_assumption(
                                                v_a_3741_,
                                                v___y_3729_,
                                                v___y_3730_,
                                                v___y_3731_,
                                                v___y_3732_,
                                            );
                                            if leanh::lean_obj_tag(v___x_3826_) == 0 {
                                                leanh::lean_dec(v_a_3825_);
                                                v___y_3746_ = v___x_3826_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v_a_3827_ =
                                                    leanh::lean_ctor_get(v___x_3826_, 0);
                                                leanh::lean_inc(v_a_3827_);
                                                v___x_3845_ =
                                                    l_Lean_Exception_isInterrupt(v_a_3827_);
                                                if v___x_3845_ == 0 {
                                                    v___x_3846_ =
                                                        l_Lean_Exception_isRuntime(v_a_3827_);
                                                    v___y_3829_ = v___x_3846_;
                                                    state = 16;
                                                    continue;
                                                } else {
                                                    leanh::lean_dec(v_a_3827_);
                                                    v___y_3829_ = v___x_3845_;
                                                    state = 16;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v_a_3847_ = leanh::lean_ctor_get(v___x_3824_, 0);
                                            v_isSharedCheck_3854_ =
                                                (!leanh::lean_is_exclusive(v___x_3824_))
                                                    as u8;
                                            if v_isSharedCheck_3854_ == 0 {
                                                v___x_3849_ = v___x_3824_;
                                                v_isShared_3850_ = v_isSharedCheck_3854_;
                                                state = 19;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3847_);
                                                leanh::lean_dec(v___x_3824_);
                                                v___x_3849_ = leanh::lean_box(0);
                                                v_isShared_3850_ = v_isSharedCheck_3854_;
                                                state = 19;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_3789_);
                                    v___x_3855_ =
                                        l_Lean_Meta_saveState___redArg(v___y_3730_, v___y_3732_);
                                    if leanh::lean_obj_tag(v___x_3855_) == 0 {
                                        v_a_3856_ = leanh::lean_ctor_get(v___x_3855_, 0);
                                        leanh::lean_inc(v_a_3856_);
                                        leanh::lean_dec_ref_known(v___x_3855_, 1);
                                        leanh::lean_inc(v_a_3741_);
                                        v___x_3857_ = l_Lean_MVarId_assumption(
                                            v_a_3741_,
                                            v___y_3729_,
                                            v___y_3730_,
                                            v___y_3731_,
                                            v___y_3732_,
                                        );
                                        if leanh::lean_obj_tag(v___x_3857_) == 0 {
                                            leanh::lean_dec(v_a_3856_);
                                            v___y_3786_ = v___x_3857_;
                                            state = 10;
                                            continue;
                                        } else {
                                            v_a_3858_ = leanh::lean_ctor_get(v___x_3857_, 0);
                                            leanh::lean_inc(v_a_3858_);
                                            v___x_3875_ = l_Lean_Exception_isInterrupt(v_a_3858_);
                                            if v___x_3875_ == 0 {
                                                v___x_3876_ = l_Lean_Exception_isRuntime(v_a_3858_);
                                                v___y_3860_ = v___x_3876_;
                                                state = 21;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_a_3858_);
                                                v___y_3860_ = v___x_3875_;
                                                state = 21;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v_a_3877_ = leanh::lean_ctor_get(v___x_3855_, 0);
                                        v_isSharedCheck_3884_ =
                                            (!leanh::lean_is_exclusive(v___x_3855_)) as u8;
                                        if v_isSharedCheck_3884_ == 0 {
                                            v___x_3879_ = v___x_3855_;
                                            v_isShared_3880_ = v_isSharedCheck_3884_;
                                            state = 24;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3877_);
                                            leanh::lean_dec(v___x_3855_);
                                            v___x_3879_ = leanh::lean_box(0);
                                            v_isShared_3880_ = v_isSharedCheck_3884_;
                                            state = 24;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v_a_3885_ = leanh::lean_ctor_get(v___x_3788_, 0);
                                v_isSharedCheck_3892_ =
                                    (!leanh::lean_is_exclusive(v___x_3788_)) as u8;
                                if v_isSharedCheck_3892_ == 0 {
                                    v___x_3887_ = v___x_3788_;
                                    v_isShared_3888_ = v_isSharedCheck_3892_;
                                    state = 26;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3885_);
                                    leanh::lean_dec(v___x_3788_);
                                    v___x_3887_ = leanh::lean_box(0);
                                    v_isShared_3888_ = v_isSharedCheck_3892_;
                                    state = 26;
                                    continue;
                                }
                            }
                        } else {
                            v_a_3735_ = v___x_3744_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3893_ = leanh::lean_ctor_get(v___x_3742_, 0);
                        v_isSharedCheck_3900_ =
                            (!leanh::lean_is_exclusive(v___x_3742_)) as u8;
                        if v_isSharedCheck_3900_ == 0 {
                            v___x_3895_ = v___x_3742_;
                            v_isShared_3896_ = v_isSharedCheck_3900_;
                            state = 28;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3893_);
                            leanh::lean_dec(v___x_3742_);
                            v___x_3895_ = leanh::lean_box(0);
                            v_isShared_3896_ = v_isSharedCheck_3900_;
                            state = 28;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3736_ = 1usize;
                v___x_3737_ = lean_usize_add(v_i_3727_, v___x_3736_);
                v_i_3727_ = v___x_3737_;
                v_b_3728_ = v_a_3735_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_3746_) == 0 {
                    leanh::lean_dec_ref_known(v___y_3746_, 1);
                    v_a_3735_ = v___x_3744_;
                    state = 1;
                    continue;
                } else {
                    return v___y_3746_;
                }
            }
            3 => {
                if v___y_3750_ == 0 {
                    leanh::lean_dec_ref(v___y_3748_);
                    v___x_3751_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_3749_,
                        v___y_3730_,
                        v___y_3732_,
                    );
                    leanh::lean_dec_ref(v___y_3749_);
                    if leanh::lean_obj_tag(v___x_3751_) == 0 {
                        v_isSharedCheck_3763_ =
                            (!leanh::lean_is_exclusive(v___x_3751_)) as u8;
                        if v_isSharedCheck_3763_ == 0 {
                            v_unused_3764_ = leanh::lean_ctor_get(v___x_3751_, 0);
                            leanh::lean_dec(v_unused_3764_);
                            v___x_3753_ = v___x_3751_;
                            v_isShared_3754_ = v_isSharedCheck_3763_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3751_);
                            v___x_3753_ = leanh::lean_box(0);
                            v_isShared_3754_ = v_isSharedCheck_3763_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___y_3746_ = v___x_3751_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3749_);
                    v___y_3746_ = v___y_3748_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_3755_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
                leanh::lean_inc(v_a_3741_);
                if v_isShared_3754_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3753_, 1);
                    leanh::lean_ctor_set(v___x_3753_, 0, v_a_3741_);
                    v___x_3757_ = v___x_3753_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3762_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3741_);
                    v___x_3757_ = v_reuseFailAlloc_3762_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3758_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3758_, 0, v___x_3755_);
                leanh::lean_ctor_set(v___x_3758_, 1, v___x_3757_);
                v___x_3759_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
                v___x_3760_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3760_, 0, v___x_3758_);
                leanh::lean_ctor_set(v___x_3760_, 1, v___x_3759_);
                v___x_3761_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                    v___x_3760_,
                    v___y_3729_,
                    v___y_3730_,
                    v___y_3731_,
                    v___y_3732_,
                );
                v___y_3746_ = v___x_3761_;
                state = 2;
                continue;
            }
            6 => {
                if leanh::lean_obj_tag(v___y_3766_) == 0 {
                    leanh::lean_dec_ref_known(v___y_3766_, 1);
                    v_a_3735_ = v___x_3744_;
                    state = 1;
                    continue;
                } else {
                    return v___y_3766_;
                }
            }
            7 => {
                if v___y_3770_ == 0 {
                    leanh::lean_dec_ref(v___y_3768_);
                    v___x_3771_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_3769_,
                        v___y_3730_,
                        v___y_3732_,
                    );
                    leanh::lean_dec_ref(v___y_3769_);
                    if leanh::lean_obj_tag(v___x_3771_) == 0 {
                        v_isSharedCheck_3783_ =
                            (!leanh::lean_is_exclusive(v___x_3771_)) as u8;
                        if v_isSharedCheck_3783_ == 0 {
                            v_unused_3784_ = leanh::lean_ctor_get(v___x_3771_, 0);
                            leanh::lean_dec(v_unused_3784_);
                            v___x_3773_ = v___x_3771_;
                            v_isShared_3774_ = v_isSharedCheck_3783_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3771_);
                            v___x_3773_ = leanh::lean_box(0);
                            v_isShared_3774_ = v_isSharedCheck_3783_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___y_3766_ = v___x_3771_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3769_);
                    v___y_3766_ = v___y_3768_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_3775_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
                leanh::lean_inc(v_a_3741_);
                if v_isShared_3774_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3773_, 1);
                    leanh::lean_ctor_set(v___x_3773_, 0, v_a_3741_);
                    v___x_3777_ = v___x_3773_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3782_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3741_);
                    v___x_3777_ = v_reuseFailAlloc_3782_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3778_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3778_, 0, v___x_3775_);
                leanh::lean_ctor_set(v___x_3778_, 1, v___x_3777_);
                v___x_3779_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
                v___x_3780_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3780_, 0, v___x_3778_);
                leanh::lean_ctor_set(v___x_3780_, 1, v___x_3779_);
                v___x_3781_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                    v___x_3780_,
                    v___y_3729_,
                    v___y_3730_,
                    v___y_3731_,
                    v___y_3732_,
                );
                v___y_3766_ = v___x_3781_;
                state = 6;
                continue;
            }
            10 => {
                if leanh::lean_obj_tag(v___y_3786_) == 0 {
                    leanh::lean_dec_ref_known(v___y_3786_, 1);
                    v_a_3735_ = v___x_3744_;
                    state = 1;
                    continue;
                } else {
                    return v___y_3786_;
                }
            }
            11 => {
                if v___y_3798_ == 0 {
                    leanh::lean_dec_ref_known(v___x_3795_, 1);
                    v___x_3799_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_3794_,
                        v___y_3730_,
                        v___y_3732_,
                    );
                    leanh::lean_dec(v_a_3794_);
                    if leanh::lean_obj_tag(v___x_3799_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3799_, 1);
                        v___x_3800_ = l_Lean_Meta_saveState___redArg(v___y_3730_, v___y_3732_);
                        if leanh::lean_obj_tag(v___x_3800_) == 0 {
                            v_a_3801_ = leanh::lean_ctor_get(v___x_3800_, 0);
                            leanh::lean_inc(v_a_3801_);
                            leanh::lean_dec_ref_known(v___x_3800_, 1);
                            leanh::lean_inc(v_a_3741_);
                            v___x_3802_ = l_Lean_MVarId_hrefl(
                                v_a_3741_,
                                v___y_3729_,
                                v___y_3730_,
                                v___y_3731_,
                                v___y_3732_,
                            );
                            if leanh::lean_obj_tag(v___x_3802_) == 0 {
                                leanh::lean_dec(v_a_3801_);
                                v___y_3766_ = v___x_3802_;
                                state = 6;
                                continue;
                            } else {
                                v_a_3803_ = leanh::lean_ctor_get(v___x_3802_, 0);
                                leanh::lean_inc(v_a_3803_);
                                v___x_3804_ = l_Lean_Exception_isInterrupt(v_a_3803_);
                                if v___x_3804_ == 0 {
                                    v___x_3805_ = l_Lean_Exception_isRuntime(v_a_3803_);
                                    v___y_3768_ = v___x_3802_;
                                    v___y_3769_ = v_a_3801_;
                                    v___y_3770_ = v___x_3805_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_3803_);
                                    v___y_3768_ = v___x_3802_;
                                    v___y_3769_ = v_a_3801_;
                                    v___y_3770_ = v___x_3804_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            v_a_3806_ = leanh::lean_ctor_get(v___x_3800_, 0);
                            v_isSharedCheck_3813_ =
                                (!leanh::lean_is_exclusive(v___x_3800_)) as u8;
                            if v_isSharedCheck_3813_ == 0 {
                                v___x_3808_ = v___x_3800_;
                                v_isShared_3809_ = v_isSharedCheck_3813_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3806_);
                                leanh::lean_dec(v___x_3800_);
                                v___x_3808_ = leanh::lean_box(0);
                                v_isShared_3809_ = v_isSharedCheck_3813_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        v___y_3766_ = v___x_3799_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3794_);
                    v___y_3766_ = v___x_3795_;
                    state = 6;
                    continue;
                }
            }
            12 => {
                if v_isShared_3809_ == 0 {
                    v___x_3811_ = v___x_3808_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3812_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
                    v___x_3811_ = v_reuseFailAlloc_3812_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3811_;
            }
            14 => {
                if v_isShared_3819_ == 0 {
                    v___x_3821_ = v___x_3818_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
                    v___x_3821_ = v_reuseFailAlloc_3822_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3821_;
            }
            16 => {
                if v___y_3829_ == 0 {
                    leanh::lean_dec_ref_known(v___x_3826_, 1);
                    v___x_3830_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_3825_,
                        v___y_3730_,
                        v___y_3732_,
                    );
                    leanh::lean_dec(v_a_3825_);
                    if leanh::lean_obj_tag(v___x_3830_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3830_, 1);
                        v___x_3831_ = l_Lean_Meta_saveState___redArg(v___y_3730_, v___y_3732_);
                        if leanh::lean_obj_tag(v___x_3831_) == 0 {
                            v_a_3832_ = leanh::lean_ctor_get(v___x_3831_, 0);
                            leanh::lean_inc(v_a_3832_);
                            leanh::lean_dec_ref_known(v___x_3831_, 1);
                            leanh::lean_inc(v_a_3741_);
                            v___x_3833_ = l_Lean_MVarId_refl(
                                v_a_3741_,
                                v___x_3791_,
                                v___y_3729_,
                                v___y_3730_,
                                v___y_3731_,
                                v___y_3732_,
                            );
                            if leanh::lean_obj_tag(v___x_3833_) == 0 {
                                leanh::lean_dec(v_a_3832_);
                                v___y_3746_ = v___x_3833_;
                                state = 2;
                                continue;
                            } else {
                                v_a_3834_ = leanh::lean_ctor_get(v___x_3833_, 0);
                                leanh::lean_inc(v_a_3834_);
                                v___x_3835_ = l_Lean_Exception_isInterrupt(v_a_3834_);
                                if v___x_3835_ == 0 {
                                    v___x_3836_ = l_Lean_Exception_isRuntime(v_a_3834_);
                                    v___y_3748_ = v___x_3833_;
                                    v___y_3749_ = v_a_3832_;
                                    v___y_3750_ = v___x_3836_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_3834_);
                                    v___y_3748_ = v___x_3833_;
                                    v___y_3749_ = v_a_3832_;
                                    v___y_3750_ = v___x_3835_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_a_3837_ = leanh::lean_ctor_get(v___x_3831_, 0);
                            v_isSharedCheck_3844_ =
                                (!leanh::lean_is_exclusive(v___x_3831_)) as u8;
                            if v_isSharedCheck_3844_ == 0 {
                                v___x_3839_ = v___x_3831_;
                                v_isShared_3840_ = v_isSharedCheck_3844_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3837_);
                                leanh::lean_dec(v___x_3831_);
                                v___x_3839_ = leanh::lean_box(0);
                                v_isShared_3840_ = v_isSharedCheck_3844_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        v___y_3746_ = v___x_3830_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3825_);
                    v___y_3746_ = v___x_3826_;
                    state = 2;
                    continue;
                }
            }
            17 => {
                if v_isShared_3840_ == 0 {
                    v___x_3842_ = v___x_3839_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3843_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
                    v___x_3842_ = v_reuseFailAlloc_3843_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3842_;
            }
            19 => {
                if v_isShared_3850_ == 0 {
                    v___x_3852_ = v___x_3849_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3853_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
                    v___x_3852_ = v_reuseFailAlloc_3853_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3852_;
            }
            21 => {
                if v___y_3860_ == 0 {
                    leanh::lean_dec_ref_known(v___x_3857_, 1);
                    v___x_3861_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_3856_,
                        v___y_3730_,
                        v___y_3732_,
                    );
                    leanh::lean_dec(v_a_3856_);
                    if leanh::lean_obj_tag(v___x_3861_) == 0 {
                        v_isSharedCheck_3873_ =
                            (!leanh::lean_is_exclusive(v___x_3861_)) as u8;
                        if v_isSharedCheck_3873_ == 0 {
                            v_unused_3874_ = leanh::lean_ctor_get(v___x_3861_, 0);
                            leanh::lean_dec(v_unused_3874_);
                            v___x_3863_ = v___x_3861_;
                            v_isShared_3864_ = v_isSharedCheck_3873_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3861_);
                            v___x_3863_ = leanh::lean_box(0);
                            v_isShared_3864_ = v_isSharedCheck_3873_;
                            state = 22;
                            continue;
                        }
                    } else {
                        v___y_3786_ = v___x_3861_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3856_);
                    v___y_3786_ = v___x_3857_;
                    state = 10;
                    continue;
                }
            }
            22 => {
                v___x_3865_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5);
                leanh::lean_inc(v_a_3741_);
                if v_isShared_3864_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3863_, 1);
                    leanh::lean_ctor_set(v___x_3863_, 0, v_a_3741_);
                    v___x_3867_ = v___x_3863_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3872_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3741_);
                    v___x_3867_ = v_reuseFailAlloc_3872_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_3868_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3868_, 0, v___x_3865_);
                leanh::lean_ctor_set(v___x_3868_, 1, v___x_3867_);
                v___x_3869_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
                v___x_3870_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3870_, 0, v___x_3868_);
                leanh::lean_ctor_set(v___x_3870_, 1, v___x_3869_);
                v___x_3871_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                    v___x_3870_,
                    v___y_3729_,
                    v___y_3730_,
                    v___y_3731_,
                    v___y_3732_,
                );
                v___y_3786_ = v___x_3871_;
                state = 10;
                continue;
            }
            24 => {
                if v_isShared_3880_ == 0 {
                    v___x_3882_ = v___x_3879_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3883_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
                    v___x_3882_ = v_reuseFailAlloc_3883_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3882_;
            }
            26 => {
                if v_isShared_3888_ == 0 {
                    v___x_3890_ = v___x_3887_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3891_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
                    v___x_3890_ = v_reuseFailAlloc_3891_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3890_;
            }
            28 => {
                if v_isShared_3896_ == 0 {
                    v___x_3898_ = v___x_3895_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3899_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
                    v___x_3898_ = v_reuseFailAlloc_3899_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___boxed(
    mut v_as_3901_: *mut leanh::LeanObject,
    mut v_sz_3902_: *mut leanh::LeanObject,
    mut v_i_3903_: *mut leanh::LeanObject,
    mut v_b_3904_: *mut leanh::LeanObject,
    mut v___y_3905_: *mut leanh::LeanObject,
    mut v___y_3906_: *mut leanh::LeanObject,
    mut v___y_3907_: *mut leanh::LeanObject,
    mut v___y_3908_: *mut leanh::LeanObject,
    mut v___y_3909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3910_: usize = 0;
    let mut v_i_boxed_3911_: usize = 0;
    let mut v_res_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3910_ = leanh::lean_unbox_usize(v_sz_3902_);
    leanh::lean_dec(v_sz_3902_);
    v_i_boxed_3911_ = leanh::lean_unbox_usize(v_i_3903_);
    leanh::lean_dec(v_i_3903_);
    v_res_3912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v_as_3901_, v_sz_boxed_3910_, v_i_boxed_3911_, v_b_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
    leanh::lean_dec(v___y_3908_);
    leanh::lean_dec_ref(v___y_3907_);
    leanh::lean_dec(v___y_3906_);
    leanh::lean_dec_ref(v___y_3905_);
    leanh::lean_dec_ref(v_as_3901_);
    return v_res_3912_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(
    mut v_a_3913_: *mut leanh::LeanObject,
    mut v_a_3914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3913_) == 0 {
                    v___x_3915_ = l_List_reverse___redArg(v_a_3914_);
                    return v___x_3915_;
                } else {
                    v_head_3916_ = leanh::lean_ctor_get(v_a_3913_, 0);
                    v_tail_3917_ = leanh::lean_ctor_get(v_a_3913_, 1);
                    v_isSharedCheck_3926_ = (!leanh::lean_is_exclusive(v_a_3913_)) as u8;
                    if v_isSharedCheck_3926_ == 0 {
                        v___x_3919_ = v_a_3913_;
                        v_isShared_3920_ = v_isSharedCheck_3926_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3917_);
                        leanh::lean_inc(v_head_3916_);
                        leanh::lean_dec(v_a_3913_);
                        v___x_3919_ = leanh::lean_box(0);
                        v_isShared_3920_ = v_isSharedCheck_3926_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3921_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3921_, 0, v_head_3916_);
                if v_isShared_3920_ == 0 {
                    leanh::lean_ctor_set(v___x_3919_, 1, v_a_3914_);
                    leanh::lean_ctor_set(v___x_3919_, 0, v___x_3921_);
                    v___x_3923_ = v___x_3919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_a_3914_);
                    v___x_3923_ = v_reuseFailAlloc_3925_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3913_ = v_tail_3917_;
                v_a_3914_ = v___x_3923_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__2___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3928_ = l_Lean_Meta_rwMatcher___lam__2___closed__0;
    v___x_3929_ = l_Lean_stringToMessageData(v___x_3928_);
    return v___x_3929_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__2___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3931_ = l_Lean_Meta_rwMatcher___lam__2___closed__2;
    v___x_3932_ = l_Lean_stringToMessageData(v___x_3931_);
    return v___x_3932_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__2___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3934_ = l_Lean_Meta_rwMatcher___lam__2___closed__4;
    v___x_3935_ = l_Lean_stringToMessageData(v___x_3934_);
    return v___x_3935_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__2___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3937_ = l_Lean_Meta_rwMatcher___lam__2___closed__6;
    v___x_3938_ = l_Lean_stringToMessageData(v___x_3937_);
    return v___x_3938_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__2___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3940_ = l_Lean_Meta_rwMatcher___lam__2___closed__8;
    v___x_3941_ = l_Lean_stringToMessageData(v___x_3940_);
    return v___x_3941_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__2___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3945_ = l_Lean_Meta_rwMatcher___lam__2___closed__11;
    v___x_3946_ = l_Lean_stringToMessageData(v___x_3945_);
    return v___x_3946_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__2___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3948_ = l_Lean_Meta_rwMatcher___lam__2___closed__13;
    v___x_3949_ = l_Lean_stringToMessageData(v___x_3948_);
    return v___x_3949_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__2___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3951_ = l_Lean_Meta_rwMatcher___lam__2___closed__15;
    v___x_3952_ = l_Lean_stringToMessageData(v___x_3951_);
    return v___x_3952_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__2___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3960_ = l_Lean_Meta_rwMatcher___lam__2___closed__21;
    v___x_3961_ = l_Lean_stringToMessageData(v___x_3960_);
    return v___x_3961_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___lam__2___closed__24() -> *mut leanh::LeanObject {
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3963_ = l_Lean_Meta_rwMatcher___lam__2___closed__23;
    v___x_3964_ = l_Lean_stringToMessageData(v___x_3963_);
    return v___x_3964_;
}
pub unsafe fn l_Lean_Meta_rwMatcher___lam__2(
    mut v___x_3965_: u8,
    mut v___x_3966_: *mut leanh::LeanObject,
    mut v_fst_3967_: *mut leanh::LeanObject,
    mut v___x_3968_: *mut leanh::LeanObject,
    mut v___x_3969_: u8,
    mut v_e_3970_: *mut leanh::LeanObject,
    mut v_snd_3971_: *mut leanh::LeanObject,
    mut v_____r_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: *mut leanh::LeanObject,
    mut v___y_3974_: *mut leanh::LeanObject,
    mut v___y_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3991_: u8 = 0;
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut v___y_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4005_: u8 = 0;
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4019_: u8 = 0;
    let mut v___y_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: u8 = 0;
    let mut v___x_4033_: u8 = 0;
    let mut v___y_4035_: u8 = 0;
    let mut v___y_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: u8 = 0;
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4059_: u8 = 0;
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v___y_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4066_: u8 = 0;
    let mut v___y_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4076_: u8 = 0;
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4080_: u8 = 0;
    let mut v_sz_4081_: usize = 0;
    let mut v___x_4082_: usize = 0;
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4085_: u8 = 0;
    let mut v___y_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4092_: usize = 0;
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: u8 = 0;
    let mut v___x_4099_: usize = 0;
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: usize = 0;
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4106_: u8 = 0;
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4110_: u8 = 0;
    let mut v___y_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4113_: u8 = 0;
    let mut v___y_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4136_: u8 = 0;
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4140_: u8 = 0;
    let mut v_fst_4142_: u8 = 0;
    let mut v_fst_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: u8 = 0;
    let mut v_a_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4155_: u8 = 0;
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: u8 = 0;
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: u8 = 0;
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4171_: u8 = 0;
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4175_: u8 = 0;
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4017_ = l_Lean_mkAppN(v___x_3966_, v_fst_3967_);
                v_sz_4081_ = lean_array_size(v_fst_3967_);
                v___x_4082_ = 0usize;
                v___x_4083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_4081_, v___x_4082_, v_fst_3967_);
                v___x_4156_ = l_Lean_Meta_rwMatcher___lam__2___closed__18;
                v___x_4157_ = leanh::lean_unsigned_to_nat(4);
                v___x_4158_ = l_Lean_Expr_isAppOfArity(v_snd_3971_, v___x_4156_, v___x_4157_);
                if v___x_4158_ == 0 {
                    v___x_4159_ = l_Lean_Meta_rwMatcher___lam__2___closed__20;
                    v___x_4160_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4161_ = l_Lean_Expr_isAppOfArity(v_snd_3971_, v___x_4159_, v___x_4160_);
                    if v___x_4161_ == 0 {
                        leanh::lean_dec_ref(v___x_4083_);
                        leanh::lean_dec_ref(v___x_4017_);
                        leanh::lean_dec_ref(v_e_3970_);
                        v___x_4162_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__22),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_rwMatcher___lam__2___closed__22_once
                            ),
                            _init_l_Lean_Meta_rwMatcher___lam__2___closed__22,
                        );
                        v___x_4163_ = l_Lean_MessageData_ofConstName(v___x_3968_, v___x_3969_);
                        v___x_4164_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4164_, 0, v___x_4162_);
                        leanh::lean_ctor_set(v___x_4164_, 1, v___x_4163_);
                        v___x_4165_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_rwMatcher___lam__2___closed__24_once
                            ),
                            _init_l_Lean_Meta_rwMatcher___lam__2___closed__24,
                        );
                        v___x_4166_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4166_, 0, v___x_4164_);
                        leanh::lean_ctor_set(v___x_4166_, 1, v___x_4165_);
                        v___x_4167_ =
                            l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                                v___x_4166_,
                                v___y_3973_,
                                v___y_3974_,
                                v___y_3975_,
                                v___y_3976_,
                            );
                        v_a_4168_ = leanh::lean_ctor_get(v___x_4167_, 0);
                        v_isSharedCheck_4175_ =
                            (!leanh::lean_is_exclusive(v___x_4167_)) as u8;
                        if v_isSharedCheck_4175_ == 0 {
                            v___x_4170_ = v___x_4167_;
                            v_isShared_4171_ = v_isSharedCheck_4175_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4168_);
                            leanh::lean_dec(v___x_4167_);
                            v___x_4170_ = leanh::lean_box(0);
                            v_isShared_4171_ = v_isSharedCheck_4175_;
                            state = 22;
                            continue;
                        }
                    } else {
                        v___x_4176_ = l_Lean_Expr_appFn_x21(v_snd_3971_);
                        v___x_4177_ = l_Lean_Expr_appArg_x21(v___x_4176_);
                        leanh::lean_dec_ref(v___x_4176_);
                        v___x_4178_ = l_Lean_Expr_appArg_x21(v_snd_3971_);
                        v_fst_4142_ = v___x_3969_;
                        v_fst_4143_ = v___x_4177_;
                        v_snd_4144_ = v___x_4178_;
                        state = 19;
                        continue;
                    }
                } else {
                    v___x_4179_ = l_Lean_Expr_appFn_x21(v_snd_3971_);
                    v___x_4180_ = l_Lean_Expr_appFn_x21(v___x_4179_);
                    leanh::lean_dec_ref(v___x_4179_);
                    v___x_4181_ = l_Lean_Expr_appArg_x21(v___x_4180_);
                    leanh::lean_dec_ref(v___x_4180_);
                    v___x_4182_ = l_Lean_Expr_appArg_x21(v_snd_3971_);
                    v_fst_4142_ = v___x_3965_;
                    v_fst_4143_ = v___x_4181_;
                    v_snd_4144_ = v___x_4182_;
                    state = 19;
                    continue;
                }
            }
            1 => {
                v___x_3981_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3981_, 0, v_proof_3980_);
                v___x_3982_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3982_, 0, v___y_3979_);
                leanh::lean_ctor_set(v___x_3982_, 1, v___x_3981_);
                leanh::lean_ctor_set_uint8(
                    v___x_3982_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3965_,
                );
                v___x_3983_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3983_, 0, v___x_3982_);
                return v___x_3983_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_3986_) == 0 {
                    v_a_3987_ = leanh::lean_ctor_get(v___y_3986_, 0);
                    leanh::lean_inc(v_a_3987_);
                    leanh::lean_dec_ref_known(v___y_3986_, 1);
                    v___y_3979_ = v___y_3985_;
                    v_proof_3980_ = v_a_3987_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_3985_);
                    v_a_3988_ = leanh::lean_ctor_get(v___y_3986_, 0);
                    v_isSharedCheck_3995_ = (!leanh::lean_is_exclusive(v___y_3986_)) as u8;
                    if v_isSharedCheck_3995_ == 0 {
                        v___x_3990_ = v___y_3986_;
                        v_isShared_3991_ = v_isSharedCheck_3995_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3988_);
                        leanh::lean_dec(v___y_3986_);
                        v___x_3990_ = leanh::lean_box(0);
                        v_isShared_3991_ = v_isSharedCheck_3995_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3991_ == 0 {
                    v___x_3993_ = v___x_3990_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3994_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
                    v___x_3993_ = v_reuseFailAlloc_3994_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3993_;
            }
            5 => {
                if v___y_4005_ == 0 {
                    leanh::lean_dec_ref(v___y_3997_);
                    v___x_4006_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__1_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__1,
                    );
                    v___x_4007_ = l_Lean_MessageData_ofExpr(v___y_3999_);
                    v___x_4008_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4008_, 0, v___x_4006_);
                    leanh::lean_ctor_set(v___x_4008_, 1, v___x_4007_);
                    v___x_4009_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__3_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__3,
                    );
                    v___x_4010_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4010_, 0, v___x_4008_);
                    leanh::lean_ctor_set(v___x_4010_, 1, v___x_4009_);
                    v___x_4011_ = l_Lean_Exception_toMessageData(v___y_4001_);
                    v___x_4012_ = l_Lean_indentD(v___x_4011_);
                    v___x_4013_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4013_, 0, v___x_4010_);
                    leanh::lean_ctor_set(v___x_4013_, 1, v___x_4012_);
                    v___x_4014_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__5_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__5,
                    );
                    v___x_4015_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4015_, 0, v___x_4013_);
                    leanh::lean_ctor_set(v___x_4015_, 1, v___x_4014_);
                    v___x_4016_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                        v___x_4015_,
                        v___y_4003_,
                        v___y_4004_,
                        v___y_3998_,
                        v___y_4000_,
                    );
                    v___y_3985_ = v___y_4002_;
                    v___y_3986_ = v___x_4016_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4001_);
                    leanh::lean_dec_ref(v___y_3999_);
                    v___y_3985_ = v___y_4002_;
                    v___y_3986_ = v___y_3997_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_4025_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(
                    v___y_4020_,
                    v___y_4022_,
                );
                v_a_4026_ = leanh::lean_ctor_get(v___x_4025_, 0);
                leanh::lean_inc(v_a_4026_);
                leanh::lean_dec_ref(v___x_4025_);
                v___x_4027_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(
                    v___x_4017_,
                    v___y_4022_,
                );
                if v___y_4019_ == 0 {
                    v_a_4028_ = leanh::lean_ctor_get(v___x_4027_, 0);
                    leanh::lean_inc(v_a_4028_);
                    leanh::lean_dec_ref(v___x_4027_);
                    v___y_3979_ = v_a_4026_;
                    v_proof_3980_ = v_a_4028_;
                    state = 1;
                    continue;
                } else {
                    v_a_4029_ = leanh::lean_ctor_get(v___x_4027_, 0);
                    leanh::lean_inc_n(v_a_4029_, 2);
                    leanh::lean_dec_ref(v___x_4027_);
                    v___x_4030_ = l_Lean_Meta_mkEqOfHEq(
                        v_a_4029_,
                        v___x_3965_,
                        v___y_4021_,
                        v___y_4022_,
                        v___y_4023_,
                        v___y_4024_,
                    );
                    if leanh::lean_obj_tag(v___x_4030_) == 0 {
                        leanh::lean_dec(v_a_4029_);
                        v___y_3985_ = v_a_4026_;
                        v___y_3986_ = v___x_4030_;
                        state = 2;
                        continue;
                    } else {
                        v_a_4031_ = leanh::lean_ctor_get(v___x_4030_, 0);
                        leanh::lean_inc(v_a_4031_);
                        v___x_4032_ = l_Lean_Exception_isInterrupt(v_a_4031_);
                        if v___x_4032_ == 0 {
                            leanh::lean_inc(v_a_4031_);
                            v___x_4033_ = l_Lean_Exception_isRuntime(v_a_4031_);
                            v___y_3997_ = v___x_4030_;
                            v___y_3998_ = v___y_4023_;
                            v___y_3999_ = v_a_4029_;
                            v___y_4000_ = v___y_4024_;
                            v___y_4001_ = v_a_4031_;
                            v___y_4002_ = v_a_4026_;
                            v___y_4003_ = v___y_4021_;
                            v___y_4004_ = v___y_4022_;
                            v___y_4005_ = v___x_4033_;
                            state = 5;
                            continue;
                        } else {
                            v___y_3997_ = v___x_4030_;
                            v___y_3998_ = v___y_4023_;
                            v___y_3999_ = v_a_4029_;
                            v___y_4000_ = v___y_4024_;
                            v___y_4001_ = v_a_4031_;
                            v___y_4002_ = v_a_4026_;
                            v___y_4003_ = v___y_4021_;
                            v___y_4004_ = v___y_4022_;
                            v___y_4005_ = v___x_4032_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_4042_ = lean_array_get_size(v_a_4041_);
                v___x_4043_ = leanh::lean_unsigned_to_nat(0);
                v___x_4044_ = lean_nat_dec_eq(v___x_4042_, v___x_4043_);
                if v___x_4044_ == 0 {
                    leanh::lean_dec_ref(v___y_4040_);
                    leanh::lean_dec_ref(v___x_4017_);
                    v___x_4045_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__7_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__7,
                    );
                    v___x_4046_ = l_Lean_MessageData_ofConstName(v___x_3968_, v___x_3969_);
                    v___x_4047_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4047_, 0, v___x_4045_);
                    leanh::lean_ctor_set(v___x_4047_, 1, v___x_4046_);
                    v___x_4048_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__9),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__9_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__9,
                    );
                    v___x_4049_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4049_, 0, v___x_4047_);
                    leanh::lean_ctor_set(v___x_4049_, 1, v___x_4048_);
                    v___x_4050_ = lean_array_to_list(v_a_4041_);
                    v___x_4051_ = leanh::lean_box(0);
                    v___x_4052_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(
                        v___x_4050_,
                        v___x_4051_,
                    );
                    v___x_4053_ = l_Lean_MessageData_ofList(v___x_4052_);
                    v___x_4054_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4054_, 0, v___x_4049_);
                    leanh::lean_ctor_set(v___x_4054_, 1, v___x_4053_);
                    v___x_4055_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                        v___x_4054_,
                        v___y_4037_,
                        v___y_4038_,
                        v___y_4036_,
                        v___y_4039_,
                    );
                    v_a_4056_ = leanh::lean_ctor_get(v___x_4055_, 0);
                    v_isSharedCheck_4063_ = (!leanh::lean_is_exclusive(v___x_4055_)) as u8;
                    if v_isSharedCheck_4063_ == 0 {
                        v___x_4058_ = v___x_4055_;
                        v_isShared_4059_ = v_isSharedCheck_4063_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4056_);
                        leanh::lean_dec(v___x_4055_);
                        v___x_4058_ = leanh::lean_box(0);
                        v_isShared_4059_ = v_isSharedCheck_4063_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_4041_);
                    leanh::lean_dec(v___x_3968_);
                    v___y_4019_ = v___y_4035_;
                    v___y_4020_ = v___y_4040_;
                    v___y_4021_ = v___y_4037_;
                    v___y_4022_ = v___y_4038_;
                    v___y_4023_ = v___y_4036_;
                    v___y_4024_ = v___y_4039_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                if v_isShared_4059_ == 0 {
                    v___x_4061_ = v___x_4058_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
                    v___x_4061_ = v_reuseFailAlloc_4062_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4061_;
            }
            10 => {
                if leanh::lean_obj_tag(v___y_4071_) == 0 {
                    v_a_4072_ = leanh::lean_ctor_get(v___y_4071_, 0);
                    leanh::lean_inc(v_a_4072_);
                    leanh::lean_dec_ref_known(v___y_4071_, 1);
                    v___y_4035_ = v___y_4066_;
                    v___y_4036_ = v___y_4065_;
                    v___y_4037_ = v___y_4067_;
                    v___y_4038_ = v___y_4068_;
                    v___y_4039_ = v___y_4069_;
                    v___y_4040_ = v___y_4070_;
                    v_a_4041_ = v_a_4072_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4070_);
                    leanh::lean_dec_ref(v___x_4017_);
                    leanh::lean_dec(v___x_3968_);
                    v_a_4073_ = leanh::lean_ctor_get(v___y_4071_, 0);
                    v_isSharedCheck_4080_ = (!leanh::lean_is_exclusive(v___y_4071_)) as u8;
                    if v_isSharedCheck_4080_ == 0 {
                        v___x_4075_ = v___y_4071_;
                        v_isShared_4076_ = v_isSharedCheck_4080_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4073_);
                        leanh::lean_dec(v___y_4071_);
                        v___x_4075_ = leanh::lean_box(0);
                        v_isShared_4076_ = v_isSharedCheck_4080_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_4076_ == 0 {
                    v___x_4078_ = v___x_4075_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4079_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
                    v___x_4078_ = v_reuseFailAlloc_4079_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4078_;
            }
            13 => {
                v___x_4091_ = leanh::lean_box(0);
                v_sz_4092_ = lean_array_size(v___x_4083_);
                v___x_4093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_4083_, v_sz_4092_, v___x_4082_, v___x_4091_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
                if leanh::lean_obj_tag(v___x_4093_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4093_, 1);
                    v___x_4094_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4095_ = lean_array_get_size(v___x_4083_);
                    v___x_4096_ = l_Lean_Meta_rwMatcher___lam__2___closed__10;
                    v___x_4097_ = lean_nat_dec_lt(v___x_4094_, v___x_4095_);
                    if v___x_4097_ == 0 {
                        leanh::lean_dec_ref(v___x_4083_);
                        v___y_4035_ = v___y_4085_;
                        v___y_4036_ = v___y_4089_;
                        v___y_4037_ = v___y_4087_;
                        v___y_4038_ = v___y_4088_;
                        v___y_4039_ = v___y_4090_;
                        v___y_4040_ = v___y_4086_;
                        v_a_4041_ = v___x_4096_;
                        state = 7;
                        continue;
                    } else {
                        v___x_4098_ = lean_nat_dec_le(v___x_4095_, v___x_4095_);
                        if v___x_4098_ == 0 {
                            if v___x_4097_ == 0 {
                                leanh::lean_dec_ref(v___x_4083_);
                                v___y_4035_ = v___y_4085_;
                                v___y_4036_ = v___y_4089_;
                                v___y_4037_ = v___y_4087_;
                                v___y_4038_ = v___y_4088_;
                                v___y_4039_ = v___y_4090_;
                                v___y_4040_ = v___y_4086_;
                                v_a_4041_ = v___x_4096_;
                                state = 7;
                                continue;
                            } else {
                                v___x_4099_ = lean_usize_of_nat(v___x_4095_);
                                v___x_4100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_3969_, v___x_4083_, v___x_4082_, v___x_4099_, v___x_4096_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
                                leanh::lean_dec_ref(v___x_4083_);
                                v___y_4065_ = v___y_4089_;
                                v___y_4066_ = v___y_4085_;
                                v___y_4067_ = v___y_4087_;
                                v___y_4068_ = v___y_4088_;
                                v___y_4069_ = v___y_4090_;
                                v___y_4070_ = v___y_4086_;
                                v___y_4071_ = v___x_4100_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v___x_4101_ = lean_usize_of_nat(v___x_4095_);
                            v___x_4102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_3969_, v___x_4083_, v___x_4082_, v___x_4101_, v___x_4096_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
                            leanh::lean_dec_ref(v___x_4083_);
                            v___y_4065_ = v___y_4089_;
                            v___y_4066_ = v___y_4085_;
                            v___y_4067_ = v___y_4087_;
                            v___y_4068_ = v___y_4088_;
                            v___y_4069_ = v___y_4090_;
                            v___y_4070_ = v___y_4086_;
                            v___y_4071_ = v___x_4102_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4086_);
                    leanh::lean_dec_ref(v___x_4083_);
                    leanh::lean_dec_ref(v___x_4017_);
                    leanh::lean_dec(v___x_3968_);
                    v_a_4103_ = leanh::lean_ctor_get(v___x_4093_, 0);
                    v_isSharedCheck_4110_ = (!leanh::lean_is_exclusive(v___x_4093_)) as u8;
                    if v_isSharedCheck_4110_ == 0 {
                        v___x_4105_ = v___x_4093_;
                        v_isShared_4106_ = v_isSharedCheck_4110_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4103_);
                        leanh::lean_dec(v___x_4093_);
                        v___x_4105_ = leanh::lean_box(0);
                        v_isShared_4106_ = v_isSharedCheck_4110_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_4106_ == 0 {
                    v___x_4108_ = v___x_4105_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4109_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
                    v___x_4108_ = v_reuseFailAlloc_4109_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4108_;
            }
            16 => {
                leanh::lean_dec_ref(v___y_4115_);
                v___x_4119_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__12_once),
                    _init_l_Lean_Meta_rwMatcher___lam__2___closed__12,
                );
                v___x_4120_ = l_Lean_MessageData_ofExpr(v___y_4116_);
                v___x_4121_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4121_, 0, v___x_4119_);
                leanh::lean_ctor_set(v___x_4121_, 1, v___x_4120_);
                v___x_4122_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__14_once),
                    _init_l_Lean_Meta_rwMatcher___lam__2___closed__14,
                );
                v___x_4123_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4123_, 0, v___x_4121_);
                leanh::lean_ctor_set(v___x_4123_, 1, v___x_4122_);
                v___x_4124_ = l_Lean_MessageData_ofConstName(v___x_3968_, v___x_3969_);
                v___x_4125_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4125_, 0, v___x_4123_);
                leanh::lean_ctor_set(v___x_4125_, 1, v___x_4124_);
                v___x_4126_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__16),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__16_once),
                    _init_l_Lean_Meta_rwMatcher___lam__2___closed__16,
                );
                v___x_4127_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4127_, 0, v___x_4125_);
                leanh::lean_ctor_set(v___x_4127_, 1, v___x_4126_);
                v___x_4128_ = l_Lean_MessageData_ofExpr(v_e_3970_);
                v___x_4129_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4129_, 0, v___x_4127_);
                leanh::lean_ctor_set(v___x_4129_, 1, v___x_4128_);
                v___x_4130_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
                v___x_4131_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4131_, 0, v___x_4129_);
                leanh::lean_ctor_set(v___x_4131_, 1, v___x_4130_);
                v___x_4132_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                    v___x_4131_,
                    v___y_4114_,
                    v___y_4118_,
                    v___y_4117_,
                    v___y_4112_,
                );
                v_a_4133_ = leanh::lean_ctor_get(v___x_4132_, 0);
                v_isSharedCheck_4140_ = (!leanh::lean_is_exclusive(v___x_4132_)) as u8;
                if v_isSharedCheck_4140_ == 0 {
                    v___x_4135_ = v___x_4132_;
                    v_isShared_4136_ = v_isSharedCheck_4140_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4133_);
                    leanh::lean_dec(v___x_4132_);
                    v___x_4135_ = leanh::lean_box(0);
                    v_isShared_4136_ = v_isSharedCheck_4140_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_4136_ == 0 {
                    v___x_4138_ = v___x_4135_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
                    v___x_4138_ = v_reuseFailAlloc_4139_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4138_;
            }
            19 => {
                leanh::lean_inc_ref(v_fst_4143_);
                leanh::lean_inc_ref(v_e_3970_);
                v___x_4145_ = l_Lean_Meta_isExprDefEq(
                    v_e_3970_,
                    v_fst_4143_,
                    v___y_3973_,
                    v___y_3974_,
                    v___y_3975_,
                    v___y_3976_,
                );
                if leanh::lean_obj_tag(v___x_4145_) == 0 {
                    v_a_4146_ = leanh::lean_ctor_get(v___x_4145_, 0);
                    leanh::lean_inc(v_a_4146_);
                    leanh::lean_dec_ref_known(v___x_4145_, 1);
                    v___x_4147_ = (leanh::lean_unbox(v_a_4146_) as u8);
                    leanh::lean_dec(v_a_4146_);
                    if v___x_4147_ == 0 {
                        leanh::lean_dec_ref(v___x_4083_);
                        leanh::lean_dec_ref(v___x_4017_);
                        v___y_4112_ = v___y_3976_;
                        v___y_4113_ = v_fst_4142_;
                        v___y_4114_ = v___y_3973_;
                        v___y_4115_ = v_snd_4144_;
                        v___y_4116_ = v_fst_4143_;
                        v___y_4117_ = v___y_3975_;
                        v___y_4118_ = v___y_3974_;
                        state = 16;
                        continue;
                    } else {
                        if v___x_3969_ == 0 {
                            leanh::lean_dec_ref(v_fst_4143_);
                            leanh::lean_dec_ref(v_e_3970_);
                            v___y_4085_ = v_fst_4142_;
                            v___y_4086_ = v_snd_4144_;
                            v___y_4087_ = v___y_3973_;
                            v___y_4088_ = v___y_3974_;
                            v___y_4089_ = v___y_3975_;
                            v___y_4090_ = v___y_3976_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_4083_);
                            leanh::lean_dec_ref(v___x_4017_);
                            v___y_4112_ = v___y_3976_;
                            v___y_4113_ = v_fst_4142_;
                            v___y_4114_ = v___y_3973_;
                            v___y_4115_ = v_snd_4144_;
                            v___y_4116_ = v_fst_4143_;
                            v___y_4117_ = v___y_3975_;
                            v___y_4118_ = v___y_3974_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_snd_4144_);
                    leanh::lean_dec_ref(v_fst_4143_);
                    leanh::lean_dec_ref(v___x_4083_);
                    leanh::lean_dec_ref(v___x_4017_);
                    leanh::lean_dec_ref(v_e_3970_);
                    leanh::lean_dec(v___x_3968_);
                    v_a_4148_ = leanh::lean_ctor_get(v___x_4145_, 0);
                    v_isSharedCheck_4155_ = (!leanh::lean_is_exclusive(v___x_4145_)) as u8;
                    if v_isSharedCheck_4155_ == 0 {
                        v___x_4150_ = v___x_4145_;
                        v_isShared_4151_ = v_isSharedCheck_4155_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4148_);
                        leanh::lean_dec(v___x_4145_);
                        v___x_4150_ = leanh::lean_box(0);
                        v_isShared_4151_ = v_isSharedCheck_4155_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_4151_ == 0 {
                    v___x_4153_ = v___x_4150_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4154_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
                    v___x_4153_ = v_reuseFailAlloc_4154_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4153_;
            }
            22 => {
                if v_isShared_4171_ == 0 {
                    v___x_4173_ = v___x_4170_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4174_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
                    v___x_4173_ = v_reuseFailAlloc_4174_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4173_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_rwMatcher___lam__2___boxed(
    mut v___x_4183_: *mut leanh::LeanObject,
    mut v___x_4184_: *mut leanh::LeanObject,
    mut v_fst_4185_: *mut leanh::LeanObject,
    mut v___x_4186_: *mut leanh::LeanObject,
    mut v___x_4187_: *mut leanh::LeanObject,
    mut v_e_4188_: *mut leanh::LeanObject,
    mut v_snd_4189_: *mut leanh::LeanObject,
    mut v_____r_4190_: *mut leanh::LeanObject,
    mut v___y_4191_: *mut leanh::LeanObject,
    mut v___y_4192_: *mut leanh::LeanObject,
    mut v___y_4193_: *mut leanh::LeanObject,
    mut v___y_4194_: *mut leanh::LeanObject,
    mut v___y_4195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_108698__boxed_4196_: u8 = 0;
    let mut v___x_108702__boxed_4197_: u8 = 0;
    let mut v_res_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_108698__boxed_4196_ = (leanh::lean_unbox(v___x_4183_) as u8);
    v___x_108702__boxed_4197_ = (leanh::lean_unbox(v___x_4187_) as u8);
    v_res_4198_ = l_Lean_Meta_rwMatcher___lam__2(
        v___x_108698__boxed_4196_,
        v___x_4184_,
        v_fst_4185_,
        v___x_4186_,
        v___x_108702__boxed_4197_,
        v_e_4188_,
        v_snd_4189_,
        v_____r_4190_,
        v___y_4191_,
        v___y_4192_,
        v___y_4193_,
        v___y_4194_,
    );
    leanh::lean_dec(v___y_4194_);
    leanh::lean_dec_ref(v___y_4193_);
    leanh::lean_dec(v___y_4192_);
    leanh::lean_dec_ref(v___y_4191_);
    leanh::lean_dec_ref(v_snd_4189_);
    return v_res_4198_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(
    mut v___x_4199_: u8,
    mut v_as_4200_: *mut leanh::LeanObject,
    mut v_i_4201_: usize,
    mut v_stop_4202_: usize,
    mut v_b_4203_: *mut leanh::LeanObject,
    mut v___y_4204_: *mut leanh::LeanObject,
    mut v___y_4205_: *mut leanh::LeanObject,
    mut v___y_4206_: *mut leanh::LeanObject,
    mut v___y_4207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: usize = 0;
    let mut v___x_4212_: usize = 0;
    let mut v___x_4214_: u8 = 0;
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4217_: u8 = 0;
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: u8 = 0;
    let mut v_a_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: u8 = 0;
    let mut v_a_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4227_: u8 = 0;
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4231_: u8 = 0;
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4214_ = lean_usize_dec_eq(v_i_4201_, v_stop_4202_);
                if v___x_4214_ == 0 {
                    v___x_4215_ = lean_array_uget_borrowed(v_as_4200_, v_i_4201_);
                    v___x_4219_ =
                        l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(
                            v___x_4215_,
                            v___y_4205_,
                        );
                    if leanh::lean_obj_tag(v___x_4219_) == 0 {
                        v_a_4220_ = leanh::lean_ctor_get(v___x_4219_, 0);
                        leanh::lean_inc(v_a_4220_);
                        leanh::lean_dec_ref_known(v___x_4219_, 1);
                        v___x_4221_ = (leanh::lean_unbox(v_a_4220_) as u8);
                        leanh::lean_dec(v_a_4220_);
                        if v___x_4221_ == 0 {
                            v_a_4217_ = v___x_4199_;
                            state = 2;
                            continue;
                        } else {
                            v_a_4210_ = v_b_4203_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_4219_) == 0 {
                            v_a_4222_ = leanh::lean_ctor_get(v___x_4219_, 0);
                            leanh::lean_inc(v_a_4222_);
                            leanh::lean_dec_ref_known(v___x_4219_, 1);
                            v___x_4223_ = (leanh::lean_unbox(v_a_4222_) as u8);
                            leanh::lean_dec(v_a_4222_);
                            v_a_4217_ = v___x_4223_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_4203_);
                            v_a_4224_ = leanh::lean_ctor_get(v___x_4219_, 0);
                            v_isSharedCheck_4231_ =
                                (!leanh::lean_is_exclusive(v___x_4219_)) as u8;
                            if v_isSharedCheck_4231_ == 0 {
                                v___x_4226_ = v___x_4219_;
                                v_isShared_4227_ = v_isSharedCheck_4231_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4224_);
                                leanh::lean_dec(v___x_4219_);
                                v___x_4226_ = leanh::lean_box(0);
                                v_isShared_4227_ = v_isSharedCheck_4231_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_4232_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4232_, 0, v_b_4203_);
                    return v___x_4232_;
                }
            }
            1 => {
                v___x_4211_ = 1usize;
                v___x_4212_ = lean_usize_add(v_i_4201_, v___x_4211_);
                v_i_4201_ = v___x_4212_;
                v_b_4203_ = v_a_4210_;
                state = 0;
                continue;
            }
            2 => {
                if v_a_4217_ == 0 {
                    v_a_4210_ = v_b_4203_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v___x_4215_);
                    v___x_4218_ = lean_array_push(v_b_4203_, v___x_4215_);
                    v_a_4210_ = v___x_4218_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_4227_ == 0 {
                    v___x_4229_ = v___x_4226_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4230_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
                    v___x_4229_ = v_reuseFailAlloc_4230_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13___boxed(
    mut v___x_4233_: *mut leanh::LeanObject,
    mut v_as_4234_: *mut leanh::LeanObject,
    mut v_i_4235_: *mut leanh::LeanObject,
    mut v_stop_4236_: *mut leanh::LeanObject,
    mut v_b_4237_: *mut leanh::LeanObject,
    mut v___y_4238_: *mut leanh::LeanObject,
    mut v___y_4239_: *mut leanh::LeanObject,
    mut v___y_4240_: *mut leanh::LeanObject,
    mut v___y_4241_: *mut leanh::LeanObject,
    mut v___y_4242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_109183__boxed_4243_: u8 = 0;
    let mut v_i_boxed_4244_: usize = 0;
    let mut v_stop_boxed_4245_: usize = 0;
    let mut v_res_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_109183__boxed_4243_ = (leanh::lean_unbox(v___x_4233_) as u8);
    v_i_boxed_4244_ = leanh::lean_unbox_usize(v_i_4235_);
    leanh::lean_dec(v_i_4235_);
    v_stop_boxed_4245_ = leanh::lean_unbox_usize(v_stop_4236_);
    leanh::lean_dec(v_stop_4236_);
    v_res_4246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_109183__boxed_4243_, v_as_4234_, v_i_boxed_4244_, v_stop_boxed_4245_, v_b_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
    leanh::lean_dec(v___y_4241_);
    leanh::lean_dec_ref(v___y_4240_);
    leanh::lean_dec(v___y_4239_);
    leanh::lean_dec_ref(v___y_4238_);
    leanh::lean_dec_ref(v_as_4234_);
    return v_res_4246_;
}
pub unsafe fn l_Lean_Meta_rwMatcher___lam__3(
    mut v___x_4247_: u8,
    mut v___x_4248_: *mut leanh::LeanObject,
    mut v_fst_4249_: *mut leanh::LeanObject,
    mut v___x_4250_: *mut leanh::LeanObject,
    mut v___x_4251_: u8,
    mut v_e_4252_: *mut leanh::LeanObject,
    mut v___y_4253_: u8,
    mut v_snd_4254_: *mut leanh::LeanObject,
    mut v_____r_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
    mut v___y_4259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4274_: u8 = 0;
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4278_: u8 = 0;
    let mut v___y_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4288_: u8 = 0;
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4303_: u8 = 0;
    let mut v___y_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: u8 = 0;
    let mut v___x_4316_: u8 = 0;
    let mut v___y_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4322_: u8 = 0;
    let mut v___y_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: u8 = 0;
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v___y_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4352_: u8 = 0;
    let mut v___y_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4359_: u8 = 0;
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4363_: u8 = 0;
    let mut v_sz_4364_: usize = 0;
    let mut v___x_4365_: usize = 0;
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4369_: u8 = 0;
    let mut v___y_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4375_: usize = 0;
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4381_: u8 = 0;
    let mut v___x_4382_: usize = 0;
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: usize = 0;
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4389_: u8 = 0;
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4393_: u8 = 0;
    let mut v_fst_4395_: u8 = 0;
    let mut v_fst_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: u8 = 0;
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut v_a_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4426_: u8 = 0;
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4430_: u8 = 0;
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: u8 = 0;
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: u8 = 0;
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4450_: u8 = 0;
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4300_ = l_Lean_mkAppN(v___x_4248_, v_fst_4249_);
                v_sz_4364_ = lean_array_size(v_fst_4249_);
                v___x_4365_ = 0usize;
                v___x_4366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_4364_, v___x_4365_, v_fst_4249_);
                v___x_4431_ = l_Lean_Meta_rwMatcher___lam__2___closed__18;
                v___x_4432_ = leanh::lean_unsigned_to_nat(4);
                v___x_4433_ = l_Lean_Expr_isAppOfArity(v_snd_4254_, v___x_4431_, v___x_4432_);
                if v___x_4433_ == 0 {
                    v___x_4434_ = l_Lean_Meta_rwMatcher___lam__2___closed__20;
                    v___x_4435_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4436_ = l_Lean_Expr_isAppOfArity(v_snd_4254_, v___x_4434_, v___x_4435_);
                    if v___x_4436_ == 0 {
                        leanh::lean_dec_ref(v___x_4366_);
                        leanh::lean_dec_ref(v___x_4300_);
                        leanh::lean_dec_ref(v_e_4252_);
                        v___x_4437_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__22),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_rwMatcher___lam__2___closed__22_once
                            ),
                            _init_l_Lean_Meta_rwMatcher___lam__2___closed__22,
                        );
                        v___x_4438_ = l_Lean_MessageData_ofConstName(v___x_4250_, v___x_4436_);
                        v___x_4439_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4439_, 0, v___x_4437_);
                        leanh::lean_ctor_set(v___x_4439_, 1, v___x_4438_);
                        v___x_4440_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_rwMatcher___lam__2___closed__24_once
                            ),
                            _init_l_Lean_Meta_rwMatcher___lam__2___closed__24,
                        );
                        v___x_4441_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4441_, 0, v___x_4439_);
                        leanh::lean_ctor_set(v___x_4441_, 1, v___x_4440_);
                        v___x_4442_ =
                            l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                                v___x_4441_,
                                v___y_4256_,
                                v___y_4257_,
                                v___y_4258_,
                                v___y_4259_,
                            );
                        v_a_4443_ = leanh::lean_ctor_get(v___x_4442_, 0);
                        v_isSharedCheck_4450_ =
                            (!leanh::lean_is_exclusive(v___x_4442_)) as u8;
                        if v_isSharedCheck_4450_ == 0 {
                            v___x_4445_ = v___x_4442_;
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4443_);
                            leanh::lean_dec(v___x_4442_);
                            v___x_4445_ = leanh::lean_box(0);
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 21;
                            continue;
                        }
                    } else {
                        v___x_4451_ = l_Lean_Expr_appFn_x21(v_snd_4254_);
                        v___x_4452_ = l_Lean_Expr_appArg_x21(v___x_4451_);
                        leanh::lean_dec_ref(v___x_4451_);
                        v___x_4453_ = l_Lean_Expr_appArg_x21(v_snd_4254_);
                        v_fst_4395_ = v___x_4433_;
                        v_fst_4396_ = v___x_4452_;
                        v_snd_4397_ = v___x_4453_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___x_4454_ = l_Lean_Expr_appFn_x21(v_snd_4254_);
                    v___x_4455_ = l_Lean_Expr_appFn_x21(v___x_4454_);
                    leanh::lean_dec_ref(v___x_4454_);
                    v___x_4456_ = l_Lean_Expr_appArg_x21(v___x_4455_);
                    leanh::lean_dec_ref(v___x_4455_);
                    v___x_4457_ = l_Lean_Expr_appArg_x21(v_snd_4254_);
                    v_fst_4395_ = v___x_4247_;
                    v_fst_4396_ = v___x_4456_;
                    v_snd_4397_ = v___x_4457_;
                    state = 16;
                    continue;
                }
            }
            1 => {
                v___x_4264_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4264_, 0, v_proof_4263_);
                v___x_4265_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_4265_, 0, v___y_4262_);
                leanh::lean_ctor_set(v___x_4265_, 1, v___x_4264_);
                leanh::lean_ctor_set_uint8(
                    v___x_4265_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4247_,
                );
                v___x_4266_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4266_, 0, v___x_4265_);
                return v___x_4266_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_4269_) == 0 {
                    v_a_4270_ = leanh::lean_ctor_get(v___y_4269_, 0);
                    leanh::lean_inc(v_a_4270_);
                    leanh::lean_dec_ref_known(v___y_4269_, 1);
                    v___y_4262_ = v___y_4268_;
                    v_proof_4263_ = v_a_4270_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4268_);
                    v_a_4271_ = leanh::lean_ctor_get(v___y_4269_, 0);
                    v_isSharedCheck_4278_ = (!leanh::lean_is_exclusive(v___y_4269_)) as u8;
                    if v_isSharedCheck_4278_ == 0 {
                        v___x_4273_ = v___y_4269_;
                        v_isShared_4274_ = v_isSharedCheck_4278_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4271_);
                        leanh::lean_dec(v___y_4269_);
                        v___x_4273_ = leanh::lean_box(0);
                        v_isShared_4274_ = v_isSharedCheck_4278_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4274_ == 0 {
                    v___x_4276_ = v___x_4273_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
                    v___x_4276_ = v_reuseFailAlloc_4277_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4276_;
            }
            5 => {
                if v___y_4288_ == 0 {
                    leanh::lean_dec_ref(v___y_4281_);
                    v___x_4289_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__1_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__1,
                    );
                    v___x_4290_ = l_Lean_MessageData_ofExpr(v___y_4285_);
                    v___x_4291_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4291_, 0, v___x_4289_);
                    leanh::lean_ctor_set(v___x_4291_, 1, v___x_4290_);
                    v___x_4292_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__3_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__3,
                    );
                    v___x_4293_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4293_, 0, v___x_4291_);
                    leanh::lean_ctor_set(v___x_4293_, 1, v___x_4292_);
                    v___x_4294_ = l_Lean_Exception_toMessageData(v___y_4283_);
                    v___x_4295_ = l_Lean_indentD(v___x_4294_);
                    v___x_4296_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4296_, 0, v___x_4293_);
                    leanh::lean_ctor_set(v___x_4296_, 1, v___x_4295_);
                    v___x_4297_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__5_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__5,
                    );
                    v___x_4298_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4298_, 0, v___x_4296_);
                    leanh::lean_ctor_set(v___x_4298_, 1, v___x_4297_);
                    v___x_4299_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                        v___x_4298_,
                        v___y_4280_,
                        v___y_4287_,
                        v___y_4286_,
                        v___y_4284_,
                    );
                    v___y_4268_ = v___y_4282_;
                    v___y_4269_ = v___x_4299_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4285_);
                    leanh::lean_dec_ref(v___y_4283_);
                    v___y_4268_ = v___y_4282_;
                    v___y_4269_ = v___y_4281_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_4308_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(
                    v___y_4302_,
                    v___y_4305_,
                );
                v_a_4309_ = leanh::lean_ctor_get(v___x_4308_, 0);
                leanh::lean_inc(v_a_4309_);
                leanh::lean_dec_ref(v___x_4308_);
                v___x_4310_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(
                    v___x_4300_,
                    v___y_4305_,
                );
                if v___y_4303_ == 0 {
                    v_a_4311_ = leanh::lean_ctor_get(v___x_4310_, 0);
                    leanh::lean_inc(v_a_4311_);
                    leanh::lean_dec_ref(v___x_4310_);
                    v___y_4262_ = v_a_4309_;
                    v_proof_4263_ = v_a_4311_;
                    state = 1;
                    continue;
                } else {
                    v_a_4312_ = leanh::lean_ctor_get(v___x_4310_, 0);
                    leanh::lean_inc_n(v_a_4312_, 2);
                    leanh::lean_dec_ref(v___x_4310_);
                    v___x_4313_ = l_Lean_Meta_mkEqOfHEq(
                        v_a_4312_,
                        v___x_4247_,
                        v___y_4304_,
                        v___y_4305_,
                        v___y_4306_,
                        v___y_4307_,
                    );
                    if leanh::lean_obj_tag(v___x_4313_) == 0 {
                        leanh::lean_dec(v_a_4312_);
                        v___y_4268_ = v_a_4309_;
                        v___y_4269_ = v___x_4313_;
                        state = 2;
                        continue;
                    } else {
                        v_a_4314_ = leanh::lean_ctor_get(v___x_4313_, 0);
                        leanh::lean_inc(v_a_4314_);
                        v___x_4315_ = l_Lean_Exception_isInterrupt(v_a_4314_);
                        if v___x_4315_ == 0 {
                            leanh::lean_inc(v_a_4314_);
                            v___x_4316_ = l_Lean_Exception_isRuntime(v_a_4314_);
                            v___y_4280_ = v___y_4304_;
                            v___y_4281_ = v___x_4313_;
                            v___y_4282_ = v_a_4309_;
                            v___y_4283_ = v_a_4314_;
                            v___y_4284_ = v___y_4307_;
                            v___y_4285_ = v_a_4312_;
                            v___y_4286_ = v___y_4306_;
                            v___y_4287_ = v___y_4305_;
                            v___y_4288_ = v___x_4316_;
                            state = 5;
                            continue;
                        } else {
                            v___y_4280_ = v___y_4304_;
                            v___y_4281_ = v___x_4313_;
                            v___y_4282_ = v_a_4309_;
                            v___y_4283_ = v_a_4314_;
                            v___y_4284_ = v___y_4307_;
                            v___y_4285_ = v_a_4312_;
                            v___y_4286_ = v___y_4306_;
                            v___y_4287_ = v___y_4305_;
                            v___y_4288_ = v___x_4315_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_4325_ = lean_array_get_size(v_a_4324_);
                v___x_4326_ = leanh::lean_unsigned_to_nat(0);
                v___x_4327_ = lean_nat_dec_eq(v___x_4325_, v___x_4326_);
                if v___x_4327_ == 0 {
                    leanh::lean_dec_ref(v___y_4320_);
                    leanh::lean_dec_ref(v___x_4300_);
                    v___x_4328_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__7_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__7,
                    );
                    v___x_4329_ = l_Lean_MessageData_ofConstName(v___x_4250_, v___x_4327_);
                    v___x_4330_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4330_, 0, v___x_4328_);
                    leanh::lean_ctor_set(v___x_4330_, 1, v___x_4329_);
                    v___x_4331_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__9),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__9_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__9,
                    );
                    v___x_4332_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4332_, 0, v___x_4330_);
                    leanh::lean_ctor_set(v___x_4332_, 1, v___x_4331_);
                    v___x_4333_ = lean_array_to_list(v_a_4324_);
                    v___x_4334_ = leanh::lean_box(0);
                    v___x_4335_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(
                        v___x_4333_,
                        v___x_4334_,
                    );
                    v___x_4336_ = l_Lean_MessageData_ofList(v___x_4335_);
                    v___x_4337_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4337_, 0, v___x_4332_);
                    leanh::lean_ctor_set(v___x_4337_, 1, v___x_4336_);
                    v___x_4338_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                        v___x_4337_,
                        v___y_4321_,
                        v___y_4319_,
                        v___y_4323_,
                        v___y_4318_,
                    );
                    v_a_4339_ = leanh::lean_ctor_get(v___x_4338_, 0);
                    v_isSharedCheck_4346_ = (!leanh::lean_is_exclusive(v___x_4338_)) as u8;
                    if v_isSharedCheck_4346_ == 0 {
                        v___x_4341_ = v___x_4338_;
                        v_isShared_4342_ = v_isSharedCheck_4346_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4339_);
                        leanh::lean_dec(v___x_4338_);
                        v___x_4341_ = leanh::lean_box(0);
                        v_isShared_4342_ = v_isSharedCheck_4346_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_4324_);
                    leanh::lean_dec(v___x_4250_);
                    v___y_4302_ = v___y_4320_;
                    v___y_4303_ = v___y_4322_;
                    v___y_4304_ = v___y_4321_;
                    v___y_4305_ = v___y_4319_;
                    v___y_4306_ = v___y_4323_;
                    v___y_4307_ = v___y_4318_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                if v_isShared_4342_ == 0 {
                    v___x_4344_ = v___x_4341_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4345_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
                    v___x_4344_ = v_reuseFailAlloc_4345_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4344_;
            }
            10 => {
                if leanh::lean_obj_tag(v___y_4354_) == 0 {
                    v_a_4355_ = leanh::lean_ctor_get(v___y_4354_, 0);
                    leanh::lean_inc(v_a_4355_);
                    leanh::lean_dec_ref_known(v___y_4354_, 1);
                    v___y_4318_ = v___y_4348_;
                    v___y_4319_ = v___y_4349_;
                    v___y_4320_ = v___y_4351_;
                    v___y_4321_ = v___y_4350_;
                    v___y_4322_ = v___y_4352_;
                    v___y_4323_ = v___y_4353_;
                    v_a_4324_ = v_a_4355_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4351_);
                    leanh::lean_dec_ref(v___x_4300_);
                    leanh::lean_dec(v___x_4250_);
                    v_a_4356_ = leanh::lean_ctor_get(v___y_4354_, 0);
                    v_isSharedCheck_4363_ = (!leanh::lean_is_exclusive(v___y_4354_)) as u8;
                    if v_isSharedCheck_4363_ == 0 {
                        v___x_4358_ = v___y_4354_;
                        v_isShared_4359_ = v_isSharedCheck_4363_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4356_);
                        leanh::lean_dec(v___y_4354_);
                        v___x_4358_ = leanh::lean_box(0);
                        v_isShared_4359_ = v_isSharedCheck_4363_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_4359_ == 0 {
                    v___x_4361_ = v___x_4358_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
                    v___x_4361_ = v_reuseFailAlloc_4362_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4361_;
            }
            13 => {
                v___x_4374_ = leanh::lean_box(0);
                v_sz_4375_ = lean_array_size(v___x_4366_);
                v___x_4376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_4366_, v_sz_4375_, v___x_4365_, v___x_4374_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
                if leanh::lean_obj_tag(v___x_4376_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4376_, 1);
                    v___x_4377_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4378_ = lean_array_get_size(v___x_4366_);
                    v___x_4379_ = l_Lean_Meta_rwMatcher___lam__2___closed__10;
                    v___x_4380_ = lean_nat_dec_lt(v___x_4377_, v___x_4378_);
                    if v___x_4380_ == 0 {
                        leanh::lean_dec_ref(v___x_4366_);
                        v___y_4318_ = v___y_4373_;
                        v___y_4319_ = v___y_4371_;
                        v___y_4320_ = v___y_4368_;
                        v___y_4321_ = v___y_4370_;
                        v___y_4322_ = v___y_4369_;
                        v___y_4323_ = v___y_4372_;
                        v_a_4324_ = v___x_4379_;
                        state = 7;
                        continue;
                    } else {
                        v___x_4381_ = lean_nat_dec_le(v___x_4378_, v___x_4378_);
                        if v___x_4381_ == 0 {
                            if v___x_4380_ == 0 {
                                leanh::lean_dec_ref(v___x_4366_);
                                v___y_4318_ = v___y_4373_;
                                v___y_4319_ = v___y_4371_;
                                v___y_4320_ = v___y_4368_;
                                v___y_4321_ = v___y_4370_;
                                v___y_4322_ = v___y_4369_;
                                v___y_4323_ = v___y_4372_;
                                v_a_4324_ = v___x_4379_;
                                state = 7;
                                continue;
                            } else {
                                v___x_4382_ = lean_usize_of_nat(v___x_4378_);
                                v___x_4383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_4251_, v___x_4366_, v___x_4365_, v___x_4382_, v___x_4379_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
                                leanh::lean_dec_ref(v___x_4366_);
                                v___y_4348_ = v___y_4373_;
                                v___y_4349_ = v___y_4371_;
                                v___y_4350_ = v___y_4370_;
                                v___y_4351_ = v___y_4368_;
                                v___y_4352_ = v___y_4369_;
                                v___y_4353_ = v___y_4372_;
                                v___y_4354_ = v___x_4383_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v___x_4384_ = lean_usize_of_nat(v___x_4378_);
                            v___x_4385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_4251_, v___x_4366_, v___x_4365_, v___x_4384_, v___x_4379_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
                            leanh::lean_dec_ref(v___x_4366_);
                            v___y_4348_ = v___y_4373_;
                            v___y_4349_ = v___y_4371_;
                            v___y_4350_ = v___y_4370_;
                            v___y_4351_ = v___y_4368_;
                            v___y_4352_ = v___y_4369_;
                            v___y_4353_ = v___y_4372_;
                            v___y_4354_ = v___x_4385_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4368_);
                    leanh::lean_dec_ref(v___x_4366_);
                    leanh::lean_dec_ref(v___x_4300_);
                    leanh::lean_dec(v___x_4250_);
                    v_a_4386_ = leanh::lean_ctor_get(v___x_4376_, 0);
                    v_isSharedCheck_4393_ = (!leanh::lean_is_exclusive(v___x_4376_)) as u8;
                    if v_isSharedCheck_4393_ == 0 {
                        v___x_4388_ = v___x_4376_;
                        v_isShared_4389_ = v_isSharedCheck_4393_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4386_);
                        leanh::lean_dec(v___x_4376_);
                        v___x_4388_ = leanh::lean_box(0);
                        v_isShared_4389_ = v_isSharedCheck_4393_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_4389_ == 0 {
                    v___x_4391_ = v___x_4388_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4392_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
                    v___x_4391_ = v_reuseFailAlloc_4392_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4391_;
            }
            16 => {
                leanh::lean_inc_ref(v_fst_4396_);
                leanh::lean_inc_ref(v_e_4252_);
                v___x_4398_ = l_Lean_Meta_isExprDefEq(
                    v_e_4252_,
                    v_fst_4396_,
                    v___y_4256_,
                    v___y_4257_,
                    v___y_4258_,
                    v___y_4259_,
                );
                if leanh::lean_obj_tag(v___x_4398_) == 0 {
                    v_a_4399_ = leanh::lean_ctor_get(v___x_4398_, 0);
                    leanh::lean_inc(v_a_4399_);
                    leanh::lean_dec_ref_known(v___x_4398_, 1);
                    v___x_4400_ = (leanh::lean_unbox(v_a_4399_) as u8);
                    leanh::lean_dec(v_a_4399_);
                    if v___x_4400_ == 0 {
                        if v___x_4251_ == 0 {
                            leanh::lean_dec_ref(v_fst_4396_);
                            leanh::lean_dec_ref(v_e_4252_);
                            v___y_4368_ = v_snd_4397_;
                            v___y_4369_ = v_fst_4395_;
                            v___y_4370_ = v___y_4256_;
                            v___y_4371_ = v___y_4257_;
                            v___y_4372_ = v___y_4258_;
                            v___y_4373_ = v___y_4259_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_snd_4397_);
                            leanh::lean_dec_ref(v___x_4366_);
                            leanh::lean_dec_ref(v___x_4300_);
                            v___x_4401_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_rwMatcher___lam__2___closed__12
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_rwMatcher___lam__2___closed__12_once
                                ),
                                _init_l_Lean_Meta_rwMatcher___lam__2___closed__12,
                            );
                            v___x_4402_ = l_Lean_MessageData_ofExpr(v_fst_4396_);
                            v___x_4403_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4403_, 0, v___x_4401_);
                            leanh::lean_ctor_set(v___x_4403_, 1, v___x_4402_);
                            v___x_4404_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_rwMatcher___lam__2___closed__14
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_rwMatcher___lam__2___closed__14_once
                                ),
                                _init_l_Lean_Meta_rwMatcher___lam__2___closed__14,
                            );
                            v___x_4405_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4405_, 0, v___x_4403_);
                            leanh::lean_ctor_set(v___x_4405_, 1, v___x_4404_);
                            v___x_4406_ = l_Lean_MessageData_ofConstName(v___x_4250_, v___y_4253_);
                            v___x_4407_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4407_, 0, v___x_4405_);
                            leanh::lean_ctor_set(v___x_4407_, 1, v___x_4406_);
                            v___x_4408_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_rwMatcher___lam__2___closed__16
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_rwMatcher___lam__2___closed__16_once
                                ),
                                _init_l_Lean_Meta_rwMatcher___lam__2___closed__16,
                            );
                            v___x_4409_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4409_, 0, v___x_4407_);
                            leanh::lean_ctor_set(v___x_4409_, 1, v___x_4408_);
                            v___x_4410_ = l_Lean_MessageData_ofExpr(v_e_4252_);
                            v___x_4411_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4411_, 0, v___x_4409_);
                            leanh::lean_ctor_set(v___x_4411_, 1, v___x_4410_);
                            v___x_4412_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
                            v___x_4413_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4413_, 0, v___x_4411_);
                            leanh::lean_ctor_set(v___x_4413_, 1, v___x_4412_);
                            v___x_4414_ =
                                l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                                    v___x_4413_,
                                    v___y_4256_,
                                    v___y_4257_,
                                    v___y_4258_,
                                    v___y_4259_,
                                );
                            v_a_4415_ = leanh::lean_ctor_get(v___x_4414_, 0);
                            v_isSharedCheck_4422_ =
                                (!leanh::lean_is_exclusive(v___x_4414_)) as u8;
                            if v_isSharedCheck_4422_ == 0 {
                                v___x_4417_ = v___x_4414_;
                                v_isShared_4418_ = v_isSharedCheck_4422_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4415_);
                                leanh::lean_dec(v___x_4414_);
                                v___x_4417_ = leanh::lean_box(0);
                                v_isShared_4418_ = v_isSharedCheck_4422_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_fst_4396_);
                        leanh::lean_dec_ref(v_e_4252_);
                        v___y_4368_ = v_snd_4397_;
                        v___y_4369_ = v_fst_4395_;
                        v___y_4370_ = v___y_4256_;
                        v___y_4371_ = v___y_4257_;
                        v___y_4372_ = v___y_4258_;
                        v___y_4373_ = v___y_4259_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_snd_4397_);
                    leanh::lean_dec_ref(v_fst_4396_);
                    leanh::lean_dec_ref(v___x_4366_);
                    leanh::lean_dec_ref(v___x_4300_);
                    leanh::lean_dec_ref(v_e_4252_);
                    leanh::lean_dec(v___x_4250_);
                    v_a_4423_ = leanh::lean_ctor_get(v___x_4398_, 0);
                    v_isSharedCheck_4430_ = (!leanh::lean_is_exclusive(v___x_4398_)) as u8;
                    if v_isSharedCheck_4430_ == 0 {
                        v___x_4425_ = v___x_4398_;
                        v_isShared_4426_ = v_isSharedCheck_4430_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4423_);
                        leanh::lean_dec(v___x_4398_);
                        v___x_4425_ = leanh::lean_box(0);
                        v_isShared_4426_ = v_isSharedCheck_4430_;
                        state = 19;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_4418_ == 0 {
                    v___x_4420_ = v___x_4417_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4421_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
                    v___x_4420_ = v_reuseFailAlloc_4421_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4420_;
            }
            19 => {
                if v_isShared_4426_ == 0 {
                    v___x_4428_ = v___x_4425_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4429_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
                    v___x_4428_ = v_reuseFailAlloc_4429_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4428_;
            }
            21 => {
                if v_isShared_4446_ == 0 {
                    v___x_4448_ = v___x_4445_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4449_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
                    v___x_4448_ = v_reuseFailAlloc_4449_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_rwMatcher___lam__3___boxed(
    mut v___x_4458_: *mut leanh::LeanObject,
    mut v___x_4459_: *mut leanh::LeanObject,
    mut v_fst_4460_: *mut leanh::LeanObject,
    mut v___x_4461_: *mut leanh::LeanObject,
    mut v___x_4462_: *mut leanh::LeanObject,
    mut v_e_4463_: *mut leanh::LeanObject,
    mut v___y_4464_: *mut leanh::LeanObject,
    mut v_snd_4465_: *mut leanh::LeanObject,
    mut v_____r_4466_: *mut leanh::LeanObject,
    mut v___y_4467_: *mut leanh::LeanObject,
    mut v___y_4468_: *mut leanh::LeanObject,
    mut v___y_4469_: *mut leanh::LeanObject,
    mut v___y_4470_: *mut leanh::LeanObject,
    mut v___y_4471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_109290__boxed_4472_: u8 = 0;
    let mut v___x_109294__boxed_4473_: u8 = 0;
    let mut v___y_109295__boxed_4474_: u8 = 0;
    let mut v_res_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_109290__boxed_4472_ = (leanh::lean_unbox(v___x_4458_) as u8);
    v___x_109294__boxed_4473_ = (leanh::lean_unbox(v___x_4462_) as u8);
    v___y_109295__boxed_4474_ = (leanh::lean_unbox(v___y_4464_) as u8);
    v_res_4475_ = l_Lean_Meta_rwMatcher___lam__3(
        v___x_109290__boxed_4472_,
        v___x_4459_,
        v_fst_4460_,
        v___x_4461_,
        v___x_109294__boxed_4473_,
        v_e_4463_,
        v___y_109295__boxed_4474_,
        v_snd_4465_,
        v_____r_4466_,
        v___y_4467_,
        v___y_4468_,
        v___y_4469_,
        v___y_4470_,
    );
    leanh::lean_dec(v___y_4470_);
    leanh::lean_dec_ref(v___y_4469_);
    leanh::lean_dec(v___y_4468_);
    leanh::lean_dec_ref(v___y_4467_);
    leanh::lean_dec_ref(v_snd_4465_);
    return v_res_4475_;
}
pub unsafe fn l_Lean_Meta_rwMatcher___lam__4(
    mut v___x_4476_: u8,
    mut v___x_4477_: *mut leanh::LeanObject,
    mut v_fst_4478_: *mut leanh::LeanObject,
    mut v___x_4479_: *mut leanh::LeanObject,
    mut v___x_4480_: u8,
    mut v_e_4481_: *mut leanh::LeanObject,
    mut v_snd_4482_: *mut leanh::LeanObject,
    mut v_____r_4483_: *mut leanh::LeanObject,
    mut v___y_4484_: *mut leanh::LeanObject,
    mut v___y_4485_: *mut leanh::LeanObject,
    mut v___y_4486_: *mut leanh::LeanObject,
    mut v___y_4487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4506_: u8 = 0;
    let mut v___y_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4516_: u8 = 0;
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4530_: u8 = 0;
    let mut v___y_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: u8 = 0;
    let mut v___x_4544_: u8 = 0;
    let mut v___y_4546_: u8 = 0;
    let mut v___y_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: u8 = 0;
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4570_: u8 = 0;
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4574_: u8 = 0;
    let mut v___y_4576_: u8 = 0;
    let mut v___y_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4587_: u8 = 0;
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4591_: u8 = 0;
    let mut v_sz_4592_: usize = 0;
    let mut v___x_4593_: usize = 0;
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4596_: u8 = 0;
    let mut v___y_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4603_: usize = 0;
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: u8 = 0;
    let mut v___x_4609_: u8 = 0;
    let mut v___x_4610_: usize = 0;
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: usize = 0;
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4617_: u8 = 0;
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4621_: u8 = 0;
    let mut v___y_4623_: u8 = 0;
    let mut v___y_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4647_: u8 = 0;
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4651_: u8 = 0;
    let mut v_fst_4653_: u8 = 0;
    let mut v_fst_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: u8 = 0;
    let mut v_a_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4662_: u8 = 0;
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4666_: u8 = 0;
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: u8 = 0;
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: u8 = 0;
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4682_: u8 = 0;
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4686_: u8 = 0;
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4528_ = l_Lean_mkAppN(v___x_4477_, v_fst_4478_);
                v_sz_4592_ = lean_array_size(v_fst_4478_);
                v___x_4593_ = 0usize;
                v___x_4594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_4592_, v___x_4593_, v_fst_4478_);
                v___x_4667_ = l_Lean_Meta_rwMatcher___lam__2___closed__18;
                v___x_4668_ = leanh::lean_unsigned_to_nat(4);
                v___x_4669_ = l_Lean_Expr_isAppOfArity(v_snd_4482_, v___x_4667_, v___x_4668_);
                if v___x_4669_ == 0 {
                    v___x_4670_ = l_Lean_Meta_rwMatcher___lam__2___closed__20;
                    v___x_4671_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4672_ = l_Lean_Expr_isAppOfArity(v_snd_4482_, v___x_4670_, v___x_4671_);
                    if v___x_4672_ == 0 {
                        leanh::lean_dec_ref(v___x_4594_);
                        leanh::lean_dec_ref(v___x_4528_);
                        leanh::lean_dec_ref(v_e_4481_);
                        v___x_4673_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__22),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_rwMatcher___lam__2___closed__22_once
                            ),
                            _init_l_Lean_Meta_rwMatcher___lam__2___closed__22,
                        );
                        v___x_4674_ = l_Lean_MessageData_ofConstName(v___x_4479_, v___x_4480_);
                        v___x_4675_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4675_, 0, v___x_4673_);
                        leanh::lean_ctor_set(v___x_4675_, 1, v___x_4674_);
                        v___x_4676_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_rwMatcher___lam__2___closed__24_once
                            ),
                            _init_l_Lean_Meta_rwMatcher___lam__2___closed__24,
                        );
                        v___x_4677_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4677_, 0, v___x_4675_);
                        leanh::lean_ctor_set(v___x_4677_, 1, v___x_4676_);
                        v___x_4678_ =
                            l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                                v___x_4677_,
                                v___y_4484_,
                                v___y_4485_,
                                v___y_4486_,
                                v___y_4487_,
                            );
                        v_a_4679_ = leanh::lean_ctor_get(v___x_4678_, 0);
                        v_isSharedCheck_4686_ =
                            (!leanh::lean_is_exclusive(v___x_4678_)) as u8;
                        if v_isSharedCheck_4686_ == 0 {
                            v___x_4681_ = v___x_4678_;
                            v_isShared_4682_ = v_isSharedCheck_4686_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4679_);
                            leanh::lean_dec(v___x_4678_);
                            v___x_4681_ = leanh::lean_box(0);
                            v_isShared_4682_ = v_isSharedCheck_4686_;
                            state = 22;
                            continue;
                        }
                    } else {
                        v___x_4687_ = l_Lean_Expr_appFn_x21(v_snd_4482_);
                        v___x_4688_ = l_Lean_Expr_appArg_x21(v___x_4687_);
                        leanh::lean_dec_ref(v___x_4687_);
                        v___x_4689_ = l_Lean_Expr_appArg_x21(v_snd_4482_);
                        v_fst_4653_ = v___x_4480_;
                        v_fst_4654_ = v___x_4688_;
                        v_snd_4655_ = v___x_4689_;
                        state = 19;
                        continue;
                    }
                } else {
                    v___x_4690_ = l_Lean_Expr_appFn_x21(v_snd_4482_);
                    v___x_4691_ = l_Lean_Expr_appFn_x21(v___x_4690_);
                    leanh::lean_dec_ref(v___x_4690_);
                    v___x_4692_ = l_Lean_Expr_appArg_x21(v___x_4691_);
                    leanh::lean_dec_ref(v___x_4691_);
                    v___x_4693_ = l_Lean_Expr_appArg_x21(v_snd_4482_);
                    v_fst_4653_ = v___x_4476_;
                    v_fst_4654_ = v___x_4692_;
                    v_snd_4655_ = v___x_4693_;
                    state = 19;
                    continue;
                }
            }
            1 => {
                v___x_4492_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4492_, 0, v_proof_4491_);
                v___x_4493_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_4493_, 0, v___y_4490_);
                leanh::lean_ctor_set(v___x_4493_, 1, v___x_4492_);
                leanh::lean_ctor_set_uint8(
                    v___x_4493_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4476_,
                );
                v___x_4494_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4494_, 0, v___x_4493_);
                return v___x_4494_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_4497_) == 0 {
                    v_a_4498_ = leanh::lean_ctor_get(v___y_4497_, 0);
                    leanh::lean_inc(v_a_4498_);
                    leanh::lean_dec_ref_known(v___y_4497_, 1);
                    v___y_4490_ = v___y_4496_;
                    v_proof_4491_ = v_a_4498_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4496_);
                    v_a_4499_ = leanh::lean_ctor_get(v___y_4497_, 0);
                    v_isSharedCheck_4506_ = (!leanh::lean_is_exclusive(v___y_4497_)) as u8;
                    if v_isSharedCheck_4506_ == 0 {
                        v___x_4501_ = v___y_4497_;
                        v_isShared_4502_ = v_isSharedCheck_4506_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4499_);
                        leanh::lean_dec(v___y_4497_);
                        v___x_4501_ = leanh::lean_box(0);
                        v_isShared_4502_ = v_isSharedCheck_4506_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4502_ == 0 {
                    v___x_4504_ = v___x_4501_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4505_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4499_);
                    v___x_4504_ = v_reuseFailAlloc_4505_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4504_;
            }
            5 => {
                if v___y_4516_ == 0 {
                    leanh::lean_dec_ref(v___y_4512_);
                    v___x_4517_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__1_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__1,
                    );
                    v___x_4518_ = l_Lean_MessageData_ofExpr(v___y_4511_);
                    v___x_4519_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4519_, 0, v___x_4517_);
                    leanh::lean_ctor_set(v___x_4519_, 1, v___x_4518_);
                    v___x_4520_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__3_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__3,
                    );
                    v___x_4521_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4521_, 0, v___x_4519_);
                    leanh::lean_ctor_set(v___x_4521_, 1, v___x_4520_);
                    v___x_4522_ = l_Lean_Exception_toMessageData(v___y_4510_);
                    v___x_4523_ = l_Lean_indentD(v___x_4522_);
                    v___x_4524_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4524_, 0, v___x_4521_);
                    leanh::lean_ctor_set(v___x_4524_, 1, v___x_4523_);
                    v___x_4525_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__5_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__5,
                    );
                    v___x_4526_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4526_, 0, v___x_4524_);
                    leanh::lean_ctor_set(v___x_4526_, 1, v___x_4525_);
                    v___x_4527_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                        v___x_4526_,
                        v___y_4509_,
                        v___y_4513_,
                        v___y_4508_,
                        v___y_4514_,
                    );
                    v___y_4496_ = v___y_4515_;
                    v___y_4497_ = v___x_4527_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4511_);
                    leanh::lean_dec_ref(v___y_4510_);
                    v___y_4496_ = v___y_4515_;
                    v___y_4497_ = v___y_4512_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_4536_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(
                    v___y_4531_,
                    v___y_4533_,
                );
                v_a_4537_ = leanh::lean_ctor_get(v___x_4536_, 0);
                leanh::lean_inc(v_a_4537_);
                leanh::lean_dec_ref(v___x_4536_);
                v___x_4538_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(
                    v___x_4528_,
                    v___y_4533_,
                );
                if v___y_4530_ == 0 {
                    v_a_4539_ = leanh::lean_ctor_get(v___x_4538_, 0);
                    leanh::lean_inc(v_a_4539_);
                    leanh::lean_dec_ref(v___x_4538_);
                    v___y_4490_ = v_a_4537_;
                    v_proof_4491_ = v_a_4539_;
                    state = 1;
                    continue;
                } else {
                    v_a_4540_ = leanh::lean_ctor_get(v___x_4538_, 0);
                    leanh::lean_inc_n(v_a_4540_, 2);
                    leanh::lean_dec_ref(v___x_4538_);
                    v___x_4541_ = l_Lean_Meta_mkEqOfHEq(
                        v_a_4540_,
                        v___x_4476_,
                        v___y_4532_,
                        v___y_4533_,
                        v___y_4534_,
                        v___y_4535_,
                    );
                    if leanh::lean_obj_tag(v___x_4541_) == 0 {
                        leanh::lean_dec(v_a_4540_);
                        v___y_4496_ = v_a_4537_;
                        v___y_4497_ = v___x_4541_;
                        state = 2;
                        continue;
                    } else {
                        v_a_4542_ = leanh::lean_ctor_get(v___x_4541_, 0);
                        leanh::lean_inc(v_a_4542_);
                        v___x_4543_ = l_Lean_Exception_isInterrupt(v_a_4542_);
                        if v___x_4543_ == 0 {
                            leanh::lean_inc(v_a_4542_);
                            v___x_4544_ = l_Lean_Exception_isRuntime(v_a_4542_);
                            v___y_4508_ = v___y_4534_;
                            v___y_4509_ = v___y_4532_;
                            v___y_4510_ = v_a_4542_;
                            v___y_4511_ = v_a_4540_;
                            v___y_4512_ = v___x_4541_;
                            v___y_4513_ = v___y_4533_;
                            v___y_4514_ = v___y_4535_;
                            v___y_4515_ = v_a_4537_;
                            v___y_4516_ = v___x_4544_;
                            state = 5;
                            continue;
                        } else {
                            v___y_4508_ = v___y_4534_;
                            v___y_4509_ = v___y_4532_;
                            v___y_4510_ = v_a_4542_;
                            v___y_4511_ = v_a_4540_;
                            v___y_4512_ = v___x_4541_;
                            v___y_4513_ = v___y_4533_;
                            v___y_4514_ = v___y_4535_;
                            v___y_4515_ = v_a_4537_;
                            v___y_4516_ = v___x_4543_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_4553_ = lean_array_get_size(v_a_4552_);
                v___x_4554_ = leanh::lean_unsigned_to_nat(0);
                v___x_4555_ = lean_nat_dec_eq(v___x_4553_, v___x_4554_);
                if v___x_4555_ == 0 {
                    leanh::lean_dec_ref(v___y_4549_);
                    leanh::lean_dec_ref(v___x_4528_);
                    v___x_4556_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__7_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__7,
                    );
                    v___x_4557_ = l_Lean_MessageData_ofConstName(v___x_4479_, v___x_4480_);
                    v___x_4558_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4558_, 0, v___x_4556_);
                    leanh::lean_ctor_set(v___x_4558_, 1, v___x_4557_);
                    v___x_4559_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__9),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__9_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__9,
                    );
                    v___x_4560_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4560_, 0, v___x_4558_);
                    leanh::lean_ctor_set(v___x_4560_, 1, v___x_4559_);
                    v___x_4561_ = lean_array_to_list(v_a_4552_);
                    v___x_4562_ = leanh::lean_box(0);
                    v___x_4563_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(
                        v___x_4561_,
                        v___x_4562_,
                    );
                    v___x_4564_ = l_Lean_MessageData_ofList(v___x_4563_);
                    v___x_4565_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4565_, 0, v___x_4560_);
                    leanh::lean_ctor_set(v___x_4565_, 1, v___x_4564_);
                    v___x_4566_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                        v___x_4565_,
                        v___y_4551_,
                        v___y_4548_,
                        v___y_4550_,
                        v___y_4547_,
                    );
                    v_a_4567_ = leanh::lean_ctor_get(v___x_4566_, 0);
                    v_isSharedCheck_4574_ = (!leanh::lean_is_exclusive(v___x_4566_)) as u8;
                    if v_isSharedCheck_4574_ == 0 {
                        v___x_4569_ = v___x_4566_;
                        v_isShared_4570_ = v_isSharedCheck_4574_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4567_);
                        leanh::lean_dec(v___x_4566_);
                        v___x_4569_ = leanh::lean_box(0);
                        v_isShared_4570_ = v_isSharedCheck_4574_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_4552_);
                    leanh::lean_dec(v___x_4479_);
                    v___y_4530_ = v___y_4546_;
                    v___y_4531_ = v___y_4549_;
                    v___y_4532_ = v___y_4551_;
                    v___y_4533_ = v___y_4548_;
                    v___y_4534_ = v___y_4550_;
                    v___y_4535_ = v___y_4547_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                if v_isShared_4570_ == 0 {
                    v___x_4572_ = v___x_4569_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4573_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_a_4567_);
                    v___x_4572_ = v_reuseFailAlloc_4573_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4572_;
            }
            10 => {
                if leanh::lean_obj_tag(v___y_4582_) == 0 {
                    v_a_4583_ = leanh::lean_ctor_get(v___y_4582_, 0);
                    leanh::lean_inc(v_a_4583_);
                    leanh::lean_dec_ref_known(v___y_4582_, 1);
                    v___y_4546_ = v___y_4576_;
                    v___y_4547_ = v___y_4577_;
                    v___y_4548_ = v___y_4578_;
                    v___y_4549_ = v___y_4579_;
                    v___y_4550_ = v___y_4581_;
                    v___y_4551_ = v___y_4580_;
                    v_a_4552_ = v_a_4583_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4579_);
                    leanh::lean_dec_ref(v___x_4528_);
                    leanh::lean_dec(v___x_4479_);
                    v_a_4584_ = leanh::lean_ctor_get(v___y_4582_, 0);
                    v_isSharedCheck_4591_ = (!leanh::lean_is_exclusive(v___y_4582_)) as u8;
                    if v_isSharedCheck_4591_ == 0 {
                        v___x_4586_ = v___y_4582_;
                        v_isShared_4587_ = v_isSharedCheck_4591_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4584_);
                        leanh::lean_dec(v___y_4582_);
                        v___x_4586_ = leanh::lean_box(0);
                        v_isShared_4587_ = v_isSharedCheck_4591_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_4587_ == 0 {
                    v___x_4589_ = v___x_4586_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4590_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
                    v___x_4589_ = v_reuseFailAlloc_4590_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4589_;
            }
            13 => {
                v___x_4602_ = leanh::lean_box(0);
                v_sz_4603_ = lean_array_size(v___x_4594_);
                v___x_4604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_4594_, v_sz_4603_, v___x_4593_, v___x_4602_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
                if leanh::lean_obj_tag(v___x_4604_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4604_, 1);
                    v___x_4605_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4606_ = lean_array_get_size(v___x_4594_);
                    v___x_4607_ = l_Lean_Meta_rwMatcher___lam__2___closed__10;
                    v___x_4608_ = lean_nat_dec_lt(v___x_4605_, v___x_4606_);
                    if v___x_4608_ == 0 {
                        leanh::lean_dec_ref(v___x_4594_);
                        v___y_4546_ = v___y_4596_;
                        v___y_4547_ = v___y_4601_;
                        v___y_4548_ = v___y_4599_;
                        v___y_4549_ = v___y_4597_;
                        v___y_4550_ = v___y_4600_;
                        v___y_4551_ = v___y_4598_;
                        v_a_4552_ = v___x_4607_;
                        state = 7;
                        continue;
                    } else {
                        v___x_4609_ = lean_nat_dec_le(v___x_4606_, v___x_4606_);
                        if v___x_4609_ == 0 {
                            if v___x_4608_ == 0 {
                                leanh::lean_dec_ref(v___x_4594_);
                                v___y_4546_ = v___y_4596_;
                                v___y_4547_ = v___y_4601_;
                                v___y_4548_ = v___y_4599_;
                                v___y_4549_ = v___y_4597_;
                                v___y_4550_ = v___y_4600_;
                                v___y_4551_ = v___y_4598_;
                                v_a_4552_ = v___x_4607_;
                                state = 7;
                                continue;
                            } else {
                                v___x_4610_ = lean_usize_of_nat(v___x_4606_);
                                v___x_4611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_4480_, v___x_4594_, v___x_4593_, v___x_4610_, v___x_4607_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
                                leanh::lean_dec_ref(v___x_4594_);
                                v___y_4576_ = v___y_4596_;
                                v___y_4577_ = v___y_4601_;
                                v___y_4578_ = v___y_4599_;
                                v___y_4579_ = v___y_4597_;
                                v___y_4580_ = v___y_4598_;
                                v___y_4581_ = v___y_4600_;
                                v___y_4582_ = v___x_4611_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v___x_4612_ = lean_usize_of_nat(v___x_4606_);
                            v___x_4613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_4480_, v___x_4594_, v___x_4593_, v___x_4612_, v___x_4607_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
                            leanh::lean_dec_ref(v___x_4594_);
                            v___y_4576_ = v___y_4596_;
                            v___y_4577_ = v___y_4601_;
                            v___y_4578_ = v___y_4599_;
                            v___y_4579_ = v___y_4597_;
                            v___y_4580_ = v___y_4598_;
                            v___y_4581_ = v___y_4600_;
                            v___y_4582_ = v___x_4613_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4597_);
                    leanh::lean_dec_ref(v___x_4594_);
                    leanh::lean_dec_ref(v___x_4528_);
                    leanh::lean_dec(v___x_4479_);
                    v_a_4614_ = leanh::lean_ctor_get(v___x_4604_, 0);
                    v_isSharedCheck_4621_ = (!leanh::lean_is_exclusive(v___x_4604_)) as u8;
                    if v_isSharedCheck_4621_ == 0 {
                        v___x_4616_ = v___x_4604_;
                        v_isShared_4617_ = v_isSharedCheck_4621_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4614_);
                        leanh::lean_dec(v___x_4604_);
                        v___x_4616_ = leanh::lean_box(0);
                        v_isShared_4617_ = v_isSharedCheck_4621_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_4617_ == 0 {
                    v___x_4619_ = v___x_4616_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4620_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
                    v___x_4619_ = v_reuseFailAlloc_4620_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4619_;
            }
            16 => {
                leanh::lean_dec_ref(v___y_4626_);
                v___x_4630_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__12_once),
                    _init_l_Lean_Meta_rwMatcher___lam__2___closed__12,
                );
                v___x_4631_ = l_Lean_MessageData_ofExpr(v___y_4624_);
                v___x_4632_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4632_, 0, v___x_4630_);
                leanh::lean_ctor_set(v___x_4632_, 1, v___x_4631_);
                v___x_4633_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__14_once),
                    _init_l_Lean_Meta_rwMatcher___lam__2___closed__14,
                );
                v___x_4634_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4634_, 0, v___x_4632_);
                leanh::lean_ctor_set(v___x_4634_, 1, v___x_4633_);
                v___x_4635_ = l_Lean_MessageData_ofConstName(v___x_4479_, v___x_4480_);
                v___x_4636_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4636_, 0, v___x_4634_);
                leanh::lean_ctor_set(v___x_4636_, 1, v___x_4635_);
                v___x_4637_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__16),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__16_once),
                    _init_l_Lean_Meta_rwMatcher___lam__2___closed__16,
                );
                v___x_4638_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4638_, 0, v___x_4636_);
                leanh::lean_ctor_set(v___x_4638_, 1, v___x_4637_);
                v___x_4639_ = l_Lean_MessageData_ofExpr(v_e_4481_);
                v___x_4640_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4640_, 0, v___x_4638_);
                leanh::lean_ctor_set(v___x_4640_, 1, v___x_4639_);
                v___x_4641_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
                v___x_4642_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4642_, 0, v___x_4640_);
                leanh::lean_ctor_set(v___x_4642_, 1, v___x_4641_);
                v___x_4643_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                    v___x_4642_,
                    v___y_4628_,
                    v___y_4629_,
                    v___y_4625_,
                    v___y_4627_,
                );
                v_a_4644_ = leanh::lean_ctor_get(v___x_4643_, 0);
                v_isSharedCheck_4651_ = (!leanh::lean_is_exclusive(v___x_4643_)) as u8;
                if v_isSharedCheck_4651_ == 0 {
                    v___x_4646_ = v___x_4643_;
                    v_isShared_4647_ = v_isSharedCheck_4651_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4644_);
                    leanh::lean_dec(v___x_4643_);
                    v___x_4646_ = leanh::lean_box(0);
                    v_isShared_4647_ = v_isSharedCheck_4651_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_4647_ == 0 {
                    v___x_4649_ = v___x_4646_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4650_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
                    v___x_4649_ = v_reuseFailAlloc_4650_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4649_;
            }
            19 => {
                leanh::lean_inc_ref(v_fst_4654_);
                leanh::lean_inc_ref(v_e_4481_);
                v___x_4656_ = l_Lean_Meta_isExprDefEq(
                    v_e_4481_,
                    v_fst_4654_,
                    v___y_4484_,
                    v___y_4485_,
                    v___y_4486_,
                    v___y_4487_,
                );
                if leanh::lean_obj_tag(v___x_4656_) == 0 {
                    v_a_4657_ = leanh::lean_ctor_get(v___x_4656_, 0);
                    leanh::lean_inc(v_a_4657_);
                    leanh::lean_dec_ref_known(v___x_4656_, 1);
                    v___x_4658_ = (leanh::lean_unbox(v_a_4657_) as u8);
                    leanh::lean_dec(v_a_4657_);
                    if v___x_4658_ == 0 {
                        leanh::lean_dec_ref(v___x_4594_);
                        leanh::lean_dec_ref(v___x_4528_);
                        v___y_4623_ = v_fst_4653_;
                        v___y_4624_ = v_fst_4654_;
                        v___y_4625_ = v___y_4486_;
                        v___y_4626_ = v_snd_4655_;
                        v___y_4627_ = v___y_4487_;
                        v___y_4628_ = v___y_4484_;
                        v___y_4629_ = v___y_4485_;
                        state = 16;
                        continue;
                    } else {
                        if v___x_4480_ == 0 {
                            leanh::lean_dec_ref(v_fst_4654_);
                            leanh::lean_dec_ref(v_e_4481_);
                            v___y_4596_ = v_fst_4653_;
                            v___y_4597_ = v_snd_4655_;
                            v___y_4598_ = v___y_4484_;
                            v___y_4599_ = v___y_4485_;
                            v___y_4600_ = v___y_4486_;
                            v___y_4601_ = v___y_4487_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_4594_);
                            leanh::lean_dec_ref(v___x_4528_);
                            v___y_4623_ = v_fst_4653_;
                            v___y_4624_ = v_fst_4654_;
                            v___y_4625_ = v___y_4486_;
                            v___y_4626_ = v_snd_4655_;
                            v___y_4627_ = v___y_4487_;
                            v___y_4628_ = v___y_4484_;
                            v___y_4629_ = v___y_4485_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_snd_4655_);
                    leanh::lean_dec_ref(v_fst_4654_);
                    leanh::lean_dec_ref(v___x_4594_);
                    leanh::lean_dec_ref(v___x_4528_);
                    leanh::lean_dec_ref(v_e_4481_);
                    leanh::lean_dec(v___x_4479_);
                    v_a_4659_ = leanh::lean_ctor_get(v___x_4656_, 0);
                    v_isSharedCheck_4666_ = (!leanh::lean_is_exclusive(v___x_4656_)) as u8;
                    if v_isSharedCheck_4666_ == 0 {
                        v___x_4661_ = v___x_4656_;
                        v_isShared_4662_ = v_isSharedCheck_4666_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4659_);
                        leanh::lean_dec(v___x_4656_);
                        v___x_4661_ = leanh::lean_box(0);
                        v_isShared_4662_ = v_isSharedCheck_4666_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_4662_ == 0 {
                    v___x_4664_ = v___x_4661_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4665_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4659_);
                    v___x_4664_ = v_reuseFailAlloc_4665_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4664_;
            }
            22 => {
                if v_isShared_4682_ == 0 {
                    v___x_4684_ = v___x_4681_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
                    v___x_4684_ = v_reuseFailAlloc_4685_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_rwMatcher___lam__4___boxed(
    mut v___x_4694_: *mut leanh::LeanObject,
    mut v___x_4695_: *mut leanh::LeanObject,
    mut v_fst_4696_: *mut leanh::LeanObject,
    mut v___x_4697_: *mut leanh::LeanObject,
    mut v___x_4698_: *mut leanh::LeanObject,
    mut v_e_4699_: *mut leanh::LeanObject,
    mut v_snd_4700_: *mut leanh::LeanObject,
    mut v_____r_4701_: *mut leanh::LeanObject,
    mut v___y_4702_: *mut leanh::LeanObject,
    mut v___y_4703_: *mut leanh::LeanObject,
    mut v___y_4704_: *mut leanh::LeanObject,
    mut v___y_4705_: *mut leanh::LeanObject,
    mut v___y_4706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_109778__boxed_4707_: u8 = 0;
    let mut v___x_109782__boxed_4708_: u8 = 0;
    let mut v_res_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_109778__boxed_4707_ = (leanh::lean_unbox(v___x_4694_) as u8);
    v___x_109782__boxed_4708_ = (leanh::lean_unbox(v___x_4698_) as u8);
    v_res_4709_ = l_Lean_Meta_rwMatcher___lam__4(
        v___x_109778__boxed_4707_,
        v___x_4695_,
        v_fst_4696_,
        v___x_4697_,
        v___x_109782__boxed_4708_,
        v_e_4699_,
        v_snd_4700_,
        v_____r_4701_,
        v___y_4702_,
        v___y_4703_,
        v___y_4704_,
        v___y_4705_,
    );
    leanh::lean_dec(v___y_4705_);
    leanh::lean_dec_ref(v___y_4704_);
    leanh::lean_dec(v___y_4703_);
    leanh::lean_dec_ref(v___y_4702_);
    leanh::lean_dec_ref(v_snd_4700_);
    return v_res_4709_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0() -> f64 {
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: f64 = 0.0;
    v___x_4710_ = leanh::lean_unsigned_to_nat(0);
    v___x_4711_ = lean_float_of_nat(v___x_4710_);
    return v___x_4711_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(
    mut v_cls_4715_: *mut leanh::LeanObject,
    mut v_msg_4716_: *mut leanh::LeanObject,
    mut v___y_4717_: *mut leanh::LeanObject,
    mut v___y_4718_: *mut leanh::LeanObject,
    mut v___y_4719_: *mut leanh::LeanObject,
    mut v___y_4720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4740_: u8 = 0;
    let mut v_tid_4741_: u64 = 0;
    let mut v_traces_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4745_: u8 = 0;
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: f64 = 0.0;
    let mut v___x_4748_: u8 = 0;
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4766_: u8 = 0;
    let mut v_isSharedCheck_4767_: u8 = 0;
    let mut v_isSharedCheck_4768_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4722_ = leanh::lean_ctor_get(v___y_4719_, 5);
                v___x_4723_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
                v_a_4724_ = leanh::lean_ctor_get(v___x_4723_, 0);
                v_isSharedCheck_4768_ = (!leanh::lean_is_exclusive(v___x_4723_)) as u8;
                if v_isSharedCheck_4768_ == 0 {
                    v___x_4726_ = v___x_4723_;
                    v_isShared_4727_ = v_isSharedCheck_4768_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4724_);
                    leanh::lean_dec(v___x_4723_);
                    v___x_4726_ = leanh::lean_box(0);
                    v_isShared_4727_ = v_isSharedCheck_4768_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4728_ = lean_st_ref_take(v___y_4720_);
                v_traceState_4729_ = leanh::lean_ctor_get(v___x_4728_, 4);
                v_env_4730_ = leanh::lean_ctor_get(v___x_4728_, 0);
                v_nextMacroScope_4731_ = leanh::lean_ctor_get(v___x_4728_, 1);
                v_ngen_4732_ = leanh::lean_ctor_get(v___x_4728_, 2);
                v_auxDeclNGen_4733_ = leanh::lean_ctor_get(v___x_4728_, 3);
                v_cache_4734_ = leanh::lean_ctor_get(v___x_4728_, 5);
                v_messages_4735_ = leanh::lean_ctor_get(v___x_4728_, 6);
                v_infoState_4736_ = leanh::lean_ctor_get(v___x_4728_, 7);
                v_snapshotTasks_4737_ = leanh::lean_ctor_get(v___x_4728_, 8);
                v_isSharedCheck_4767_ = (!leanh::lean_is_exclusive(v___x_4728_)) as u8;
                if v_isSharedCheck_4767_ == 0 {
                    v___x_4739_ = v___x_4728_;
                    v_isShared_4740_ = v_isSharedCheck_4767_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4737_);
                    leanh::lean_inc(v_infoState_4736_);
                    leanh::lean_inc(v_messages_4735_);
                    leanh::lean_inc(v_cache_4734_);
                    leanh::lean_inc(v_traceState_4729_);
                    leanh::lean_inc(v_auxDeclNGen_4733_);
                    leanh::lean_inc(v_ngen_4732_);
                    leanh::lean_inc(v_nextMacroScope_4731_);
                    leanh::lean_inc(v_env_4730_);
                    leanh::lean_dec(v___x_4728_);
                    v___x_4739_ = leanh::lean_box(0);
                    v_isShared_4740_ = v_isSharedCheck_4767_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4741_ = leanh::lean_ctor_get_uint64(
                    v_traceState_4729_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4742_ = leanh::lean_ctor_get(v_traceState_4729_, 0);
                v_isSharedCheck_4766_ =
                    (!leanh::lean_is_exclusive(v_traceState_4729_)) as u8;
                if v_isSharedCheck_4766_ == 0 {
                    v___x_4744_ = v_traceState_4729_;
                    v_isShared_4745_ = v_isSharedCheck_4766_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_4742_);
                    leanh::lean_dec(v_traceState_4729_);
                    v___x_4744_ = leanh::lean_box(0);
                    v_isShared_4745_ = v_isSharedCheck_4766_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4746_ = leanh::lean_box(0);
                v___x_4747_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once
                    ),
                    _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0,
                );
                v___x_4748_ = 0;
                v___x_4749_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1;
                v___x_4750_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_4750_, 0, v_cls_4715_);
                leanh::lean_ctor_set(v___x_4750_, 1, v___x_4746_);
                leanh::lean_ctor_set(v___x_4750_, 2, v___x_4749_);
                leanh::lean_ctor_set_float(
                    v___x_4750_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4747_,
                );
                leanh::lean_ctor_set_float(
                    v___x_4750_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4747_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4750_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4748_,
                );
                v___x_4751_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2;
                v___x_4752_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4752_, 0, v___x_4750_);
                leanh::lean_ctor_set(v___x_4752_, 1, v_a_4724_);
                leanh::lean_ctor_set(v___x_4752_, 2, v___x_4751_);
                leanh::lean_inc(v_ref_4722_);
                v___x_4753_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4753_, 0, v_ref_4722_);
                leanh::lean_ctor_set(v___x_4753_, 1, v___x_4752_);
                v___x_4754_ = l_Lean_PersistentArray_push___redArg(v_traces_4742_, v___x_4753_);
                if v_isShared_4745_ == 0 {
                    leanh::lean_ctor_set(v___x_4744_, 0, v___x_4754_);
                    v___x_4756_ = v___x_4744_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4765_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4754_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4765_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_4741_,
                    );
                    v___x_4756_ = v_reuseFailAlloc_4765_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4740_ == 0 {
                    leanh::lean_ctor_set(v___x_4739_, 4, v___x_4756_);
                    v___x_4758_ = v___x_4739_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4764_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_env_4730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 1, v_nextMacroScope_4731_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 2, v_ngen_4732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 3, v_auxDeclNGen_4733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 4, v___x_4756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 5, v_cache_4734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 6, v_messages_4735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 7, v_infoState_4736_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 8, v_snapshotTasks_4737_);
                    v___x_4758_ = v_reuseFailAlloc_4764_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4759_ = lean_st_ref_set(v___y_4720_, v___x_4758_);
                v___x_4760_ = leanh::lean_box(0);
                if v_isShared_4727_ == 0 {
                    leanh::lean_ctor_set(v___x_4726_, 0, v___x_4760_);
                    v___x_4762_ = v___x_4726_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4763_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4763_, 0, v___x_4760_);
                    v___x_4762_ = v_reuseFailAlloc_4763_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4762_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(
    mut v_cls_4769_: *mut leanh::LeanObject,
    mut v_msg_4770_: *mut leanh::LeanObject,
    mut v___y_4771_: *mut leanh::LeanObject,
    mut v___y_4772_: *mut leanh::LeanObject,
    mut v___y_4773_: *mut leanh::LeanObject,
    mut v___y_4774_: *mut leanh::LeanObject,
    mut v___y_4775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4776_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(
        v_cls_4769_,
        v_msg_4770_,
        v___y_4771_,
        v___y_4772_,
        v___y_4773_,
        v___y_4774_,
    );
    leanh::lean_dec(v___y_4774_);
    leanh::lean_dec_ref(v___y_4773_);
    leanh::lean_dec(v___y_4772_);
    leanh::lean_dec_ref(v___y_4771_);
    return v_res_4776_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(
    mut v_as_4777_: *mut leanh::LeanObject,
    mut v_i_4778_: usize,
    mut v_stop_4779_: usize,
    mut v_b_4780_: *mut leanh::LeanObject,
    mut v___y_4781_: *mut leanh::LeanObject,
    mut v___y_4782_: *mut leanh::LeanObject,
    mut v___y_4783_: *mut leanh::LeanObject,
    mut v___y_4784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: usize = 0;
    let mut v___x_4789_: usize = 0;
    let mut v___x_4791_: u8 = 0;
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: u8 = 0;
    let mut v_a_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: u8 = 0;
    let mut v_a_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4803_: u8 = 0;
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4807_: u8 = 0;
    let mut v___x_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4791_ = lean_usize_dec_eq(v_i_4778_, v_stop_4779_);
                if v___x_4791_ == 0 {
                    v___x_4792_ = lean_array_uget_borrowed(v_as_4777_, v_i_4778_);
                    v___x_4795_ =
                        l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(
                            v___x_4792_,
                            v___y_4782_,
                        );
                    if leanh::lean_obj_tag(v___x_4795_) == 0 {
                        v_a_4796_ = leanh::lean_ctor_get(v___x_4795_, 0);
                        leanh::lean_inc(v_a_4796_);
                        leanh::lean_dec_ref_known(v___x_4795_, 1);
                        v___x_4797_ = (leanh::lean_unbox(v_a_4796_) as u8);
                        leanh::lean_dec(v_a_4796_);
                        if v___x_4797_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_4787_ = v_b_4780_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_4795_) == 0 {
                            v_a_4798_ = leanh::lean_ctor_get(v___x_4795_, 0);
                            leanh::lean_inc(v_a_4798_);
                            leanh::lean_dec_ref_known(v___x_4795_, 1);
                            v___x_4799_ = (leanh::lean_unbox(v_a_4798_) as u8);
                            leanh::lean_dec(v_a_4798_);
                            if v___x_4799_ == 0 {
                                v_a_4787_ = v_b_4780_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_4780_);
                            v_a_4800_ = leanh::lean_ctor_get(v___x_4795_, 0);
                            v_isSharedCheck_4807_ =
                                (!leanh::lean_is_exclusive(v___x_4795_)) as u8;
                            if v_isSharedCheck_4807_ == 0 {
                                v___x_4802_ = v___x_4795_;
                                v_isShared_4803_ = v_isSharedCheck_4807_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4800_);
                                leanh::lean_dec(v___x_4795_);
                                v___x_4802_ = leanh::lean_box(0);
                                v_isShared_4803_ = v_isSharedCheck_4807_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_4808_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4808_, 0, v_b_4780_);
                    return v___x_4808_;
                }
            }
            1 => {
                v___x_4788_ = 1usize;
                v___x_4789_ = lean_usize_add(v_i_4778_, v___x_4788_);
                v_i_4778_ = v___x_4789_;
                v_b_4780_ = v_a_4787_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v___x_4792_);
                v___x_4794_ = lean_array_push(v_b_4780_, v___x_4792_);
                v_a_4787_ = v___x_4794_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_4803_ == 0 {
                    v___x_4805_ = v___x_4802_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
                    v___x_4805_ = v_reuseFailAlloc_4806_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4805_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8___boxed(
    mut v_as_4809_: *mut leanh::LeanObject,
    mut v_i_4810_: *mut leanh::LeanObject,
    mut v_stop_4811_: *mut leanh::LeanObject,
    mut v_b_4812_: *mut leanh::LeanObject,
    mut v___y_4813_: *mut leanh::LeanObject,
    mut v___y_4814_: *mut leanh::LeanObject,
    mut v___y_4815_: *mut leanh::LeanObject,
    mut v___y_4816_: *mut leanh::LeanObject,
    mut v___y_4817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4818_: usize = 0;
    let mut v_stop_boxed_4819_: usize = 0;
    let mut v_res_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4818_ = leanh::lean_unbox_usize(v_i_4810_);
    leanh::lean_dec(v_i_4810_);
    v_stop_boxed_4819_ = leanh::lean_unbox_usize(v_stop_4811_);
    leanh::lean_dec(v_stop_4811_);
    v_res_4820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v_as_4809_, v_i_boxed_4818_, v_stop_boxed_4819_, v_b_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
    leanh::lean_dec(v___y_4816_);
    leanh::lean_dec_ref(v___y_4815_);
    leanh::lean_dec(v___y_4814_);
    leanh::lean_dec_ref(v___y_4813_);
    leanh::lean_dec_ref(v_as_4809_);
    return v_res_4820_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16(
    mut v_sz_4821_: usize,
    mut v_i_4822_: usize,
    mut v_bs_4823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4824_: u8 = 0;
    let mut v_v_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: usize = 0;
    let mut v___x_4830_: usize = 0;
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4824_ = lean_usize_dec_lt(v_i_4822_, v_sz_4821_);
                if v___x_4824_ == 0 {
                    return v_bs_4823_;
                } else {
                    v_v_4825_ = lean_array_uget_borrowed(v_bs_4823_, v_i_4822_);
                    v_msg_4826_ = leanh::lean_ctor_get(v_v_4825_, 1);
                    leanh::lean_inc_ref(v_msg_4826_);
                    v___x_4827_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4828_ = lean_array_uset(v_bs_4823_, v_i_4822_, v___x_4827_);
                    v___x_4829_ = 1usize;
                    v___x_4830_ = lean_usize_add(v_i_4822_, v___x_4829_);
                    v___x_4831_ = lean_array_uset(v_bs_x27_4828_, v_i_4822_, v_msg_4826_);
                    v_i_4822_ = v___x_4830_;
                    v_bs_4823_ = v___x_4831_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16___boxed(
    mut v_sz_4833_: *mut leanh::LeanObject,
    mut v_i_4834_: *mut leanh::LeanObject,
    mut v_bs_4835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4836_: usize = 0;
    let mut v_i_boxed_4837_: usize = 0;
    let mut v_res_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4836_ = leanh::lean_unbox_usize(v_sz_4833_);
    leanh::lean_dec(v_sz_4833_);
    v_i_boxed_4837_ = leanh::lean_unbox_usize(v_i_4834_);
    leanh::lean_dec(v_i_4834_);
    v_res_4838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16(v_sz_boxed_4836_, v_i_boxed_4837_, v_bs_4835_);
    return v_res_4838_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(
    mut v_oldTraces_4839_: *mut leanh::LeanObject,
    mut v_data_4840_: *mut leanh::LeanObject,
    mut v_ref_4841_: *mut leanh::LeanObject,
    mut v_msg_4842_: *mut leanh::LeanObject,
    mut v___y_4843_: *mut leanh::LeanObject,
    mut v___y_4844_: *mut leanh::LeanObject,
    mut v___y_4845_: *mut leanh::LeanObject,
    mut v___y_4846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4860_: u8 = 0;
    let mut v_cancelTk_x3f_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4862_: u8 = 0;
    let mut v_inheritedTraceOptions_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4870_: usize = 0;
    let mut v___x_4871_: usize = 0;
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4878_: u8 = 0;
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4891_: u8 = 0;
    let mut v_tid_4892_: u64 = 0;
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4895_: u8 = 0;
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4909_: u8 = 0;
    let mut v_unused_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4911_: u8 = 0;
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4848_ = leanh::lean_ctor_get(v___y_4845_, 0);
                v_fileMap_4849_ = leanh::lean_ctor_get(v___y_4845_, 1);
                v_options_4850_ = leanh::lean_ctor_get(v___y_4845_, 2);
                v_currRecDepth_4851_ = leanh::lean_ctor_get(v___y_4845_, 3);
                v_maxRecDepth_4852_ = leanh::lean_ctor_get(v___y_4845_, 4);
                v_ref_4853_ = leanh::lean_ctor_get(v___y_4845_, 5);
                v_currNamespace_4854_ = leanh::lean_ctor_get(v___y_4845_, 6);
                v_openDecls_4855_ = leanh::lean_ctor_get(v___y_4845_, 7);
                v_initHeartbeats_4856_ = leanh::lean_ctor_get(v___y_4845_, 8);
                v_maxHeartbeats_4857_ = leanh::lean_ctor_get(v___y_4845_, 9);
                v_quotContext_4858_ = leanh::lean_ctor_get(v___y_4845_, 10);
                v_currMacroScope_4859_ = leanh::lean_ctor_get(v___y_4845_, 11);
                v_diag_4860_ = leanh::lean_ctor_get_uint8(
                    v___y_4845_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4861_ = leanh::lean_ctor_get(v___y_4845_, 12);
                v_suppressElabErrors_4862_ = leanh::lean_ctor_get_uint8(
                    v___y_4845_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4863_ = leanh::lean_ctor_get(v___y_4845_, 13);
                v___x_4864_ = lean_st_ref_get(v___y_4846_);
                v_traceState_4865_ = leanh::lean_ctor_get(v___x_4864_, 4);
                leanh::lean_inc_ref(v_traceState_4865_);
                leanh::lean_dec(v___x_4864_);
                v_traces_4866_ = leanh::lean_ctor_get(v_traceState_4865_, 0);
                leanh::lean_inc_ref(v_traces_4866_);
                leanh::lean_dec_ref(v_traceState_4865_);
                v_ref_4867_ = l_Lean_replaceRef(v_ref_4841_, v_ref_4853_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_4863_);
                leanh::lean_inc(v_cancelTk_x3f_4861_);
                leanh::lean_inc(v_currMacroScope_4859_);
                leanh::lean_inc(v_quotContext_4858_);
                leanh::lean_inc(v_maxHeartbeats_4857_);
                leanh::lean_inc(v_initHeartbeats_4856_);
                leanh::lean_inc(v_openDecls_4855_);
                leanh::lean_inc(v_currNamespace_4854_);
                leanh::lean_inc(v_maxRecDepth_4852_);
                leanh::lean_inc(v_currRecDepth_4851_);
                leanh::lean_inc_ref(v_options_4850_);
                leanh::lean_inc_ref(v_fileMap_4849_);
                leanh::lean_inc_ref(v_fileName_4848_);
                v___x_4868_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_4868_, 0, v_fileName_4848_);
                leanh::lean_ctor_set(v___x_4868_, 1, v_fileMap_4849_);
                leanh::lean_ctor_set(v___x_4868_, 2, v_options_4850_);
                leanh::lean_ctor_set(v___x_4868_, 3, v_currRecDepth_4851_);
                leanh::lean_ctor_set(v___x_4868_, 4, v_maxRecDepth_4852_);
                leanh::lean_ctor_set(v___x_4868_, 5, v_ref_4867_);
                leanh::lean_ctor_set(v___x_4868_, 6, v_currNamespace_4854_);
                leanh::lean_ctor_set(v___x_4868_, 7, v_openDecls_4855_);
                leanh::lean_ctor_set(v___x_4868_, 8, v_initHeartbeats_4856_);
                leanh::lean_ctor_set(v___x_4868_, 9, v_maxHeartbeats_4857_);
                leanh::lean_ctor_set(v___x_4868_, 10, v_quotContext_4858_);
                leanh::lean_ctor_set(v___x_4868_, 11, v_currMacroScope_4859_);
                leanh::lean_ctor_set(v___x_4868_, 12, v_cancelTk_x3f_4861_);
                leanh::lean_ctor_set(v___x_4868_, 13, v_inheritedTraceOptions_4863_);
                leanh::lean_ctor_set_uint8(
                    v___x_4868_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_4860_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4868_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4862_,
                );
                v___x_4869_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4866_);
                leanh::lean_dec_ref(v_traces_4866_);
                v_sz_4870_ = lean_array_size(v___x_4869_);
                v___x_4871_ = 0usize;
                v___x_4872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16(v_sz_4870_, v___x_4871_, v___x_4869_);
                v_msg_4873_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v_msg_4873_, 0, v_data_4840_);
                leanh::lean_ctor_set(v_msg_4873_, 1, v_msg_4842_);
                leanh::lean_ctor_set(v_msg_4873_, 2, v___x_4872_);
                v___x_4874_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_4873_, v___y_4843_, v___y_4844_, v___x_4868_, v___y_4846_);
                leanh::lean_dec_ref_known(v___x_4868_, 14);
                v_a_4875_ = leanh::lean_ctor_get(v___x_4874_, 0);
                v_isSharedCheck_4912_ = (!leanh::lean_is_exclusive(v___x_4874_)) as u8;
                if v_isSharedCheck_4912_ == 0 {
                    v___x_4877_ = v___x_4874_;
                    v_isShared_4878_ = v_isSharedCheck_4912_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4875_);
                    leanh::lean_dec(v___x_4874_);
                    v___x_4877_ = leanh::lean_box(0);
                    v_isShared_4878_ = v_isSharedCheck_4912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4879_ = lean_st_ref_take(v___y_4846_);
                v_traceState_4880_ = leanh::lean_ctor_get(v___x_4879_, 4);
                v_env_4881_ = leanh::lean_ctor_get(v___x_4879_, 0);
                v_nextMacroScope_4882_ = leanh::lean_ctor_get(v___x_4879_, 1);
                v_ngen_4883_ = leanh::lean_ctor_get(v___x_4879_, 2);
                v_auxDeclNGen_4884_ = leanh::lean_ctor_get(v___x_4879_, 3);
                v_cache_4885_ = leanh::lean_ctor_get(v___x_4879_, 5);
                v_messages_4886_ = leanh::lean_ctor_get(v___x_4879_, 6);
                v_infoState_4887_ = leanh::lean_ctor_get(v___x_4879_, 7);
                v_snapshotTasks_4888_ = leanh::lean_ctor_get(v___x_4879_, 8);
                v_isSharedCheck_4911_ = (!leanh::lean_is_exclusive(v___x_4879_)) as u8;
                if v_isSharedCheck_4911_ == 0 {
                    v___x_4890_ = v___x_4879_;
                    v_isShared_4891_ = v_isSharedCheck_4911_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4888_);
                    leanh::lean_inc(v_infoState_4887_);
                    leanh::lean_inc(v_messages_4886_);
                    leanh::lean_inc(v_cache_4885_);
                    leanh::lean_inc(v_traceState_4880_);
                    leanh::lean_inc(v_auxDeclNGen_4884_);
                    leanh::lean_inc(v_ngen_4883_);
                    leanh::lean_inc(v_nextMacroScope_4882_);
                    leanh::lean_inc(v_env_4881_);
                    leanh::lean_dec(v___x_4879_);
                    v___x_4890_ = leanh::lean_box(0);
                    v_isShared_4891_ = v_isSharedCheck_4911_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4892_ = leanh::lean_ctor_get_uint64(
                    v_traceState_4880_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4909_ =
                    (!leanh::lean_is_exclusive(v_traceState_4880_)) as u8;
                if v_isSharedCheck_4909_ == 0 {
                    v_unused_4910_ = leanh::lean_ctor_get(v_traceState_4880_, 0);
                    leanh::lean_dec(v_unused_4910_);
                    v___x_4894_ = v_traceState_4880_;
                    v_isShared_4895_ = v_isSharedCheck_4909_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_4880_);
                    v___x_4894_ = leanh::lean_box(0);
                    v_isShared_4895_ = v_isSharedCheck_4909_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4896_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4896_, 0, v_ref_4841_);
                leanh::lean_ctor_set(v___x_4896_, 1, v_a_4875_);
                v___x_4897_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4839_, v___x_4896_);
                if v_isShared_4895_ == 0 {
                    leanh::lean_ctor_set(v___x_4894_, 0, v___x_4897_);
                    v___x_4899_ = v___x_4894_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4908_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4897_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4908_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_4892_,
                    );
                    v___x_4899_ = v_reuseFailAlloc_4908_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4891_ == 0 {
                    leanh::lean_ctor_set(v___x_4890_, 4, v___x_4899_);
                    v___x_4901_ = v___x_4890_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4907_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_env_4881_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 1, v_nextMacroScope_4882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 2, v_ngen_4883_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 3, v_auxDeclNGen_4884_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 4, v___x_4899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 5, v_cache_4885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 6, v_messages_4886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 7, v_infoState_4887_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4907_, 8, v_snapshotTasks_4888_);
                    v___x_4901_ = v_reuseFailAlloc_4907_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4902_ = lean_st_ref_set(v___y_4846_, v___x_4901_);
                v___x_4903_ = leanh::lean_box(0);
                if v_isShared_4878_ == 0 {
                    leanh::lean_ctor_set(v___x_4877_, 0, v___x_4903_);
                    v___x_4905_ = v___x_4877_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4906_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4903_);
                    v___x_4905_ = v_reuseFailAlloc_4906_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___boxed(
    mut v_oldTraces_4913_: *mut leanh::LeanObject,
    mut v_data_4914_: *mut leanh::LeanObject,
    mut v_ref_4915_: *mut leanh::LeanObject,
    mut v_msg_4916_: *mut leanh::LeanObject,
    mut v___y_4917_: *mut leanh::LeanObject,
    mut v___y_4918_: *mut leanh::LeanObject,
    mut v___y_4919_: *mut leanh::LeanObject,
    mut v___y_4920_: *mut leanh::LeanObject,
    mut v___y_4921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4922_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_oldTraces_4913_, v_data_4914_, v_ref_4915_, v_msg_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
    leanh::lean_dec(v___y_4920_);
    leanh::lean_dec_ref(v___y_4919_);
    leanh::lean_dec(v___y_4918_);
    leanh::lean_dec_ref(v___y_4917_);
    return v_res_4922_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(
    mut v_opts_4923_: *mut leanh::LeanObject,
    mut v_opt_4924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4925_ = leanh::lean_ctor_get(v_opt_4924_, 0);
    v_defValue_4926_ = leanh::lean_ctor_get(v_opt_4924_, 1);
    v_map_4927_ = leanh::lean_ctor_get(v_opts_4923_, 0);
    v___x_4928_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4927_,
            v_name_4925_,
        );
    if leanh::lean_obj_tag(v___x_4928_) == 0 {
        leanh::lean_inc(v_defValue_4926_);
        return v_defValue_4926_;
    } else {
        let mut v_val_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4929_ = leanh::lean_ctor_get(v___x_4928_, 0);
        leanh::lean_inc(v_val_4929_);
        leanh::lean_dec_ref_known(v___x_4928_, 1);
        if leanh::lean_obj_tag(v_val_4929_) == 3 {
            let mut v_v_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_4930_ = leanh::lean_ctor_get(v_val_4929_, 0);
            leanh::lean_inc(v_v_4930_);
            leanh::lean_dec_ref_known(v_val_4929_, 1);
            return v_v_4930_;
        } else {
            leanh::lean_dec(v_val_4929_);
            leanh::lean_inc(v_defValue_4926_);
            return v_defValue_4926_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(
    mut v_opts_4931_: *mut leanh::LeanObject,
    mut v_opt_4932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4933_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_4931_, v_opt_4932_);
    leanh::lean_dec_ref(v_opt_4932_);
    leanh::lean_dec_ref(v_opts_4931_);
    return v_res_4933_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(
    mut v_x_4934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4939_: u8 = 0;
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4943_: u8 = 0;
    let mut v_a_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4947_: u8 = 0;
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4934_) == 0 {
                    v_a_4936_ = leanh::lean_ctor_get(v_x_4934_, 0);
                    v_isSharedCheck_4943_ = (!leanh::lean_is_exclusive(v_x_4934_)) as u8;
                    if v_isSharedCheck_4943_ == 0 {
                        v___x_4938_ = v_x_4934_;
                        v_isShared_4939_ = v_isSharedCheck_4943_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4936_);
                        leanh::lean_dec(v_x_4934_);
                        v___x_4938_ = leanh::lean_box(0);
                        v_isShared_4939_ = v_isSharedCheck_4943_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4944_ = leanh::lean_ctor_get(v_x_4934_, 0);
                    v_isSharedCheck_4951_ = (!leanh::lean_is_exclusive(v_x_4934_)) as u8;
                    if v_isSharedCheck_4951_ == 0 {
                        v___x_4946_ = v_x_4934_;
                        v_isShared_4947_ = v_isSharedCheck_4951_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4944_);
                        leanh::lean_dec(v_x_4934_);
                        v___x_4946_ = leanh::lean_box(0);
                        v_isShared_4947_ = v_isSharedCheck_4951_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4939_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4938_, 1);
                    v___x_4941_ = v___x_4938_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4942_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4936_);
                    v___x_4941_ = v_reuseFailAlloc_4942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4941_;
            }
            3 => {
                if v_isShared_4947_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4946_, 0);
                    v___x_4949_ = v___x_4946_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4950_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_a_4944_);
                    v___x_4949_ = v_reuseFailAlloc_4950_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg___boxed(
    mut v_x_4952_: *mut leanh::LeanObject,
    mut v___y_4953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4954_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_x_4952_);
    return v_res_4954_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(
    mut v_e_4955_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_e_4955_) == 0 {
        let mut v___x_4956_: u8 = 0;
        v___x_4956_ = 2;
        return v___x_4956_;
    } else {
        let mut v___x_4957_: u8 = 0;
        v___x_4957_ = 0;
        return v___x_4957_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13___boxed(
    mut v_e_4958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4959_: u8 = 0;
    let mut v_r_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4959_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_e_4958_);
    leanh::lean_dec_ref(v_e_4958_);
    v_r_4960_ = leanh::lean_box((v_res_4959_) as usize);
    return v_r_4960_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4962_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0;
    v___x_4963_ = l_Lean_stringToMessageData(v___x_4962_);
    return v___x_4963_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2()
-> f64 {
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: f64 = 0.0;
    v___x_4964_ = leanh::lean_unsigned_to_nat(1000);
    v___x_4965_ = lean_float_of_nat(v___x_4964_);
    return v___x_4965_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(
    mut v_cls_4966_: *mut leanh::LeanObject,
    mut v_collapsed_4967_: u8,
    mut v_tag_4968_: *mut leanh::LeanObject,
    mut v_opts_4969_: *mut leanh::LeanObject,
    mut v_clsEnabled_4970_: u8,
    mut v_oldTraces_4971_: *mut leanh::LeanObject,
    mut v_msg_4972_: *mut leanh::LeanObject,
    mut v_resStartStop_4973_: *mut leanh::LeanObject,
    mut v___y_4974_: *mut leanh::LeanObject,
    mut v___y_4975_: *mut leanh::LeanObject,
    mut v___y_4976_: *mut leanh::LeanObject,
    mut v___y_4977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4983_: u8 = 0;
    let mut v___y_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4993_: u8 = 0;
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4997_: u8 = 0;
    let mut v_fst_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5002_: u8 = 0;
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: u8 = 0;
    let mut v___y_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5008_: u8 = 0;
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: f64 = 0.0;
    let mut v_data_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: f64 = 0.0;
    let mut v___x_5022_: f64 = 0.0;
    let mut v_reuseFailAlloc_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5031_: u8 = 0;
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5044_: u8 = 0;
    let mut v_tid_5045_: u64 = 0;
    let mut v_traces_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5049_: u8 = 0;
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut v_isSharedCheck_5060_: u8 = 0;
    let mut v___y_5062_: f64 = 0.0;
    let mut v___x_5063_: f64 = 0.0;
    let mut v___x_5064_: f64 = 0.0;
    let mut v___x_5065_: f64 = 0.0;
    let mut v___x_5066_: u8 = 0;
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: u8 = 0;
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: f64 = 0.0;
    let mut v___x_5072_: f64 = 0.0;
    let mut v___x_5073_: f64 = 0.0;
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: f64 = 0.0;
    let mut v_isSharedCheck_5077_: u8 = 0;
    let mut v_isSharedCheck_5078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4979_ = leanh::lean_ctor_get(v_resStartStop_4973_, 0);
                v_snd_4980_ = leanh::lean_ctor_get(v_resStartStop_4973_, 1);
                v_isSharedCheck_5078_ =
                    (!leanh::lean_is_exclusive(v_resStartStop_4973_)) as u8;
                if v_isSharedCheck_5078_ == 0 {
                    v___x_4982_ = v_resStartStop_4973_;
                    v_isShared_4983_ = v_isSharedCheck_5078_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4980_);
                    leanh::lean_inc(v_fst_4979_);
                    leanh::lean_dec(v_resStartStop_4973_);
                    v___x_4982_ = leanh::lean_box(0);
                    v_isShared_4983_ = v_isSharedCheck_5078_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_4998_ = leanh::lean_ctor_get(v_snd_4980_, 0);
                v_snd_4999_ = leanh::lean_ctor_get(v_snd_4980_, 1);
                v_isSharedCheck_5077_ = (!leanh::lean_is_exclusive(v_snd_4980_)) as u8;
                if v_isSharedCheck_5077_ == 0 {
                    v___x_5001_ = v_snd_4980_;
                    v_isShared_5002_ = v_isSharedCheck_5077_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4999_);
                    leanh::lean_inc(v_fst_4998_);
                    leanh::lean_dec(v_snd_4980_);
                    v___x_5001_ = leanh::lean_box(0);
                    v_isShared_5002_ = v_isSharedCheck_5077_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_4986_);
                v___x_4988_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_oldTraces_4971_, v_data_4987_, v___y_4986_, v___y_4985_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
                if leanh::lean_obj_tag(v___x_4988_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4988_, 1);
                    v___x_4989_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_fst_4979_);
                    return v___x_4989_;
                } else {
                    leanh::lean_dec(v_fst_4979_);
                    v_a_4990_ = leanh::lean_ctor_get(v___x_4988_, 0);
                    v_isSharedCheck_4997_ = (!leanh::lean_is_exclusive(v___x_4988_)) as u8;
                    if v_isSharedCheck_4997_ == 0 {
                        v___x_4992_ = v___x_4988_;
                        v_isShared_4993_ = v_isSharedCheck_4997_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4990_);
                        leanh::lean_dec(v___x_4988_);
                        v___x_4992_ = leanh::lean_box(0);
                        v_isShared_4993_ = v_isSharedCheck_4997_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4993_ == 0 {
                    v___x_4995_ = v___x_4992_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4996_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
                    v___x_4995_ = v_reuseFailAlloc_4996_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4995_;
            }
            5 => {
                v___x_5003_ = l_Lean_trace_profiler;
                v___x_5004_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(
                    v_opts_4969_,
                    v___x_5003_,
                );
                if v___x_5004_ == 0 {
                    v___y_5031_ = v___x_5004_;
                    state = 10;
                    continue;
                } else {
                    v___x_5067_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_5068_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(
                        v_opts_4969_,
                        v___x_5067_,
                    );
                    if v___x_5068_ == 0 {
                        v___x_5069_ = l_Lean_trace_profiler_threshold;
                        v___x_5070_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_4969_, v___x_5069_);
                        v___x_5071_ = lean_float_of_nat(v___x_5070_);
                        v___x_5072_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2);
                        v___x_5073_ = lean_float_div(v___x_5071_, v___x_5072_);
                        v___y_5062_ = v___x_5073_;
                        state = 15;
                        continue;
                    } else {
                        v___x_5074_ = l_Lean_trace_profiler_threshold;
                        v___x_5075_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_4969_, v___x_5074_);
                        v___x_5076_ = lean_float_of_nat(v___x_5075_);
                        v___y_5062_ = v___x_5076_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_5008_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_fst_4979_);
                v___x_5009_ = l_Lean_TraceResult_toEmoji(v_result_5008_);
                v___x_5010_ = l_Lean_stringToMessageData(v___x_5009_);
                v___x_5011_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__5_once),
                    _init_l_Lean_Meta_rwMatcher___lam__2___closed__5,
                );
                if v_isShared_5002_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5001_, 7);
                    leanh::lean_ctor_set(v___x_5001_, 1, v___x_5011_);
                    leanh::lean_ctor_set(v___x_5001_, 0, v___x_5010_);
                    v___x_5013_ = v___x_5001_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5024_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5024_, 0, v___x_5010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5024_, 1, v___x_5011_);
                    v___x_5013_ = v_reuseFailAlloc_5024_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4983_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4982_, 7);
                    leanh::lean_ctor_set(v___x_4982_, 1, v_a_5007_);
                    leanh::lean_ctor_set(v___x_4982_, 0, v___x_5013_);
                    v_m_5015_ = v___x_4982_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5023_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 0, v___x_5013_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 1, v_a_5007_);
                    v_m_5015_ = v_reuseFailAlloc_5023_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5016_ = leanh::lean_box((v_result_5008_) as usize);
                v___x_5017_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5017_, 0, v___x_5016_);
                v___x_5018_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once
                    ),
                    _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0,
                );
                leanh::lean_inc_ref(v_tag_4968_);
                leanh::lean_inc_ref(v___x_5017_);
                leanh::lean_inc(v_cls_4966_);
                v_data_5019_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v_data_5019_, 0, v_cls_4966_);
                leanh::lean_ctor_set(v_data_5019_, 1, v___x_5017_);
                leanh::lean_ctor_set(v_data_5019_, 2, v_tag_4968_);
                leanh::lean_ctor_set_float(
                    v_data_5019_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_5018_,
                );
                leanh::lean_ctor_set_float(
                    v_data_5019_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5018_,
                );
                leanh::lean_ctor_set_uint8(
                    v_data_5019_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_4967_,
                );
                if v___x_5004_ == 0 {
                    leanh::lean_dec_ref_known(v___x_5017_, 1);
                    leanh::lean_dec(v_snd_4999_);
                    leanh::lean_dec(v_fst_4998_);
                    leanh::lean_dec_ref(v_tag_4968_);
                    leanh::lean_dec(v_cls_4966_);
                    v___y_4985_ = v_m_5015_;
                    v___y_4986_ = v___y_5006_;
                    v_data_4987_ = v_data_5019_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_data_5019_, 3);
                    v_data_5020_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    leanh::lean_ctor_set(v_data_5020_, 0, v_cls_4966_);
                    leanh::lean_ctor_set(v_data_5020_, 1, v___x_5017_);
                    leanh::lean_ctor_set(v_data_5020_, 2, v_tag_4968_);
                    v___x_5021_ = leanh::lean_unbox_float(v_fst_4998_);
                    leanh::lean_dec(v_fst_4998_);
                    leanh::lean_ctor_set_float(
                        v_data_5020_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_5021_,
                    );
                    v___x_5022_ = leanh::lean_unbox_float(v_snd_4999_);
                    leanh::lean_dec(v_snd_4999_);
                    leanh::lean_ctor_set_float(
                        v_data_5020_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_5022_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_data_5020_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_4967_,
                    );
                    v___y_4985_ = v_m_5015_;
                    v___y_4986_ = v___y_5006_;
                    v_data_4987_ = v_data_5020_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_5026_ = leanh::lean_ctor_get(v___y_4976_, 5);
                leanh::lean_inc(v___y_4977_);
                leanh::lean_inc_ref(v___y_4976_);
                leanh::lean_inc(v___y_4975_);
                leanh::lean_inc_ref(v___y_4974_);
                leanh::lean_inc(v_fst_4979_);
                v___x_5027_ = leanh::lean_apply_6(
                    v_msg_4972_,
                    v_fst_4979_,
                    v___y_4974_,
                    v___y_4975_,
                    v___y_4976_,
                    v___y_4977_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5027_) == 0 {
                    v_a_5028_ = leanh::lean_ctor_get(v___x_5027_, 0);
                    leanh::lean_inc(v_a_5028_);
                    leanh::lean_dec_ref_known(v___x_5027_, 1);
                    v___y_5006_ = v_ref_5026_;
                    v_a_5007_ = v_a_5028_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_5027_, 1);
                    v___x_5029_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1);
                    v___y_5006_ = v_ref_5026_;
                    v_a_5007_ = v___x_5029_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_4970_ == 0 {
                    if v___y_5031_ == 0 {
                        leanh::lean_del_object(v___x_5001_);
                        leanh::lean_dec(v_snd_4999_);
                        leanh::lean_dec(v_fst_4998_);
                        leanh::lean_del_object(v___x_4982_);
                        leanh::lean_dec_ref(v_msg_4972_);
                        leanh::lean_dec_ref(v_tag_4968_);
                        leanh::lean_dec(v_cls_4966_);
                        v___x_5032_ = lean_st_ref_take(v___y_4977_);
                        v_traceState_5033_ = leanh::lean_ctor_get(v___x_5032_, 4);
                        v_env_5034_ = leanh::lean_ctor_get(v___x_5032_, 0);
                        v_nextMacroScope_5035_ = leanh::lean_ctor_get(v___x_5032_, 1);
                        v_ngen_5036_ = leanh::lean_ctor_get(v___x_5032_, 2);
                        v_auxDeclNGen_5037_ = leanh::lean_ctor_get(v___x_5032_, 3);
                        v_cache_5038_ = leanh::lean_ctor_get(v___x_5032_, 5);
                        v_messages_5039_ = leanh::lean_ctor_get(v___x_5032_, 6);
                        v_infoState_5040_ = leanh::lean_ctor_get(v___x_5032_, 7);
                        v_snapshotTasks_5041_ = leanh::lean_ctor_get(v___x_5032_, 8);
                        v_isSharedCheck_5060_ =
                            (!leanh::lean_is_exclusive(v___x_5032_)) as u8;
                        if v_isSharedCheck_5060_ == 0 {
                            v___x_5043_ = v___x_5032_;
                            v_isShared_5044_ = v_isSharedCheck_5060_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_5041_);
                            leanh::lean_inc(v_infoState_5040_);
                            leanh::lean_inc(v_messages_5039_);
                            leanh::lean_inc(v_cache_5038_);
                            leanh::lean_inc(v_traceState_5033_);
                            leanh::lean_inc(v_auxDeclNGen_5037_);
                            leanh::lean_inc(v_ngen_5036_);
                            leanh::lean_inc(v_nextMacroScope_5035_);
                            leanh::lean_inc(v_env_5034_);
                            leanh::lean_dec(v___x_5032_);
                            v___x_5043_ = leanh::lean_box(0);
                            v_isShared_5044_ = v_isSharedCheck_5060_;
                            state = 11;
                            continue;
                        }
                    } else {
                        state = 9;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_tid_5045_ = leanh::lean_ctor_get_uint64(
                    v_traceState_5033_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5046_ = leanh::lean_ctor_get(v_traceState_5033_, 0);
                v_isSharedCheck_5059_ =
                    (!leanh::lean_is_exclusive(v_traceState_5033_)) as u8;
                if v_isSharedCheck_5059_ == 0 {
                    v___x_5048_ = v_traceState_5033_;
                    v_isShared_5049_ = v_isSharedCheck_5059_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_5046_);
                    leanh::lean_dec(v_traceState_5033_);
                    v___x_5048_ = leanh::lean_box(0);
                    v_isShared_5049_ = v_isSharedCheck_5059_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5050_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_4971_, v_traces_5046_);
                leanh::lean_dec_ref(v_traces_5046_);
                if v_isShared_5049_ == 0 {
                    leanh::lean_ctor_set(v___x_5048_, 0, v___x_5050_);
                    v___x_5052_ = v___x_5048_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5058_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5050_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5058_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_5045_,
                    );
                    v___x_5052_ = v_reuseFailAlloc_5058_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5044_ == 0 {
                    leanh::lean_ctor_set(v___x_5043_, 4, v___x_5052_);
                    v___x_5054_ = v___x_5043_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5057_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_env_5034_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 1, v_nextMacroScope_5035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 2, v_ngen_5036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 3, v_auxDeclNGen_5037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 4, v___x_5052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 5, v_cache_5038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 6, v_messages_5039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 7, v_infoState_5040_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 8, v_snapshotTasks_5041_);
                    v___x_5054_ = v_reuseFailAlloc_5057_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_5055_ = lean_st_ref_set(v___y_4977_, v___x_5054_);
                v___x_5056_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_fst_4979_);
                return v___x_5056_;
            }
            15 => {
                v___x_5063_ = leanh::lean_unbox_float(v_snd_4999_);
                v___x_5064_ = leanh::lean_unbox_float(v_fst_4998_);
                v___x_5065_ = lean_float_sub(v___x_5063_, v___x_5064_);
                v___x_5066_ = lean_float_decLt(v___y_5062_, v___x_5065_);
                v___y_5031_ = v___x_5066_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___boxed(
    mut v_cls_5079_: *mut leanh::LeanObject,
    mut v_collapsed_5080_: *mut leanh::LeanObject,
    mut v_tag_5081_: *mut leanh::LeanObject,
    mut v_opts_5082_: *mut leanh::LeanObject,
    mut v_clsEnabled_5083_: *mut leanh::LeanObject,
    mut v_oldTraces_5084_: *mut leanh::LeanObject,
    mut v_msg_5085_: *mut leanh::LeanObject,
    mut v_resStartStop_5086_: *mut leanh::LeanObject,
    mut v___y_5087_: *mut leanh::LeanObject,
    mut v___y_5088_: *mut leanh::LeanObject,
    mut v___y_5089_: *mut leanh::LeanObject,
    mut v___y_5090_: *mut leanh::LeanObject,
    mut v___y_5091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_collapsed_boxed_5092_: u8 = 0;
    let mut v_clsEnabled_boxed_5093_: u8 = 0;
    let mut v_res_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5092_ = (leanh::lean_unbox(v_collapsed_5080_) as u8);
    v_clsEnabled_boxed_5093_ = (leanh::lean_unbox(v_clsEnabled_5083_) as u8);
    v_res_5094_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v_cls_5079_, v_collapsed_boxed_5092_, v_tag_5081_, v_opts_5082_, v_clsEnabled_boxed_5093_, v_oldTraces_5084_, v_msg_5085_, v_resStartStop_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_);
    leanh::lean_dec(v___y_5090_);
    leanh::lean_dec_ref(v___y_5089_);
    leanh::lean_dec(v___y_5088_);
    leanh::lean_dec_ref(v___y_5087_);
    leanh::lean_dec_ref(v_opts_5082_);
    return v_res_5094_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(
    mut v_a_5095_: *mut leanh::LeanObject,
    mut v___y_5096_: *mut leanh::LeanObject,
    mut v___y_5097_: *mut leanh::LeanObject,
    mut v___y_5098_: *mut leanh::LeanObject,
    mut v___y_5099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5105_: u8 = 0;
    let mut v_val_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: u8 = 0;
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5115_: u8 = 0;
    let mut v_a_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5119_: u8 = 0;
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5101_ = l_Lean_Meta_reduceRecMatcher_x3f(
                    v_a_5095_,
                    v___y_5096_,
                    v___y_5097_,
                    v___y_5098_,
                    v___y_5099_,
                );
                if leanh::lean_obj_tag(v___x_5101_) == 0 {
                    v_a_5102_ = leanh::lean_ctor_get(v___x_5101_, 0);
                    v_isSharedCheck_5115_ = (!leanh::lean_is_exclusive(v___x_5101_)) as u8;
                    if v_isSharedCheck_5115_ == 0 {
                        v___x_5104_ = v___x_5101_;
                        v_isShared_5105_ = v_isSharedCheck_5115_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5102_);
                        leanh::lean_dec(v___x_5101_);
                        v___x_5104_ = leanh::lean_box(0);
                        v_isShared_5105_ = v_isSharedCheck_5115_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_5095_);
                    v_a_5116_ = leanh::lean_ctor_get(v___x_5101_, 0);
                    v_isSharedCheck_5123_ = (!leanh::lean_is_exclusive(v___x_5101_)) as u8;
                    if v_isSharedCheck_5123_ == 0 {
                        v___x_5118_ = v___x_5101_;
                        v_isShared_5119_ = v_isSharedCheck_5123_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5116_);
                        leanh::lean_dec(v___x_5101_);
                        v___x_5118_ = leanh::lean_box(0);
                        v_isShared_5119_ = v_isSharedCheck_5123_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5102_) == 1 {
                    leanh::lean_del_object(v___x_5104_);
                    leanh::lean_dec_ref(v_a_5095_);
                    v_val_5106_ = leanh::lean_ctor_get(v_a_5102_, 0);
                    leanh::lean_inc(v_val_5106_);
                    leanh::lean_dec_ref_known(v_a_5102_, 1);
                    v___x_5107_ = l_Lean_Expr_headBeta(v_val_5106_);
                    v_a_5095_ = v___x_5107_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_5102_);
                    leanh::lean_inc_ref(v_a_5095_);
                    v___x_5109_ = l_Lean_Expr_headBeta(v_a_5095_);
                    v___x_5110_ = lean_expr_eqv(v_a_5095_, v___x_5109_);
                    if v___x_5110_ == 0 {
                        leanh::lean_del_object(v___x_5104_);
                        leanh::lean_dec_ref(v_a_5095_);
                        v_a_5095_ = v___x_5109_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_5109_);
                        if v_isShared_5105_ == 0 {
                            leanh::lean_ctor_set(v___x_5104_, 0, v_a_5095_);
                            v___x_5113_ = v___x_5104_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5114_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5095_);
                            v___x_5113_ = v_reuseFailAlloc_5114_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5113_;
            }
            3 => {
                if v_isShared_5119_ == 0 {
                    v___x_5121_ = v___x_5118_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5122_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
                    v___x_5121_ = v_reuseFailAlloc_5122_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg___boxed(
    mut v_a_5124_: *mut leanh::LeanObject,
    mut v___y_5125_: *mut leanh::LeanObject,
    mut v___y_5126_: *mut leanh::LeanObject,
    mut v___y_5127_: *mut leanh::LeanObject,
    mut v___y_5128_: *mut leanh::LeanObject,
    mut v___y_5129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5130_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(
            v_a_5124_,
            v___y_5125_,
            v___y_5126_,
            v___y_5127_,
            v___y_5128_,
        );
    leanh::lean_dec(v___y_5128_);
    leanh::lean_dec_ref(v___y_5127_);
    leanh::lean_dec(v___y_5126_);
    leanh::lean_dec_ref(v___y_5125_);
    return v_res_5130_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5135_ = l_Lean_Meta_rwMatcher___closed__2;
    v___x_5136_ = l_Lean_stringToMessageData(v___x_5135_);
    return v___x_5136_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5138_ = l_Lean_Meta_rwMatcher___closed__4;
    v___x_5139_ = l_Lean_stringToMessageData(v___x_5138_);
    return v___x_5139_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___closed__6() -> f64 {
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: f64 = 0.0;
    v___x_5140_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_5141_ = lean_float_of_nat(v___x_5140_);
    return v___x_5141_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5143_ = l_Lean_Meta_rwMatcher___closed__7;
    v___x_5144_ = l_Lean_stringToMessageData(v___x_5143_);
    return v___x_5144_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5152_ = l_Lean_Meta_rwMatcher___closed__12;
    v___x_5153_ = l_Lean_Meta_rwMatcher___closed__1;
    v___x_5154_ = l_Lean_Name_append(v___x_5153_, v___x_5152_);
    return v___x_5154_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5156_ = l_Lean_Meta_rwMatcher___closed__14;
    v___x_5157_ = l_Lean_stringToMessageData(v___x_5156_);
    return v___x_5157_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5159_ = l_Lean_Meta_rwMatcher___closed__16;
    v___x_5160_ = l_Lean_stringToMessageData(v___x_5159_);
    return v___x_5160_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5162_ = l_Lean_Meta_rwMatcher___closed__18;
    v___x_5163_ = l_Lean_stringToMessageData(v___x_5162_);
    return v___x_5163_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5165_ = l_Lean_Meta_rwMatcher___closed__20;
    v___x_5166_ = l_Lean_stringToMessageData(v___x_5165_);
    return v___x_5166_;
}
pub unsafe fn _init_l_Lean_Meta_rwMatcher___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5167_ = leanh::lean_box(0);
    v_dummy_5168_ = l_Lean_Expr_sort___override(v___x_5167_);
    return v_dummy_5168_;
}
pub unsafe fn l_Lean_Meta_rwMatcher(
    mut v_altIdx_5178_: *mut leanh::LeanObject,
    mut v_e_5179_: *mut leanh::LeanObject,
    mut v_a_5180_: *mut leanh::LeanObject,
    mut v_a_5181_: *mut leanh::LeanObject,
    mut v_a_5182_: *mut leanh::LeanObject,
    mut v_a_5183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5190_: u8 = 0;
    let mut v_a_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5195_: u8 = 0;
    let mut v_a_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5199_: u8 = 0;
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5203_: u8 = 0;
    let mut v___y_5205_: u8 = 0;
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5210_: u8 = 0;
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5223_: u8 = 0;
    let mut v_options_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5225_: u8 = 0;
    let mut v_inheritedTraceOptions_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: u8 = 0;
    let mut v___x_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5244_: u8 = 0;
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5248_: u8 = 0;
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: u8 = 0;
    let mut v___x_5256_: u8 = 0;
    let mut v___y_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5264_: u8 = 0;
    let mut v___y_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5272_: u8 = 0;
    let mut v___y_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5281_: u8 = 0;
    let mut v___y_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5292_: u8 = 0;
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5306_: u8 = 0;
    let mut v___y_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5310_: u8 = 0;
    let mut v___y_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: u8 = 0;
    let mut v___x_5324_: u8 = 0;
    let mut v___y_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5327_: u8 = 0;
    let mut v___y_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5329_: u8 = 0;
    let mut v___y_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5335_: u8 = 0;
    let mut v___y_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: u8 = 0;
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5356_: u8 = 0;
    let mut v___y_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5358_: u8 = 0;
    let mut v___y_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5364_: u8 = 0;
    let mut v___y_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5371_: u8 = 0;
    let mut v___y_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5373_: u8 = 0;
    let mut v___y_5374_: usize = 0;
    let mut v___y_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5378_: u8 = 0;
    let mut v___y_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5386_: usize = 0;
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: u8 = 0;
    let mut v___x_5392_: u8 = 0;
    let mut v___x_5393_: usize = 0;
    let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: usize = 0;
    let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5399_: u8 = 0;
    let mut v___y_5400_: u8 = 0;
    let mut v___y_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5402_: usize = 0;
    let mut v___y_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5407_: u8 = 0;
    let mut v_fst_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: u8 = 0;
    let mut v___x_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5437_: u8 = 0;
    let mut v___y_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5442_: u8 = 0;
    let mut v___y_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: f64 = 0.0;
    let mut v___x_5447_: f64 = 0.0;
    let mut v___x_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5455_: u8 = 0;
    let mut v___y_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5462_: u8 = 0;
    let mut v___y_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5468_: u8 = 0;
    let mut v___y_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5475_: u8 = 0;
    let mut v___y_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5481_: u8 = 0;
    let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5485_: u8 = 0;
    let mut v_a_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5491_: u8 = 0;
    let mut v___y_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5497_: u8 = 0;
    let mut v_a_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: f64 = 0.0;
    let mut v___x_5501_: f64 = 0.0;
    let mut v___x_5502_: f64 = 0.0;
    let mut v___x_5503_: f64 = 0.0;
    let mut v___x_5504_: f64 = 0.0;
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5512_: u8 = 0;
    let mut v___y_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5520_: u8 = 0;
    let mut v_a_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5525_: u8 = 0;
    let mut v___y_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5533_: u8 = 0;
    let mut v___y_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5538_: u8 = 0;
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5542_: u8 = 0;
    let mut v_a_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5546_: u8 = 0;
    let mut v___y_5547_: u8 = 0;
    let mut v___y_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5551_: u8 = 0;
    let mut v___y_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5558_: u8 = 0;
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: u8 = 0;
    let mut v___x_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: u8 = 0;
    let mut v___x_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5574_: u8 = 0;
    let mut v___x_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: u8 = 0;
    let mut v___x_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5589_: u8 = 0;
    let mut v_unused_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5604_: u8 = 0;
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: u8 = 0;
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5619_: u8 = 0;
    let mut v_unused_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5624_: u8 = 0;
    let mut v___x_5625_: u8 = 0;
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5630_: u8 = 0;
    let mut v___x_5631_: u8 = 0;
    let mut v_options_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5633_: u8 = 0;
    let mut v_inheritedTraceOptions_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: u8 = 0;
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5645_: u8 = 0;
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5649_: u8 = 0;
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: u8 = 0;
    let mut v_options_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5657_: u8 = 0;
    let mut v_inheritedTraceOptions_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: u8 = 0;
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5682_: u8 = 0;
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5686_: u8 = 0;
    let mut v_reuseFailAlloc_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5690_: u8 = 0;
    let mut v_nargs_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: u8 = 0;
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5714_: u8 = 0;
    let mut v_snd_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5718_: u8 = 0;
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5720_: usize = 0;
    let mut v___x_5721_: usize = 0;
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: u8 = 0;
    let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: u8 = 0;
    let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5747_: u8 = 0;
    let mut v_unused_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5749_: u8 = 0;
    let mut v_a_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: u8 = 0;
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: u8 = 0;
    let mut v___x_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: u8 = 0;
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5773_: u8 = 0;
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5783_: u8 = 0;
    let mut v_unused_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5790_: u8 = 0;
    let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5794_: u8 = 0;
    let mut v_isSharedCheck_5795_: u8 = 0;
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5800_: u8 = 0;
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5806_: u8 = 0;
    let mut v_a_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5810_: u8 = 0;
    let mut v___x_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5814_: u8 = 0;
    let mut v___x_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: u8 = 0;
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5815_ = l_Lean_Meta_rwMatcher___closed__25;
                v___x_5816_ = l_Lean_Expr_isAppOf(v_e_5179_, v___x_5815_);
                if v___x_5816_ == 0 {
                    v___x_5817_ = l_Lean_Meta_rwMatcher___closed__27;
                    v___x_5818_ = l_Lean_Expr_isAppOf(v_e_5179_, v___x_5817_);
                    v___y_5624_ = v___x_5818_;
                    state = 37;
                    continue;
                } else {
                    v___y_5624_ = v___x_5816_;
                    state = 37;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_5186_) == 0 {
                    v_a_5187_ = leanh::lean_ctor_get(v___y_5186_, 0);
                    v_isSharedCheck_5195_ = (!leanh::lean_is_exclusive(v___y_5186_)) as u8;
                    if v_isSharedCheck_5195_ == 0 {
                        v___x_5189_ = v___y_5186_;
                        v_isShared_5190_ = v_isSharedCheck_5195_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5187_);
                        leanh::lean_dec(v___y_5186_);
                        v___x_5189_ = leanh::lean_box(0);
                        v_isShared_5190_ = v_isSharedCheck_5195_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5196_ = leanh::lean_ctor_get(v___y_5186_, 0);
                    v_isSharedCheck_5203_ = (!leanh::lean_is_exclusive(v___y_5186_)) as u8;
                    if v_isSharedCheck_5203_ == 0 {
                        v___x_5198_ = v___y_5186_;
                        v_isShared_5199_ = v_isSharedCheck_5203_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5196_);
                        leanh::lean_dec(v___y_5186_);
                        v___x_5198_ = leanh::lean_box(0);
                        v_isShared_5199_ = v_isSharedCheck_5203_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_a_5191_ = leanh::lean_ctor_get(v_a_5187_, 0);
                leanh::lean_inc(v_a_5191_);
                leanh::lean_dec(v_a_5187_);
                if v_isShared_5190_ == 0 {
                    leanh::lean_ctor_set(v___x_5189_, 0, v_a_5191_);
                    v___x_5193_ = v___x_5189_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5194_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_a_5191_);
                    v___x_5193_ = v_reuseFailAlloc_5194_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5193_;
            }
            4 => {
                if v_isShared_5199_ == 0 {
                    v___x_5201_ = v___x_5198_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5202_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_a_5196_);
                    v___x_5201_ = v_reuseFailAlloc_5202_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5201_;
            }
            6 => {
                v___x_5206_ = leanh::lean_box(0);
                v___x_5207_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_5207_, 0, v_e_5179_);
                leanh::lean_ctor_set(v___x_5207_, 1, v___x_5206_);
                leanh::lean_ctor_set_uint8(
                    v___x_5207_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___y_5205_,
                );
                v___x_5208_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5208_, 0, v___x_5207_);
                return v___x_5208_;
            }
            7 => {
                v___x_5211_ = leanh::lean_box(0);
                v___x_5212_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_5212_, 0, v_e_5179_);
                leanh::lean_ctor_set(v___x_5212_, 1, v___x_5211_);
                leanh::lean_ctor_set_uint8(
                    v___x_5212_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___y_5210_,
                );
                v___x_5213_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5213_, 0, v___x_5212_);
                return v___x_5213_;
            }
            8 => {
                v___x_5216_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_5183_);
                leanh::lean_inc_ref(v_a_5182_);
                leanh::lean_inc(v_a_5181_);
                leanh::lean_inc_ref(v_a_5180_);
                v___x_5217_ = leanh::lean_apply_6(
                    v___y_5215_,
                    v___x_5216_,
                    v_a_5180_,
                    v_a_5181_,
                    v_a_5182_,
                    v_a_5183_,
                    leanh::lean_box(0),
                );
                v___y_5186_ = v___x_5217_;
                state = 1;
                continue;
            }
            9 => {
                if v___y_5223_ == 0 {
                    v_options_5224_ = leanh::lean_ctor_get(v_a_5182_, 2);
                    v_hasTrace_5225_ = leanh::lean_ctor_get_uint8(
                        v_options_5224_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5225_ == 0 {
                        leanh::lean_dec_ref(v___y_5222_);
                        leanh::lean_dec(v___y_5221_);
                        leanh::lean_dec(v___y_5220_);
                        v___y_5215_ = v___y_5219_;
                        state = 8;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5226_ = leanh::lean_ctor_get(v_a_5182_, 13);
                        v___x_5227_ = l_Lean_Meta_rwMatcher___closed__1;
                        leanh::lean_inc(v___y_5220_);
                        v___x_5228_ = l_Lean_Name_append(v___x_5227_, v___y_5220_);
                        v___x_5229_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5226_,
                            v_options_5224_,
                            v___x_5228_,
                        );
                        leanh::lean_dec(v___x_5228_);
                        if v___x_5229_ == 0 {
                            leanh::lean_dec_ref(v___y_5222_);
                            leanh::lean_dec(v___y_5221_);
                            leanh::lean_dec(v___y_5220_);
                            v___y_5215_ = v___y_5219_;
                            state = 8;
                            continue;
                        } else {
                            v___x_5230_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__3),
                                core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__3_once),
                                _init_l_Lean_Meta_rwMatcher___closed__3,
                            );
                            v___x_5231_ = l_Lean_MessageData_ofConstName(v___y_5221_, v___y_5223_);
                            v___x_5232_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5232_, 0, v___x_5230_);
                            leanh::lean_ctor_set(v___x_5232_, 1, v___x_5231_);
                            v___x_5233_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__5),
                                core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__5_once),
                                _init_l_Lean_Meta_rwMatcher___closed__5,
                            );
                            v___x_5234_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5234_, 0, v___x_5232_);
                            leanh::lean_ctor_set(v___x_5234_, 1, v___x_5233_);
                            v___x_5235_ = l_Lean_Exception_toMessageData(v___y_5222_);
                            v___x_5236_ = l_Lean_indentD(v___x_5235_);
                            v___x_5237_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5237_, 0, v___x_5234_);
                            leanh::lean_ctor_set(v___x_5237_, 1, v___x_5236_);
                            v___x_5238_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(
                                v___y_5220_,
                                v___x_5237_,
                                v_a_5180_,
                                v_a_5181_,
                                v_a_5182_,
                                v_a_5183_,
                            );
                            if leanh::lean_obj_tag(v___x_5238_) == 0 {
                                v_a_5239_ = leanh::lean_ctor_get(v___x_5238_, 0);
                                leanh::lean_inc(v_a_5239_);
                                leanh::lean_dec_ref_known(v___x_5238_, 1);
                                leanh::lean_inc(v_a_5183_);
                                leanh::lean_inc_ref(v_a_5182_);
                                leanh::lean_inc(v_a_5181_);
                                leanh::lean_inc_ref(v_a_5180_);
                                v___x_5240_ = leanh::lean_apply_6(
                                    v___y_5219_,
                                    v_a_5239_,
                                    v_a_5180_,
                                    v_a_5181_,
                                    v_a_5182_,
                                    v_a_5183_,
                                    leanh::lean_box(0),
                                );
                                v___y_5186_ = v___x_5240_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___y_5219_);
                                v_a_5241_ = leanh::lean_ctor_get(v___x_5238_, 0);
                                v_isSharedCheck_5248_ =
                                    (!leanh::lean_is_exclusive(v___x_5238_)) as u8;
                                if v_isSharedCheck_5248_ == 0 {
                                    v___x_5243_ = v___x_5238_;
                                    v_isShared_5244_ = v_isSharedCheck_5248_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5241_);
                                    leanh::lean_dec(v___x_5238_);
                                    v___x_5243_ = leanh::lean_box(0);
                                    v_isShared_5244_ = v_isSharedCheck_5248_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_5221_);
                    leanh::lean_dec(v___y_5220_);
                    leanh::lean_dec_ref(v___y_5219_);
                    v___x_5249_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5249_, 0, v___y_5222_);
                    return v___x_5249_;
                }
            }
            10 => {
                if v_isShared_5244_ == 0 {
                    v___x_5246_ = v___x_5243_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5247_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_a_5241_);
                    v___x_5246_ = v_reuseFailAlloc_5247_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5246_;
            }
            12 => {
                v___x_5255_ = l_Lean_Exception_isInterrupt(v_a_5254_);
                if v___x_5255_ == 0 {
                    leanh::lean_inc_ref(v_a_5254_);
                    v___x_5256_ = l_Lean_Exception_isRuntime(v_a_5254_);
                    v___y_5219_ = v___y_5251_;
                    v___y_5220_ = v___y_5252_;
                    v___y_5221_ = v___y_5253_;
                    v___y_5222_ = v_a_5254_;
                    v___y_5223_ = v___x_5256_;
                    state = 9;
                    continue;
                } else {
                    v___y_5219_ = v___y_5251_;
                    v___y_5220_ = v___y_5252_;
                    v___y_5221_ = v___y_5253_;
                    v___y_5222_ = v_a_5254_;
                    v___y_5223_ = v___x_5255_;
                    state = 9;
                    continue;
                }
            }
            13 => {
                if leanh::lean_obj_tag(v___y_5261_) == 0 {
                    leanh::lean_dec(v___y_5260_);
                    leanh::lean_dec(v___y_5259_);
                    leanh::lean_dec_ref(v___y_5258_);
                    return v___y_5261_;
                } else {
                    v_a_5262_ = leanh::lean_ctor_get(v___y_5261_, 0);
                    leanh::lean_inc(v_a_5262_);
                    leanh::lean_dec_ref_known(v___y_5261_, 1);
                    v___y_5251_ = v___y_5258_;
                    v___y_5252_ = v___y_5259_;
                    v___y_5253_ = v___y_5260_;
                    v_a_5254_ = v_a_5262_;
                    state = 12;
                    continue;
                }
            }
            14 => {
                v___x_5267_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5267_, 0, v_proof_5266_);
                v___x_5268_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_5268_, 0, v___y_5265_);
                leanh::lean_ctor_set(v___x_5268_, 1, v___x_5267_);
                leanh::lean_ctor_set_uint8(
                    v___x_5268_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___y_5264_,
                );
                v___x_5269_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5269_, 0, v___x_5268_);
                return v___x_5269_;
            }
            15 => {
                if leanh::lean_obj_tag(v___y_5276_) == 0 {
                    leanh::lean_dec(v___y_5275_);
                    leanh::lean_dec(v___y_5273_);
                    leanh::lean_dec_ref(v___y_5271_);
                    v_a_5277_ = leanh::lean_ctor_get(v___y_5276_, 0);
                    leanh::lean_inc(v_a_5277_);
                    leanh::lean_dec_ref_known(v___y_5276_, 1);
                    v___y_5264_ = v___y_5272_;
                    v___y_5265_ = v___y_5274_;
                    v_proof_5266_ = v_a_5277_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_5274_);
                    v_a_5278_ = leanh::lean_ctor_get(v___y_5276_, 0);
                    leanh::lean_inc(v_a_5278_);
                    leanh::lean_dec_ref_known(v___y_5276_, 1);
                    v___y_5251_ = v___y_5271_;
                    v___y_5252_ = v___y_5273_;
                    v___y_5253_ = v___y_5275_;
                    v_a_5254_ = v_a_5278_;
                    state = 12;
                    continue;
                }
            }
            16 => {
                if v___y_5292_ == 0 {
                    leanh::lean_dec_ref(v___y_5280_);
                    v___x_5293_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__1_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__1,
                    );
                    v___x_5294_ = l_Lean_MessageData_ofExpr(v___y_5286_);
                    v___x_5295_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5295_, 0, v___x_5293_);
                    leanh::lean_ctor_set(v___x_5295_, 1, v___x_5294_);
                    v___x_5296_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__3_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__3,
                    );
                    v___x_5297_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5297_, 0, v___x_5295_);
                    leanh::lean_ctor_set(v___x_5297_, 1, v___x_5296_);
                    v___x_5298_ = l_Lean_Exception_toMessageData(v___y_5285_);
                    v___x_5299_ = l_Lean_indentD(v___x_5298_);
                    v___x_5300_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5300_, 0, v___x_5297_);
                    leanh::lean_ctor_set(v___x_5300_, 1, v___x_5299_);
                    v___x_5301_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__5_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__5,
                    );
                    v___x_5302_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5302_, 0, v___x_5300_);
                    leanh::lean_ctor_set(v___x_5302_, 1, v___x_5301_);
                    v___x_5303_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                        v___x_5302_,
                        v___y_5282_,
                        v___y_5284_,
                        v___y_5283_,
                        v___y_5290_,
                    );
                    v___y_5271_ = v___y_5287_;
                    v___y_5272_ = v___y_5281_;
                    v___y_5273_ = v___y_5288_;
                    v___y_5274_ = v___y_5289_;
                    v___y_5275_ = v___y_5291_;
                    v___y_5276_ = v___x_5303_;
                    state = 15;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_5286_);
                    leanh::lean_dec_ref(v___y_5285_);
                    v___y_5271_ = v___y_5287_;
                    v___y_5272_ = v___y_5281_;
                    v___y_5273_ = v___y_5288_;
                    v___y_5274_ = v___y_5289_;
                    v___y_5275_ = v___y_5291_;
                    v___y_5276_ = v___y_5280_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                v___x_5316_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(
                    v___y_5311_,
                    v___y_5313_,
                );
                v_a_5317_ = leanh::lean_ctor_get(v___x_5316_, 0);
                leanh::lean_inc(v_a_5317_);
                leanh::lean_dec_ref(v___x_5316_);
                v___x_5318_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(
                    v___y_5309_,
                    v___y_5313_,
                );
                if v___y_5310_ == 0 {
                    leanh::lean_dec(v___y_5308_);
                    leanh::lean_dec(v___y_5307_);
                    leanh::lean_dec_ref(v___y_5305_);
                    v_a_5319_ = leanh::lean_ctor_get(v___x_5318_, 0);
                    leanh::lean_inc(v_a_5319_);
                    leanh::lean_dec_ref(v___x_5318_);
                    v___y_5264_ = v___y_5306_;
                    v___y_5265_ = v_a_5317_;
                    v_proof_5266_ = v_a_5319_;
                    state = 14;
                    continue;
                } else {
                    v_a_5320_ = leanh::lean_ctor_get(v___x_5318_, 0);
                    leanh::lean_inc_n(v_a_5320_, 2);
                    leanh::lean_dec_ref(v___x_5318_);
                    v___x_5321_ = l_Lean_Meta_mkEqOfHEq(
                        v_a_5320_,
                        v___y_5306_,
                        v___y_5312_,
                        v___y_5313_,
                        v___y_5314_,
                        v___y_5315_,
                    );
                    if leanh::lean_obj_tag(v___x_5321_) == 0 {
                        leanh::lean_dec(v_a_5320_);
                        v___y_5271_ = v___y_5305_;
                        v___y_5272_ = v___y_5306_;
                        v___y_5273_ = v___y_5307_;
                        v___y_5274_ = v_a_5317_;
                        v___y_5275_ = v___y_5308_;
                        v___y_5276_ = v___x_5321_;
                        state = 15;
                        continue;
                    } else {
                        v_a_5322_ = leanh::lean_ctor_get(v___x_5321_, 0);
                        leanh::lean_inc(v_a_5322_);
                        v___x_5323_ = l_Lean_Exception_isInterrupt(v_a_5322_);
                        if v___x_5323_ == 0 {
                            leanh::lean_inc(v_a_5322_);
                            v___x_5324_ = l_Lean_Exception_isRuntime(v_a_5322_);
                            v___y_5280_ = v___x_5321_;
                            v___y_5281_ = v___y_5306_;
                            v___y_5282_ = v___y_5312_;
                            v___y_5283_ = v___y_5314_;
                            v___y_5284_ = v___y_5313_;
                            v___y_5285_ = v_a_5322_;
                            v___y_5286_ = v_a_5320_;
                            v___y_5287_ = v___y_5305_;
                            v___y_5288_ = v___y_5307_;
                            v___y_5289_ = v_a_5317_;
                            v___y_5290_ = v___y_5315_;
                            v___y_5291_ = v___y_5308_;
                            v___y_5292_ = v___x_5324_;
                            state = 16;
                            continue;
                        } else {
                            v___y_5280_ = v___x_5321_;
                            v___y_5281_ = v___y_5306_;
                            v___y_5282_ = v___y_5312_;
                            v___y_5283_ = v___y_5314_;
                            v___y_5284_ = v___y_5313_;
                            v___y_5285_ = v_a_5322_;
                            v___y_5286_ = v_a_5320_;
                            v___y_5287_ = v___y_5305_;
                            v___y_5288_ = v___y_5307_;
                            v___y_5289_ = v_a_5317_;
                            v___y_5290_ = v___y_5315_;
                            v___y_5291_ = v___y_5308_;
                            v___y_5292_ = v___x_5323_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            18 => {
                v___x_5339_ = lean_array_get_size(v_a_5338_);
                v___x_5340_ = leanh::lean_unsigned_to_nat(0);
                v___x_5341_ = lean_nat_dec_eq(v___x_5339_, v___x_5340_);
                if v___x_5341_ == 0 {
                    leanh::lean_dec_ref(v___y_5337_);
                    leanh::lean_dec_ref(v___y_5334_);
                    v___x_5342_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__7_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__7,
                    );
                    leanh::lean_inc(v___y_5333_);
                    v___x_5343_ = l_Lean_MessageData_ofConstName(v___y_5333_, v___y_5329_);
                    v___x_5344_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5344_, 0, v___x_5342_);
                    leanh::lean_ctor_set(v___x_5344_, 1, v___x_5343_);
                    v___x_5345_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__9),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__9_once),
                        _init_l_Lean_Meta_rwMatcher___lam__2___closed__9,
                    );
                    v___x_5346_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5346_, 0, v___x_5344_);
                    leanh::lean_ctor_set(v___x_5346_, 1, v___x_5345_);
                    v___x_5347_ = lean_array_to_list(v_a_5338_);
                    v___x_5348_ = leanh::lean_box(0);
                    v___x_5349_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(
                        v___x_5347_,
                        v___x_5348_,
                    );
                    v___x_5350_ = l_Lean_MessageData_ofList(v___x_5349_);
                    v___x_5351_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5351_, 0, v___x_5346_);
                    leanh::lean_ctor_set(v___x_5351_, 1, v___x_5350_);
                    v___x_5352_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                        v___x_5351_,
                        v___y_5326_,
                        v___y_5331_,
                        v___y_5332_,
                        v___y_5336_,
                    );
                    v_a_5353_ = leanh::lean_ctor_get(v___x_5352_, 0);
                    leanh::lean_inc(v_a_5353_);
                    leanh::lean_dec_ref(v___x_5352_);
                    v___y_5251_ = v___y_5328_;
                    v___y_5252_ = v___y_5330_;
                    v___y_5253_ = v___y_5333_;
                    v_a_5254_ = v_a_5353_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_a_5338_);
                    v___y_5305_ = v___y_5328_;
                    v___y_5306_ = v___y_5327_;
                    v___y_5307_ = v___y_5330_;
                    v___y_5308_ = v___y_5333_;
                    v___y_5309_ = v___y_5334_;
                    v___y_5310_ = v___y_5335_;
                    v___y_5311_ = v___y_5337_;
                    v___y_5312_ = v___y_5326_;
                    v___y_5313_ = v___y_5331_;
                    v___y_5314_ = v___y_5332_;
                    v___y_5315_ = v___y_5336_;
                    state = 17;
                    continue;
                }
            }
            19 => {
                if leanh::lean_obj_tag(v___y_5367_) == 0 {
                    v_a_5368_ = leanh::lean_ctor_get(v___y_5367_, 0);
                    leanh::lean_inc(v_a_5368_);
                    leanh::lean_dec_ref_known(v___y_5367_, 1);
                    v___y_5326_ = v___y_5355_;
                    v___y_5327_ = v___y_5358_;
                    v___y_5328_ = v___y_5357_;
                    v___y_5329_ = v___y_5356_;
                    v___y_5330_ = v___y_5359_;
                    v___y_5331_ = v___y_5360_;
                    v___y_5332_ = v___y_5362_;
                    v___y_5333_ = v___y_5361_;
                    v___y_5334_ = v___y_5363_;
                    v___y_5335_ = v___y_5364_;
                    v___y_5336_ = v___y_5365_;
                    v___y_5337_ = v___y_5366_;
                    v_a_5338_ = v_a_5368_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_5366_);
                    leanh::lean_dec_ref(v___y_5363_);
                    v_a_5369_ = leanh::lean_ctor_get(v___y_5367_, 0);
                    leanh::lean_inc(v_a_5369_);
                    leanh::lean_dec_ref_known(v___y_5367_, 1);
                    v___y_5251_ = v___y_5357_;
                    v___y_5252_ = v___y_5359_;
                    v___y_5253_ = v___y_5361_;
                    v_a_5254_ = v_a_5369_;
                    state = 12;
                    continue;
                }
            }
            20 => {
                v___x_5385_ = leanh::lean_box(0);
                v_sz_5386_ = lean_array_size(v___y_5379_);
                v___x_5387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___y_5379_, v_sz_5386_, v___y_5374_, v___x_5385_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
                if leanh::lean_obj_tag(v___x_5387_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5387_, 1);
                    v___x_5388_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5389_ = lean_array_get_size(v___y_5379_);
                    v___x_5390_ = l_Lean_Meta_rwMatcher___lam__2___closed__10;
                    v___x_5391_ = lean_nat_dec_lt(v___x_5388_, v___x_5389_);
                    if v___x_5391_ == 0 {
                        leanh::lean_dec_ref(v___y_5379_);
                        v___y_5326_ = v___y_5381_;
                        v___y_5327_ = v___y_5373_;
                        v___y_5328_ = v___y_5372_;
                        v___y_5329_ = v___y_5371_;
                        v___y_5330_ = v___y_5375_;
                        v___y_5331_ = v___y_5382_;
                        v___y_5332_ = v___y_5383_;
                        v___y_5333_ = v___y_5376_;
                        v___y_5334_ = v___y_5377_;
                        v___y_5335_ = v___y_5378_;
                        v___y_5336_ = v___y_5384_;
                        v___y_5337_ = v___y_5380_;
                        v_a_5338_ = v___x_5390_;
                        state = 18;
                        continue;
                    } else {
                        v___x_5392_ = lean_nat_dec_le(v___x_5389_, v___x_5389_);
                        if v___x_5392_ == 0 {
                            if v___x_5391_ == 0 {
                                leanh::lean_dec_ref(v___y_5379_);
                                v___y_5326_ = v___y_5381_;
                                v___y_5327_ = v___y_5373_;
                                v___y_5328_ = v___y_5372_;
                                v___y_5329_ = v___y_5371_;
                                v___y_5330_ = v___y_5375_;
                                v___y_5331_ = v___y_5382_;
                                v___y_5332_ = v___y_5383_;
                                v___y_5333_ = v___y_5376_;
                                v___y_5334_ = v___y_5377_;
                                v___y_5335_ = v___y_5378_;
                                v___y_5336_ = v___y_5384_;
                                v___y_5337_ = v___y_5380_;
                                v_a_5338_ = v___x_5390_;
                                state = 18;
                                continue;
                            } else {
                                v___x_5393_ = lean_usize_of_nat(v___x_5389_);
                                v___x_5394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_5379_, v___y_5374_, v___x_5393_, v___x_5390_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
                                leanh::lean_dec_ref(v___y_5379_);
                                v___y_5355_ = v___y_5381_;
                                v___y_5356_ = v___y_5371_;
                                v___y_5357_ = v___y_5372_;
                                v___y_5358_ = v___y_5373_;
                                v___y_5359_ = v___y_5375_;
                                v___y_5360_ = v___y_5382_;
                                v___y_5361_ = v___y_5376_;
                                v___y_5362_ = v___y_5383_;
                                v___y_5363_ = v___y_5377_;
                                v___y_5364_ = v___y_5378_;
                                v___y_5365_ = v___y_5384_;
                                v___y_5366_ = v___y_5380_;
                                v___y_5367_ = v___x_5394_;
                                state = 19;
                                continue;
                            }
                        } else {
                            v___x_5395_ = lean_usize_of_nat(v___x_5389_);
                            v___x_5396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_5379_, v___y_5374_, v___x_5395_, v___x_5390_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
                            leanh::lean_dec_ref(v___y_5379_);
                            v___y_5355_ = v___y_5381_;
                            v___y_5356_ = v___y_5371_;
                            v___y_5357_ = v___y_5372_;
                            v___y_5358_ = v___y_5373_;
                            v___y_5359_ = v___y_5375_;
                            v___y_5360_ = v___y_5382_;
                            v___y_5361_ = v___y_5376_;
                            v___y_5362_ = v___y_5383_;
                            v___y_5363_ = v___y_5377_;
                            v___y_5364_ = v___y_5378_;
                            v___y_5365_ = v___y_5384_;
                            v___y_5366_ = v___y_5380_;
                            v___y_5367_ = v___x_5396_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_5380_);
                    leanh::lean_dec_ref(v___y_5379_);
                    leanh::lean_dec_ref(v___y_5377_);
                    v_a_5397_ = leanh::lean_ctor_get(v___x_5387_, 0);
                    leanh::lean_inc(v_a_5397_);
                    leanh::lean_dec_ref_known(v___x_5387_, 1);
                    v___y_5251_ = v___y_5372_;
                    v___y_5252_ = v___y_5375_;
                    v___y_5253_ = v___y_5376_;
                    v_a_5254_ = v_a_5397_;
                    state = 12;
                    continue;
                }
            }
            21 => {
                leanh::lean_inc_ref(v_fst_5408_);
                leanh::lean_inc_ref(v_e_5179_);
                v___x_5414_ = l_Lean_Meta_isExprDefEq(
                    v_e_5179_,
                    v_fst_5408_,
                    v___y_5410_,
                    v___y_5411_,
                    v___y_5412_,
                    v___y_5413_,
                );
                if leanh::lean_obj_tag(v___x_5414_) == 0 {
                    v_a_5415_ = leanh::lean_ctor_get(v___x_5414_, 0);
                    leanh::lean_inc(v_a_5415_);
                    leanh::lean_dec_ref_known(v___x_5414_, 1);
                    v___x_5416_ = (leanh::lean_unbox(v_a_5415_) as u8);
                    leanh::lean_dec(v_a_5415_);
                    if v___x_5416_ == 0 {
                        leanh::lean_dec_ref(v_snd_5409_);
                        leanh::lean_dec_ref(v___y_5406_);
                        leanh::lean_dec_ref(v___y_5405_);
                        v___x_5417_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__12),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_rwMatcher___lam__2___closed__12_once
                            ),
                            _init_l_Lean_Meta_rwMatcher___lam__2___closed__12,
                        );
                        v___x_5418_ = l_Lean_MessageData_ofExpr(v_fst_5408_);
                        v___x_5419_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5419_, 0, v___x_5417_);
                        leanh::lean_ctor_set(v___x_5419_, 1, v___x_5418_);
                        v___x_5420_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__14),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_rwMatcher___lam__2___closed__14_once
                            ),
                            _init_l_Lean_Meta_rwMatcher___lam__2___closed__14,
                        );
                        v___x_5421_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5421_, 0, v___x_5419_);
                        leanh::lean_ctor_set(v___x_5421_, 1, v___x_5420_);
                        leanh::lean_inc(v___y_5404_);
                        v___x_5422_ = l_Lean_MessageData_ofConstName(v___y_5404_, v___y_5399_);
                        v___x_5423_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5423_, 0, v___x_5421_);
                        leanh::lean_ctor_set(v___x_5423_, 1, v___x_5422_);
                        v___x_5424_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__16),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_rwMatcher___lam__2___closed__16_once
                            ),
                            _init_l_Lean_Meta_rwMatcher___lam__2___closed__16,
                        );
                        v___x_5425_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5425_, 0, v___x_5423_);
                        leanh::lean_ctor_set(v___x_5425_, 1, v___x_5424_);
                        v___x_5426_ = l_Lean_MessageData_ofExpr(v_e_5179_);
                        v___x_5427_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5427_, 0, v___x_5425_);
                        leanh::lean_ctor_set(v___x_5427_, 1, v___x_5426_);
                        v___x_5428_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
                        v___x_5429_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5429_, 0, v___x_5427_);
                        leanh::lean_ctor_set(v___x_5429_, 1, v___x_5428_);
                        v___x_5430_ =
                            l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                                v___x_5429_,
                                v___y_5410_,
                                v___y_5411_,
                                v___y_5412_,
                                v___y_5413_,
                            );
                        v_a_5431_ = leanh::lean_ctor_get(v___x_5430_, 0);
                        leanh::lean_inc(v_a_5431_);
                        leanh::lean_dec_ref(v___x_5430_);
                        v___y_5251_ = v___y_5401_;
                        v___y_5252_ = v___y_5403_;
                        v___y_5253_ = v___y_5404_;
                        v_a_5254_ = v_a_5431_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_fst_5408_);
                        leanh::lean_dec_ref(v_e_5179_);
                        v___y_5371_ = v___y_5399_;
                        v___y_5372_ = v___y_5401_;
                        v___y_5373_ = v___y_5400_;
                        v___y_5374_ = v___y_5402_;
                        v___y_5375_ = v___y_5403_;
                        v___y_5376_ = v___y_5404_;
                        v___y_5377_ = v___y_5405_;
                        v___y_5378_ = v_fst_5407_;
                        v___y_5379_ = v___y_5406_;
                        v___y_5380_ = v_snd_5409_;
                        v___y_5381_ = v___y_5410_;
                        v___y_5382_ = v___y_5411_;
                        v___y_5383_ = v___y_5412_;
                        v___y_5384_ = v___y_5413_;
                        state = 20;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_snd_5409_);
                    leanh::lean_dec_ref(v_fst_5408_);
                    leanh::lean_dec_ref(v___y_5406_);
                    leanh::lean_dec_ref(v___y_5405_);
                    leanh::lean_dec_ref(v_e_5179_);
                    v_a_5432_ = leanh::lean_ctor_get(v___x_5414_, 0);
                    leanh::lean_inc(v_a_5432_);
                    leanh::lean_dec_ref_known(v___x_5414_, 1);
                    v___y_5251_ = v___y_5401_;
                    v___y_5252_ = v___y_5403_;
                    v___y_5253_ = v___y_5404_;
                    v_a_5254_ = v_a_5432_;
                    state = 12;
                    continue;
                }
            }
            22 => {
                v___x_5445_ = lean_io_get_num_heartbeats();
                v___x_5446_ = lean_float_of_nat(v___y_5443_);
                v___x_5447_ = lean_float_of_nat(v___x_5445_);
                v___x_5448_ = leanh::lean_box_float(v___x_5446_);
                v___x_5449_ = leanh::lean_box_float(v___x_5447_);
                v___x_5450_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5450_, 0, v___x_5448_);
                leanh::lean_ctor_set(v___x_5450_, 1, v___x_5449_);
                v___x_5451_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5451_, 0, v_a_5444_);
                leanh::lean_ctor_set(v___x_5451_, 1, v___x_5450_);
                leanh::lean_inc_ref(v___y_5436_);
                leanh::lean_inc(v___y_5438_);
                v___x_5452_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_5438_, v___y_5437_, v___y_5436_, v___y_5439_, v___y_5442_, v___y_5440_, v___y_5434_, v___x_5451_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_);
                v___y_5258_ = v___y_5435_;
                v___y_5259_ = v___y_5438_;
                v___y_5260_ = v___y_5441_;
                v___y_5261_ = v___x_5452_;
                state = 13;
                continue;
            }
            23 => {
                v___x_5465_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5465_, 0, v_a_5464_);
                v___y_5434_ = v___y_5454_;
                v___y_5435_ = v___y_5457_;
                v___y_5436_ = v___y_5456_;
                v___y_5437_ = v___y_5455_;
                v___y_5438_ = v___y_5458_;
                v___y_5439_ = v___y_5459_;
                v___y_5440_ = v___y_5460_;
                v___y_5441_ = v___y_5461_;
                v___y_5442_ = v___y_5462_;
                v___y_5443_ = v___y_5463_;
                v_a_5444_ = v___x_5465_;
                state = 22;
                continue;
            }
            24 => {
                if leanh::lean_obj_tag(v___y_5477_) == 0 {
                    v_a_5478_ = leanh::lean_ctor_get(v___y_5477_, 0);
                    v_isSharedCheck_5485_ = (!leanh::lean_is_exclusive(v___y_5477_)) as u8;
                    if v_isSharedCheck_5485_ == 0 {
                        v___x_5480_ = v___y_5477_;
                        v_isShared_5481_ = v_isSharedCheck_5485_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5478_);
                        leanh::lean_dec(v___y_5477_);
                        v___x_5480_ = leanh::lean_box(0);
                        v_isShared_5481_ = v_isSharedCheck_5485_;
                        state = 25;
                        continue;
                    }
                } else {
                    v_a_5486_ = leanh::lean_ctor_get(v___y_5477_, 0);
                    leanh::lean_inc(v_a_5486_);
                    leanh::lean_dec_ref_known(v___y_5477_, 1);
                    v___y_5454_ = v___y_5467_;
                    v___y_5455_ = v___y_5468_;
                    v___y_5456_ = v___y_5469_;
                    v___y_5457_ = v___y_5470_;
                    v___y_5458_ = v___y_5471_;
                    v___y_5459_ = v___y_5472_;
                    v___y_5460_ = v___y_5473_;
                    v___y_5461_ = v___y_5474_;
                    v___y_5462_ = v___y_5475_;
                    v___y_5463_ = v___y_5476_;
                    v_a_5464_ = v_a_5486_;
                    state = 23;
                    continue;
                }
            }
            25 => {
                if v_isShared_5481_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5480_, 1);
                    v___x_5483_ = v___x_5480_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5484_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5484_, 0, v_a_5478_);
                    v___x_5483_ = v_reuseFailAlloc_5484_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___y_5434_ = v___y_5467_;
                v___y_5435_ = v___y_5470_;
                v___y_5436_ = v___y_5469_;
                v___y_5437_ = v___y_5468_;
                v___y_5438_ = v___y_5471_;
                v___y_5439_ = v___y_5472_;
                v___y_5440_ = v___y_5473_;
                v___y_5441_ = v___y_5474_;
                v___y_5442_ = v___y_5475_;
                v___y_5443_ = v___y_5476_;
                v_a_5444_ = v___x_5483_;
                state = 22;
                continue;
            }
            27 => {
                v___x_5499_ = lean_io_mono_nanos_now();
                v___x_5500_ = lean_float_of_nat(v___y_5495_);
                v___x_5501_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__6_once),
                    _init_l_Lean_Meta_rwMatcher___closed__6,
                );
                v___x_5502_ = lean_float_div(v___x_5500_, v___x_5501_);
                v___x_5503_ = lean_float_of_nat(v___x_5499_);
                v___x_5504_ = lean_float_div(v___x_5503_, v___x_5501_);
                v___x_5505_ = leanh::lean_box_float(v___x_5502_);
                v___x_5506_ = leanh::lean_box_float(v___x_5504_);
                v___x_5507_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5507_, 0, v___x_5505_);
                leanh::lean_ctor_set(v___x_5507_, 1, v___x_5506_);
                v___x_5508_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5508_, 0, v_a_5498_);
                leanh::lean_ctor_set(v___x_5508_, 1, v___x_5507_);
                leanh::lean_inc_ref(v___y_5490_);
                leanh::lean_inc(v___y_5492_);
                v___x_5509_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_5492_, v___y_5491_, v___y_5490_, v___y_5493_, v___y_5497_, v___y_5494_, v___y_5488_, v___x_5508_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_);
                v___y_5258_ = v___y_5489_;
                v___y_5259_ = v___y_5492_;
                v___y_5260_ = v___y_5496_;
                v___y_5261_ = v___x_5509_;
                state = 13;
                continue;
            }
            28 => {
                v___x_5522_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5522_, 0, v_a_5521_);
                v___y_5488_ = v___y_5511_;
                v___y_5489_ = v___y_5514_;
                v___y_5490_ = v___y_5513_;
                v___y_5491_ = v___y_5512_;
                v___y_5492_ = v___y_5515_;
                v___y_5493_ = v___y_5516_;
                v___y_5494_ = v___y_5518_;
                v___y_5495_ = v___y_5517_;
                v___y_5496_ = v___y_5519_;
                v___y_5497_ = v___y_5520_;
                v_a_5498_ = v___x_5522_;
                state = 27;
                continue;
            }
            29 => {
                if leanh::lean_obj_tag(v___y_5534_) == 0 {
                    v_a_5535_ = leanh::lean_ctor_get(v___y_5534_, 0);
                    v_isSharedCheck_5542_ = (!leanh::lean_is_exclusive(v___y_5534_)) as u8;
                    if v_isSharedCheck_5542_ == 0 {
                        v___x_5537_ = v___y_5534_;
                        v_isShared_5538_ = v_isSharedCheck_5542_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5535_);
                        leanh::lean_dec(v___y_5534_);
                        v___x_5537_ = leanh::lean_box(0);
                        v_isShared_5538_ = v_isSharedCheck_5542_;
                        state = 30;
                        continue;
                    }
                } else {
                    v_a_5543_ = leanh::lean_ctor_get(v___y_5534_, 0);
                    leanh::lean_inc(v_a_5543_);
                    leanh::lean_dec_ref_known(v___y_5534_, 1);
                    v___y_5511_ = v___y_5524_;
                    v___y_5512_ = v___y_5525_;
                    v___y_5513_ = v___y_5526_;
                    v___y_5514_ = v___y_5527_;
                    v___y_5515_ = v___y_5528_;
                    v___y_5516_ = v___y_5529_;
                    v___y_5517_ = v___y_5530_;
                    v___y_5518_ = v___y_5531_;
                    v___y_5519_ = v___y_5532_;
                    v___y_5520_ = v___y_5533_;
                    v_a_5521_ = v_a_5543_;
                    state = 28;
                    continue;
                }
            }
            30 => {
                if v_isShared_5538_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5537_, 1);
                    v___x_5540_ = v___x_5537_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_5541_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_a_5535_);
                    v___x_5540_ = v_reuseFailAlloc_5541_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___y_5488_ = v___y_5524_;
                v___y_5489_ = v___y_5527_;
                v___y_5490_ = v___y_5526_;
                v___y_5491_ = v___y_5525_;
                v___y_5492_ = v___y_5528_;
                v___y_5493_ = v___y_5529_;
                v___y_5494_ = v___y_5531_;
                v___y_5495_ = v___y_5530_;
                v___y_5496_ = v___y_5532_;
                v___y_5497_ = v___y_5533_;
                v_a_5498_ = v___x_5540_;
                state = 27;
                continue;
            }
            32 => {
                v___x_5559_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v_a_5183_);
                v_a_5560_ = leanh::lean_ctor_get(v___x_5559_, 0);
                leanh::lean_inc(v_a_5560_);
                leanh::lean_dec_ref(v___x_5559_);
                v___x_5561_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_5562_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(
                    v___y_5555_,
                    v___x_5561_,
                );
                if v___x_5562_ == 0 {
                    v___x_5563_ = lean_io_mono_nanos_now();
                    leanh::lean_inc(v_a_5183_);
                    leanh::lean_inc_ref(v_a_5182_);
                    leanh::lean_inc(v_a_5181_);
                    leanh::lean_inc_ref(v_a_5180_);
                    v___x_5564_ =
                        lean_infer_type(v___y_5556_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_);
                    if leanh::lean_obj_tag(v___x_5564_) == 0 {
                        v_a_5565_ = leanh::lean_ctor_get(v___x_5564_, 0);
                        leanh::lean_inc(v_a_5565_);
                        leanh::lean_dec_ref_known(v___x_5564_, 1);
                        v___x_5566_ = 0;
                        v___x_5567_ = l_Lean_Meta_forallMetaTelescope(
                            v_a_5565_,
                            v___x_5566_,
                            v_a_5180_,
                            v_a_5181_,
                            v_a_5182_,
                            v_a_5183_,
                        );
                        if leanh::lean_obj_tag(v___x_5567_) == 0 {
                            v_a_5568_ = leanh::lean_ctor_get(v___x_5567_, 0);
                            leanh::lean_inc(v_a_5568_);
                            leanh::lean_dec_ref_known(v___x_5567_, 1);
                            v_snd_5569_ = leanh::lean_ctor_get(v_a_5568_, 1);
                            leanh::lean_inc(v_snd_5569_);
                            v_fst_5570_ = leanh::lean_ctor_get(v_a_5568_, 0);
                            leanh::lean_inc(v_fst_5570_);
                            leanh::lean_dec(v_a_5568_);
                            v_snd_5571_ = leanh::lean_ctor_get(v_snd_5569_, 1);
                            v_isSharedCheck_5589_ =
                                (!leanh::lean_is_exclusive(v_snd_5569_)) as u8;
                            if v_isSharedCheck_5589_ == 0 {
                                v_unused_5590_ = leanh::lean_ctor_get(v_snd_5569_, 0);
                                leanh::lean_dec(v_unused_5590_);
                                v___x_5573_ = v_snd_5569_;
                                v_isShared_5574_ = v_isSharedCheck_5589_;
                                state = 33;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_5571_);
                                leanh::lean_dec(v_snd_5569_);
                                v___x_5573_ = leanh::lean_box(0);
                                v_isShared_5574_ = v_isSharedCheck_5589_;
                                state = 33;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___y_5549_);
                            leanh::lean_dec(v___y_5548_);
                            leanh::lean_dec_ref(v_e_5179_);
                            v_a_5591_ = leanh::lean_ctor_get(v___x_5567_, 0);
                            leanh::lean_inc(v_a_5591_);
                            leanh::lean_dec_ref_known(v___x_5567_, 1);
                            v___y_5511_ = v___y_5545_;
                            v___y_5512_ = v___y_5551_;
                            v___y_5513_ = v___y_5552_;
                            v___y_5514_ = v___y_5553_;
                            v___y_5515_ = v___y_5554_;
                            v___y_5516_ = v___y_5555_;
                            v___y_5517_ = v___x_5563_;
                            v___y_5518_ = v_a_5560_;
                            v___y_5519_ = v___y_5557_;
                            v___y_5520_ = v___y_5558_;
                            v_a_5521_ = v_a_5591_;
                            state = 28;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_5549_);
                        leanh::lean_dec(v___y_5548_);
                        leanh::lean_dec_ref(v_e_5179_);
                        v_a_5592_ = leanh::lean_ctor_get(v___x_5564_, 0);
                        leanh::lean_inc(v_a_5592_);
                        leanh::lean_dec_ref_known(v___x_5564_, 1);
                        v___y_5511_ = v___y_5545_;
                        v___y_5512_ = v___y_5551_;
                        v___y_5513_ = v___y_5552_;
                        v___y_5514_ = v___y_5553_;
                        v___y_5515_ = v___y_5554_;
                        v___y_5516_ = v___y_5555_;
                        v___y_5517_ = v___x_5563_;
                        v___y_5518_ = v_a_5560_;
                        v___y_5519_ = v___y_5557_;
                        v___y_5520_ = v___y_5558_;
                        v_a_5521_ = v_a_5592_;
                        state = 28;
                        continue;
                    }
                } else {
                    v___x_5593_ = lean_io_get_num_heartbeats();
                    leanh::lean_inc(v_a_5183_);
                    leanh::lean_inc_ref(v_a_5182_);
                    leanh::lean_inc(v_a_5181_);
                    leanh::lean_inc_ref(v_a_5180_);
                    v___x_5594_ =
                        lean_infer_type(v___y_5556_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_);
                    if leanh::lean_obj_tag(v___x_5594_) == 0 {
                        v_a_5595_ = leanh::lean_ctor_get(v___x_5594_, 0);
                        leanh::lean_inc(v_a_5595_);
                        leanh::lean_dec_ref_known(v___x_5594_, 1);
                        v___x_5596_ = 0;
                        v___x_5597_ = l_Lean_Meta_forallMetaTelescope(
                            v_a_5595_,
                            v___x_5596_,
                            v_a_5180_,
                            v_a_5181_,
                            v_a_5182_,
                            v_a_5183_,
                        );
                        if leanh::lean_obj_tag(v___x_5597_) == 0 {
                            v_a_5598_ = leanh::lean_ctor_get(v___x_5597_, 0);
                            leanh::lean_inc(v_a_5598_);
                            leanh::lean_dec_ref_known(v___x_5597_, 1);
                            v_snd_5599_ = leanh::lean_ctor_get(v_a_5598_, 1);
                            leanh::lean_inc(v_snd_5599_);
                            v_fst_5600_ = leanh::lean_ctor_get(v_a_5598_, 0);
                            leanh::lean_inc(v_fst_5600_);
                            leanh::lean_dec(v_a_5598_);
                            v_snd_5601_ = leanh::lean_ctor_get(v_snd_5599_, 1);
                            v_isSharedCheck_5619_ =
                                (!leanh::lean_is_exclusive(v_snd_5599_)) as u8;
                            if v_isSharedCheck_5619_ == 0 {
                                v_unused_5620_ = leanh::lean_ctor_get(v_snd_5599_, 0);
                                leanh::lean_dec(v_unused_5620_);
                                v___x_5603_ = v_snd_5599_;
                                v_isShared_5604_ = v_isSharedCheck_5619_;
                                state = 35;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_5601_);
                                leanh::lean_dec(v_snd_5599_);
                                v___x_5603_ = leanh::lean_box(0);
                                v_isShared_5604_ = v_isSharedCheck_5619_;
                                state = 35;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___y_5549_);
                            leanh::lean_dec(v___y_5548_);
                            leanh::lean_dec_ref(v_e_5179_);
                            v_a_5621_ = leanh::lean_ctor_get(v___x_5597_, 0);
                            leanh::lean_inc(v_a_5621_);
                            leanh::lean_dec_ref_known(v___x_5597_, 1);
                            v___y_5454_ = v___y_5545_;
                            v___y_5455_ = v___y_5551_;
                            v___y_5456_ = v___y_5552_;
                            v___y_5457_ = v___y_5553_;
                            v___y_5458_ = v___y_5554_;
                            v___y_5459_ = v___y_5555_;
                            v___y_5460_ = v_a_5560_;
                            v___y_5461_ = v___y_5557_;
                            v___y_5462_ = v___y_5558_;
                            v___y_5463_ = v___x_5593_;
                            v_a_5464_ = v_a_5621_;
                            state = 23;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_5549_);
                        leanh::lean_dec(v___y_5548_);
                        leanh::lean_dec_ref(v_e_5179_);
                        v_a_5622_ = leanh::lean_ctor_get(v___x_5594_, 0);
                        leanh::lean_inc(v_a_5622_);
                        leanh::lean_dec_ref_known(v___x_5594_, 1);
                        v___y_5454_ = v___y_5545_;
                        v___y_5455_ = v___y_5551_;
                        v___y_5456_ = v___y_5552_;
                        v___y_5457_ = v___y_5553_;
                        v___y_5458_ = v___y_5554_;
                        v___y_5459_ = v___y_5555_;
                        v___y_5460_ = v_a_5560_;
                        v___y_5461_ = v___y_5557_;
                        v___y_5462_ = v___y_5558_;
                        v___y_5463_ = v___x_5593_;
                        v_a_5464_ = v_a_5622_;
                        state = 23;
                        continue;
                    }
                }
            }
            33 => {
                v___x_5575_ = l_Lean_Meta_rwMatcher___closed__1;
                leanh::lean_inc(v___y_5554_);
                v___x_5576_ = l_Lean_Name_append(v___x_5575_, v___y_5554_);
                v___x_5577_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v___y_5550_,
                    v___y_5555_,
                    v___x_5576_,
                );
                leanh::lean_dec(v___x_5576_);
                if v___x_5577_ == 0 {
                    leanh::lean_del_object(v___x_5573_);
                    v___x_5578_ = leanh::lean_box(0);
                    v___x_5579_ = l_Lean_Meta_rwMatcher___lam__2(
                        v___y_5547_,
                        v___y_5549_,
                        v_fst_5570_,
                        v___y_5548_,
                        v___x_5562_,
                        v_e_5179_,
                        v_snd_5571_,
                        v___x_5578_,
                        v_a_5180_,
                        v_a_5181_,
                        v_a_5182_,
                        v_a_5183_,
                    );
                    leanh::lean_dec(v_snd_5571_);
                    v___y_5524_ = v___y_5545_;
                    v___y_5525_ = v___y_5551_;
                    v___y_5526_ = v___y_5552_;
                    v___y_5527_ = v___y_5553_;
                    v___y_5528_ = v___y_5554_;
                    v___y_5529_ = v___y_5555_;
                    v___y_5530_ = v___x_5563_;
                    v___y_5531_ = v_a_5560_;
                    v___y_5532_ = v___y_5557_;
                    v___y_5533_ = v___y_5558_;
                    v___y_5534_ = v___x_5579_;
                    state = 29;
                    continue;
                } else {
                    v___x_5580_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__8),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__8_once),
                        _init_l_Lean_Meta_rwMatcher___closed__8,
                    );
                    leanh::lean_inc(v_snd_5571_);
                    v___x_5581_ = l_Lean_indentExpr(v_snd_5571_);
                    if v_isShared_5574_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5573_, 7);
                        leanh::lean_ctor_set(v___x_5573_, 1, v___x_5581_);
                        leanh::lean_ctor_set(v___x_5573_, 0, v___x_5580_);
                        v___x_5583_ = v___x_5573_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_5588_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5580_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5588_, 1, v___x_5581_);
                        v___x_5583_ = v_reuseFailAlloc_5588_;
                        state = 34;
                        continue;
                    }
                }
            }
            34 => {
                leanh::lean_inc(v___y_5554_);
                v___x_5584_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(
                    v___y_5554_,
                    v___x_5583_,
                    v_a_5180_,
                    v_a_5181_,
                    v_a_5182_,
                    v_a_5183_,
                );
                if leanh::lean_obj_tag(v___x_5584_) == 0 {
                    v_a_5585_ = leanh::lean_ctor_get(v___x_5584_, 0);
                    leanh::lean_inc(v_a_5585_);
                    leanh::lean_dec_ref_known(v___x_5584_, 1);
                    v___x_5586_ = l_Lean_Meta_rwMatcher___lam__2(
                        v___y_5547_,
                        v___y_5549_,
                        v_fst_5570_,
                        v___y_5548_,
                        v___x_5562_,
                        v_e_5179_,
                        v_snd_5571_,
                        v_a_5585_,
                        v_a_5180_,
                        v_a_5181_,
                        v_a_5182_,
                        v_a_5183_,
                    );
                    leanh::lean_dec(v_snd_5571_);
                    v___y_5524_ = v___y_5545_;
                    v___y_5525_ = v___y_5551_;
                    v___y_5526_ = v___y_5552_;
                    v___y_5527_ = v___y_5553_;
                    v___y_5528_ = v___y_5554_;
                    v___y_5529_ = v___y_5555_;
                    v___y_5530_ = v___x_5563_;
                    v___y_5531_ = v_a_5560_;
                    v___y_5532_ = v___y_5557_;
                    v___y_5533_ = v___y_5558_;
                    v___y_5534_ = v___x_5586_;
                    state = 29;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_5571_);
                    leanh::lean_dec(v_fst_5570_);
                    leanh::lean_dec_ref(v___y_5549_);
                    leanh::lean_dec(v___y_5548_);
                    leanh::lean_dec_ref(v_e_5179_);
                    v_a_5587_ = leanh::lean_ctor_get(v___x_5584_, 0);
                    leanh::lean_inc(v_a_5587_);
                    leanh::lean_dec_ref_known(v___x_5584_, 1);
                    v___y_5511_ = v___y_5545_;
                    v___y_5512_ = v___y_5551_;
                    v___y_5513_ = v___y_5552_;
                    v___y_5514_ = v___y_5553_;
                    v___y_5515_ = v___y_5554_;
                    v___y_5516_ = v___y_5555_;
                    v___y_5517_ = v___x_5563_;
                    v___y_5518_ = v_a_5560_;
                    v___y_5519_ = v___y_5557_;
                    v___y_5520_ = v___y_5558_;
                    v_a_5521_ = v_a_5587_;
                    state = 28;
                    continue;
                }
            }
            35 => {
                v___x_5605_ = l_Lean_Meta_rwMatcher___closed__1;
                leanh::lean_inc(v___y_5554_);
                v___x_5606_ = l_Lean_Name_append(v___x_5605_, v___y_5554_);
                v___x_5607_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v___y_5550_,
                    v___y_5555_,
                    v___x_5606_,
                );
                leanh::lean_dec(v___x_5606_);
                if v___x_5607_ == 0 {
                    leanh::lean_del_object(v___x_5603_);
                    v___x_5608_ = leanh::lean_box(0);
                    v___x_5609_ = l_Lean_Meta_rwMatcher___lam__3(
                        v___y_5547_,
                        v___y_5549_,
                        v_fst_5600_,
                        v___y_5548_,
                        v___x_5562_,
                        v_e_5179_,
                        v___y_5546_,
                        v_snd_5601_,
                        v___x_5608_,
                        v_a_5180_,
                        v_a_5181_,
                        v_a_5182_,
                        v_a_5183_,
                    );
                    leanh::lean_dec(v_snd_5601_);
                    v___y_5467_ = v___y_5545_;
                    v___y_5468_ = v___y_5551_;
                    v___y_5469_ = v___y_5552_;
                    v___y_5470_ = v___y_5553_;
                    v___y_5471_ = v___y_5554_;
                    v___y_5472_ = v___y_5555_;
                    v___y_5473_ = v_a_5560_;
                    v___y_5474_ = v___y_5557_;
                    v___y_5475_ = v___y_5558_;
                    v___y_5476_ = v___x_5593_;
                    v___y_5477_ = v___x_5609_;
                    state = 24;
                    continue;
                } else {
                    v___x_5610_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__8),
                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__8_once),
                        _init_l_Lean_Meta_rwMatcher___closed__8,
                    );
                    leanh::lean_inc(v_snd_5601_);
                    v___x_5611_ = l_Lean_indentExpr(v_snd_5601_);
                    if v_isShared_5604_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5603_, 7);
                        leanh::lean_ctor_set(v___x_5603_, 1, v___x_5611_);
                        leanh::lean_ctor_set(v___x_5603_, 0, v___x_5610_);
                        v___x_5613_ = v___x_5603_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_5618_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5618_, 0, v___x_5610_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5618_, 1, v___x_5611_);
                        v___x_5613_ = v_reuseFailAlloc_5618_;
                        state = 36;
                        continue;
                    }
                }
            }
            36 => {
                leanh::lean_inc(v___y_5554_);
                v___x_5614_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(
                    v___y_5554_,
                    v___x_5613_,
                    v_a_5180_,
                    v_a_5181_,
                    v_a_5182_,
                    v_a_5183_,
                );
                if leanh::lean_obj_tag(v___x_5614_) == 0 {
                    v_a_5615_ = leanh::lean_ctor_get(v___x_5614_, 0);
                    leanh::lean_inc(v_a_5615_);
                    leanh::lean_dec_ref_known(v___x_5614_, 1);
                    v___x_5616_ = l_Lean_Meta_rwMatcher___lam__3(
                        v___y_5547_,
                        v___y_5549_,
                        v_fst_5600_,
                        v___y_5548_,
                        v___x_5562_,
                        v_e_5179_,
                        v___y_5546_,
                        v_snd_5601_,
                        v_a_5615_,
                        v_a_5180_,
                        v_a_5181_,
                        v_a_5182_,
                        v_a_5183_,
                    );
                    leanh::lean_dec(v_snd_5601_);
                    v___y_5467_ = v___y_5545_;
                    v___y_5468_ = v___y_5551_;
                    v___y_5469_ = v___y_5552_;
                    v___y_5470_ = v___y_5553_;
                    v___y_5471_ = v___y_5554_;
                    v___y_5472_ = v___y_5555_;
                    v___y_5473_ = v_a_5560_;
                    v___y_5474_ = v___y_5557_;
                    v___y_5475_ = v___y_5558_;
                    v___y_5476_ = v___x_5593_;
                    v___y_5477_ = v___x_5616_;
                    state = 24;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_5601_);
                    leanh::lean_dec(v_fst_5600_);
                    leanh::lean_dec_ref(v___y_5549_);
                    leanh::lean_dec(v___y_5548_);
                    leanh::lean_dec_ref(v_e_5179_);
                    v_a_5617_ = leanh::lean_ctor_get(v___x_5614_, 0);
                    leanh::lean_inc(v_a_5617_);
                    leanh::lean_dec_ref_known(v___x_5614_, 1);
                    v___y_5454_ = v___y_5545_;
                    v___y_5455_ = v___y_5551_;
                    v___y_5456_ = v___y_5552_;
                    v___y_5457_ = v___y_5553_;
                    v___y_5458_ = v___y_5554_;
                    v___y_5459_ = v___y_5555_;
                    v___y_5460_ = v_a_5560_;
                    v___y_5461_ = v___y_5557_;
                    v___y_5462_ = v___y_5558_;
                    v___y_5463_ = v___x_5593_;
                    v_a_5464_ = v_a_5617_;
                    state = 23;
                    continue;
                }
            }
            37 => {
                v___x_5625_ = 1;
                if v___y_5624_ == 0 {
                    v___x_5626_ =
                        l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(
                            v_e_5179_, v_a_5183_,
                        );
                    v_a_5627_ = leanh::lean_ctor_get(v___x_5626_, 0);
                    v_isSharedCheck_5795_ = (!leanh::lean_is_exclusive(v___x_5626_)) as u8;
                    if v_isSharedCheck_5795_ == 0 {
                        v___x_5629_ = v___x_5626_;
                        v_isShared_5630_ = v_isSharedCheck_5795_;
                        state = 38;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5627_);
                        leanh::lean_dec(v___x_5626_);
                        v___x_5629_ = leanh::lean_box(0);
                        v_isShared_5630_ = v_isSharedCheck_5795_;
                        state = 38;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_altIdx_5178_);
                    v___x_5796_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(v_e_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_);
                    if leanh::lean_obj_tag(v___x_5796_) == 0 {
                        v_a_5797_ = leanh::lean_ctor_get(v___x_5796_, 0);
                        v_isSharedCheck_5806_ =
                            (!leanh::lean_is_exclusive(v___x_5796_)) as u8;
                        if v_isSharedCheck_5806_ == 0 {
                            v___x_5799_ = v___x_5796_;
                            v_isShared_5800_ = v_isSharedCheck_5806_;
                            state = 52;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5797_);
                            leanh::lean_dec(v___x_5796_);
                            v___x_5799_ = leanh::lean_box(0);
                            v_isShared_5800_ = v_isSharedCheck_5806_;
                            state = 52;
                            continue;
                        }
                    } else {
                        v_a_5807_ = leanh::lean_ctor_get(v___x_5796_, 0);
                        v_isSharedCheck_5814_ =
                            (!leanh::lean_is_exclusive(v___x_5796_)) as u8;
                        if v_isSharedCheck_5814_ == 0 {
                            v___x_5809_ = v___x_5796_;
                            v_isShared_5810_ = v_isSharedCheck_5814_;
                            state = 54;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5807_);
                            leanh::lean_dec(v___x_5796_);
                            v___x_5809_ = leanh::lean_box(0);
                            v_isShared_5810_ = v_isSharedCheck_5814_;
                            state = 54;
                            continue;
                        }
                    }
                }
            }
            38 => {
                v___x_5631_ = (leanh::lean_unbox(v_a_5627_) as u8);
                leanh::lean_dec(v_a_5627_);
                if v___x_5631_ == 0 {
                    leanh::lean_del_object(v___x_5629_);
                    leanh::lean_dec(v_altIdx_5178_);
                    v_options_5632_ = leanh::lean_ctor_get(v_a_5182_, 2);
                    v_hasTrace_5633_ = leanh::lean_ctor_get_uint8(
                        v_options_5632_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5633_ == 0 {
                        v___y_5205_ = v___x_5625_;
                        state = 6;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5634_ = leanh::lean_ctor_get(v_a_5182_, 13);
                        v___x_5635_ = l_Lean_Meta_rwMatcher___closed__12;
                        v___x_5636_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__13),
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__13_once),
                            _init_l_Lean_Meta_rwMatcher___closed__13,
                        );
                        v___x_5637_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5634_,
                            v_options_5632_,
                            v___x_5636_,
                        );
                        if v___x_5637_ == 0 {
                            v___y_5205_ = v___x_5625_;
                            state = 6;
                            continue;
                        } else {
                            v___x_5638_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__15),
                                core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__15_once),
                                _init_l_Lean_Meta_rwMatcher___closed__15,
                            );
                            leanh::lean_inc_ref(v_e_5179_);
                            v___x_5639_ = l_Lean_indentExpr(v_e_5179_);
                            v___x_5640_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5640_, 0, v___x_5638_);
                            leanh::lean_ctor_set(v___x_5640_, 1, v___x_5639_);
                            v___x_5641_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(
                                v___x_5635_,
                                v___x_5640_,
                                v_a_5180_,
                                v_a_5181_,
                                v_a_5182_,
                                v_a_5183_,
                            );
                            if leanh::lean_obj_tag(v___x_5641_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5641_, 1);
                                v___y_5205_ = v___x_5625_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_e_5179_);
                                v_a_5642_ = leanh::lean_ctor_get(v___x_5641_, 0);
                                v_isSharedCheck_5649_ =
                                    (!leanh::lean_is_exclusive(v___x_5641_)) as u8;
                                if v_isSharedCheck_5649_ == 0 {
                                    v___x_5644_ = v___x_5641_;
                                    v_isShared_5645_ = v_isSharedCheck_5649_;
                                    state = 39;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5642_);
                                    leanh::lean_dec(v___x_5641_);
                                    v___x_5644_ = leanh::lean_box(0);
                                    v_isShared_5645_ = v_isSharedCheck_5649_;
                                    state = 39;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_5650_ = l_Lean_Expr_getAppFn(v_e_5179_);
                    v___x_5651_ = l_Lean_Expr_constName_x21(v___x_5650_);
                    leanh::lean_inc(v_a_5183_);
                    leanh::lean_inc_ref(v_a_5182_);
                    leanh::lean_inc(v_a_5181_);
                    leanh::lean_inc_ref(v_a_5180_);
                    leanh::lean_inc(v___x_5651_);
                    v___x_5652_ = lean_get_congr_match_equations_for(
                        v___x_5651_,
                        v_a_5180_,
                        v_a_5181_,
                        v_a_5182_,
                        v_a_5183_,
                    );
                    if leanh::lean_obj_tag(v___x_5652_) == 0 {
                        v_a_5653_ = leanh::lean_ctor_get(v___x_5652_, 0);
                        leanh::lean_inc(v_a_5653_);
                        leanh::lean_dec_ref_known(v___x_5652_, 1);
                        v___x_5654_ = lean_array_get_size(v_a_5653_);
                        v___x_5655_ = lean_nat_dec_lt(v_altIdx_5178_, v___x_5654_);
                        if v___x_5655_ == 0 {
                            leanh::lean_dec(v_a_5653_);
                            leanh::lean_dec_ref(v___x_5650_);
                            v_options_5656_ = leanh::lean_ctor_get(v_a_5182_, 2);
                            v_hasTrace_5657_ = leanh::lean_ctor_get_uint8(
                                v_options_5656_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            );
                            if v_hasTrace_5657_ == 0 {
                                leanh::lean_dec(v___x_5651_);
                                leanh::lean_del_object(v___x_5629_);
                                leanh::lean_dec(v_altIdx_5178_);
                                v___y_5210_ = v___x_5625_;
                                state = 7;
                                continue;
                            } else {
                                v_inheritedTraceOptions_5658_ =
                                    leanh::lean_ctor_get(v_a_5182_, 13);
                                v___x_5659_ = l_Lean_Meta_rwMatcher___closed__12;
                                v___x_5660_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__13),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_rwMatcher___closed__13_once
                                    ),
                                    _init_l_Lean_Meta_rwMatcher___closed__13,
                                );
                                v___x_5661_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v_inheritedTraceOptions_5658_,
                                        v_options_5656_,
                                        v___x_5660_,
                                    );
                                if v___x_5661_ == 0 {
                                    leanh::lean_dec(v___x_5651_);
                                    leanh::lean_del_object(v___x_5629_);
                                    leanh::lean_dec(v_altIdx_5178_);
                                    v___y_5210_ = v___x_5625_;
                                    state = 7;
                                    continue;
                                } else {
                                    v___x_5662_ = leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__17),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_rwMatcher___closed__17_once
                                        ),
                                        _init_l_Lean_Meta_rwMatcher___closed__17,
                                    );
                                    v___x_5663_ = l_Nat_reprFast(v_altIdx_5178_);
                                    if v_isShared_5630_ == 0 {
                                        leanh::lean_ctor_set_tag(v___x_5629_, 3);
                                        leanh::lean_ctor_set(v___x_5629_, 0, v___x_5663_);
                                        v___x_5665_ = v___x_5629_;
                                        state = 41;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5687_ =
                                            leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5687_,
                                            0,
                                            v___x_5663_,
                                        );
                                        v___x_5665_ = v_reuseFailAlloc_5687_;
                                        state = 41;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_5651_);
                            leanh::lean_del_object(v___x_5629_);
                            v_options_5688_ = leanh::lean_ctor_get(v_a_5182_, 2);
                            v_inheritedTraceOptions_5689_ =
                                leanh::lean_ctor_get(v_a_5182_, 13);
                            v_hasTrace_5690_ = leanh::lean_ctor_get_uint8(
                                v_options_5688_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            );
                            v_nargs_5691_ = l_Lean_Expr_getAppNumArgs(v_e_5179_);
                            v___x_5692_ = leanh::lean_box((v___x_5625_) as usize);
                            leanh::lean_inc_ref_n(v_e_5179_, 2);
                            v___f_5693_ = leanh::lean_alloc_closure(
                                l_Lean_Meta_rwMatcher___lam__0___boxed as *mut core::ffi::c_void,
                                8,
                                2,
                            );
                            leanh::lean_closure_set(v___f_5693_, 0, v_e_5179_);
                            leanh::lean_closure_set(v___f_5693_, 1, v___x_5692_);
                            v___x_5694_ = leanh::lean_box(0);
                            v___x_5695_ = lean_array_get(v___x_5694_, v_a_5653_, v_altIdx_5178_);
                            leanh::lean_dec(v_altIdx_5178_);
                            leanh::lean_dec(v_a_5653_);
                            v___x_5696_ = l_Lean_Meta_rwMatcher___closed__12;
                            v___x_5697_ = l_Lean_Expr_constLevels_x21(v___x_5650_);
                            leanh::lean_dec_ref(v___x_5650_);
                            leanh::lean_inc(v___x_5695_);
                            v___x_5698_ = l_Lean_mkConst(v___x_5695_, v___x_5697_);
                            v_dummy_5699_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__22),
                                core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__22_once),
                                _init_l_Lean_Meta_rwMatcher___closed__22,
                            );
                            leanh::lean_inc(v_nargs_5691_);
                            v___x_5700_ = lean_mk_array(v_nargs_5691_, v_dummy_5699_);
                            v___x_5701_ = leanh::lean_unsigned_to_nat(1);
                            v___x_5702_ = lean_nat_sub(v_nargs_5691_, v___x_5701_);
                            leanh::lean_dec(v_nargs_5691_);
                            v___x_5703_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_e_5179_,
                                v___x_5700_,
                                v___x_5702_,
                            );
                            v___x_5704_ = l_Lean_mkAppN(v___x_5698_, v___x_5703_);
                            leanh::lean_dec_ref(v___x_5703_);
                            if v_hasTrace_5690_ == 0 {
                                leanh::lean_inc(v_a_5183_);
                                leanh::lean_inc_ref(v_a_5182_);
                                leanh::lean_inc(v_a_5181_);
                                leanh::lean_inc_ref(v_a_5180_);
                                leanh::lean_inc_ref(v___x_5704_);
                                v___x_5705_ = lean_infer_type(
                                    v___x_5704_,
                                    v_a_5180_,
                                    v_a_5181_,
                                    v_a_5182_,
                                    v_a_5183_,
                                );
                                if leanh::lean_obj_tag(v___x_5705_) == 0 {
                                    v_a_5706_ = leanh::lean_ctor_get(v___x_5705_, 0);
                                    leanh::lean_inc(v_a_5706_);
                                    leanh::lean_dec_ref_known(v___x_5705_, 1);
                                    v___x_5707_ = 0;
                                    v___x_5708_ = l_Lean_Meta_forallMetaTelescope(
                                        v_a_5706_,
                                        v___x_5707_,
                                        v_a_5180_,
                                        v_a_5181_,
                                        v_a_5182_,
                                        v_a_5183_,
                                    );
                                    if leanh::lean_obj_tag(v___x_5708_) == 0 {
                                        v_a_5709_ = leanh::lean_ctor_get(v___x_5708_, 0);
                                        leanh::lean_inc(v_a_5709_);
                                        leanh::lean_dec_ref_known(v___x_5708_, 1);
                                        v_snd_5710_ = leanh::lean_ctor_get(v_a_5709_, 1);
                                        v_fst_5711_ = leanh::lean_ctor_get(v_a_5709_, 0);
                                        v_isSharedCheck_5749_ =
                                            (!leanh::lean_is_exclusive(v_a_5709_)) as u8;
                                        if v_isSharedCheck_5749_ == 0 {
                                            v___x_5713_ = v_a_5709_;
                                            v_isShared_5714_ = v_isSharedCheck_5749_;
                                            state = 44;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_snd_5710_);
                                            leanh::lean_inc(v_fst_5711_);
                                            leanh::lean_dec(v_a_5709_);
                                            v___x_5713_ = leanh::lean_box(0);
                                            v_isShared_5714_ = v_isSharedCheck_5749_;
                                            state = 44;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_5704_);
                                        leanh::lean_dec_ref(v_e_5179_);
                                        v_a_5750_ = leanh::lean_ctor_get(v___x_5708_, 0);
                                        leanh::lean_inc(v_a_5750_);
                                        leanh::lean_dec_ref_known(v___x_5708_, 1);
                                        v___y_5251_ = v___f_5693_;
                                        v___y_5252_ = v___x_5696_;
                                        v___y_5253_ = v___x_5695_;
                                        v_a_5254_ = v_a_5750_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_5704_);
                                    leanh::lean_dec_ref(v_e_5179_);
                                    v_a_5751_ = leanh::lean_ctor_get(v___x_5705_, 0);
                                    leanh::lean_inc(v_a_5751_);
                                    leanh::lean_dec_ref_known(v___x_5705_, 1);
                                    v___y_5251_ = v___f_5693_;
                                    v___y_5252_ = v___x_5696_;
                                    v___y_5253_ = v___x_5695_;
                                    v_a_5254_ = v_a_5751_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                v___x_5752_ = leanh::lean_box((v___y_5624_) as usize);
                                leanh::lean_inc_ref(v_e_5179_);
                                leanh::lean_inc(v___x_5695_);
                                v___f_5753_ = leanh::lean_alloc_closure(
                                    l_Lean_Meta_rwMatcher___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    9,
                                    3,
                                );
                                leanh::lean_closure_set(v___f_5753_, 0, v___x_5695_);
                                leanh::lean_closure_set(v___f_5753_, 1, v___x_5752_);
                                leanh::lean_closure_set(v___f_5753_, 2, v_e_5179_);
                                v___x_5754_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1;
                                v___x_5755_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__13),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_rwMatcher___closed__13_once
                                    ),
                                    _init_l_Lean_Meta_rwMatcher___closed__13,
                                );
                                v___x_5756_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v_inheritedTraceOptions_5689_,
                                        v_options_5688_,
                                        v___x_5755_,
                                    );
                                if v___x_5756_ == 0 {
                                    v___x_5757_ = l_Lean_trace_profiler;
                                    v___x_5758_ =
                                        l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(
                                            v_options_5688_,
                                            v___x_5757_,
                                        );
                                    if v___x_5758_ == 0 {
                                        leanh::lean_dec_ref(v___f_5753_);
                                        leanh::lean_inc(v_a_5183_);
                                        leanh::lean_inc_ref(v_a_5182_);
                                        leanh::lean_inc(v_a_5181_);
                                        leanh::lean_inc_ref(v_a_5180_);
                                        leanh::lean_inc_ref(v___x_5704_);
                                        v___x_5759_ = lean_infer_type(
                                            v___x_5704_,
                                            v_a_5180_,
                                            v_a_5181_,
                                            v_a_5182_,
                                            v_a_5183_,
                                        );
                                        if leanh::lean_obj_tag(v___x_5759_) == 0 {
                                            v_a_5760_ = leanh::lean_ctor_get(v___x_5759_, 0);
                                            leanh::lean_inc(v_a_5760_);
                                            leanh::lean_dec_ref_known(v___x_5759_, 1);
                                            v___x_5761_ = 0;
                                            v___x_5762_ = l_Lean_Meta_forallMetaTelescope(
                                                v_a_5760_,
                                                v___x_5761_,
                                                v_a_5180_,
                                                v_a_5181_,
                                                v_a_5182_,
                                                v_a_5183_,
                                            );
                                            if leanh::lean_obj_tag(v___x_5762_) == 0 {
                                                v_a_5763_ =
                                                    leanh::lean_ctor_get(v___x_5762_, 0);
                                                leanh::lean_inc(v_a_5763_);
                                                leanh::lean_dec_ref_known(v___x_5762_, 1);
                                                v_snd_5764_ =
                                                    leanh::lean_ctor_get(v_a_5763_, 1);
                                                leanh::lean_inc(v_snd_5764_);
                                                if v___x_5756_ == 0 {
                                                    v_fst_5765_ =
                                                        leanh::lean_ctor_get(v_a_5763_, 0);
                                                    leanh::lean_inc(v_fst_5765_);
                                                    leanh::lean_dec(v_a_5763_);
                                                    v_snd_5766_ =
                                                        leanh::lean_ctor_get(v_snd_5764_, 1);
                                                    leanh::lean_inc(v_snd_5766_);
                                                    leanh::lean_dec(v_snd_5764_);
                                                    v___x_5767_ = leanh::lean_box(0);
                                                    leanh::lean_inc(v___x_5695_);
                                                    v___x_5768_ = l_Lean_Meta_rwMatcher___lam__4(
                                                        v___x_5625_,
                                                        v___x_5704_,
                                                        v_fst_5765_,
                                                        v___x_5695_,
                                                        v___x_5758_,
                                                        v_e_5179_,
                                                        v_snd_5766_,
                                                        v___x_5767_,
                                                        v_a_5180_,
                                                        v_a_5181_,
                                                        v_a_5182_,
                                                        v_a_5183_,
                                                    );
                                                    leanh::lean_dec(v_snd_5766_);
                                                    v___y_5258_ = v___f_5693_;
                                                    v___y_5259_ = v___x_5696_;
                                                    v___y_5260_ = v___x_5695_;
                                                    v___y_5261_ = v___x_5768_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    v_fst_5769_ =
                                                        leanh::lean_ctor_get(v_a_5763_, 0);
                                                    leanh::lean_inc(v_fst_5769_);
                                                    leanh::lean_dec(v_a_5763_);
                                                    v_snd_5770_ =
                                                        leanh::lean_ctor_get(v_snd_5764_, 1);
                                                    v_isSharedCheck_5783_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v_snd_5764_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5783_ == 0 {
                                                        v_unused_5784_ =
                                                            leanh::lean_ctor_get(
                                                                v_snd_5764_,
                                                                0,
                                                            );
                                                        leanh::lean_dec(v_unused_5784_);
                                                        v___x_5772_ = v_snd_5764_;
                                                        v_isShared_5773_ = v_isSharedCheck_5783_;
                                                        state = 48;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_snd_5770_);
                                                        leanh::lean_dec(v_snd_5764_);
                                                        v___x_5772_ = leanh::lean_box(0);
                                                        v_isShared_5773_ = v_isSharedCheck_5783_;
                                                        state = 48;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_5704_);
                                                leanh::lean_dec_ref(v_e_5179_);
                                                v_a_5785_ =
                                                    leanh::lean_ctor_get(v___x_5762_, 0);
                                                leanh::lean_inc(v_a_5785_);
                                                leanh::lean_dec_ref_known(v___x_5762_, 1);
                                                v___y_5251_ = v___f_5693_;
                                                v___y_5252_ = v___x_5696_;
                                                v___y_5253_ = v___x_5695_;
                                                v_a_5254_ = v_a_5785_;
                                                state = 12;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_5704_);
                                            leanh::lean_dec_ref(v_e_5179_);
                                            v_a_5786_ = leanh::lean_ctor_get(v___x_5759_, 0);
                                            leanh::lean_inc(v_a_5786_);
                                            leanh::lean_dec_ref_known(v___x_5759_, 1);
                                            v___y_5251_ = v___f_5693_;
                                            v___y_5252_ = v___x_5696_;
                                            v___y_5253_ = v___x_5695_;
                                            v_a_5254_ = v_a_5786_;
                                            state = 12;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_inc_ref(v___x_5704_);
                                        leanh::lean_inc(v___x_5695_);
                                        v___y_5545_ = v___f_5753_;
                                        v___y_5546_ = v___y_5624_;
                                        v___y_5547_ = v___x_5625_;
                                        v___y_5548_ = v___x_5695_;
                                        v___y_5549_ = v___x_5704_;
                                        v___y_5550_ = v_inheritedTraceOptions_5689_;
                                        v___y_5551_ = v___x_5625_;
                                        v___y_5552_ = v___x_5754_;
                                        v___y_5553_ = v___f_5693_;
                                        v___y_5554_ = v___x_5696_;
                                        v___y_5555_ = v_options_5688_;
                                        v___y_5556_ = v___x_5704_;
                                        v___y_5557_ = v___x_5695_;
                                        v___y_5558_ = v___x_5756_;
                                        state = 32;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc_ref(v___x_5704_);
                                    leanh::lean_inc(v___x_5695_);
                                    v___y_5545_ = v___f_5753_;
                                    v___y_5546_ = v___y_5624_;
                                    v___y_5547_ = v___x_5625_;
                                    v___y_5548_ = v___x_5695_;
                                    v___y_5549_ = v___x_5704_;
                                    v___y_5550_ = v_inheritedTraceOptions_5689_;
                                    v___y_5551_ = v___x_5625_;
                                    v___y_5552_ = v___x_5754_;
                                    v___y_5553_ = v___f_5693_;
                                    v___y_5554_ = v___x_5696_;
                                    v___y_5555_ = v_options_5688_;
                                    v___y_5556_ = v___x_5704_;
                                    v___y_5557_ = v___x_5695_;
                                    v___y_5558_ = v___x_5756_;
                                    state = 32;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_5651_);
                        leanh::lean_dec_ref(v___x_5650_);
                        leanh::lean_del_object(v___x_5629_);
                        leanh::lean_dec_ref(v_e_5179_);
                        leanh::lean_dec(v_altIdx_5178_);
                        v_a_5787_ = leanh::lean_ctor_get(v___x_5652_, 0);
                        v_isSharedCheck_5794_ =
                            (!leanh::lean_is_exclusive(v___x_5652_)) as u8;
                        if v_isSharedCheck_5794_ == 0 {
                            v___x_5789_ = v___x_5652_;
                            v_isShared_5790_ = v_isSharedCheck_5794_;
                            state = 50;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5787_);
                            leanh::lean_dec(v___x_5652_);
                            v___x_5789_ = leanh::lean_box(0);
                            v_isShared_5790_ = v_isSharedCheck_5794_;
                            state = 50;
                            continue;
                        }
                    }
                }
            }
            39 => {
                if v_isShared_5645_ == 0 {
                    v___x_5647_ = v___x_5644_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5648_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_a_5642_);
                    v___x_5647_ = v_reuseFailAlloc_5648_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_5647_;
            }
            41 => {
                v___x_5666_ = l_Lean_MessageData_ofFormat(v___x_5665_);
                v___x_5667_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5667_, 0, v___x_5662_);
                leanh::lean_ctor_set(v___x_5667_, 1, v___x_5666_);
                v___x_5668_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__19),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__19_once),
                    _init_l_Lean_Meta_rwMatcher___closed__19,
                );
                v___x_5669_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5669_, 0, v___x_5667_);
                leanh::lean_ctor_set(v___x_5669_, 1, v___x_5668_);
                v___x_5670_ = l_Nat_reprFast(v___x_5654_);
                v___x_5671_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5671_, 0, v___x_5670_);
                v___x_5672_ = l_Lean_MessageData_ofFormat(v___x_5671_);
                v___x_5673_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5673_, 0, v___x_5669_);
                leanh::lean_ctor_set(v___x_5673_, 1, v___x_5672_);
                v___x_5674_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__21),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__21_once),
                    _init_l_Lean_Meta_rwMatcher___closed__21,
                );
                v___x_5675_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5675_, 0, v___x_5673_);
                leanh::lean_ctor_set(v___x_5675_, 1, v___x_5674_);
                v___x_5676_ = l_Lean_MessageData_ofConstName(v___x_5651_, v___y_5624_);
                v___x_5677_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5677_, 0, v___x_5675_);
                leanh::lean_ctor_set(v___x_5677_, 1, v___x_5676_);
                v___x_5678_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(
                    v___x_5659_,
                    v___x_5677_,
                    v_a_5180_,
                    v_a_5181_,
                    v_a_5182_,
                    v_a_5183_,
                );
                if leanh::lean_obj_tag(v___x_5678_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5678_, 1);
                    v___y_5210_ = v___x_5625_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_5179_);
                    v_a_5679_ = leanh::lean_ctor_get(v___x_5678_, 0);
                    v_isSharedCheck_5686_ = (!leanh::lean_is_exclusive(v___x_5678_)) as u8;
                    if v_isSharedCheck_5686_ == 0 {
                        v___x_5681_ = v___x_5678_;
                        v_isShared_5682_ = v_isSharedCheck_5686_;
                        state = 42;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5679_);
                        leanh::lean_dec(v___x_5678_);
                        v___x_5681_ = leanh::lean_box(0);
                        v_isShared_5682_ = v_isSharedCheck_5686_;
                        state = 42;
                        continue;
                    }
                }
            }
            42 => {
                if v_isShared_5682_ == 0 {
                    v___x_5684_ = v___x_5681_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_5685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5685_, 0, v_a_5679_);
                    v___x_5684_ = v_reuseFailAlloc_5685_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_5684_;
            }
            44 => {
                v_snd_5715_ = leanh::lean_ctor_get(v_snd_5710_, 1);
                v_isSharedCheck_5747_ = (!leanh::lean_is_exclusive(v_snd_5710_)) as u8;
                if v_isSharedCheck_5747_ == 0 {
                    v_unused_5748_ = leanh::lean_ctor_get(v_snd_5710_, 0);
                    leanh::lean_dec(v_unused_5748_);
                    v___x_5717_ = v_snd_5710_;
                    v_isShared_5718_ = v_isSharedCheck_5747_;
                    state = 45;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5715_);
                    leanh::lean_dec(v_snd_5710_);
                    v___x_5717_ = leanh::lean_box(0);
                    v_isShared_5718_ = v_isSharedCheck_5747_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                v___x_5719_ = l_Lean_mkAppN(v___x_5704_, v_fst_5711_);
                v_sz_5720_ = lean_array_size(v_fst_5711_);
                v___x_5721_ = 0usize;
                v___x_5722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_5720_, v___x_5721_, v_fst_5711_);
                v___x_5723_ = l_Lean_Meta_rwMatcher___lam__2___closed__18;
                v___x_5724_ = leanh::lean_unsigned_to_nat(4);
                v___x_5725_ = l_Lean_Expr_isAppOfArity(v_snd_5715_, v___x_5723_, v___x_5724_);
                if v___x_5725_ == 0 {
                    v___x_5726_ = l_Lean_Meta_rwMatcher___lam__2___closed__20;
                    v___x_5727_ = leanh::lean_unsigned_to_nat(3);
                    v___x_5728_ = l_Lean_Expr_isAppOfArity(v_snd_5715_, v___x_5726_, v___x_5727_);
                    if v___x_5728_ == 0 {
                        leanh::lean_dec_ref(v___x_5722_);
                        leanh::lean_dec_ref(v___x_5719_);
                        leanh::lean_dec(v_snd_5715_);
                        leanh::lean_dec_ref(v_e_5179_);
                        v___x_5729_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__22),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_rwMatcher___lam__2___closed__22_once
                            ),
                            _init_l_Lean_Meta_rwMatcher___lam__2___closed__22,
                        );
                        leanh::lean_inc(v___x_5695_);
                        v___x_5730_ = l_Lean_MessageData_ofConstName(v___x_5695_, v_hasTrace_5690_);
                        if v_isShared_5718_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_5717_, 7);
                            leanh::lean_ctor_set(v___x_5717_, 1, v___x_5730_);
                            leanh::lean_ctor_set(v___x_5717_, 0, v___x_5729_);
                            v___x_5732_ = v___x_5717_;
                            state = 46;
                            continue;
                        } else {
                            v_reuseFailAlloc_5739_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5739_, 0, v___x_5729_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5739_, 1, v___x_5730_);
                            v___x_5732_ = v_reuseFailAlloc_5739_;
                            state = 46;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_5717_);
                        leanh::lean_del_object(v___x_5713_);
                        v___x_5740_ = l_Lean_Expr_appFn_x21(v_snd_5715_);
                        v___x_5741_ = l_Lean_Expr_appArg_x21(v___x_5740_);
                        leanh::lean_dec_ref(v___x_5740_);
                        v___x_5742_ = l_Lean_Expr_appArg_x21(v_snd_5715_);
                        leanh::lean_dec(v_snd_5715_);
                        v___y_5399_ = v_hasTrace_5690_;
                        v___y_5400_ = v___x_5625_;
                        v___y_5401_ = v___f_5693_;
                        v___y_5402_ = v___x_5721_;
                        v___y_5403_ = v___x_5696_;
                        v___y_5404_ = v___x_5695_;
                        v___y_5405_ = v___x_5719_;
                        v___y_5406_ = v___x_5722_;
                        v_fst_5407_ = v_hasTrace_5690_;
                        v_fst_5408_ = v___x_5741_;
                        v_snd_5409_ = v___x_5742_;
                        v___y_5410_ = v_a_5180_;
                        v___y_5411_ = v_a_5181_;
                        v___y_5412_ = v_a_5182_;
                        v___y_5413_ = v_a_5183_;
                        state = 21;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5717_);
                    leanh::lean_del_object(v___x_5713_);
                    v___x_5743_ = l_Lean_Expr_appFn_x21(v_snd_5715_);
                    v___x_5744_ = l_Lean_Expr_appFn_x21(v___x_5743_);
                    leanh::lean_dec_ref(v___x_5743_);
                    v___x_5745_ = l_Lean_Expr_appArg_x21(v___x_5744_);
                    leanh::lean_dec_ref(v___x_5744_);
                    v___x_5746_ = l_Lean_Expr_appArg_x21(v_snd_5715_);
                    leanh::lean_dec(v_snd_5715_);
                    v___y_5399_ = v_hasTrace_5690_;
                    v___y_5400_ = v___x_5625_;
                    v___y_5401_ = v___f_5693_;
                    v___y_5402_ = v___x_5721_;
                    v___y_5403_ = v___x_5696_;
                    v___y_5404_ = v___x_5695_;
                    v___y_5405_ = v___x_5719_;
                    v___y_5406_ = v___x_5722_;
                    v_fst_5407_ = v___x_5625_;
                    v_fst_5408_ = v___x_5745_;
                    v_snd_5409_ = v___x_5746_;
                    v___y_5410_ = v_a_5180_;
                    v___y_5411_ = v_a_5181_;
                    v___y_5412_ = v_a_5182_;
                    v___y_5413_ = v_a_5183_;
                    state = 21;
                    continue;
                }
            }
            46 => {
                v___x_5733_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__24),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___lam__2___closed__24_once),
                    _init_l_Lean_Meta_rwMatcher___lam__2___closed__24,
                );
                if v_isShared_5714_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5713_, 7);
                    leanh::lean_ctor_set(v___x_5713_, 1, v___x_5733_);
                    leanh::lean_ctor_set(v___x_5713_, 0, v___x_5732_);
                    v___x_5735_ = v___x_5713_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_5738_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5738_, 0, v___x_5732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5738_, 1, v___x_5733_);
                    v___x_5735_ = v_reuseFailAlloc_5738_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                v___x_5736_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
                    v___x_5735_,
                    v_a_5180_,
                    v_a_5181_,
                    v_a_5182_,
                    v_a_5183_,
                );
                v_a_5737_ = leanh::lean_ctor_get(v___x_5736_, 0);
                leanh::lean_inc(v_a_5737_);
                leanh::lean_dec_ref(v___x_5736_);
                v___y_5251_ = v___f_5693_;
                v___y_5252_ = v___x_5696_;
                v___y_5253_ = v___x_5695_;
                v_a_5254_ = v_a_5737_;
                state = 12;
                continue;
            }
            48 => {
                v___x_5774_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_rwMatcher___closed__8_once),
                    _init_l_Lean_Meta_rwMatcher___closed__8,
                );
                leanh::lean_inc(v_snd_5770_);
                v___x_5775_ = l_Lean_indentExpr(v_snd_5770_);
                if v_isShared_5773_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5772_, 7);
                    leanh::lean_ctor_set(v___x_5772_, 1, v___x_5775_);
                    leanh::lean_ctor_set(v___x_5772_, 0, v___x_5774_);
                    v___x_5777_ = v___x_5772_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_5782_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5782_, 0, v___x_5774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5782_, 1, v___x_5775_);
                    v___x_5777_ = v_reuseFailAlloc_5782_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                v___x_5778_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(
                    v___x_5696_,
                    v___x_5777_,
                    v_a_5180_,
                    v_a_5181_,
                    v_a_5182_,
                    v_a_5183_,
                );
                if leanh::lean_obj_tag(v___x_5778_) == 0 {
                    v_a_5779_ = leanh::lean_ctor_get(v___x_5778_, 0);
                    leanh::lean_inc(v_a_5779_);
                    leanh::lean_dec_ref_known(v___x_5778_, 1);
                    leanh::lean_inc(v___x_5695_);
                    v___x_5780_ = l_Lean_Meta_rwMatcher___lam__4(
                        v___x_5625_,
                        v___x_5704_,
                        v_fst_5769_,
                        v___x_5695_,
                        v___x_5758_,
                        v_e_5179_,
                        v_snd_5770_,
                        v_a_5779_,
                        v_a_5180_,
                        v_a_5181_,
                        v_a_5182_,
                        v_a_5183_,
                    );
                    leanh::lean_dec(v_snd_5770_);
                    v___y_5258_ = v___f_5693_;
                    v___y_5259_ = v___x_5696_;
                    v___y_5260_ = v___x_5695_;
                    v___y_5261_ = v___x_5780_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_5770_);
                    leanh::lean_dec(v_fst_5769_);
                    leanh::lean_dec_ref(v___x_5704_);
                    leanh::lean_dec_ref(v_e_5179_);
                    v_a_5781_ = leanh::lean_ctor_get(v___x_5778_, 0);
                    leanh::lean_inc(v_a_5781_);
                    leanh::lean_dec_ref_known(v___x_5778_, 1);
                    v___y_5251_ = v___f_5693_;
                    v___y_5252_ = v___x_5696_;
                    v___y_5253_ = v___x_5695_;
                    v_a_5254_ = v_a_5781_;
                    state = 12;
                    continue;
                }
            }
            50 => {
                if v_isShared_5790_ == 0 {
                    v___x_5792_ = v___x_5789_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_5793_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5793_, 0, v_a_5787_);
                    v___x_5792_ = v_reuseFailAlloc_5793_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_5792_;
            }
            52 => {
                v___x_5801_ = leanh::lean_box(0);
                v___x_5802_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_5802_, 0, v_a_5797_);
                leanh::lean_ctor_set(v___x_5802_, 1, v___x_5801_);
                leanh::lean_ctor_set_uint8(
                    v___x_5802_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5625_,
                );
                if v_isShared_5800_ == 0 {
                    leanh::lean_ctor_set(v___x_5799_, 0, v___x_5802_);
                    v___x_5804_ = v___x_5799_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_5805_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5805_, 0, v___x_5802_);
                    v___x_5804_ = v_reuseFailAlloc_5805_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_5804_;
            }
            54 => {
                if v_isShared_5810_ == 0 {
                    v___x_5812_ = v___x_5809_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_5813_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5813_, 0, v_a_5807_);
                    v___x_5812_ = v_reuseFailAlloc_5813_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_5812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_rwMatcher___boxed(
    mut v_altIdx_5819_: *mut leanh::LeanObject,
    mut v_e_5820_: *mut leanh::LeanObject,
    mut v_a_5821_: *mut leanh::LeanObject,
    mut v_a_5822_: *mut leanh::LeanObject,
    mut v_a_5823_: *mut leanh::LeanObject,
    mut v_a_5824_: *mut leanh::LeanObject,
    mut v_a_5825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5826_ = l_Lean_Meta_rwMatcher(
        v_altIdx_5819_,
        v_e_5820_,
        v_a_5821_,
        v_a_5822_,
        v_a_5823_,
        v_a_5824_,
    );
    leanh::lean_dec(v_a_5824_);
    leanh::lean_dec_ref(v_a_5823_);
    leanh::lean_dec(v_a_5822_);
    leanh::lean_dec_ref(v_a_5821_);
    return v_res_5826_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(
    mut v_mvarId_5827_: *mut leanh::LeanObject,
    mut v___y_5828_: *mut leanh::LeanObject,
    mut v___y_5829_: *mut leanh::LeanObject,
    mut v___y_5830_: *mut leanh::LeanObject,
    mut v___y_5831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5833_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(
        v_mvarId_5827_,
        v___y_5829_,
    );
    return v___x_5833_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(
    mut v_mvarId_5834_: *mut leanh::LeanObject,
    mut v___y_5835_: *mut leanh::LeanObject,
    mut v___y_5836_: *mut leanh::LeanObject,
    mut v___y_5837_: *mut leanh::LeanObject,
    mut v___y_5838_: *mut leanh::LeanObject,
    mut v___y_5839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5840_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(
        v_mvarId_5834_,
        v___y_5835_,
        v___y_5836_,
        v___y_5837_,
        v___y_5838_,
    );
    leanh::lean_dec(v___y_5838_);
    leanh::lean_dec_ref(v___y_5837_);
    leanh::lean_dec(v___y_5836_);
    leanh::lean_dec_ref(v___y_5835_);
    leanh::lean_dec(v_mvarId_5834_);
    return v_res_5840_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(
    mut v_00_u03b1_5841_: *mut leanh::LeanObject,
    mut v_msg_5842_: *mut leanh::LeanObject,
    mut v___y_5843_: *mut leanh::LeanObject,
    mut v___y_5844_: *mut leanh::LeanObject,
    mut v___y_5845_: *mut leanh::LeanObject,
    mut v___y_5846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5848_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(
        v_msg_5842_,
        v___y_5843_,
        v___y_5844_,
        v___y_5845_,
        v___y_5846_,
    );
    return v___x_5848_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___boxed(
    mut v_00_u03b1_5849_: *mut leanh::LeanObject,
    mut v_msg_5850_: *mut leanh::LeanObject,
    mut v___y_5851_: *mut leanh::LeanObject,
    mut v___y_5852_: *mut leanh::LeanObject,
    mut v___y_5853_: *mut leanh::LeanObject,
    mut v___y_5854_: *mut leanh::LeanObject,
    mut v___y_5855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5856_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(
        v_00_u03b1_5849_,
        v_msg_5850_,
        v___y_5851_,
        v___y_5852_,
        v___y_5853_,
        v___y_5854_,
    );
    leanh::lean_dec(v___y_5854_);
    leanh::lean_dec_ref(v___y_5853_);
    leanh::lean_dec(v___y_5852_);
    leanh::lean_dec_ref(v___y_5851_);
    return v_res_5856_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(
    mut v_00_u03b1_5857_: *mut leanh::LeanObject,
    mut v_x_5858_: *mut leanh::LeanObject,
    mut v___y_5859_: *mut leanh::LeanObject,
    mut v___y_5860_: *mut leanh::LeanObject,
    mut v___y_5861_: *mut leanh::LeanObject,
    mut v___y_5862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5864_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_x_5858_);
    return v___x_5864_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(
    mut v_00_u03b1_5865_: *mut leanh::LeanObject,
    mut v_x_5866_: *mut leanh::LeanObject,
    mut v___y_5867_: *mut leanh::LeanObject,
    mut v___y_5868_: *mut leanh::LeanObject,
    mut v___y_5869_: *mut leanh::LeanObject,
    mut v___y_5870_: *mut leanh::LeanObject,
    mut v___y_5871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5872_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_00_u03b1_5865_, v_x_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
    leanh::lean_dec(v___y_5870_);
    leanh::lean_dec_ref(v___y_5869_);
    leanh::lean_dec(v___y_5868_);
    leanh::lean_dec_ref(v___y_5867_);
    return v_res_5872_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14(
    mut v_inst_5873_: *mut leanh::LeanObject,
    mut v_a_5874_: *mut leanh::LeanObject,
    mut v___y_5875_: *mut leanh::LeanObject,
    mut v___y_5876_: *mut leanh::LeanObject,
    mut v___y_5877_: *mut leanh::LeanObject,
    mut v___y_5878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5880_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(
            v_a_5874_,
            v___y_5875_,
            v___y_5876_,
            v___y_5877_,
            v___y_5878_,
        );
    return v___x_5880_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___boxed(
    mut v_inst_5881_: *mut leanh::LeanObject,
    mut v_a_5882_: *mut leanh::LeanObject,
    mut v___y_5883_: *mut leanh::LeanObject,
    mut v___y_5884_: *mut leanh::LeanObject,
    mut v___y_5885_: *mut leanh::LeanObject,
    mut v___y_5886_: *mut leanh::LeanObject,
    mut v___y_5887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5888_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14(
        v_inst_5881_,
        v_a_5882_,
        v___y_5883_,
        v___y_5884_,
        v___y_5885_,
        v___y_5886_,
    );
    leanh::lean_dec(v___y_5886_);
    leanh::lean_dec_ref(v___y_5885_);
    leanh::lean_dec(v___y_5884_);
    leanh::lean_dec_ref(v___y_5883_);
    return v_res_5888_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(
    mut v_00_u03b2_5889_: *mut leanh::LeanObject,
    mut v_x_5890_: *mut leanh::LeanObject,
    mut v_x_5891_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5892_: u8 = 0;
    v___x_5892_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_5890_, v_x_5891_);
    return v___x_5892_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(
    mut v_00_u03b2_5893_: *mut leanh::LeanObject,
    mut v_x_5894_: *mut leanh::LeanObject,
    mut v_x_5895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5896_: u8 = 0;
    let mut v_r_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5896_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(v_00_u03b2_5893_, v_x_5894_, v_x_5895_);
    leanh::lean_dec(v_x_5895_);
    leanh::lean_dec_ref(v_x_5894_);
    v_r_5897_ = leanh::lean_box((v_res_5896_) as usize);
    return v_r_5897_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(
    mut v_00_u03b2_5898_: *mut leanh::LeanObject,
    mut v_x_5899_: *mut leanh::LeanObject,
    mut v_x_5900_: usize,
    mut v_x_5901_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5902_: u8 = 0;
    v___x_5902_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_5899_, v_x_5900_, v_x_5901_);
    return v___x_5902_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(
    mut v_00_u03b2_5903_: *mut leanh::LeanObject,
    mut v_x_5904_: *mut leanh::LeanObject,
    mut v_x_5905_: *mut leanh::LeanObject,
    mut v_x_5906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_112373__boxed_5907_: usize = 0;
    let mut v_res_5908_: u8 = 0;
    let mut v_r_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_112373__boxed_5907_ = leanh::lean_unbox_usize(v_x_5905_);
    leanh::lean_dec(v_x_5905_);
    v_res_5908_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(v_00_u03b2_5903_, v_x_5904_, v_x_112373__boxed_5907_, v_x_5906_);
    leanh::lean_dec(v_x_5906_);
    leanh::lean_dec_ref(v_x_5904_);
    v_r_5909_ = leanh::lean_box((v_res_5908_) as usize);
    return v_r_5909_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20(
    mut v_00_u03b2_5910_: *mut leanh::LeanObject,
    mut v_keys_5911_: *mut leanh::LeanObject,
    mut v_vals_5912_: *mut leanh::LeanObject,
    mut v_heq_5913_: *mut leanh::LeanObject,
    mut v_i_5914_: *mut leanh::LeanObject,
    mut v_k_5915_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5916_: u8 = 0;
    v___x_5916_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(v_keys_5911_, v_i_5914_, v_k_5915_);
    return v___x_5916_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___boxed(
    mut v_00_u03b2_5917_: *mut leanh::LeanObject,
    mut v_keys_5918_: *mut leanh::LeanObject,
    mut v_vals_5919_: *mut leanh::LeanObject,
    mut v_heq_5920_: *mut leanh::LeanObject,
    mut v_i_5921_: *mut leanh::LeanObject,
    mut v_k_5922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5923_: u8 = 0;
    let mut v_r_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5923_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20(v_00_u03b2_5917_, v_keys_5918_, v_vals_5919_, v_heq_5920_, v_i_5921_, v_k_5922_);
    leanh::lean_dec(v_k_5922_);
    leanh::lean_dec_ref(v_vals_5919_);
    leanh::lean_dec_ref(v_keys_5918_);
    v_r_5924_ = leanh::lean_box((v_res_5923_) as usize);
    return v_r_5924_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_Rewrite(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_Rewrite(
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
pub unsafe fn initialize_Lean_Meta_Match_Rewrite(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assumption(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Match_Rewrite(builtin);
}