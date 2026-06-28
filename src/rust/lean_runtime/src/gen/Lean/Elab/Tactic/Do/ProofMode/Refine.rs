// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Refine
// Imports: Lean.Elab.Tactic.Do.ProofMode.Assumption
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_instReprTSyntax_repr___redArg,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr6,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_SavedState_restore___redArg, l_Lean_Elab_Tactic_evalTactic,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_saveState___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withoutRecover___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Assumption::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Basic::l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg;
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Exact::{
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr;
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::l_Lean_Elab_Tactic_elabTerm;
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_expandMacroImpl_x3f;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_beta, l_Lean_Expr_getAppFn_x27,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isConstOf, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_sort___override, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_instInhabitedExpr, l_Lean_mkApp6, l_Lean_mkConst,
};
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::r#gen::Std::Tactic::Do::Syntax::l_Lean_Parser_Tactic_MRefinePat_parse___boxed;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq,
    lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_9, lean_apply_11, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1_value)
                as *mut LeanObject,
            13771926289831477797 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1_value: LeanStringObject<53> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 53,
        m_capacity: 53,
        m_length: 52,
        m_data: [
            78, 101, 105, 116, 104, 101, 114, 32, 97, 32, 99, 111, 110, 106, 117, 110, 99, 116,
            105, 111, 110, 32, 110, 111, 114, 32, 97, 110, 32, 101, 120, 105, 115, 116, 101, 110,
            116, 105, 97, 108, 32, 113, 117, 97, 110, 116, 105, 102, 105, 101, 114, 32, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            101, 120, 105, 115, 116, 115, 95, 105, 110, 116, 114, 111, 39, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4_value: LeanStringObject<55> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 55,
        m_capacity: 55,
        m_length: 53,
        m_data: [
            112, 97, 116, 116, 101, 114, 110, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 101,
            108, 97, 98, 111, 114, 97, 116, 101, 32, 116, 111, 32, 97, 32, 116, 101, 114, 109, 32,
            116, 111, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 32, 207, 136, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [101, 120, 105, 115, 116, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [97, 110, 100, 95, 105, 110, 116, 114, 111, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value: LeanStringObject<4> =
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
        m_data: [83, 116, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [68, 111, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [83, 80, 114, 101, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value: LeanStringObject<4> =
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
        m_data: [97, 110, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value)
                as *mut LeanObject,
            14620467112940626392 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value)
                as *mut LeanObject,
            142734480563613395 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value)
                as *mut LeanObject,
            6030293614678436448 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19_value: LeanStringObject<4> =
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
        m_data: [102, 58, 32, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [44, 32, 97, 114, 103, 115, 58, 32, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 115, 111, 108, 118, 101, 32, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            32, 98, 121, 32, 97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            117, 110, 107, 110, 111, 119, 110, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105,
            115, 32, 96, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [96, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0: u64 = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7_value) as *mut LeanObject,7870113334857981723 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1_value) as *mut LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0_value: LeanStringObject<158> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [109, 114, 101, 102, 105, 110, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2_value)
                as *mut LeanObject,
            6333567104024089553 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 108, 97, 98, 77, 82, 101, 102, 105, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2_value) as *mut LeanObject,5372934286266800045 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 13, m_data: [109, 114, 101, 102, 105, 110, 101, 80, 97, 116, 226, 159, 168, 95, 226, 159, 169, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1_value) as *mut LeanObject,14125490278268599519 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 114, 101, 102, 105, 110, 101, 80, 97, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4_value) as *mut LeanObject,8766709874229489008 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 13, m_data: [109, 114, 101, 102, 105, 110, 101, 80, 97, 116, 226, 140, 156, 95, 226, 140, 157, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0_value) as *mut LeanObject,10488206668377814853 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 140, 156, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 140, 157, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [109, 101, 120, 105, 115, 116, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0_value)
                as *mut LeanObject,
            1667259957697292907 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [112, 97, 114, 101, 110, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2_value)
                as *mut LeanObject,
            8689124066155232629 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [40, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [59, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [116, 97, 99, 116, 105, 99, 84, 114, 121, 95, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10_value)
                as *mut LeanObject,
            10962186005905108258 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12_value: LeanStringObject<4> =
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
        m_data: [116, 114, 121, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [109, 97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13_value)
                as *mut LeanObject,
            1814919757381564531 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [41, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16_value: LeanStringObject<13> =
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
        m_data: [109, 114, 101, 102, 105, 110, 101, 80, 97, 116, 63, 95, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16_value)
                as *mut LeanObject,
            12626967213392556061 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [63, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [104, 111, 108, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20_value)
                as *mut LeanObject,
            3984140175429830279 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [95, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 108, 97, 98, 77, 69, 120, 105, 115, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0_value) as *mut LeanObject,8076920694872788882 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(
    mut v_pat_2576_: *mut LeanObject,
    mut v_expected_2577_: *mut LeanObject,
    mut v_a_2578_: *mut LeanObject,
    mut v_a_2579_: *mut LeanObject,
    mut v_a_2580_: *mut LeanObject,
    mut v_a_2581_: *mut LeanObject,
    mut v_a_2582_: *mut LeanObject,
    mut v_a_2583_: *mut LeanObject,
    mut v_a_2584_: *mut LeanObject,
    mut v_a_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2602_: u8 = 0;
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2607_: u8 = 0;
    let mut v_a_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2611_: u8 = 0;
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2615_: u8 = 0;
    let mut v_h_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: u8 = 0;
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: u8 = 0;
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2635_: u8 = 0;
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_pat_2576_) {
                2 => {
                    v_h_2616_ = lean_ctor_get(v_pat_2576_, 0);
                    lean_inc(v_h_2616_);
                    lean_dec_ref_known(v_pat_2576_, 1);
                    v_t_2588_ = v_h_2616_;
                    v___y_2589_ = v_a_2578_;
                    v___y_2590_ = v_a_2579_;
                    v___y_2591_ = v_a_2580_;
                    v___y_2592_ = v_a_2581_;
                    v___y_2593_ = v_a_2582_;
                    v___y_2594_ = v_a_2583_;
                    v___y_2595_ = v_a_2584_;
                    v___y_2596_ = v_a_2585_;
                    state = 1;
                    continue;
                }
                0 => {
                    v_name_2617_ = lean_ctor_get(v_pat_2576_, 0);
                    v_isSharedCheck_2635_ = (!lean_is_exclusive(v_pat_2576_)) as u8;
                    if v_isSharedCheck_2635_ == 0 {
                        v___x_2619_ = v_pat_2576_;
                        v_isShared_2620_ = v_isSharedCheck_2635_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_name_2617_);
                        lean_dec(v_pat_2576_);
                        v___x_2619_ = lean_box(0);
                        v_isShared_2620_ = v_isSharedCheck_2635_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_expected_2577_);
                    lean_dec_ref(v_pat_2576_);
                    v___x_2636_ = lean_box(0);
                    v___x_2637_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2637_, 0, v___x_2636_);
                    return v___x_2637_;
                }
            },
            1 => {
                v___x_2597_ = 0;
                v___x_2598_ = l_Lean_Elab_Tactic_elabTerm(
                    v_t_2588_,
                    v_expected_2577_,
                    v___x_2597_,
                    v___y_2589_,
                    v___y_2590_,
                    v___y_2591_,
                    v___y_2592_,
                    v___y_2593_,
                    v___y_2594_,
                    v___y_2595_,
                    v___y_2596_,
                );
                if lean_obj_tag(v___x_2598_) == 0 {
                    v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
                    v_isSharedCheck_2607_ = (!lean_is_exclusive(v___x_2598_)) as u8;
                    if v_isSharedCheck_2607_ == 0 {
                        v___x_2601_ = v___x_2598_;
                        v_isShared_2602_ = v_isSharedCheck_2607_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2599_);
                        lean_dec(v___x_2598_);
                        v___x_2601_ = lean_box(0);
                        v_isShared_2602_ = v_isSharedCheck_2607_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2608_ = lean_ctor_get(v___x_2598_, 0);
                    v_isSharedCheck_2615_ = (!lean_is_exclusive(v___x_2598_)) as u8;
                    if v_isSharedCheck_2615_ == 0 {
                        v___x_2610_ = v___x_2598_;
                        v_isShared_2611_ = v_isSharedCheck_2615_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2608_);
                        lean_dec(v___x_2598_);
                        v___x_2610_ = lean_box(0);
                        v_isShared_2611_ = v_isSharedCheck_2615_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2603_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2603_, 0, v_a_2599_);
                if v_isShared_2602_ == 0 {
                    lean_ctor_set(v___x_2601_, 0, v___x_2603_);
                    v___x_2605_ = v___x_2601_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
                    v___x_2605_ = v_reuseFailAlloc_2606_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2605_;
            }
            4 => {
                if v_isShared_2611_ == 0 {
                    v___x_2613_ = v___x_2610_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
                    v___x_2613_ = v_reuseFailAlloc_2614_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2613_;
            }
            6 => {
                v___x_2621_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
                lean_inc(v_name_2617_);
                v___x_2622_ = l_Lean_Syntax_isOfKind(v_name_2617_, v___x_2621_);
                if v___x_2622_ == 0 {
                    lean_dec(v_name_2617_);
                    lean_dec(v_expected_2577_);
                    v___x_2623_ = lean_box(0);
                    if v_isShared_2620_ == 0 {
                        lean_ctor_set(v___x_2619_, 0, v___x_2623_);
                        v___x_2625_ = v___x_2619_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
                        v___x_2625_ = v_reuseFailAlloc_2626_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_2627_ = lean_unsigned_to_nat(0);
                    v___x_2628_ = l_Lean_Syntax_getArg(v_name_2617_, v___x_2627_);
                    lean_dec(v_name_2617_);
                    v___x_2629_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4;
                    lean_inc(v___x_2628_);
                    v___x_2630_ = l_Lean_Syntax_isOfKind(v___x_2628_, v___x_2629_);
                    if v___x_2630_ == 0 {
                        lean_dec(v___x_2628_);
                        lean_dec(v_expected_2577_);
                        v___x_2631_ = lean_box(0);
                        if v_isShared_2620_ == 0 {
                            lean_ctor_set(v___x_2619_, 0, v___x_2631_);
                            v___x_2633_ = v___x_2619_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
                            v___x_2633_ = v_reuseFailAlloc_2634_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2619_);
                        v_t_2588_ = v___x_2628_;
                        v___y_2589_ = v_a_2578_;
                        v___y_2590_ = v_a_2579_;
                        v___y_2591_ = v_a_2580_;
                        v___y_2592_ = v_a_2581_;
                        v___y_2593_ = v_a_2582_;
                        v___y_2594_ = v_a_2583_;
                        v___y_2595_ = v_a_2584_;
                        v___y_2596_ = v_a_2585_;
                        state = 1;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2625_;
            }
            8 => {
                return v___x_2633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___boxed(
    mut v_pat_2638_: *mut LeanObject,
    mut v_expected_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
    mut v_a_2641_: *mut LeanObject,
    mut v_a_2642_: *mut LeanObject,
    mut v_a_2643_: *mut LeanObject,
    mut v_a_2644_: *mut LeanObject,
    mut v_a_2645_: *mut LeanObject,
    mut v_a_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
    mut v_a_2648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2649_: *mut LeanObject = core::ptr::null_mut();
    v_res_2649_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(
        v_pat_2638_,
        v_expected_2639_,
        v_a_2640_,
        v_a_2641_,
        v_a_2642_,
        v_a_2643_,
        v_a_2644_,
        v_a_2645_,
        v_a_2646_,
        v_a_2647_,
    );
    lean_dec(v_a_2647_);
    lean_dec_ref(v_a_2646_);
    lean_dec(v_a_2645_);
    lean_dec_ref(v_a_2644_);
    lean_dec(v_a_2643_);
    lean_dec_ref(v_a_2642_);
    lean_dec(v_a_2641_);
    lean_dec_ref(v_a_2640_);
    return v_res_2649_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    v___x_2650_ = lean_box(0);
    v___x_2651_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2652_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2652_, 0, v___x_2651_);
    lean_ctor_set(v___x_2652_, 1, v___x_2650_);
    return v___x_2652_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    v___x_2654_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0);
    v___x_2655_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2655_, 0, v___x_2654_);
    return v___x_2655_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___boxed(
    mut v___y_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2657_: *mut LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
    return v_res_2657_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0(
    mut v_00_u03b1_2658_: *mut LeanObject,
    mut v___y_2659_: *mut LeanObject,
    mut v___y_2660_: *mut LeanObject,
    mut v___y_2661_: *mut LeanObject,
    mut v___y_2662_: *mut LeanObject,
    mut v___y_2663_: *mut LeanObject,
    mut v___y_2664_: *mut LeanObject,
    mut v___y_2665_: *mut LeanObject,
    mut v___y_2666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    v___x_2668_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
    return v___x_2668_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___boxed(
    mut v_00_u03b1_2669_: *mut LeanObject,
    mut v___y_2670_: *mut LeanObject,
    mut v___y_2671_: *mut LeanObject,
    mut v___y_2672_: *mut LeanObject,
    mut v___y_2673_: *mut LeanObject,
    mut v___y_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
    mut v___y_2676_: *mut LeanObject,
    mut v___y_2677_: *mut LeanObject,
    mut v___y_2678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2679_: *mut LeanObject = core::ptr::null_mut();
    v_res_2679_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0(v_00_u03b1_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
    lean_dec(v___y_2677_);
    lean_dec_ref(v___y_2676_);
    lean_dec(v___y_2675_);
    lean_dec_ref(v___y_2674_);
    lean_dec(v___y_2673_);
    lean_dec_ref(v___y_2672_);
    lean_dec(v___y_2671_);
    lean_dec_ref(v___y_2670_);
    return v_res_2679_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(
    mut v___x_2680_: *mut LeanObject,
    mut v_00___2681_: *mut LeanObject,
) -> u8 {
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: u8 = 0;
    v___x_2682_ = lean_unsigned_to_nat(3);
    v___x_2683_ = lean_array_get_size(v___x_2680_);
    v___x_2684_ = lean_nat_dec_le(v___x_2682_, v___x_2683_);
    return v___x_2684_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0___boxed(
    mut v___x_2685_: *mut LeanObject,
    mut v_00___2686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2687_: u8 = 0;
    let mut v_r_2688_: *mut LeanObject = core::ptr::null_mut();
    v_res_2687_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(v___x_2685_, v_00___2686_);
    lean_dec_ref(v___x_2685_);
    v_r_2688_ = lean_box((v_res_2687_) as usize);
    return v_r_2688_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__2(
    mut v_a_2689_: *mut LeanObject,
    mut v_a_2690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2696_: u8 = 0;
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2689_) == 0 {
                    v___x_2691_ = l_List_reverse___redArg(v_a_2690_);
                    return v___x_2691_;
                } else {
                    v_head_2692_ = lean_ctor_get(v_a_2689_, 0);
                    v_tail_2693_ = lean_ctor_get(v_a_2689_, 1);
                    v_isSharedCheck_2702_ = (!lean_is_exclusive(v_a_2689_)) as u8;
                    if v_isSharedCheck_2702_ == 0 {
                        v___x_2695_ = v_a_2689_;
                        v_isShared_2696_ = v_isSharedCheck_2702_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2693_);
                        lean_inc(v_head_2692_);
                        lean_dec(v_a_2689_);
                        v___x_2695_ = lean_box(0);
                        v_isShared_2696_ = v_isSharedCheck_2702_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2697_ = l_Lean_MessageData_ofExpr(v_head_2692_);
                if v_isShared_2696_ == 0 {
                    lean_ctor_set(v___x_2695_, 1, v_a_2690_);
                    lean_ctor_set(v___x_2695_, 0, v___x_2697_);
                    v___x_2699_ = v___x_2695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2697_);
                    lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_a_2690_);
                    v___x_2699_ = v_reuseFailAlloc_2701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2689_ = v_tail_2693_;
                v_a_2690_ = v___x_2699_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(
    mut v_msgData_2703_: *mut LeanObject,
    mut v___y_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    v___x_2709_ = lean_st_ref_get(v___y_2707_);
    v_env_2710_ = lean_ctor_get(v___x_2709_, 0);
    lean_inc_ref(v_env_2710_);
    lean_dec(v___x_2709_);
    v___x_2711_ = lean_st_ref_get(v___y_2705_);
    v_mctx_2712_ = lean_ctor_get(v___x_2711_, 0);
    lean_inc_ref(v_mctx_2712_);
    lean_dec(v___x_2711_);
    v_lctx_2713_ = lean_ctor_get(v___y_2704_, 2);
    v_options_2714_ = lean_ctor_get(v___y_2706_, 2);
    lean_inc_ref(v_options_2714_);
    lean_inc_ref(v_lctx_2713_);
    v___x_2715_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2715_, 0, v_env_2710_);
    lean_ctor_set(v___x_2715_, 1, v_mctx_2712_);
    lean_ctor_set(v___x_2715_, 2, v_lctx_2713_);
    lean_ctor_set(v___x_2715_, 3, v_options_2714_);
    v___x_2716_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2716_, 0, v___x_2715_);
    lean_ctor_set(v___x_2716_, 1, v_msgData_2703_);
    v___x_2717_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2717_, 0, v___x_2716_);
    return v___x_2717_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1___boxed(
    mut v_msgData_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2724_: *mut LeanObject = core::ptr::null_mut();
    v_res_2724_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msgData_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
    lean_dec(v___y_2722_);
    lean_dec_ref(v___y_2721_);
    lean_dec(v___y_2720_);
    lean_dec_ref(v___y_2719_);
    return v_res_2724_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(
    mut v_msg_2725_: *mut LeanObject,
    mut v___y_2726_: *mut LeanObject,
    mut v___y_2727_: *mut LeanObject,
    mut v___y_2728_: *mut LeanObject,
    mut v___y_2729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2736_: u8 = 0;
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2731_ = lean_ctor_get(v___y_2728_, 5);
                v___x_2732_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
                v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
                v_isSharedCheck_2741_ = (!lean_is_exclusive(v___x_2732_)) as u8;
                if v_isSharedCheck_2741_ == 0 {
                    v___x_2735_ = v___x_2732_;
                    v_isShared_2736_ = v_isSharedCheck_2741_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2733_);
                    lean_dec(v___x_2732_);
                    v___x_2735_ = lean_box(0);
                    v_isShared_2736_ = v_isSharedCheck_2741_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2731_);
                v___x_2737_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2737_, 0, v_ref_2731_);
                lean_ctor_set(v___x_2737_, 1, v_a_2733_);
                if v_isShared_2736_ == 0 {
                    lean_ctor_set_tag(v___x_2735_, 1);
                    lean_ctor_set(v___x_2735_, 0, v___x_2737_);
                    v___x_2739_ = v___x_2735_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
                    v___x_2739_ = v_reuseFailAlloc_2740_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg___boxed(
    mut v_msg_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
    mut v___y_2744_: *mut LeanObject,
    mut v___y_2745_: *mut LeanObject,
    mut v___y_2746_: *mut LeanObject,
    mut v___y_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2748_: *mut LeanObject = core::ptr::null_mut();
    v_res_2748_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(
            v_msg_2742_,
            v___y_2743_,
            v___y_2744_,
            v___y_2745_,
            v___y_2746_,
        );
    lean_dec(v___y_2746_);
    lean_dec_ref(v___y_2745_);
    lean_dec(v___y_2744_);
    lean_dec_ref(v___y_2743_);
    return v_res_2748_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0()
-> f64 {
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: f64 = 0.0;
    v___x_2749_ = lean_unsigned_to_nat(0);
    v___x_2750_ = lean_float_of_nat(v___x_2749_);
    return v___x_2750_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(
    mut v_cls_2754_: *mut LeanObject,
    mut v_msg_2755_: *mut LeanObject,
    mut v___y_2756_: *mut LeanObject,
    mut v___y_2757_: *mut LeanObject,
    mut v___y_2758_: *mut LeanObject,
    mut v___y_2759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2779_: u8 = 0;
    let mut v_tid_2780_: u64 = 0;
    let mut v_traces_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: f64 = 0.0;
    let mut v___x_2787_: u8 = 0;
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2761_ = lean_ctor_get(v___y_2758_, 5);
                v___x_2762_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
                v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
                v_isSharedCheck_2807_ = (!lean_is_exclusive(v___x_2762_)) as u8;
                if v_isSharedCheck_2807_ == 0 {
                    v___x_2765_ = v___x_2762_;
                    v_isShared_2766_ = v_isSharedCheck_2807_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2763_);
                    lean_dec(v___x_2762_);
                    v___x_2765_ = lean_box(0);
                    v_isShared_2766_ = v_isSharedCheck_2807_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2767_ = lean_st_ref_take(v___y_2759_);
                v_traceState_2768_ = lean_ctor_get(v___x_2767_, 4);
                v_env_2769_ = lean_ctor_get(v___x_2767_, 0);
                v_nextMacroScope_2770_ = lean_ctor_get(v___x_2767_, 1);
                v_ngen_2771_ = lean_ctor_get(v___x_2767_, 2);
                v_auxDeclNGen_2772_ = lean_ctor_get(v___x_2767_, 3);
                v_cache_2773_ = lean_ctor_get(v___x_2767_, 5);
                v_messages_2774_ = lean_ctor_get(v___x_2767_, 6);
                v_infoState_2775_ = lean_ctor_get(v___x_2767_, 7);
                v_snapshotTasks_2776_ = lean_ctor_get(v___x_2767_, 8);
                v_isSharedCheck_2806_ = (!lean_is_exclusive(v___x_2767_)) as u8;
                if v_isSharedCheck_2806_ == 0 {
                    v___x_2778_ = v___x_2767_;
                    v_isShared_2779_ = v_isSharedCheck_2806_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2776_);
                    lean_inc(v_infoState_2775_);
                    lean_inc(v_messages_2774_);
                    lean_inc(v_cache_2773_);
                    lean_inc(v_traceState_2768_);
                    lean_inc(v_auxDeclNGen_2772_);
                    lean_inc(v_ngen_2771_);
                    lean_inc(v_nextMacroScope_2770_);
                    lean_inc(v_env_2769_);
                    lean_dec(v___x_2767_);
                    v___x_2778_ = lean_box(0);
                    v_isShared_2779_ = v_isSharedCheck_2806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2780_ = lean_ctor_get_uint64(
                    v_traceState_2768_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2781_ = lean_ctor_get(v_traceState_2768_, 0);
                v_isSharedCheck_2805_ = (!lean_is_exclusive(v_traceState_2768_)) as u8;
                if v_isSharedCheck_2805_ == 0 {
                    v___x_2783_ = v_traceState_2768_;
                    v_isShared_2784_ = v_isSharedCheck_2805_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2781_);
                    lean_dec(v_traceState_2768_);
                    v___x_2783_ = lean_box(0);
                    v_isShared_2784_ = v_isSharedCheck_2805_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2785_ = lean_box(0);
                v___x_2786_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0);
                v___x_2787_ = 0;
                v___x_2788_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1;
                v___x_2789_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2789_, 0, v_cls_2754_);
                lean_ctor_set(v___x_2789_, 1, v___x_2785_);
                lean_ctor_set(v___x_2789_, 2, v___x_2788_);
                lean_ctor_set_float(
                    v___x_2789_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2786_,
                );
                lean_ctor_set_float(
                    v___x_2789_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2786_,
                );
                lean_ctor_set_uint8(
                    v___x_2789_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2787_,
                );
                v___x_2790_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2;
                v___x_2791_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2791_, 0, v___x_2789_);
                lean_ctor_set(v___x_2791_, 1, v_a_2763_);
                lean_ctor_set(v___x_2791_, 2, v___x_2790_);
                lean_inc(v_ref_2761_);
                v___x_2792_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2792_, 0, v_ref_2761_);
                lean_ctor_set(v___x_2792_, 1, v___x_2791_);
                v___x_2793_ = l_Lean_PersistentArray_push___redArg(v_traces_2781_, v___x_2792_);
                if v_isShared_2784_ == 0 {
                    lean_ctor_set(v___x_2783_, 0, v___x_2793_);
                    v___x_2795_ = v___x_2783_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2793_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2804_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2780_,
                    );
                    v___x_2795_ = v_reuseFailAlloc_2804_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2779_ == 0 {
                    lean_ctor_set(v___x_2778_, 4, v___x_2795_);
                    v___x_2797_ = v___x_2778_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_env_2769_);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_nextMacroScope_2770_);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 2, v_ngen_2771_);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 3, v_auxDeclNGen_2772_);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 4, v___x_2795_);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 5, v_cache_2773_);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 6, v_messages_2774_);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 7, v_infoState_2775_);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 8, v_snapshotTasks_2776_);
                    v___x_2797_ = v_reuseFailAlloc_2803_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2798_ = lean_st_ref_set(v___y_2759_, v___x_2797_);
                v___x_2799_ = lean_box(0);
                if v_isShared_2766_ == 0 {
                    lean_ctor_set(v___x_2765_, 0, v___x_2799_);
                    v___x_2801_ = v___x_2765_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
                    v___x_2801_ = v_reuseFailAlloc_2802_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___boxed(
    mut v_cls_2808_: *mut LeanObject,
    mut v_msg_2809_: *mut LeanObject,
    mut v___y_2810_: *mut LeanObject,
    mut v___y_2811_: *mut LeanObject,
    mut v___y_2812_: *mut LeanObject,
    mut v___y_2813_: *mut LeanObject,
    mut v___y_2814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2815_: *mut LeanObject = core::ptr::null_mut();
    v_res_2815_ =
        l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(
            v_cls_2808_,
            v_msg_2809_,
            v___y_2810_,
            v___y_2811_,
            v___y_2812_,
            v___y_2813_,
        );
    lean_dec(v___y_2813_);
    lean_dec_ref(v___y_2812_);
    lean_dec(v___y_2811_);
    lean_dec_ref(v___y_2810_);
    return v_res_2815_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(
    mut v_msg_2816_: *mut LeanObject,
    mut v___y_2817_: *mut LeanObject,
    mut v___y_2818_: *mut LeanObject,
    mut v___y_2819_: *mut LeanObject,
    mut v___y_2820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2822_ = lean_ctor_get(v___y_2819_, 5);
                v___x_2823_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
                v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
                v_isSharedCheck_2832_ = (!lean_is_exclusive(v___x_2823_)) as u8;
                if v_isSharedCheck_2832_ == 0 {
                    v___x_2826_ = v___x_2823_;
                    v_isShared_2827_ = v_isSharedCheck_2832_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2824_);
                    lean_dec(v___x_2823_);
                    v___x_2826_ = lean_box(0);
                    v_isShared_2827_ = v_isSharedCheck_2832_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2822_);
                v___x_2828_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2828_, 0, v_ref_2822_);
                lean_ctor_set(v___x_2828_, 1, v_a_2824_);
                if v_isShared_2827_ == 0 {
                    lean_ctor_set_tag(v___x_2826_, 1);
                    lean_ctor_set(v___x_2826_, 0, v___x_2828_);
                    v___x_2830_ = v___x_2826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
                    v___x_2830_ = v_reuseFailAlloc_2831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg___boxed(
    mut v_msg_2833_: *mut LeanObject,
    mut v___y_2834_: *mut LeanObject,
    mut v___y_2835_: *mut LeanObject,
    mut v___y_2836_: *mut LeanObject,
    mut v___y_2837_: *mut LeanObject,
    mut v___y_2838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2839_: *mut LeanObject = core::ptr::null_mut();
    v_res_2839_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(
            v_msg_2833_,
            v___y_2834_,
            v___y_2835_,
            v___y_2836_,
            v___y_2837_,
        );
    lean_dec(v___y_2837_);
    lean_dec_ref(v___y_2836_);
    lean_dec(v___y_2835_);
    lean_dec_ref(v___y_2834_);
    return v_res_2839_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0() -> *mut LeanObject {
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2841_: *mut LeanObject = core::ptr::null_mut();
    v___x_2840_ = lean_box(0);
    v_dummy_2841_ = l_Lean_Expr_sort___override(v___x_2840_);
    return v_dummy_2841_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2() -> *mut LeanObject {
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    v___x_2843_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1;
    v___x_2844_ = l_Lean_stringToMessageData(v___x_2843_);
    return v___x_2844_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5() -> *mut LeanObject {
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    v___x_2847_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4;
    v___x_2848_ = l_Lean_stringToMessageData(v___x_2847_);
    return v___x_2848_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18() -> *mut LeanObject {
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    v___x_2868_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15;
    v___x_2869_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17;
    v___x_2870_ = l_Lean_Name_append(v___x_2869_, v___x_2868_);
    return v___x_2870_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20() -> *mut LeanObject {
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    v___x_2872_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19;
    v___x_2873_ = l_Lean_stringToMessageData(v___x_2872_);
    return v___x_2873_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22() -> *mut LeanObject {
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    v___x_2875_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21;
    v___x_2876_ = l_Lean_stringToMessageData(v___x_2875_);
    return v___x_2876_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24() -> *mut LeanObject {
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    v___x_2878_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23;
    v___x_2879_ = l_Lean_stringToMessageData(v___x_2878_);
    return v___x_2879_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26() -> *mut LeanObject {
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    v___x_2881_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25;
    v___x_2882_ = l_Lean_stringToMessageData(v___x_2881_);
    return v___x_2882_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28() -> *mut LeanObject {
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    v___x_2884_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27;
    v___x_2885_ = l_Lean_stringToMessageData(v___x_2884_);
    return v___x_2885_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30() -> *mut LeanObject {
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    v___x_2887_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29;
    v___x_2888_ = l_Lean_stringToMessageData(v___x_2887_);
    return v___x_2888_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___boxed(
    mut v_goal_2889_: *mut LeanObject,
    mut v_pat_2890_: *mut LeanObject,
    mut v_k_2891_: *mut LeanObject,
    mut v_a_2892_: *mut LeanObject,
    mut v_a_2893_: *mut LeanObject,
    mut v_a_2894_: *mut LeanObject,
    mut v_a_2895_: *mut LeanObject,
    mut v_a_2896_: *mut LeanObject,
    mut v_a_2897_: *mut LeanObject,
    mut v_a_2898_: *mut LeanObject,
    mut v_a_2899_: *mut LeanObject,
    mut v_a_2900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2901_: *mut LeanObject = core::ptr::null_mut();
    v_res_2901_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
        v_goal_2889_,
        v_pat_2890_,
        v_k_2891_,
        v_a_2892_,
        v_a_2893_,
        v_a_2894_,
        v_a_2895_,
        v_a_2896_,
        v_a_2897_,
        v_a_2898_,
        v_a_2899_,
    );
    lean_dec(v_a_2899_);
    lean_dec_ref(v_a_2898_);
    lean_dec(v_a_2897_);
    lean_dec_ref(v_a_2896_);
    lean_dec(v_a_2895_);
    lean_dec_ref(v_a_2894_);
    lean_dec(v_a_2893_);
    lean_dec_ref(v_a_2892_);
    return v_res_2901_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
    mut v_goal_2902_: *mut LeanObject,
    mut v_pat_2903_: *mut LeanObject,
    mut v_k_2904_: *mut LeanObject,
    mut v_a_2905_: *mut LeanObject,
    mut v_a_2906_: *mut LeanObject,
    mut v_a_2907_: *mut LeanObject,
    mut v_a_2908_: *mut LeanObject,
    mut v_a_2909_: *mut LeanObject,
    mut v_a_2910_: *mut LeanObject,
    mut v_a_2911_: *mut LeanObject,
    mut v_a_2912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2917_: u8 = 0;
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: u8 = 0;
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: u8 = 0;
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2940_: u8 = 0;
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2952_: u8 = 0;
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_isSharedCheck_2957_: u8 = 0;
    let mut v_unused_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    let mut v___x_2960_: u8 = 0;
    let mut v_reuseFailAlloc_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2965_: u8 = 0;
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2969_: u8 = 0;
    let mut v_isSharedCheck_2970_: u8 = 0;
    let mut v_args_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2982_: u8 = 0;
    let mut v_u_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2989_: u8 = 0;
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2995_: u8 = 0;
    let mut v_inheritedTraceOptions_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2997_: u8 = 0;
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3017_: u8 = 0;
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut v_a_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3067_: u8 = 0;
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3071_: u8 = 0;
    let mut v_reuseFailAlloc_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3079_: u8 = 0;
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut v_reuseFailAlloc_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3097_: u8 = 0;
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: u8 = 0;
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3126_: u8 = 0;
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3136_: u8 = 0;
    let mut v_reuseFailAlloc_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut v___y_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: u8 = 0;
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: u8 = 0;
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: u8 = 0;
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3176_: u8 = 0;
    let mut v_isSharedCheck_3177_: u8 = 0;
    let mut v_isSharedCheck_3178_: u8 = 0;
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v_unused_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut v_h_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v_val_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3203_: u8 = 0;
    let mut v_a_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3207_: u8 = 0;
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3211_: u8 = 0;
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3220_: u8 = 0;
    let mut v_val_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_a_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3236_: u8 = 0;
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3245_: u8 = 0;
    let mut v_val_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut v_a_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v_name_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_pat_2903_) {
                0 => {
                    v_name_2914_ = lean_ctor_get(v_pat_2903_, 0);
                    v_isSharedCheck_2970_ = (!lean_is_exclusive(v_pat_2903_)) as u8;
                    if v_isSharedCheck_2970_ == 0 {
                        v___x_2916_ = v_pat_2903_;
                        v_isShared_2917_ = v_isSharedCheck_2970_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_name_2914_);
                        lean_dec(v_pat_2903_);
                        v___x_2916_ = lean_box(0);
                        v_isShared_2917_ = v_isSharedCheck_2970_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_args_2971_ = lean_ctor_get(v_pat_2903_, 0);
                    v_isSharedCheck_3181_ = (!lean_is_exclusive(v_pat_2903_)) as u8;
                    if v_isSharedCheck_3181_ == 0 {
                        v___x_2973_ = v_pat_2903_;
                        v_isShared_2974_ = v_isSharedCheck_3181_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_args_2971_);
                        lean_dec(v_pat_2903_);
                        v___x_2973_ = lean_box(0);
                        v_isShared_2974_ = v_isSharedCheck_3181_;
                        state = 12;
                        continue;
                    }
                }
                2 => {
                    lean_dec_ref(v_k_2904_);
                    v_h_3182_ = lean_ctor_get(v_pat_2903_, 0);
                    lean_inc(v_h_3182_);
                    lean_dec_ref_known(v_pat_2903_, 1);
                    v___x_3183_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(
                        v_goal_2902_,
                        v_h_3182_,
                        v_a_2905_,
                        v_a_2906_,
                        v_a_2907_,
                        v_a_2908_,
                        v_a_2909_,
                        v_a_2910_,
                        v_a_2911_,
                        v_a_2912_,
                    );
                    return v___x_3183_;
                }
                3 => {
                    lean_dec_ref(v_k_2904_);
                    v_h_3184_ = lean_ctor_get(v_pat_2903_, 0);
                    lean_inc_n(v_h_3184_, 2);
                    lean_dec_ref_known(v_pat_2903_, 1);
                    v___x_3185_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
                    v___x_3186_ = l_Lean_Syntax_isOfKind(v_h_3184_, v___x_3185_);
                    if v___x_3186_ == 0 {
                        lean_dec(v_h_3184_);
                        lean_inc_ref(v_goal_2902_);
                        v___x_3187_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(
                            v_goal_2902_,
                            v_a_2909_,
                            v_a_2910_,
                            v_a_2911_,
                            v_a_2912_,
                        );
                        if lean_obj_tag(v___x_3187_) == 0 {
                            v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
                            v_isSharedCheck_3203_ = (!lean_is_exclusive(v___x_3187_)) as u8;
                            if v_isSharedCheck_3203_ == 0 {
                                v___x_3190_ = v___x_3187_;
                                v_isShared_3191_ = v_isSharedCheck_3203_;
                                state = 35;
                                continue;
                            } else {
                                lean_inc(v_a_3188_);
                                lean_dec(v___x_3187_);
                                v___x_3190_ = lean_box(0);
                                v_isShared_3191_ = v_isSharedCheck_3203_;
                                state = 35;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_goal_2902_);
                            v_a_3204_ = lean_ctor_get(v___x_3187_, 0);
                            v_isSharedCheck_3211_ = (!lean_is_exclusive(v___x_3187_)) as u8;
                            if v_isSharedCheck_3211_ == 0 {
                                v___x_3206_ = v___x_3187_;
                                v_isShared_3207_ = v_isSharedCheck_3211_;
                                state = 37;
                                continue;
                            } else {
                                lean_inc(v_a_3204_);
                                lean_dec(v___x_3187_);
                                v___x_3206_ = lean_box(0);
                                v_isShared_3207_ = v_isSharedCheck_3211_;
                                state = 37;
                                continue;
                            }
                        }
                    } else {
                        v___x_3212_ = lean_unsigned_to_nat(0);
                        v_name_3213_ = l_Lean_Syntax_getArg(v_h_3184_, v___x_3212_);
                        lean_dec(v_h_3184_);
                        v___x_3214_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4;
                        lean_inc(v_name_3213_);
                        v___x_3215_ = l_Lean_Syntax_isOfKind(v_name_3213_, v___x_3214_);
                        if v___x_3215_ == 0 {
                            lean_dec(v_name_3213_);
                            lean_inc_ref(v_goal_2902_);
                            v___x_3216_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(
                                v_goal_2902_,
                                v_a_2909_,
                                v_a_2910_,
                                v_a_2911_,
                                v_a_2912_,
                            );
                            if lean_obj_tag(v___x_3216_) == 0 {
                                v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
                                v_isSharedCheck_3232_ = (!lean_is_exclusive(v___x_3216_)) as u8;
                                if v_isSharedCheck_3232_ == 0 {
                                    v___x_3219_ = v___x_3216_;
                                    v_isShared_3220_ = v_isSharedCheck_3232_;
                                    state = 39;
                                    continue;
                                } else {
                                    lean_inc(v_a_3217_);
                                    lean_dec(v___x_3216_);
                                    v___x_3219_ = lean_box(0);
                                    v_isShared_3220_ = v_isSharedCheck_3232_;
                                    state = 39;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_goal_2902_);
                                v_a_3233_ = lean_ctor_get(v___x_3216_, 0);
                                v_isSharedCheck_3240_ = (!lean_is_exclusive(v___x_3216_)) as u8;
                                if v_isSharedCheck_3240_ == 0 {
                                    v___x_3235_ = v___x_3216_;
                                    v_isShared_3236_ = v_isSharedCheck_3240_;
                                    state = 41;
                                    continue;
                                } else {
                                    lean_inc(v_a_3233_);
                                    lean_dec(v___x_3216_);
                                    v___x_3235_ = lean_box(0);
                                    v_isShared_3236_ = v_isSharedCheck_3240_;
                                    state = 41;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc(v_name_3213_);
                            v___x_3241_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(
                                v_goal_2902_,
                                v_name_3213_,
                                v_a_2909_,
                                v_a_2910_,
                                v_a_2911_,
                                v_a_2912_,
                            );
                            if lean_obj_tag(v___x_3241_) == 0 {
                                v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
                                v_isSharedCheck_3257_ = (!lean_is_exclusive(v___x_3241_)) as u8;
                                if v_isSharedCheck_3257_ == 0 {
                                    v___x_3244_ = v___x_3241_;
                                    v_isShared_3245_ = v_isSharedCheck_3257_;
                                    state = 43;
                                    continue;
                                } else {
                                    lean_inc(v_a_3242_);
                                    lean_dec(v___x_3241_);
                                    v___x_3244_ = lean_box(0);
                                    v_isShared_3245_ = v_isSharedCheck_3257_;
                                    state = 43;
                                    continue;
                                }
                            } else {
                                lean_dec(v_name_3213_);
                                v_a_3258_ = lean_ctor_get(v___x_3241_, 0);
                                v_isSharedCheck_3265_ = (!lean_is_exclusive(v___x_3241_)) as u8;
                                if v_isSharedCheck_3265_ == 0 {
                                    v___x_3260_ = v___x_3241_;
                                    v_isShared_3261_ = v_isSharedCheck_3265_;
                                    state = 45;
                                    continue;
                                } else {
                                    lean_inc(v_a_3258_);
                                    lean_dec(v___x_3241_);
                                    v___x_3260_ = lean_box(0);
                                    v_isShared_3261_ = v_isSharedCheck_3265_;
                                    state = 45;
                                    continue;
                                }
                            }
                        }
                    }
                }
                _ => {
                    v_name_3266_ = lean_ctor_get(v_pat_2903_, 0);
                    lean_inc(v_name_3266_);
                    lean_dec_ref_known(v_pat_2903_, 1);
                    lean_inc(v_a_2912_);
                    lean_inc_ref(v_a_2911_);
                    lean_inc(v_a_2910_);
                    lean_inc_ref(v_a_2909_);
                    lean_inc(v_a_2908_);
                    lean_inc_ref(v_a_2907_);
                    lean_inc(v_a_2906_);
                    lean_inc_ref(v_a_2905_);
                    v___x_3267_ = lean_apply_11(
                        v_k_2904_,
                        v_goal_2902_,
                        v_name_3266_,
                        v_a_2905_,
                        v_a_2906_,
                        v_a_2907_,
                        v_a_2908_,
                        v_a_2909_,
                        v_a_2910_,
                        v_a_2911_,
                        v_a_2912_,
                        lean_box(0),
                    );
                    return v___x_3267_;
                }
            },
            1 => {
                v___x_2918_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
                lean_inc(v_name_2914_);
                v___x_2919_ = l_Lean_Syntax_isOfKind(v_name_2914_, v___x_2918_);
                if v___x_2919_ == 0 {
                    if v_isShared_2917_ == 0 {
                        lean_ctor_set_tag(v___x_2916_, 3);
                        v___x_2921_ = v___x_2916_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2923_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_name_2914_);
                        v___x_2921_ = v_reuseFailAlloc_2923_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2924_ = lean_unsigned_to_nat(0);
                    v___x_2925_ = l_Lean_Syntax_getArg(v_name_2914_, v___x_2924_);
                    v___x_2926_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4;
                    v___x_2927_ = l_Lean_Syntax_isOfKind(v___x_2925_, v___x_2926_);
                    if v___x_2927_ == 0 {
                        if v_isShared_2917_ == 0 {
                            lean_ctor_set_tag(v___x_2916_, 3);
                            v___x_2929_ = v___x_2916_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2931_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_name_2914_);
                            v___x_2929_ = v_reuseFailAlloc_2931_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2932_ = l_Lean_Elab_Tactic_saveState___redArg(
                            v_a_2906_, v_a_2908_, v_a_2910_, v_a_2912_,
                        );
                        if lean_obj_tag(v___x_2932_) == 0 {
                            v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
                            lean_inc(v_a_2933_);
                            lean_dec_ref_known(v___x_2932_, 1);
                            lean_inc(v_name_2914_);
                            if v_isShared_2917_ == 0 {
                                lean_ctor_set_tag(v___x_2916_, 2);
                                v___x_2935_ = v___x_2916_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2961_ = lean_alloc_ctor(2, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_name_2914_);
                                v___x_2935_ = v_reuseFailAlloc_2961_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2916_);
                            lean_dec(v_name_2914_);
                            lean_dec_ref(v_k_2904_);
                            lean_dec_ref(v_goal_2902_);
                            v_a_2962_ = lean_ctor_get(v___x_2932_, 0);
                            v_isSharedCheck_2969_ = (!lean_is_exclusive(v___x_2932_)) as u8;
                            if v_isSharedCheck_2969_ == 0 {
                                v___x_2964_ = v___x_2932_;
                                v_isShared_2965_ = v_isSharedCheck_2969_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_2962_);
                                lean_dec(v___x_2932_);
                                v___x_2964_ = lean_box(0);
                                v_isShared_2965_ = v_isSharedCheck_2969_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v_pat_2903_ = v___x_2921_;
                state = 0;
                continue;
            }
            3 => {
                v_pat_2903_ = v___x_2929_;
                state = 0;
                continue;
            }
            4 => {
                lean_inc_ref(v_k_2904_);
                lean_inc_ref(v_goal_2902_);
                v___x_2936_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___boxed as *mut core::ffi::c_void,
                    12,
                    3,
                );
                lean_closure_set(v___x_2936_, 0, v_goal_2902_);
                lean_closure_set(v___x_2936_, 1, v___x_2935_);
                lean_closure_set(v___x_2936_, 2, v_k_2904_);
                v___x_2937_ = l_Lean_Elab_Tactic_withoutRecover___redArg(
                    v___x_2936_,
                    v_a_2905_,
                    v_a_2906_,
                    v_a_2907_,
                    v_a_2908_,
                    v_a_2909_,
                    v_a_2910_,
                    v_a_2911_,
                    v_a_2912_,
                );
                if lean_obj_tag(v___x_2937_) == 0 {
                    lean_dec(v_a_2933_);
                    lean_dec(v_name_2914_);
                    lean_dec_ref(v_k_2904_);
                    lean_dec_ref(v_goal_2902_);
                    return v___x_2937_;
                } else {
                    v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
                    lean_inc(v_a_2938_);
                    v___x_2959_ = l_Lean_Exception_isInterrupt(v_a_2938_);
                    if v___x_2959_ == 0 {
                        v___x_2960_ = l_Lean_Exception_isRuntime(v_a_2938_);
                        v___y_2940_ = v___x_2960_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_a_2938_);
                        v___y_2940_ = v___x_2959_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v___y_2940_ == 0 {
                    v_isSharedCheck_2957_ = (!lean_is_exclusive(v___x_2937_)) as u8;
                    if v_isSharedCheck_2957_ == 0 {
                        v_unused_2958_ = lean_ctor_get(v___x_2937_, 0);
                        lean_dec(v_unused_2958_);
                        v___x_2942_ = v___x_2937_;
                        v_isShared_2943_ = v_isSharedCheck_2957_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v___x_2937_);
                        v___x_2942_ = lean_box(0);
                        v_isShared_2943_ = v_isSharedCheck_2957_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2933_);
                    lean_dec(v_name_2914_);
                    lean_dec_ref(v_k_2904_);
                    lean_dec_ref(v_goal_2902_);
                    return v___x_2937_;
                }
            }
            6 => {
                v___x_2944_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                    v_a_2933_,
                    v___y_2940_,
                    v_a_2906_,
                    v_a_2907_,
                    v_a_2908_,
                    v_a_2909_,
                    v_a_2910_,
                    v_a_2911_,
                    v_a_2912_,
                );
                if lean_obj_tag(v___x_2944_) == 0 {
                    lean_dec_ref_known(v___x_2944_, 1);
                    if v_isShared_2943_ == 0 {
                        lean_ctor_set_tag(v___x_2942_, 3);
                        lean_ctor_set(v___x_2942_, 0, v_name_2914_);
                        v___x_2946_ = v___x_2942_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2948_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_name_2914_);
                        v___x_2946_ = v_reuseFailAlloc_2948_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2942_);
                    lean_dec(v_name_2914_);
                    lean_dec_ref(v_k_2904_);
                    lean_dec_ref(v_goal_2902_);
                    v_a_2949_ = lean_ctor_get(v___x_2944_, 0);
                    v_isSharedCheck_2956_ = (!lean_is_exclusive(v___x_2944_)) as u8;
                    if v_isSharedCheck_2956_ == 0 {
                        v___x_2951_ = v___x_2944_;
                        v_isShared_2952_ = v_isSharedCheck_2956_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2949_);
                        lean_dec(v___x_2944_);
                        v___x_2951_ = lean_box(0);
                        v_isShared_2952_ = v_isSharedCheck_2956_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                v_pat_2903_ = v___x_2946_;
                state = 0;
                continue;
            }
            8 => {
                if v_isShared_2952_ == 0 {
                    v___x_2954_ = v___x_2951_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
                    v___x_2954_ = v_reuseFailAlloc_2955_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2954_;
            }
            10 => {
                if v_isShared_2965_ == 0 {
                    v___x_2967_ = v___x_2964_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
                    v___x_2967_ = v_reuseFailAlloc_2968_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2967_;
            }
            12 => {
                if lean_obj_tag(v_args_2971_) == 0 {
                    lean_del_object(v___x_2973_);
                    lean_dec_ref(v_k_2904_);
                    lean_dec_ref(v_goal_2902_);
                    v___x_2975_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
                    return v___x_2975_;
                } else {
                    v_tail_2976_ = lean_ctor_get(v_args_2971_, 1);
                    if lean_obj_tag(v_tail_2976_) == 0 {
                        lean_del_object(v___x_2973_);
                        v_head_2977_ = lean_ctor_get(v_args_2971_, 0);
                        lean_inc(v_head_2977_);
                        lean_dec_ref_known(v_args_2971_, 2);
                        v_pat_2903_ = v_head_2977_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_tail_2976_);
                        v_head_2979_ = lean_ctor_get(v_args_2971_, 0);
                        v_isSharedCheck_3179_ = (!lean_is_exclusive(v_args_2971_)) as u8;
                        if v_isSharedCheck_3179_ == 0 {
                            v_unused_3180_ = lean_ctor_get(v_args_2971_, 1);
                            lean_dec(v_unused_3180_);
                            v___x_2981_ = v_args_2971_;
                            v_isShared_2982_ = v_isSharedCheck_3179_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_head_2979_);
                            lean_dec(v_args_2971_);
                            v___x_2981_ = lean_box(0);
                            v_isShared_2982_ = v_isSharedCheck_3179_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            13 => {
                v_u_2983_ = lean_ctor_get(v_goal_2902_, 0);
                v_00_u03c3s_2984_ = lean_ctor_get(v_goal_2902_, 1);
                v_hyps_2985_ = lean_ctor_get(v_goal_2902_, 2);
                v_target_2986_ = lean_ctor_get(v_goal_2902_, 3);
                v_isSharedCheck_3178_ = (!lean_is_exclusive(v_goal_2902_)) as u8;
                if v_isSharedCheck_3178_ == 0 {
                    v___x_2988_ = v_goal_2902_;
                    v_isShared_2989_ = v_isSharedCheck_3178_;
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_target_2986_);
                    lean_inc(v_hyps_2985_);
                    lean_inc(v_00_u03c3s_2984_);
                    lean_inc(v_u_2983_);
                    lean_dec(v_goal_2902_);
                    v___x_2988_ = lean_box(0);
                    v_isShared_2989_ = v_isSharedCheck_3178_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2990_ =
                    l_Lean_Meta_whnfR(v_target_2986_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
                if lean_obj_tag(v___x_2990_) == 0 {
                    v_options_2991_ = lean_ctor_get(v_a_2911_, 2);
                    v_a_2992_ = lean_ctor_get(v___x_2990_, 0);
                    v_isSharedCheck_3177_ = (!lean_is_exclusive(v___x_2990_)) as u8;
                    if v_isSharedCheck_3177_ == 0 {
                        v___x_2994_ = v___x_2990_;
                        v_isShared_2995_ = v_isSharedCheck_3177_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_2992_);
                        lean_dec(v___x_2990_);
                        v___x_2994_ = lean_box(0);
                        v_isShared_2995_ = v_isSharedCheck_3177_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2988_);
                    lean_dec_ref(v_hyps_2985_);
                    lean_dec_ref(v_00_u03c3s_2984_);
                    lean_dec(v_u_2983_);
                    lean_del_object(v___x_2981_);
                    lean_dec(v_head_2979_);
                    lean_dec(v_tail_2976_);
                    lean_del_object(v___x_2973_);
                    lean_dec_ref(v_k_2904_);
                    return v___x_2990_;
                }
            }
            15 => {
                v_inheritedTraceOptions_2996_ = lean_ctor_get(v_a_2911_, 13);
                v_hasTrace_2997_ = lean_ctor_get_uint8(
                    v_options_2991_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_2998_ = l_Lean_Expr_getAppFn_x27(v_a_2992_);
                v_nargs_2999_ = l_Lean_Expr_getAppNumArgs(v_a_2992_);
                v_dummy_3000_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0,
                );
                lean_inc(v_nargs_2999_);
                v___x_3001_ = lean_mk_array(v_nargs_2999_, v_dummy_3000_);
                v___x_3002_ = lean_unsigned_to_nat(1);
                v___x_3003_ = lean_nat_sub(v_nargs_2999_, v___x_3002_);
                lean_dec(v_nargs_2999_);
                lean_inc(v_a_2992_);
                v___x_3004_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_a_2992_,
                    v___x_3001_,
                    v___x_3003_,
                );
                if v_hasTrace_2997_ == 0 {
                    v___y_3140_ = v_a_2905_;
                    v___y_3141_ = v_a_2906_;
                    v___y_3142_ = v_a_2907_;
                    v___y_3143_ = v_a_2908_;
                    v___y_3144_ = v_a_2909_;
                    v___y_3145_ = v_a_2910_;
                    v___y_3146_ = v_a_2911_;
                    v___y_3147_ = v_a_2912_;
                    state = 32;
                    continue;
                } else {
                    v___x_3155_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15;
                    v___x_3156_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18,
                    );
                    v___x_3157_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2996_,
                        v_options_2991_,
                        v___x_3156_,
                    );
                    if v___x_3157_ == 0 {
                        v___y_3140_ = v_a_2905_;
                        v___y_3141_ = v_a_2906_;
                        v___y_3142_ = v_a_2907_;
                        v___y_3143_ = v_a_2908_;
                        v___y_3144_ = v_a_2909_;
                        v___y_3145_ = v_a_2910_;
                        v___y_3146_ = v_a_2911_;
                        v___y_3147_ = v_a_2912_;
                        state = 32;
                        continue;
                    } else {
                        v___x_3158_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20,
                        );
                        lean_inc_ref(v___x_2998_);
                        v___x_3159_ = l_Lean_MessageData_ofExpr(v___x_2998_);
                        v___x_3160_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3160_, 0, v___x_3158_);
                        lean_ctor_set(v___x_3160_, 1, v___x_3159_);
                        v___x_3161_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22,
                        );
                        v___x_3162_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3162_, 0, v___x_3160_);
                        lean_ctor_set(v___x_3162_, 1, v___x_3161_);
                        lean_inc_ref(v___x_3004_);
                        v___x_3163_ = lean_array_to_list(v___x_3004_);
                        v___x_3164_ = lean_box(0);
                        v___x_3165_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__2(v___x_3163_, v___x_3164_);
                        v___x_3166_ = l_Lean_MessageData_ofList(v___x_3165_);
                        v___x_3167_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3167_, 0, v___x_3162_);
                        lean_ctor_set(v___x_3167_, 1, v___x_3166_);
                        v___x_3168_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v___x_3155_, v___x_3167_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
                        if lean_obj_tag(v___x_3168_) == 0 {
                            lean_dec_ref_known(v___x_3168_, 1);
                            v___y_3140_ = v_a_2905_;
                            v___y_3141_ = v_a_2906_;
                            v___y_3142_ = v_a_2907_;
                            v___y_3143_ = v_a_2908_;
                            v___y_3144_ = v_a_2909_;
                            v___y_3145_ = v_a_2910_;
                            v___y_3146_ = v_a_2911_;
                            v___y_3147_ = v_a_2912_;
                            state = 32;
                            continue;
                        } else {
                            lean_dec_ref(v___x_3004_);
                            lean_dec_ref(v___x_2998_);
                            lean_del_object(v___x_2994_);
                            lean_dec(v_a_2992_);
                            lean_del_object(v___x_2988_);
                            lean_dec_ref(v_hyps_2985_);
                            lean_dec_ref(v_00_u03c3s_2984_);
                            lean_dec(v_u_2983_);
                            lean_del_object(v___x_2981_);
                            lean_dec(v_head_2979_);
                            lean_dec(v_tail_2976_);
                            lean_del_object(v___x_2973_);
                            lean_dec_ref(v_k_2904_);
                            v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
                            v_isSharedCheck_3176_ = (!lean_is_exclusive(v___x_3168_)) as u8;
                            if v_isSharedCheck_3176_ == 0 {
                                v___x_3171_ = v___x_3168_;
                                v_isShared_3172_ = v_isSharedCheck_3176_;
                                state = 33;
                                continue;
                            } else {
                                lean_inc(v_a_3169_);
                                lean_dec(v___x_3168_);
                                v___x_3171_ = lean_box(0);
                                v_isShared_3172_ = v_isSharedCheck_3176_;
                                state = 33;
                                continue;
                            }
                        }
                    }
                }
            }
            16 => {
                if v___y_3017_ == 0 {
                    lean_dec_ref(v___x_3004_);
                    lean_del_object(v___x_2994_);
                    lean_del_object(v___x_2988_);
                    lean_dec_ref(v_hyps_2985_);
                    lean_dec_ref(v_00_u03c3s_2984_);
                    lean_dec(v_u_2983_);
                    lean_del_object(v___x_2981_);
                    lean_dec(v_head_2979_);
                    lean_dec(v_tail_2976_);
                    lean_del_object(v___x_2973_);
                    lean_dec_ref(v_k_2904_);
                    v___x_3018_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2,
                    );
                    v___x_3019_ = l_Lean_MessageData_ofExpr(v_a_2992_);
                    v___x_3020_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3020_, 0, v___x_3018_);
                    lean_ctor_set(v___x_3020_, 1, v___x_3019_);
                    v___x_3021_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v___x_3020_, v___y_3016_, v___y_3014_, v___y_3008_, v___y_3006_);
                    return v___x_3021_;
                } else {
                    lean_dec(v_a_2992_);
                    v___x_3022_ = l_Lean_instInhabitedExpr;
                    v___x_3023_ = lean_unsigned_to_nat(0);
                    v___x_3024_ = lean_array_get(v___x_3022_, v___x_3004_, v___x_3023_);
                    lean_inc(v___x_3024_);
                    if v_isShared_2995_ == 0 {
                        lean_ctor_set_tag(v___x_2994_, 1);
                        lean_ctor_set(v___x_2994_, 0, v___x_3024_);
                        v___x_3026_ = v___x_2994_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3024_);
                        v___x_3026_ = v_reuseFailAlloc_3084_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                v___x_3027_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(
                    v_head_2979_,
                    v___x_3026_,
                    v___y_3009_,
                    v___y_3010_,
                    v___y_3007_,
                    v___y_3012_,
                    v___y_3016_,
                    v___y_3014_,
                    v___y_3008_,
                    v___y_3006_,
                );
                if lean_obj_tag(v___x_3027_) == 0 {
                    v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
                    lean_inc(v_a_3028_);
                    lean_dec_ref_known(v___x_3027_, 1);
                    if lean_obj_tag(v_a_3028_) == 1 {
                        v_val_3029_ = lean_ctor_get(v_a_3028_, 0);
                        lean_inc_n(v_val_3029_, 2);
                        lean_dec_ref_known(v_a_3028_, 1);
                        v___x_3030_ = lean_unsigned_to_nat(2);
                        v___x_3031_ = lean_array_get(v___x_3022_, v___x_3004_, v___x_3030_);
                        v___x_3032_ = lean_mk_empty_array_with_capacity(v___x_3002_);
                        v___x_3033_ = lean_array_push(v___x_3032_, v_val_3029_);
                        v___x_3034_ = lean_unsigned_to_nat(3);
                        v___x_3035_ = lean_array_get_size(v___x_3004_);
                        v___x_3036_ =
                            l_Array_toSubarray___redArg(v___x_3004_, v___x_3034_, v___x_3035_);
                        v___x_3037_ = l_Subarray_copy___redArg(v___x_3036_);
                        v___x_3038_ = l_Array_append___redArg(v___x_3033_, v___x_3037_);
                        lean_dec_ref(v___x_3037_);
                        lean_inc(v___x_3031_);
                        v___x_3039_ = l_Lean_Expr_beta(v___x_3031_, v___x_3038_);
                        lean_inc_ref(v_hyps_2985_);
                        lean_inc_ref(v_00_u03c3s_2984_);
                        lean_inc(v_u_2983_);
                        if v_isShared_2989_ == 0 {
                            lean_ctor_set(v___x_2988_, 3, v___x_3039_);
                            v___x_3041_ = v___x_2988_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_u_2983_);
                            lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_00_u03c3s_2984_);
                            lean_ctor_set(v_reuseFailAlloc_3073_, 2, v_hyps_2985_);
                            lean_ctor_set(v_reuseFailAlloc_3073_, 3, v___x_3039_);
                            v___x_3041_ = v_reuseFailAlloc_3073_;
                            state = 18;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3028_);
                        lean_dec(v___x_3024_);
                        lean_dec_ref(v___x_3004_);
                        lean_del_object(v___x_2988_);
                        lean_dec_ref(v_hyps_2985_);
                        lean_dec_ref(v_00_u03c3s_2984_);
                        lean_dec(v_u_2983_);
                        lean_del_object(v___x_2981_);
                        lean_dec(v_tail_2976_);
                        lean_del_object(v___x_2973_);
                        lean_dec_ref(v_k_2904_);
                        v___x_3074_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5,
                        );
                        v___x_3075_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v___x_3074_, v___y_3016_, v___y_3014_, v___y_3008_, v___y_3006_);
                        return v___x_3075_;
                    }
                } else {
                    lean_dec(v___x_3024_);
                    lean_dec_ref(v___x_3004_);
                    lean_del_object(v___x_2988_);
                    lean_dec_ref(v_hyps_2985_);
                    lean_dec_ref(v_00_u03c3s_2984_);
                    lean_dec(v_u_2983_);
                    lean_del_object(v___x_2981_);
                    lean_dec(v_tail_2976_);
                    lean_del_object(v___x_2973_);
                    lean_dec_ref(v_k_2904_);
                    v_a_3076_ = lean_ctor_get(v___x_3027_, 0);
                    v_isSharedCheck_3083_ = (!lean_is_exclusive(v___x_3027_)) as u8;
                    if v_isSharedCheck_3083_ == 0 {
                        v___x_3078_ = v___x_3027_;
                        v_isShared_3079_ = v_isSharedCheck_3083_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_3076_);
                        lean_dec(v___x_3027_);
                        v___x_3078_ = lean_box(0);
                        v_isShared_3079_ = v_isSharedCheck_3083_;
                        state = 25;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_2974_ == 0 {
                    lean_ctor_set(v___x_2973_, 0, v_tail_2976_);
                    v___x_3043_ = v___x_2973_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_tail_2976_);
                    v___x_3043_ = v_reuseFailAlloc_3072_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_3044_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
                    v___x_3041_,
                    v___x_3043_,
                    v_k_2904_,
                    v___y_3009_,
                    v___y_3010_,
                    v___y_3007_,
                    v___y_3012_,
                    v___y_3016_,
                    v___y_3014_,
                    v___y_3008_,
                    v___y_3006_,
                );
                if lean_obj_tag(v___x_3044_) == 0 {
                    v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
                    lean_inc(v_a_3045_);
                    lean_dec_ref_known(v___x_3044_, 1);
                    lean_inc(v___x_3024_);
                    v___x_3046_ = l_Lean_Meta_getLevel(
                        v___x_3024_,
                        v___y_3016_,
                        v___y_3014_,
                        v___y_3008_,
                        v___y_3006_,
                    );
                    if lean_obj_tag(v___x_3046_) == 0 {
                        v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
                        v_isSharedCheck_3063_ = (!lean_is_exclusive(v___x_3046_)) as u8;
                        if v_isSharedCheck_3063_ == 0 {
                            v___x_3049_ = v___x_3046_;
                            v_isShared_3050_ = v_isSharedCheck_3063_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_3047_);
                            lean_dec(v___x_3046_);
                            v___x_3049_ = lean_box(0);
                            v_isShared_3050_ = v_isSharedCheck_3063_;
                            state = 20;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3045_);
                        lean_dec(v___x_3031_);
                        lean_dec(v_val_3029_);
                        lean_dec(v___x_3024_);
                        lean_dec_ref(v_hyps_2985_);
                        lean_dec_ref(v_00_u03c3s_2984_);
                        lean_dec(v_u_2983_);
                        lean_del_object(v___x_2981_);
                        v_a_3064_ = lean_ctor_get(v___x_3046_, 0);
                        v_isSharedCheck_3071_ = (!lean_is_exclusive(v___x_3046_)) as u8;
                        if v_isSharedCheck_3071_ == 0 {
                            v___x_3066_ = v___x_3046_;
                            v_isShared_3067_ = v_isSharedCheck_3071_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_3064_);
                            lean_dec(v___x_3046_);
                            v___x_3066_ = lean_box(0);
                            v_isShared_3067_ = v_isSharedCheck_3071_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_3031_);
                    lean_dec(v_val_3029_);
                    lean_dec(v___x_3024_);
                    lean_dec_ref(v_hyps_2985_);
                    lean_dec_ref(v_00_u03c3s_2984_);
                    lean_dec(v_u_2983_);
                    lean_del_object(v___x_2981_);
                    return v___x_3044_;
                }
            }
            20 => {
                v___x_3051_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3;
                lean_inc_ref(v___y_3011_);
                lean_inc_ref(v___y_3013_);
                lean_inc_ref(v___y_3015_);
                v___x_3052_ =
                    l_Lean_Name_mkStr4(v___y_3015_, v___y_3013_, v___y_3011_, v___x_3051_);
                v___x_3053_ = lean_box(0);
                if v_isShared_2982_ == 0 {
                    lean_ctor_set(v___x_2981_, 1, v___x_3053_);
                    lean_ctor_set(v___x_2981_, 0, v_u_2983_);
                    v___x_3055_ = v___x_2981_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_u_2983_);
                    lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3053_);
                    v___x_3055_ = v_reuseFailAlloc_3062_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_3056_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3056_, 0, v_a_3047_);
                lean_ctor_set(v___x_3056_, 1, v___x_3055_);
                v___x_3057_ = l_Lean_mkConst(v___x_3052_, v___x_3056_);
                v___x_3058_ = l_Lean_mkApp6(
                    v___x_3057_,
                    v___x_3024_,
                    v_00_u03c3s_2984_,
                    v_hyps_2985_,
                    v___x_3031_,
                    v_val_3029_,
                    v_a_3045_,
                );
                if v_isShared_3050_ == 0 {
                    lean_ctor_set(v___x_3049_, 0, v___x_3058_);
                    v___x_3060_ = v___x_3049_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
                    v___x_3060_ = v_reuseFailAlloc_3061_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3060_;
            }
            23 => {
                if v_isShared_3067_ == 0 {
                    v___x_3069_ = v___x_3066_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
                    v___x_3069_ = v_reuseFailAlloc_3070_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3069_;
            }
            25 => {
                if v_isShared_3079_ == 0 {
                    v___x_3081_ = v___x_3078_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
                    v___x_3081_ = v_reuseFailAlloc_3082_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3081_;
            }
            27 => {
                if v___y_3097_ == 0 {
                    v___x_3098_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6;
                    lean_inc_ref(v___y_3092_);
                    lean_inc_ref(v___y_3094_);
                    lean_inc_ref(v___y_3096_);
                    v___x_3099_ =
                        l_Lean_Name_mkStr4(v___y_3096_, v___y_3094_, v___y_3092_, v___x_3098_);
                    v___x_3100_ = l_Lean_Expr_isConstOf(v___x_2998_, v___x_3099_);
                    lean_dec(v___x_3099_);
                    lean_dec_ref(v___x_2998_);
                    if v___x_3100_ == 0 {
                        v___y_3006_ = v___y_3086_;
                        v___y_3007_ = v___y_3087_;
                        v___y_3008_ = v___y_3088_;
                        v___y_3009_ = v___y_3089_;
                        v___y_3010_ = v___y_3090_;
                        v___y_3011_ = v___y_3092_;
                        v___y_3012_ = v___y_3091_;
                        v___y_3013_ = v___y_3094_;
                        v___y_3014_ = v___y_3093_;
                        v___y_3015_ = v___y_3096_;
                        v___y_3016_ = v___y_3095_;
                        v___y_3017_ = v___x_3100_;
                        state = 16;
                        continue;
                    } else {
                        v___x_3101_ = lean_box(0);
                        v___x_3102_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(
                            v___x_3004_,
                            v___x_3101_,
                        );
                        v___y_3006_ = v___y_3086_;
                        v___y_3007_ = v___y_3087_;
                        v___y_3008_ = v___y_3088_;
                        v___y_3009_ = v___y_3089_;
                        v___y_3010_ = v___y_3090_;
                        v___y_3011_ = v___y_3092_;
                        v___y_3012_ = v___y_3091_;
                        v___y_3013_ = v___y_3094_;
                        v___y_3014_ = v___y_3093_;
                        v___y_3015_ = v___y_3096_;
                        v___y_3016_ = v___y_3095_;
                        v___y_3017_ = v___x_3102_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2998_);
                    lean_del_object(v___x_2994_);
                    lean_dec(v_a_2992_);
                    lean_del_object(v___x_2988_);
                    lean_del_object(v___x_2981_);
                    lean_del_object(v___x_2973_);
                    v___x_3103_ = l_Lean_instInhabitedExpr;
                    v___x_3104_ = lean_array_get(v___x_3103_, v___x_3004_, v___x_3002_);
                    v___x_3105_ = lean_unsigned_to_nat(3);
                    v___x_3106_ = lean_array_get_size(v___x_3004_);
                    lean_inc_ref(v___x_3004_);
                    v___x_3107_ =
                        l_Array_toSubarray___redArg(v___x_3004_, v___x_3105_, v___x_3106_);
                    v___x_3108_ = l_Subarray_copy___redArg(v___x_3107_);
                    lean_inc_ref(v___x_3108_);
                    v___x_3109_ = l_Lean_Expr_beta(v___x_3104_, v___x_3108_);
                    lean_inc_ref(v___x_3109_);
                    lean_inc_ref(v_hyps_2985_);
                    lean_inc_ref(v_00_u03c3s_2984_);
                    lean_inc(v_u_2983_);
                    v___x_3110_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v___x_3110_, 0, v_u_2983_);
                    lean_ctor_set(v___x_3110_, 1, v_00_u03c3s_2984_);
                    lean_ctor_set(v___x_3110_, 2, v_hyps_2985_);
                    lean_ctor_set(v___x_3110_, 3, v___x_3109_);
                    lean_inc_ref(v_k_2904_);
                    v___x_3111_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
                        v___x_3110_,
                        v_head_2979_,
                        v_k_2904_,
                        v___y_3089_,
                        v___y_3090_,
                        v___y_3087_,
                        v___y_3091_,
                        v___y_3095_,
                        v___y_3093_,
                        v___y_3088_,
                        v___y_3086_,
                    );
                    if lean_obj_tag(v___x_3111_) == 0 {
                        v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
                        v_isSharedCheck_3138_ = (!lean_is_exclusive(v___x_3111_)) as u8;
                        if v_isSharedCheck_3138_ == 0 {
                            v___x_3114_ = v___x_3111_;
                            v_isShared_3115_ = v_isSharedCheck_3138_;
                            state = 28;
                            continue;
                        } else {
                            lean_inc(v_a_3112_);
                            lean_dec(v___x_3111_);
                            v___x_3114_ = lean_box(0);
                            v_isShared_3115_ = v_isSharedCheck_3138_;
                            state = 28;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3109_);
                        lean_dec_ref(v___x_3108_);
                        lean_dec_ref(v___x_3004_);
                        lean_dec_ref(v_hyps_2985_);
                        lean_dec_ref(v_00_u03c3s_2984_);
                        lean_dec(v_u_2983_);
                        lean_dec(v_tail_2976_);
                        lean_dec_ref(v_k_2904_);
                        return v___x_3111_;
                    }
                }
            }
            28 => {
                v___x_3116_ = lean_unsigned_to_nat(2);
                v___x_3117_ = lean_array_get(v___x_3103_, v___x_3004_, v___x_3116_);
                lean_dec_ref(v___x_3004_);
                v___x_3118_ = l_Lean_Expr_beta(v___x_3117_, v___x_3108_);
                lean_inc_ref(v___x_3118_);
                lean_inc_ref(v_hyps_2985_);
                lean_inc_ref(v_00_u03c3s_2984_);
                lean_inc(v_u_2983_);
                v___x_3119_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_3119_, 0, v_u_2983_);
                lean_ctor_set(v___x_3119_, 1, v_00_u03c3s_2984_);
                lean_ctor_set(v___x_3119_, 2, v_hyps_2985_);
                lean_ctor_set(v___x_3119_, 3, v___x_3118_);
                if v_isShared_3115_ == 0 {
                    lean_ctor_set_tag(v___x_3114_, 1);
                    lean_ctor_set(v___x_3114_, 0, v_tail_2976_);
                    v___x_3121_ = v___x_3114_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_tail_2976_);
                    v___x_3121_ = v_reuseFailAlloc_3137_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_3122_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
                    v___x_3119_,
                    v___x_3121_,
                    v_k_2904_,
                    v___y_3089_,
                    v___y_3090_,
                    v___y_3087_,
                    v___y_3091_,
                    v___y_3095_,
                    v___y_3093_,
                    v___y_3088_,
                    v___y_3086_,
                );
                if lean_obj_tag(v___x_3122_) == 0 {
                    v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
                    v_isSharedCheck_3136_ = (!lean_is_exclusive(v___x_3122_)) as u8;
                    if v_isSharedCheck_3136_ == 0 {
                        v___x_3125_ = v___x_3122_;
                        v_isShared_3126_ = v_isSharedCheck_3136_;
                        state = 30;
                        continue;
                    } else {
                        lean_inc(v_a_3123_);
                        lean_dec(v___x_3122_);
                        v___x_3125_ = lean_box(0);
                        v_isShared_3126_ = v_isSharedCheck_3136_;
                        state = 30;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3118_);
                    lean_dec(v_a_3112_);
                    lean_dec_ref(v___x_3109_);
                    lean_dec_ref(v_hyps_2985_);
                    lean_dec_ref(v_00_u03c3s_2984_);
                    lean_dec(v_u_2983_);
                    return v___x_3122_;
                }
            }
            30 => {
                v___x_3127_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7;
                lean_inc_ref(v___y_3092_);
                lean_inc_ref(v___y_3094_);
                lean_inc_ref(v___y_3096_);
                v___x_3128_ =
                    l_Lean_Name_mkStr4(v___y_3096_, v___y_3094_, v___y_3092_, v___x_3127_);
                v___x_3129_ = lean_box(0);
                v___x_3130_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3130_, 0, v_u_2983_);
                lean_ctor_set(v___x_3130_, 1, v___x_3129_);
                v___x_3131_ = l_Lean_mkConst(v___x_3128_, v___x_3130_);
                v___x_3132_ = l_Lean_mkApp6(
                    v___x_3131_,
                    v_00_u03c3s_2984_,
                    v_hyps_2985_,
                    v___x_3109_,
                    v___x_3118_,
                    v_a_3112_,
                    v_a_3123_,
                );
                if v_isShared_3126_ == 0 {
                    lean_ctor_set(v___x_3125_, 0, v___x_3132_);
                    v___x_3134_ = v___x_3125_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
                    v___x_3134_ = v_reuseFailAlloc_3135_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3134_;
            }
            32 => {
                v___x_3148_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8;
                v___x_3149_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9;
                v___x_3150_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10;
                v___x_3151_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12;
                v___x_3152_ = l_Lean_Expr_isConstOf(v___x_2998_, v___x_3151_);
                if v___x_3152_ == 0 {
                    v___y_3086_ = v___y_3147_;
                    v___y_3087_ = v___y_3142_;
                    v___y_3088_ = v___y_3146_;
                    v___y_3089_ = v___y_3140_;
                    v___y_3090_ = v___y_3141_;
                    v___y_3091_ = v___y_3143_;
                    v___y_3092_ = v___x_3150_;
                    v___y_3093_ = v___y_3145_;
                    v___y_3094_ = v___x_3149_;
                    v___y_3095_ = v___y_3144_;
                    v___y_3096_ = v___x_3148_;
                    v___y_3097_ = v___x_3152_;
                    state = 27;
                    continue;
                } else {
                    v___x_3153_ = lean_box(0);
                    v___x_3154_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(
                        v___x_3004_,
                        v___x_3153_,
                    );
                    v___y_3086_ = v___y_3147_;
                    v___y_3087_ = v___y_3142_;
                    v___y_3088_ = v___y_3146_;
                    v___y_3089_ = v___y_3140_;
                    v___y_3090_ = v___y_3141_;
                    v___y_3091_ = v___y_3143_;
                    v___y_3092_ = v___x_3150_;
                    v___y_3093_ = v___y_3145_;
                    v___y_3094_ = v___x_3149_;
                    v___y_3095_ = v___y_3144_;
                    v___y_3096_ = v___x_3148_;
                    v___y_3097_ = v___x_3154_;
                    state = 27;
                    continue;
                }
            }
            33 => {
                if v_isShared_3172_ == 0 {
                    v___x_3174_ = v___x_3171_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
                    v___x_3174_ = v_reuseFailAlloc_3175_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3174_;
            }
            35 => {
                if lean_obj_tag(v_a_3188_) == 1 {
                    lean_dec_ref(v_goal_2902_);
                    v_val_3192_ = lean_ctor_get(v_a_3188_, 0);
                    lean_inc(v_val_3192_);
                    lean_dec_ref_known(v_a_3188_, 1);
                    if v_isShared_3191_ == 0 {
                        lean_ctor_set(v___x_3190_, 0, v_val_3192_);
                        v___x_3194_ = v___x_3190_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_val_3192_);
                        v___x_3194_ = v_reuseFailAlloc_3195_;
                        state = 36;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3190_);
                    lean_dec(v_a_3188_);
                    v_target_3196_ = lean_ctor_get(v_goal_2902_, 3);
                    lean_inc_ref(v_target_3196_);
                    lean_dec_ref(v_goal_2902_);
                    v___x_3197_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24,
                    );
                    v___x_3198_ = l_Lean_MessageData_ofExpr(v_target_3196_);
                    v___x_3199_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3199_, 0, v___x_3197_);
                    lean_ctor_set(v___x_3199_, 1, v___x_3198_);
                    v___x_3200_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26,
                    );
                    v___x_3201_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3201_, 0, v___x_3199_);
                    lean_ctor_set(v___x_3201_, 1, v___x_3200_);
                    v___x_3202_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_3201_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
                    return v___x_3202_;
                }
            }
            36 => {
                return v___x_3194_;
            }
            37 => {
                if v_isShared_3207_ == 0 {
                    v___x_3209_ = v___x_3206_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
                    v___x_3209_ = v_reuseFailAlloc_3210_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3209_;
            }
            39 => {
                if lean_obj_tag(v_a_3217_) == 1 {
                    lean_dec_ref(v_goal_2902_);
                    v_val_3221_ = lean_ctor_get(v_a_3217_, 0);
                    lean_inc(v_val_3221_);
                    lean_dec_ref_known(v_a_3217_, 1);
                    if v_isShared_3220_ == 0 {
                        lean_ctor_set(v___x_3219_, 0, v_val_3221_);
                        v___x_3223_ = v___x_3219_;
                        state = 40;
                        continue;
                    } else {
                        v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_val_3221_);
                        v___x_3223_ = v_reuseFailAlloc_3224_;
                        state = 40;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3219_);
                    lean_dec(v_a_3217_);
                    v_target_3225_ = lean_ctor_get(v_goal_2902_, 3);
                    lean_inc_ref(v_target_3225_);
                    lean_dec_ref(v_goal_2902_);
                    v___x_3226_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24,
                    );
                    v___x_3227_ = l_Lean_MessageData_ofExpr(v_target_3225_);
                    v___x_3228_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3228_, 0, v___x_3226_);
                    lean_ctor_set(v___x_3228_, 1, v___x_3227_);
                    v___x_3229_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26,
                    );
                    v___x_3230_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3230_, 0, v___x_3228_);
                    lean_ctor_set(v___x_3230_, 1, v___x_3229_);
                    v___x_3231_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_3230_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
                    return v___x_3231_;
                }
            }
            40 => {
                return v___x_3223_;
            }
            41 => {
                if v_isShared_3236_ == 0 {
                    v___x_3238_ = v___x_3235_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
                    v___x_3238_ = v_reuseFailAlloc_3239_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3238_;
            }
            43 => {
                if lean_obj_tag(v_a_3242_) == 1 {
                    lean_dec(v_name_3213_);
                    v_val_3246_ = lean_ctor_get(v_a_3242_, 0);
                    lean_inc(v_val_3246_);
                    lean_dec_ref_known(v_a_3242_, 1);
                    if v_isShared_3245_ == 0 {
                        lean_ctor_set(v___x_3244_, 0, v_val_3246_);
                        v___x_3248_ = v___x_3244_;
                        state = 44;
                        continue;
                    } else {
                        v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_val_3246_);
                        v___x_3248_ = v_reuseFailAlloc_3249_;
                        state = 44;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3244_);
                    lean_dec(v_a_3242_);
                    v___x_3250_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28,
                    );
                    v___x_3251_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_3213_);
                    v___x_3252_ = l_Lean_MessageData_ofFormat(v___x_3251_);
                    v___x_3253_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3253_, 0, v___x_3250_);
                    lean_ctor_set(v___x_3253_, 1, v___x_3252_);
                    v___x_3254_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30,
                    );
                    v___x_3255_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3255_, 0, v___x_3253_);
                    lean_ctor_set(v___x_3255_, 1, v___x_3254_);
                    v___x_3256_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_3255_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
                    return v___x_3256_;
                }
            }
            44 => {
                return v___x_3248_;
            }
            45 => {
                if v_isShared_3261_ == 0 {
                    v___x_3263_ = v___x_3260_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
                    v___x_3263_ = v_reuseFailAlloc_3264_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_3263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1(
    mut v_00_u03b1_3268_: *mut LeanObject,
    mut v_msg_3269_: *mut LeanObject,
    mut v___y_3270_: *mut LeanObject,
    mut v___y_3271_: *mut LeanObject,
    mut v___y_3272_: *mut LeanObject,
    mut v___y_3273_: *mut LeanObject,
    mut v___y_3274_: *mut LeanObject,
    mut v___y_3275_: *mut LeanObject,
    mut v___y_3276_: *mut LeanObject,
    mut v___y_3277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    v___x_3279_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(
            v_msg_3269_,
            v___y_3274_,
            v___y_3275_,
            v___y_3276_,
            v___y_3277_,
        );
    return v___x_3279_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___boxed(
    mut v_00_u03b1_3280_: *mut LeanObject,
    mut v_msg_3281_: *mut LeanObject,
    mut v___y_3282_: *mut LeanObject,
    mut v___y_3283_: *mut LeanObject,
    mut v___y_3284_: *mut LeanObject,
    mut v___y_3285_: *mut LeanObject,
    mut v___y_3286_: *mut LeanObject,
    mut v___y_3287_: *mut LeanObject,
    mut v___y_3288_: *mut LeanObject,
    mut v___y_3289_: *mut LeanObject,
    mut v___y_3290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3291_: *mut LeanObject = core::ptr::null_mut();
    v_res_3291_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1(
        v_00_u03b1_3280_,
        v_msg_3281_,
        v___y_3282_,
        v___y_3283_,
        v___y_3284_,
        v___y_3285_,
        v___y_3286_,
        v___y_3287_,
        v___y_3288_,
        v___y_3289_,
    );
    lean_dec(v___y_3289_);
    lean_dec_ref(v___y_3288_);
    lean_dec(v___y_3287_);
    lean_dec_ref(v___y_3286_);
    lean_dec(v___y_3285_);
    lean_dec_ref(v___y_3284_);
    lean_dec(v___y_3283_);
    lean_dec_ref(v___y_3282_);
    return v_res_3291_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3(
    mut v_cls_3292_: *mut LeanObject,
    mut v_msg_3293_: *mut LeanObject,
    mut v___y_3294_: *mut LeanObject,
    mut v___y_3295_: *mut LeanObject,
    mut v___y_3296_: *mut LeanObject,
    mut v___y_3297_: *mut LeanObject,
    mut v___y_3298_: *mut LeanObject,
    mut v___y_3299_: *mut LeanObject,
    mut v___y_3300_: *mut LeanObject,
    mut v___y_3301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    v___x_3303_ =
        l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(
            v_cls_3292_,
            v_msg_3293_,
            v___y_3298_,
            v___y_3299_,
            v___y_3300_,
            v___y_3301_,
        );
    return v___x_3303_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___boxed(
    mut v_cls_3304_: *mut LeanObject,
    mut v_msg_3305_: *mut LeanObject,
    mut v___y_3306_: *mut LeanObject,
    mut v___y_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
    mut v___y_3309_: *mut LeanObject,
    mut v___y_3310_: *mut LeanObject,
    mut v___y_3311_: *mut LeanObject,
    mut v___y_3312_: *mut LeanObject,
    mut v___y_3313_: *mut LeanObject,
    mut v___y_3314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3315_: *mut LeanObject = core::ptr::null_mut();
    v_res_3315_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3(
        v_cls_3304_,
        v_msg_3305_,
        v___y_3306_,
        v___y_3307_,
        v___y_3308_,
        v___y_3309_,
        v___y_3310_,
        v___y_3311_,
        v___y_3312_,
        v___y_3313_,
    );
    lean_dec(v___y_3313_);
    lean_dec_ref(v___y_3312_);
    lean_dec(v___y_3311_);
    lean_dec_ref(v___y_3310_);
    lean_dec(v___y_3309_);
    lean_dec_ref(v___y_3308_);
    lean_dec(v___y_3307_);
    lean_dec_ref(v___y_3306_);
    return v_res_3315_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4(
    mut v_00_u03b1_3316_: *mut LeanObject,
    mut v_msg_3317_: *mut LeanObject,
    mut v___y_3318_: *mut LeanObject,
    mut v___y_3319_: *mut LeanObject,
    mut v___y_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    v___x_3323_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(
            v_msg_3317_,
            v___y_3318_,
            v___y_3319_,
            v___y_3320_,
            v___y_3321_,
        );
    return v___x_3323_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___boxed(
    mut v_00_u03b1_3324_: *mut LeanObject,
    mut v_msg_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
    mut v___y_3327_: *mut LeanObject,
    mut v___y_3328_: *mut LeanObject,
    mut v___y_3329_: *mut LeanObject,
    mut v___y_3330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3331_: *mut LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4(
        v_00_u03b1_3324_,
        v_msg_3325_,
        v___y_3326_,
        v___y_3327_,
        v___y_3328_,
        v___y_3329_,
    );
    lean_dec(v___y_3329_);
    lean_dec_ref(v___y_3328_);
    lean_dec(v___y_3327_);
    lean_dec_ref(v___y_3326_);
    return v_res_3331_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0(
    mut v_x_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
    mut v___y_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3336_);
    lean_inc_ref(v___y_3335_);
    lean_inc(v___y_3334_);
    lean_inc_ref(v___y_3333_);
    v___x_3342_ = lean_apply_9(
        v_x_3332_,
        v___y_3333_,
        v___y_3334_,
        v___y_3335_,
        v___y_3336_,
        v___y_3337_,
        v___y_3338_,
        v___y_3339_,
        v___y_3340_,
        lean_box(0),
    );
    return v___x_3342_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0___boxed(
    mut v_x_3343_: *mut LeanObject,
    mut v___y_3344_: *mut LeanObject,
    mut v___y_3345_: *mut LeanObject,
    mut v___y_3346_: *mut LeanObject,
    mut v___y_3347_: *mut LeanObject,
    mut v___y_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
    mut v___y_3352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3353_: *mut LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0(v_x_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
    lean_dec(v___y_3347_);
    lean_dec_ref(v___y_3346_);
    lean_dec(v___y_3345_);
    lean_dec_ref(v___y_3344_);
    return v_res_3353_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(
    mut v_mvarId_3354_: *mut LeanObject,
    mut v_x_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
    mut v___y_3359_: *mut LeanObject,
    mut v___y_3360_: *mut LeanObject,
    mut v___y_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3370_: u8 = 0;
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3359_);
                lean_inc_ref(v___y_3358_);
                lean_inc(v___y_3357_);
                lean_inc_ref(v___y_3356_);
                v___f_3365_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_3365_, 0, v_x_3355_);
                lean_closure_set(v___f_3365_, 1, v___y_3356_);
                lean_closure_set(v___f_3365_, 2, v___y_3357_);
                lean_closure_set(v___f_3365_, 3, v___y_3358_);
                lean_closure_set(v___f_3365_, 4, v___y_3359_);
                v___x_3366_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_3354_,
                    v___f_3365_,
                    v___y_3360_,
                    v___y_3361_,
                    v___y_3362_,
                    v___y_3363_,
                );
                if lean_obj_tag(v___x_3366_) == 0 {
                    return v___x_3366_;
                } else {
                    v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
                    v_isSharedCheck_3374_ = (!lean_is_exclusive(v___x_3366_)) as u8;
                    if v_isSharedCheck_3374_ == 0 {
                        v___x_3369_ = v___x_3366_;
                        v_isShared_3370_ = v_isSharedCheck_3374_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3367_);
                        lean_dec(v___x_3366_);
                        v___x_3369_ = lean_box(0);
                        v_isShared_3370_ = v_isSharedCheck_3374_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3370_ == 0 {
                    v___x_3372_ = v___x_3369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
                    v___x_3372_ = v_reuseFailAlloc_3373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___boxed(
    mut v_mvarId_3375_: *mut LeanObject,
    mut v_x_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
    mut v___y_3379_: *mut LeanObject,
    mut v___y_3380_: *mut LeanObject,
    mut v___y_3381_: *mut LeanObject,
    mut v___y_3382_: *mut LeanObject,
    mut v___y_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3386_: *mut LeanObject = core::ptr::null_mut();
    v_res_3386_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_mvarId_3375_, v_x_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
    lean_dec(v___y_3384_);
    lean_dec_ref(v___y_3383_);
    lean_dec(v___y_3382_);
    lean_dec_ref(v___y_3381_);
    lean_dec(v___y_3380_);
    lean_dec_ref(v___y_3379_);
    lean_dec(v___y_3378_);
    lean_dec_ref(v___y_3377_);
    return v_res_3386_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2(
    mut v_00_u03b1_3387_: *mut LeanObject,
    mut v_mvarId_3388_: *mut LeanObject,
    mut v_x_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
    mut v___y_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    v___x_3399_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_mvarId_3388_, v_x_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
    return v___x_3399_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___boxed(
    mut v_00_u03b1_3400_: *mut LeanObject,
    mut v_mvarId_3401_: *mut LeanObject,
    mut v_x_3402_: *mut LeanObject,
    mut v___y_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
    mut v___y_3406_: *mut LeanObject,
    mut v___y_3407_: *mut LeanObject,
    mut v___y_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
    mut v___y_3411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3412_: *mut LeanObject = core::ptr::null_mut();
    v_res_3412_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2(
            v_00_u03b1_3400_,
            v_mvarId_3401_,
            v_x_3402_,
            v___y_3403_,
            v___y_3404_,
            v___y_3405_,
            v___y_3406_,
            v___y_3407_,
            v___y_3408_,
            v___y_3409_,
            v___y_3410_,
        );
    lean_dec(v___y_3410_);
    lean_dec_ref(v___y_3409_);
    lean_dec(v___y_3408_);
    lean_dec_ref(v___y_3407_);
    lean_dec(v___y_3406_);
    lean_dec_ref(v___y_3405_);
    lean_dec(v___y_3404_);
    lean_dec_ref(v___y_3403_);
    return v_res_3412_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(
    mut v_val_3413_: *mut LeanObject,
    mut v_goal_3414_: *mut LeanObject,
    mut v_name_3415_: *mut LeanObject,
    mut v___y_3416_: *mut LeanObject,
    mut v___y_3417_: *mut LeanObject,
    mut v___y_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
    mut v___y_3421_: *mut LeanObject,
    mut v___y_3422_: *mut LeanObject,
    mut v___y_3423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3431_: u8 = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3425_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_3414_);
                v___x_3426_ = l_Lean_Syntax_getId(v_name_3415_);
                v___x_3427_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_3425_,
                    v___x_3426_,
                    v___y_3420_,
                    v___y_3421_,
                    v___y_3422_,
                    v___y_3423_,
                );
                if lean_obj_tag(v___x_3427_) == 0 {
                    v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
                    v_isSharedCheck_3439_ = (!lean_is_exclusive(v___x_3427_)) as u8;
                    if v_isSharedCheck_3439_ == 0 {
                        v___x_3430_ = v___x_3427_;
                        v_isShared_3431_ = v_isSharedCheck_3439_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3428_);
                        lean_dec(v___x_3427_);
                        v___x_3430_ = lean_box(0);
                        v_isShared_3431_ = v_isSharedCheck_3439_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3427_;
                }
            }
            1 => {
                v___x_3432_ = lean_st_ref_take(v_val_3413_);
                v___x_3433_ = l_Lean_Expr_mvarId_x21(v_a_3428_);
                v___x_3434_ = lean_array_push(v___x_3432_, v___x_3433_);
                v___x_3435_ = lean_st_ref_set(v_val_3413_, v___x_3434_);
                if v_isShared_3431_ == 0 {
                    v___x_3437_ = v___x_3430_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3428_);
                    v___x_3437_ = v_reuseFailAlloc_3438_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed(
    mut v_val_3440_: *mut LeanObject,
    mut v_goal_3441_: *mut LeanObject,
    mut v_name_3442_: *mut LeanObject,
    mut v___y_3443_: *mut LeanObject,
    mut v___y_3444_: *mut LeanObject,
    mut v___y_3445_: *mut LeanObject,
    mut v___y_3446_: *mut LeanObject,
    mut v___y_3447_: *mut LeanObject,
    mut v___y_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
    mut v___y_3450_: *mut LeanObject,
    mut v___y_3451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3452_: *mut LeanObject = core::ptr::null_mut();
    v_res_3452_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(
        v_val_3440_,
        v_goal_3441_,
        v_name_3442_,
        v___y_3443_,
        v___y_3444_,
        v___y_3445_,
        v___y_3446_,
        v___y_3447_,
        v___y_3448_,
        v___y_3449_,
        v___y_3450_,
    );
    lean_dec(v___y_3450_);
    lean_dec_ref(v___y_3449_);
    lean_dec(v___y_3448_);
    lean_dec_ref(v___y_3447_);
    lean_dec(v___y_3446_);
    lean_dec_ref(v___y_3445_);
    lean_dec(v___y_3444_);
    lean_dec_ref(v___y_3443_);
    lean_dec(v_name_3442_);
    lean_dec(v_val_3440_);
    return v_res_3452_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(
    mut v_x_3453_: *mut LeanObject,
    mut v_x_3454_: *mut LeanObject,
    mut v_x_3455_: *mut LeanObject,
    mut v_x_3456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3461_: u8 = 0;
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: u8 = 0;
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3457_ = lean_ctor_get(v_x_3453_, 0);
                v_vs_3458_ = lean_ctor_get(v_x_3453_, 1);
                v_isSharedCheck_3482_ = (!lean_is_exclusive(v_x_3453_)) as u8;
                if v_isSharedCheck_3482_ == 0 {
                    v___x_3460_ = v_x_3453_;
                    v_isShared_3461_ = v_isSharedCheck_3482_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3458_);
                    lean_inc(v_ks_3457_);
                    lean_dec(v_x_3453_);
                    v___x_3460_ = lean_box(0);
                    v_isShared_3461_ = v_isSharedCheck_3482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3462_ = lean_array_get_size(v_ks_3457_);
                v___x_3463_ = lean_nat_dec_lt(v_x_3454_, v___x_3462_);
                if v___x_3463_ == 0 {
                    lean_dec(v_x_3454_);
                    v___x_3464_ = lean_array_push(v_ks_3457_, v_x_3455_);
                    v___x_3465_ = lean_array_push(v_vs_3458_, v_x_3456_);
                    if v_isShared_3461_ == 0 {
                        lean_ctor_set(v___x_3460_, 1, v___x_3465_);
                        lean_ctor_set(v___x_3460_, 0, v___x_3464_);
                        v___x_3467_ = v___x_3460_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3464_);
                        lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3465_);
                        v___x_3467_ = v_reuseFailAlloc_3468_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3469_ = lean_array_fget_borrowed(v_ks_3457_, v_x_3454_);
                    v___x_3470_ = l_Lean_instBEqMVarId_beq(v_x_3455_, v_k_x27_3469_);
                    if v___x_3470_ == 0 {
                        if v_isShared_3461_ == 0 {
                            v___x_3472_ = v___x_3460_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_ks_3457_);
                            lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_vs_3458_);
                            v___x_3472_ = v_reuseFailAlloc_3476_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3477_ = lean_array_fset(v_ks_3457_, v_x_3454_, v_x_3455_);
                        v___x_3478_ = lean_array_fset(v_vs_3458_, v_x_3454_, v_x_3456_);
                        lean_dec(v_x_3454_);
                        if v_isShared_3461_ == 0 {
                            lean_ctor_set(v___x_3460_, 1, v___x_3478_);
                            lean_ctor_set(v___x_3460_, 0, v___x_3477_);
                            v___x_3480_ = v___x_3460_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3477_);
                            lean_ctor_set(v_reuseFailAlloc_3481_, 1, v___x_3478_);
                            v___x_3480_ = v_reuseFailAlloc_3481_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3467_;
            }
            3 => {
                v___x_3473_ = lean_unsigned_to_nat(1);
                v___x_3474_ = lean_nat_add(v_x_3454_, v___x_3473_);
                lean_dec(v_x_3454_);
                v_x_3453_ = v___x_3472_;
                v_x_3454_ = v___x_3474_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(
    mut v_n_3483_: *mut LeanObject,
    mut v_k_3484_: *mut LeanObject,
    mut v_v_3485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    v___x_3486_ = lean_unsigned_to_nat(0);
    v___x_3487_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(v_n_3483_, v___x_3486_, v_k_3484_, v_v_3485_);
    return v___x_3487_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0()
-> usize {
    let mut v___x_3488_: usize = 0;
    let mut v___x_3489_: usize = 0;
    let mut v___x_3490_: usize = 0;
    v___x_3488_ = 5usize;
    v___x_3489_ = 1usize;
    v___x_3490_ = lean_usize_shift_left(v___x_3489_, v___x_3488_);
    return v___x_3490_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1()
-> usize {
    let mut v___x_3491_: usize = 0;
    let mut v___x_3492_: usize = 0;
    let mut v___x_3493_: usize = 0;
    v___x_3491_ = 1usize;
    v___x_3492_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0);
    v___x_3493_ = lean_usize_sub(v___x_3492_, v___x_3491_);
    return v___x_3493_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    v___x_3494_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3494_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(
    mut v_x_3495_: *mut LeanObject,
    mut v_x_3496_: usize,
    mut v_x_3497_: usize,
    mut v_x_3498_: *mut LeanObject,
    mut v_x_3499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: usize = 0;
    let mut v___x_3502_: usize = 0;
    let mut v___x_3503_: usize = 0;
    let mut v___x_3504_: usize = 0;
    let mut v_j_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v_v_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3524_: u8 = 0;
    let mut v___x_3525_: u8 = 0;
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3531_: u8 = 0;
    let mut v_node_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v___x_3536_: usize = 0;
    let mut v___x_3537_: usize = 0;
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3544_: u8 = 0;
    let mut v_unused_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3550_: u8 = 0;
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3555_: u8 = 0;
    let mut v_ks_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: usize = 0;
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: u8 = 0;
    let mut v_reuseFailAlloc_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3495_) == 0 {
                    v_es_3500_ = lean_ctor_get(v_x_3495_, 0);
                    v___x_3501_ = 5usize;
                    v___x_3502_ = 1usize;
                    v___x_3503_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1);
                    v___x_3504_ = lean_usize_land(v_x_3496_, v___x_3503_);
                    v_j_3505_ = lean_usize_to_nat(v___x_3504_);
                    v___x_3506_ = lean_array_get_size(v_es_3500_);
                    v___x_3507_ = lean_nat_dec_lt(v_j_3505_, v___x_3506_);
                    if v___x_3507_ == 0 {
                        lean_dec(v_j_3505_);
                        lean_dec(v_x_3499_);
                        lean_dec(v_x_3498_);
                        return v_x_3495_;
                    } else {
                        lean_inc_ref(v_es_3500_);
                        v_isSharedCheck_3544_ = (!lean_is_exclusive(v_x_3495_)) as u8;
                        if v_isSharedCheck_3544_ == 0 {
                            v_unused_3545_ = lean_ctor_get(v_x_3495_, 0);
                            lean_dec(v_unused_3545_);
                            v___x_3509_ = v_x_3495_;
                            v_isShared_3510_ = v_isSharedCheck_3544_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3495_);
                            v___x_3509_ = lean_box(0);
                            v_isShared_3510_ = v_isSharedCheck_3544_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3546_ = lean_ctor_get(v_x_3495_, 0);
                    v_vs_3547_ = lean_ctor_get(v_x_3495_, 1);
                    v_isSharedCheck_3567_ = (!lean_is_exclusive(v_x_3495_)) as u8;
                    if v_isSharedCheck_3567_ == 0 {
                        v___x_3549_ = v_x_3495_;
                        v_isShared_3550_ = v_isSharedCheck_3567_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3547_);
                        lean_inc(v_ks_3546_);
                        lean_dec(v_x_3495_);
                        v___x_3549_ = lean_box(0);
                        v_isShared_3550_ = v_isSharedCheck_3567_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3511_ = lean_array_fget(v_es_3500_, v_j_3505_);
                v___x_3512_ = lean_box(0);
                v_xs_x27_3513_ = lean_array_fset(v_es_3500_, v_j_3505_, v___x_3512_);
                match lean_obj_tag(v_v_3511_) {
                    0 => {
                        v_key_3520_ = lean_ctor_get(v_v_3511_, 0);
                        v_val_3521_ = lean_ctor_get(v_v_3511_, 1);
                        v_isSharedCheck_3531_ = (!lean_is_exclusive(v_v_3511_)) as u8;
                        if v_isSharedCheck_3531_ == 0 {
                            v___x_3523_ = v_v_3511_;
                            v_isShared_3524_ = v_isSharedCheck_3531_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3521_);
                            lean_inc(v_key_3520_);
                            lean_dec(v_v_3511_);
                            v___x_3523_ = lean_box(0);
                            v_isShared_3524_ = v_isSharedCheck_3531_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3532_ = lean_ctor_get(v_v_3511_, 0);
                        v_isSharedCheck_3542_ = (!lean_is_exclusive(v_v_3511_)) as u8;
                        if v_isSharedCheck_3542_ == 0 {
                            v___x_3534_ = v_v_3511_;
                            v_isShared_3535_ = v_isSharedCheck_3542_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3532_);
                            lean_dec(v_v_3511_);
                            v___x_3534_ = lean_box(0);
                            v_isShared_3535_ = v_isSharedCheck_3542_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3543_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3543_, 0, v_x_3498_);
                        lean_ctor_set(v___x_3543_, 1, v_x_3499_);
                        v___y_3515_ = v___x_3543_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3516_ = lean_array_fset(v_xs_x27_3513_, v_j_3505_, v___y_3515_);
                lean_dec(v_j_3505_);
                if v_isShared_3510_ == 0 {
                    lean_ctor_set(v___x_3509_, 0, v___x_3516_);
                    v___x_3518_ = v___x_3509_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
                    v___x_3518_ = v_reuseFailAlloc_3519_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3518_;
            }
            4 => {
                v___x_3525_ = l_Lean_instBEqMVarId_beq(v_x_3498_, v_key_3520_);
                if v___x_3525_ == 0 {
                    lean_del_object(v___x_3523_);
                    v___x_3526_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3520_,
                        v_val_3521_,
                        v_x_3498_,
                        v_x_3499_,
                    );
                    v___x_3527_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3527_, 0, v___x_3526_);
                    v___y_3515_ = v___x_3527_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3521_);
                    lean_dec(v_key_3520_);
                    if v_isShared_3524_ == 0 {
                        lean_ctor_set(v___x_3523_, 1, v_x_3499_);
                        lean_ctor_set(v___x_3523_, 0, v_x_3498_);
                        v___x_3529_ = v___x_3523_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_x_3498_);
                        lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_x_3499_);
                        v___x_3529_ = v_reuseFailAlloc_3530_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3515_ = v___x_3529_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3536_ = lean_usize_shift_right(v_x_3496_, v___x_3501_);
                v___x_3537_ = lean_usize_add(v_x_3497_, v___x_3502_);
                v___x_3538_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_node_3532_, v___x_3536_, v___x_3537_, v_x_3498_, v_x_3499_);
                if v_isShared_3535_ == 0 {
                    lean_ctor_set(v___x_3534_, 0, v___x_3538_);
                    v___x_3540_ = v___x_3534_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
                    v___x_3540_ = v_reuseFailAlloc_3541_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3515_ = v___x_3540_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3550_ == 0 {
                    v___x_3552_ = v___x_3549_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_ks_3546_);
                    lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_vs_3547_);
                    v___x_3552_ = v_reuseFailAlloc_3566_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3553_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(v___x_3552_, v_x_3498_, v_x_3499_);
                v___x_3561_ = 7usize;
                v___x_3562_ = lean_usize_dec_le(v___x_3561_, v_x_3497_);
                if v___x_3562_ == 0 {
                    v___x_3563_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3553_);
                    v___x_3564_ = lean_unsigned_to_nat(4);
                    v___x_3565_ = lean_nat_dec_lt(v___x_3563_, v___x_3564_);
                    lean_dec(v___x_3563_);
                    v___y_3555_ = v___x_3565_;
                    state = 10;
                    continue;
                } else {
                    v___y_3555_ = v___x_3562_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3555_ == 0 {
                    v_ks_3556_ = lean_ctor_get(v_newNode_3553_, 0);
                    lean_inc_ref(v_ks_3556_);
                    v_vs_3557_ = lean_ctor_get(v_newNode_3553_, 1);
                    lean_inc_ref(v_vs_3557_);
                    lean_dec_ref(v_newNode_3553_);
                    v___x_3558_ = lean_unsigned_to_nat(0);
                    v___x_3559_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2);
                    v___x_3560_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_x_3497_, v_ks_3556_, v_vs_3557_, v___x_3558_, v___x_3559_);
                    lean_dec_ref(v_vs_3557_);
                    lean_dec_ref(v_ks_3556_);
                    return v___x_3560_;
                } else {
                    return v_newNode_3553_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(
    mut v_depth_3568_: usize,
    mut v_keys_3569_: *mut LeanObject,
    mut v_vals_3570_: *mut LeanObject,
    mut v_i_3571_: *mut LeanObject,
    mut v_entries_3572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v_k_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: u64 = 0;
    let mut v_h_3578_: usize = 0;
    let mut v___x_3579_: usize = 0;
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: usize = 0;
    let mut v___x_3582_: usize = 0;
    let mut v___x_3583_: usize = 0;
    let mut v_h_3584_: usize = 0;
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3573_ = lean_array_get_size(v_keys_3569_);
                v___x_3574_ = lean_nat_dec_lt(v_i_3571_, v___x_3573_);
                if v___x_3574_ == 0 {
                    lean_dec(v_i_3571_);
                    return v_entries_3572_;
                } else {
                    v_k_3575_ = lean_array_fget_borrowed(v_keys_3569_, v_i_3571_);
                    v_v_3576_ = lean_array_fget_borrowed(v_vals_3570_, v_i_3571_);
                    v___x_3577_ = l_Lean_instHashableMVarId_hash(v_k_3575_);
                    v_h_3578_ = lean_uint64_to_usize(v___x_3577_);
                    v___x_3579_ = 5usize;
                    v___x_3580_ = lean_unsigned_to_nat(1);
                    v___x_3581_ = 1usize;
                    v___x_3582_ = lean_usize_sub(v_depth_3568_, v___x_3581_);
                    v___x_3583_ = lean_usize_mul(v___x_3579_, v___x_3582_);
                    v_h_3584_ = lean_usize_shift_right(v_h_3578_, v___x_3583_);
                    v___x_3585_ = lean_nat_add(v_i_3571_, v___x_3580_);
                    lean_dec(v_i_3571_);
                    lean_inc(v_v_3576_);
                    lean_inc(v_k_3575_);
                    v___x_3586_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_entries_3572_, v_h_3584_, v_depth_3568_, v_k_3575_, v_v_3576_);
                    v_i_3571_ = v___x_3585_;
                    v_entries_3572_ = v___x_3586_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg___boxed(
    mut v_depth_3588_: *mut LeanObject,
    mut v_keys_3589_: *mut LeanObject,
    mut v_vals_3590_: *mut LeanObject,
    mut v_i_3591_: *mut LeanObject,
    mut v_entries_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3593_: usize = 0;
    let mut v_res_3594_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3593_ = lean_unbox_usize(v_depth_3588_);
    lean_dec(v_depth_3588_);
    v_res_3594_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_depth_boxed_3593_, v_keys_3589_, v_vals_3590_, v_i_3591_, v_entries_3592_);
    lean_dec_ref(v_vals_3590_);
    lean_dec_ref(v_keys_3589_);
    return v_res_3594_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___boxed(
    mut v_x_3595_: *mut LeanObject,
    mut v_x_3596_: *mut LeanObject,
    mut v_x_3597_: *mut LeanObject,
    mut v_x_3598_: *mut LeanObject,
    mut v_x_3599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_18004__boxed_3600_: usize = 0;
    let mut v_x_18005__boxed_3601_: usize = 0;
    let mut v_res_3602_: *mut LeanObject = core::ptr::null_mut();
    v_x_18004__boxed_3600_ = lean_unbox_usize(v_x_3596_);
    lean_dec(v_x_3596_);
    v_x_18005__boxed_3601_ = lean_unbox_usize(v_x_3597_);
    lean_dec(v_x_3597_);
    v_res_3602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_3595_, v_x_18004__boxed_3600_, v_x_18005__boxed_3601_, v_x_3598_, v_x_3599_);
    return v_res_3602_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(
    mut v_x_3603_: *mut LeanObject,
    mut v_x_3604_: *mut LeanObject,
    mut v_x_3605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3606_: u64 = 0;
    let mut v___x_3607_: usize = 0;
    let mut v___x_3608_: usize = 0;
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    v___x_3606_ = l_Lean_instHashableMVarId_hash(v_x_3604_);
    v___x_3607_ = lean_uint64_to_usize(v___x_3606_);
    v___x_3608_ = 1usize;
    v___x_3609_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_3603_, v___x_3607_, v___x_3608_, v_x_3604_, v_x_3605_);
    return v___x_3609_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(
    mut v_mvarId_3610_: *mut LeanObject,
    mut v_val_3611_: *mut LeanObject,
    mut v___y_3612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v_depth_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3635_: u8 = 0;
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3614_ = lean_st_ref_take(v___y_3612_);
                v_mctx_3615_ = lean_ctor_get(v___x_3614_, 0);
                v_cache_3616_ = lean_ctor_get(v___x_3614_, 1);
                v_zetaDeltaFVarIds_3617_ = lean_ctor_get(v___x_3614_, 2);
                v_postponed_3618_ = lean_ctor_get(v___x_3614_, 3);
                v_diag_3619_ = lean_ctor_get(v___x_3614_, 4);
                v_isSharedCheck_3647_ = (!lean_is_exclusive(v___x_3614_)) as u8;
                if v_isSharedCheck_3647_ == 0 {
                    v___x_3621_ = v___x_3614_;
                    v_isShared_3622_ = v_isSharedCheck_3647_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_3619_);
                    lean_inc(v_postponed_3618_);
                    lean_inc(v_zetaDeltaFVarIds_3617_);
                    lean_inc(v_cache_3616_);
                    lean_inc(v_mctx_3615_);
                    lean_dec(v___x_3614_);
                    v___x_3621_ = lean_box(0);
                    v_isShared_3622_ = v_isSharedCheck_3647_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3623_ = lean_ctor_get(v_mctx_3615_, 0);
                v_levelAssignDepth_3624_ = lean_ctor_get(v_mctx_3615_, 1);
                v_lmvarCounter_3625_ = lean_ctor_get(v_mctx_3615_, 2);
                v_mvarCounter_3626_ = lean_ctor_get(v_mctx_3615_, 3);
                v_lDecls_3627_ = lean_ctor_get(v_mctx_3615_, 4);
                v_decls_3628_ = lean_ctor_get(v_mctx_3615_, 5);
                v_userNames_3629_ = lean_ctor_get(v_mctx_3615_, 6);
                v_lAssignment_3630_ = lean_ctor_get(v_mctx_3615_, 7);
                v_eAssignment_3631_ = lean_ctor_get(v_mctx_3615_, 8);
                v_dAssignment_3632_ = lean_ctor_get(v_mctx_3615_, 9);
                v_isSharedCheck_3646_ = (!lean_is_exclusive(v_mctx_3615_)) as u8;
                if v_isSharedCheck_3646_ == 0 {
                    v___x_3634_ = v_mctx_3615_;
                    v_isShared_3635_ = v_isSharedCheck_3646_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_3632_);
                    lean_inc(v_eAssignment_3631_);
                    lean_inc(v_lAssignment_3630_);
                    lean_inc(v_userNames_3629_);
                    lean_inc(v_decls_3628_);
                    lean_inc(v_lDecls_3627_);
                    lean_inc(v_mvarCounter_3626_);
                    lean_inc(v_lmvarCounter_3625_);
                    lean_inc(v_levelAssignDepth_3624_);
                    lean_inc(v_depth_3623_);
                    lean_dec(v_mctx_3615_);
                    v___x_3634_ = lean_box(0);
                    v_isShared_3635_ = v_isSharedCheck_3646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3636_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(v_eAssignment_3631_, v_mvarId_3610_, v_val_3611_);
                if v_isShared_3635_ == 0 {
                    lean_ctor_set(v___x_3634_, 8, v___x_3636_);
                    v___x_3638_ = v___x_3634_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_depth_3623_);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_levelAssignDepth_3624_);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 2, v_lmvarCounter_3625_);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 3, v_mvarCounter_3626_);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 4, v_lDecls_3627_);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 5, v_decls_3628_);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 6, v_userNames_3629_);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 7, v_lAssignment_3630_);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 8, v___x_3636_);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 9, v_dAssignment_3632_);
                    v___x_3638_ = v_reuseFailAlloc_3645_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3622_ == 0 {
                    lean_ctor_set(v___x_3621_, 0, v___x_3638_);
                    v___x_3640_ = v___x_3621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3638_);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_cache_3616_);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_zetaDeltaFVarIds_3617_);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_postponed_3618_);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 4, v_diag_3619_);
                    v___x_3640_ = v_reuseFailAlloc_3644_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3641_ = lean_st_ref_set(v___y_3612_, v___x_3640_);
                v___x_3642_ = lean_box(0);
                v___x_3643_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3643_, 0, v___x_3642_);
                return v___x_3643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg___boxed(
    mut v_mvarId_3648_: *mut LeanObject,
    mut v_val_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
    mut v___y_3651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3652_: *mut LeanObject = core::ptr::null_mut();
    v_res_3652_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(
            v_mvarId_3648_,
            v_val_3649_,
            v___y_3650_,
        );
    lean_dec(v___y_3650_);
    return v_res_3652_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(
    mut v___x_3653_: *mut LeanObject,
    mut v_snd_3654_: *mut LeanObject,
    mut v_a_3655_: *mut LeanObject,
    mut v_fst_3656_: *mut LeanObject,
    mut v___y_3657_: *mut LeanObject,
    mut v___y_3658_: *mut LeanObject,
    mut v___y_3659_: *mut LeanObject,
    mut v___y_3660_: *mut LeanObject,
    mut v___y_3661_: *mut LeanObject,
    mut v___y_3662_: *mut LeanObject,
    mut v___y_3663_: *mut LeanObject,
    mut v___y_3664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3677_: u8 = 0;
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3666_ = lean_st_mk_ref(v___x_3653_);
                lean_inc(v___x_3666_);
                v___f_3667_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    1,
                );
                lean_closure_set(v___f_3667_, 0, v___x_3666_);
                v___x_3668_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
                    v_snd_3654_,
                    v_a_3655_,
                    v___f_3667_,
                    v___y_3657_,
                    v___y_3658_,
                    v___y_3659_,
                    v___y_3660_,
                    v___y_3661_,
                    v___y_3662_,
                    v___y_3663_,
                    v___y_3664_,
                );
                if lean_obj_tag(v___x_3668_) == 0 {
                    v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
                    lean_inc(v_a_3669_);
                    lean_dec_ref_known(v___x_3668_, 1);
                    v___x_3670_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(v_fst_3656_, v_a_3669_, v___y_3662_);
                    lean_dec_ref(v___x_3670_);
                    v___x_3671_ = lean_st_ref_get(v___x_3666_);
                    lean_dec(v___x_3666_);
                    v___x_3672_ = lean_array_to_list(v___x_3671_);
                    v___x_3673_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_3672_,
                        v___y_3658_,
                        v___y_3661_,
                        v___y_3662_,
                        v___y_3663_,
                        v___y_3664_,
                    );
                    return v___x_3673_;
                } else {
                    lean_dec(v___x_3666_);
                    lean_dec(v_fst_3656_);
                    v_a_3674_ = lean_ctor_get(v___x_3668_, 0);
                    v_isSharedCheck_3681_ = (!lean_is_exclusive(v___x_3668_)) as u8;
                    if v_isSharedCheck_3681_ == 0 {
                        v___x_3676_ = v___x_3668_;
                        v_isShared_3677_ = v_isSharedCheck_3681_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3674_);
                        lean_dec(v___x_3668_);
                        v___x_3676_ = lean_box(0);
                        v_isShared_3677_ = v_isSharedCheck_3681_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3677_ == 0 {
                    v___x_3679_ = v___x_3676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
                    v___x_3679_ = v_reuseFailAlloc_3680_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1___boxed(
    mut v___x_3682_: *mut LeanObject,
    mut v_snd_3683_: *mut LeanObject,
    mut v_a_3684_: *mut LeanObject,
    mut v_fst_3685_: *mut LeanObject,
    mut v___y_3686_: *mut LeanObject,
    mut v___y_3687_: *mut LeanObject,
    mut v___y_3688_: *mut LeanObject,
    mut v___y_3689_: *mut LeanObject,
    mut v___y_3690_: *mut LeanObject,
    mut v___y_3691_: *mut LeanObject,
    mut v___y_3692_: *mut LeanObject,
    mut v___y_3693_: *mut LeanObject,
    mut v___y_3694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3695_: *mut LeanObject = core::ptr::null_mut();
    v_res_3695_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(
        v___x_3682_,
        v_snd_3683_,
        v_a_3684_,
        v_fst_3685_,
        v___y_3686_,
        v___y_3687_,
        v___y_3688_,
        v___y_3689_,
        v___y_3690_,
        v___y_3691_,
        v___y_3692_,
        v___y_3693_,
    );
    lean_dec(v___y_3693_);
    lean_dec_ref(v___y_3692_);
    lean_dec(v___y_3691_);
    lean_dec_ref(v___y_3690_);
    lean_dec(v___y_3689_);
    lean_dec_ref(v___y_3688_);
    lean_dec(v___y_3687_);
    lean_dec_ref(v___y_3686_);
    return v_res_3695_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(
    mut v_ref_3696_: *mut LeanObject,
    mut v_msg_3697_: *mut LeanObject,
    mut v___y_3698_: *mut LeanObject,
    mut v___y_3699_: *mut LeanObject,
    mut v___y_3700_: *mut LeanObject,
    mut v___y_3701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3715_: u8 = 0;
    let mut v_cancelTk_x3f_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3717_: u8 = 0;
    let mut v_inheritedTraceOptions_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3703_ = lean_ctor_get(v___y_3700_, 0);
    v_fileMap_3704_ = lean_ctor_get(v___y_3700_, 1);
    v_options_3705_ = lean_ctor_get(v___y_3700_, 2);
    v_currRecDepth_3706_ = lean_ctor_get(v___y_3700_, 3);
    v_maxRecDepth_3707_ = lean_ctor_get(v___y_3700_, 4);
    v_ref_3708_ = lean_ctor_get(v___y_3700_, 5);
    v_currNamespace_3709_ = lean_ctor_get(v___y_3700_, 6);
    v_openDecls_3710_ = lean_ctor_get(v___y_3700_, 7);
    v_initHeartbeats_3711_ = lean_ctor_get(v___y_3700_, 8);
    v_maxHeartbeats_3712_ = lean_ctor_get(v___y_3700_, 9);
    v_quotContext_3713_ = lean_ctor_get(v___y_3700_, 10);
    v_currMacroScope_3714_ = lean_ctor_get(v___y_3700_, 11);
    v_diag_3715_ = lean_ctor_get_uint8(
        v___y_3700_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3716_ = lean_ctor_get(v___y_3700_, 12);
    v_suppressElabErrors_3717_ = lean_ctor_get_uint8(
        v___y_3700_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3718_ = lean_ctor_get(v___y_3700_, 13);
    v_ref_3719_ = l_Lean_replaceRef(v_ref_3696_, v_ref_3708_);
    lean_inc_ref(v_inheritedTraceOptions_3718_);
    lean_inc(v_cancelTk_x3f_3716_);
    lean_inc(v_currMacroScope_3714_);
    lean_inc(v_quotContext_3713_);
    lean_inc(v_maxHeartbeats_3712_);
    lean_inc(v_initHeartbeats_3711_);
    lean_inc(v_openDecls_3710_);
    lean_inc(v_currNamespace_3709_);
    lean_inc(v_maxRecDepth_3707_);
    lean_inc(v_currRecDepth_3706_);
    lean_inc_ref(v_options_3705_);
    lean_inc_ref(v_fileMap_3704_);
    lean_inc_ref(v_fileName_3703_);
    v___x_3720_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3720_, 0, v_fileName_3703_);
    lean_ctor_set(v___x_3720_, 1, v_fileMap_3704_);
    lean_ctor_set(v___x_3720_, 2, v_options_3705_);
    lean_ctor_set(v___x_3720_, 3, v_currRecDepth_3706_);
    lean_ctor_set(v___x_3720_, 4, v_maxRecDepth_3707_);
    lean_ctor_set(v___x_3720_, 5, v_ref_3719_);
    lean_ctor_set(v___x_3720_, 6, v_currNamespace_3709_);
    lean_ctor_set(v___x_3720_, 7, v_openDecls_3710_);
    lean_ctor_set(v___x_3720_, 8, v_initHeartbeats_3711_);
    lean_ctor_set(v___x_3720_, 9, v_maxHeartbeats_3712_);
    lean_ctor_set(v___x_3720_, 10, v_quotContext_3713_);
    lean_ctor_set(v___x_3720_, 11, v_currMacroScope_3714_);
    lean_ctor_set(v___x_3720_, 12, v_cancelTk_x3f_3716_);
    lean_ctor_set(v___x_3720_, 13, v_inheritedTraceOptions_3718_);
    lean_ctor_set_uint8(
        v___x_3720_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3715_,
    );
    lean_ctor_set_uint8(
        v___x_3720_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3717_,
    );
    v___x_3721_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(
            v_msg_3697_,
            v___y_3698_,
            v___y_3699_,
            v___x_3720_,
            v___y_3701_,
        );
    lean_dec_ref_known(v___x_3720_, 14);
    return v___x_3721_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg___boxed(
    mut v_ref_3722_: *mut LeanObject,
    mut v_msg_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
    mut v___y_3725_: *mut LeanObject,
    mut v___y_3726_: *mut LeanObject,
    mut v___y_3727_: *mut LeanObject,
    mut v___y_3728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3729_: *mut LeanObject = core::ptr::null_mut();
    v_res_3729_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_ref_3722_, v_msg_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
    lean_dec(v___y_3727_);
    lean_dec_ref(v___y_3726_);
    lean_dec(v___y_3725_);
    lean_dec_ref(v___y_3724_);
    lean_dec(v_ref_3722_);
    return v_res_3729_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    v___x_3735_ = l_Lean_maxRecDepthErrorMessage;
    v___x_3736_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3736_, 0, v___x_3735_);
    return v___x_3736_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    v___x_3737_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3);
    v___x_3738_ = l_Lean_MessageData_ofFormat(v___x_3737_);
    return v___x_3738_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    v___x_3739_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4);
    v___x_3740_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2;
    v___x_3741_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_3741_, 0, v___x_3740_);
    lean_ctor_set(v___x_3741_, 1, v___x_3739_);
    return v___x_3741_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(
    mut v_ref_3742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    v___x_3744_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5);
    v___x_3745_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3745_, 0, v_ref_3742_);
    lean_ctor_set(v___x_3745_, 1, v___x_3744_);
    v___x_3746_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3746_, 0, v___x_3745_);
    return v___x_3746_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___boxed(
    mut v_ref_3747_: *mut LeanObject,
    mut v___y_3748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3749_: *mut LeanObject = core::ptr::null_mut();
    v_res_3749_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_ref_3747_);
    return v_res_3749_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(
    mut v_a_3750_: *mut LeanObject,
    mut v_x_3751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: u8 = 0;
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3751_) == 0 {
                    v___x_3752_ = lean_box(0);
                    return v___x_3752_;
                } else {
                    v_key_3753_ = lean_ctor_get(v_x_3751_, 0);
                    v_value_3754_ = lean_ctor_get(v_x_3751_, 1);
                    v_tail_3755_ = lean_ctor_get(v_x_3751_, 2);
                    v___x_3756_ = lean_name_eq(v_key_3753_, v_a_3750_);
                    if v___x_3756_ == 0 {
                        v_x_3751_ = v_tail_3755_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3754_);
                        v___x_3758_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3758_, 0, v_value_3754_);
                        return v___x_3758_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg___boxed(
    mut v_a_3759_: *mut LeanObject,
    mut v_x_3760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3761_: *mut LeanObject = core::ptr::null_mut();
    v_res_3761_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_3759_, v_x_3760_);
    lean_dec(v_x_3760_);
    lean_dec(v_a_3759_);
    return v_res_3761_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: u64 = 0;
    v___x_3762_ = lean_unsigned_to_nat(1723);
    v___x_3763_ = lean_uint64_of_nat(v___x_3762_);
    return v___x_3763_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(
    mut v_m_3764_: *mut LeanObject,
    mut v_a_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: u64 = 0;
    let mut v___x_3770_: u64 = 0;
    let mut v___x_3771_: u64 = 0;
    let mut v_fold_3772_: u64 = 0;
    let mut v___x_3773_: u64 = 0;
    let mut v___x_3774_: u64 = 0;
    let mut v___x_3775_: u64 = 0;
    let mut v___x_3776_: usize = 0;
    let mut v___x_3777_: usize = 0;
    let mut v___x_3778_: usize = 0;
    let mut v___x_3779_: usize = 0;
    let mut v___x_3780_: usize = 0;
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: u64 = 0;
    let mut v_hash_3784_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3766_ = lean_ctor_get(v_m_3764_, 1);
                v___x_3767_ = lean_array_get_size(v_buckets_3766_);
                if lean_obj_tag(v_a_3765_) == 0 {
                    v___x_3783_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0);
                    v___y_3769_ = v___x_3783_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3784_ = lean_ctor_get_uint64(
                        v_a_3765_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3769_ = v_hash_3784_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3770_ = 32u64;
                v___x_3771_ = lean_uint64_shift_right(v___y_3769_, v___x_3770_);
                v_fold_3772_ = lean_uint64_xor(v___y_3769_, v___x_3771_);
                v___x_3773_ = 16u64;
                v___x_3774_ = lean_uint64_shift_right(v_fold_3772_, v___x_3773_);
                v___x_3775_ = lean_uint64_xor(v_fold_3772_, v___x_3774_);
                v___x_3776_ = lean_uint64_to_usize(v___x_3775_);
                v___x_3777_ = lean_usize_of_nat(v___x_3767_);
                v___x_3778_ = 1usize;
                v___x_3779_ = lean_usize_sub(v___x_3777_, v___x_3778_);
                v___x_3780_ = lean_usize_land(v___x_3776_, v___x_3779_);
                v___x_3781_ = lean_array_uget_borrowed(v_buckets_3766_, v___x_3780_);
                v___x_3782_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_3765_, v___x_3781_);
                return v___x_3782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_m_3785_: *mut LeanObject,
    mut v_a_3786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3787_: *mut LeanObject = core::ptr::null_mut();
    v_res_3787_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v_m_3785_, v_a_3786_);
    lean_dec(v_a_3786_);
    lean_dec_ref(v_m_3785_);
    return v_res_3787_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(
    mut v_keys_3788_: *mut LeanObject,
    mut v_i_3789_: *mut LeanObject,
    mut v_k_3790_: *mut LeanObject,
) -> u8 {
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: u8 = 0;
    let mut v_k_x27_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: u8 = 0;
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3791_ = lean_array_get_size(v_keys_3788_);
                v___x_3792_ = lean_nat_dec_lt(v_i_3789_, v___x_3791_);
                if v___x_3792_ == 0 {
                    lean_dec(v_i_3789_);
                    return v___x_3792_;
                } else {
                    v_k_x27_3793_ = lean_array_fget_borrowed(v_keys_3788_, v_i_3789_);
                    v___x_3794_ = l_Lean_instBEqExtraModUse_beq(v_k_3790_, v_k_x27_3793_);
                    if v___x_3794_ == 0 {
                        v___x_3795_ = lean_unsigned_to_nat(1);
                        v___x_3796_ = lean_nat_add(v_i_3789_, v___x_3795_);
                        lean_dec(v_i_3789_);
                        v_i_3789_ = v___x_3796_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_3789_);
                        return v___x_3794_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg___boxed(
    mut v_keys_3798_: *mut LeanObject,
    mut v_i_3799_: *mut LeanObject,
    mut v_k_3800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3801_: u8 = 0;
    let mut v_r_3802_: *mut LeanObject = core::ptr::null_mut();
    v_res_3801_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_keys_3798_, v_i_3799_, v_k_3800_);
    lean_dec_ref(v_k_3800_);
    lean_dec_ref(v_keys_3798_);
    v_r_3802_ = lean_box((v_res_3801_) as usize);
    return v_r_3802_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(
    mut v_x_3803_: *mut LeanObject,
    mut v_x_3804_: usize,
    mut v_x_3805_: *mut LeanObject,
) -> u8 {
    let mut v_es_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: usize = 0;
    let mut v___x_3809_: usize = 0;
    let mut v___x_3810_: usize = 0;
    let mut v_j_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: u8 = 0;
    let mut v_node_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: usize = 0;
    let mut v___x_3818_: u8 = 0;
    let mut v_ks_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3803_) == 0 {
                    v_es_3806_ = lean_ctor_get(v_x_3803_, 0);
                    v___x_3807_ = lean_box(2);
                    v___x_3808_ = 5usize;
                    v___x_3809_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1);
                    v___x_3810_ = lean_usize_land(v_x_3804_, v___x_3809_);
                    v_j_3811_ = lean_usize_to_nat(v___x_3810_);
                    v___x_3812_ = lean_array_get_borrowed(v___x_3807_, v_es_3806_, v_j_3811_);
                    lean_dec(v_j_3811_);
                    match lean_obj_tag(v___x_3812_) {
                        0 => {
                            v_key_3813_ = lean_ctor_get(v___x_3812_, 0);
                            v___x_3814_ = l_Lean_instBEqExtraModUse_beq(v_x_3805_, v_key_3813_);
                            return v___x_3814_;
                        }
                        1 => {
                            v_node_3815_ = lean_ctor_get(v___x_3812_, 0);
                            v___x_3816_ = lean_usize_shift_right(v_x_3804_, v___x_3808_);
                            v_x_3803_ = v_node_3815_;
                            v_x_3804_ = v___x_3816_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3818_ = 0;
                            return v___x_3818_;
                        }
                    }
                } else {
                    v_ks_3819_ = lean_ctor_get(v_x_3803_, 0);
                    v___x_3820_ = lean_unsigned_to_nat(0);
                    v___x_3821_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_ks_3819_, v___x_3820_, v_x_3805_);
                    return v___x_3821_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg___boxed(
    mut v_x_3822_: *mut LeanObject,
    mut v_x_3823_: *mut LeanObject,
    mut v_x_3824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_18437__boxed_3825_: usize = 0;
    let mut v_res_3826_: u8 = 0;
    let mut v_r_3827_: *mut LeanObject = core::ptr::null_mut();
    v_x_18437__boxed_3825_ = lean_unbox_usize(v_x_3823_);
    lean_dec(v_x_3823_);
    v_res_3826_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_3822_, v_x_18437__boxed_3825_, v_x_3824_);
    lean_dec_ref(v_x_3824_);
    lean_dec_ref(v_x_3822_);
    v_r_3827_ = lean_box((v_res_3826_) as usize);
    return v_r_3827_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_x_3828_: *mut LeanObject,
    mut v_x_3829_: *mut LeanObject,
) -> u8 {
    let mut v___x_3830_: u64 = 0;
    let mut v___x_3831_: usize = 0;
    let mut v___x_3832_: u8 = 0;
    v___x_3830_ = l_Lean_instHashableExtraModUse_hash(v_x_3829_);
    v___x_3831_ = lean_uint64_to_usize(v___x_3830_);
    v___x_3832_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_3828_, v___x_3831_, v_x_3829_);
    return v___x_3832_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_x_3833_: *mut LeanObject,
    mut v_x_3834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3835_: u8 = 0;
    let mut v_r_3836_: *mut LeanObject = core::ptr::null_mut();
    v_res_3835_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v_x_3833_, v_x_3834_);
    lean_dec_ref(v_x_3834_);
    lean_dec_ref(v_x_3833_);
    v_r_3836_ = lean_box((v_res_3835_) as usize);
    return v_r_3836_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    v___x_3839_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1;
    v___x_3840_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0;
    v___x_3841_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_3840_, v___x_3839_);
    return v___x_3841_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    v___x_3842_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3842_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    v___x_3843_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3);
    v___x_3844_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3844_, 0, v___x_3843_);
    return v___x_3844_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    v___x_3845_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4);
    v___x_3846_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3846_, 0, v___x_3845_);
    lean_ctor_set(v___x_3846_, 1, v___x_3845_);
    return v___x_3846_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    v___x_3847_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4);
    v___x_3848_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_3848_, 0, v___x_3847_);
    lean_ctor_set(v___x_3848_, 1, v___x_3847_);
    lean_ctor_set(v___x_3848_, 2, v___x_3847_);
    lean_ctor_set(v___x_3848_, 3, v___x_3847_);
    lean_ctor_set(v___x_3848_, 4, v___x_3847_);
    lean_ctor_set(v___x_3848_, 5, v___x_3847_);
    return v___x_3848_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    v___x_3853_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9;
    v___x_3854_ = l_Lean_stringToMessageData(v___x_3853_);
    return v___x_3854_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12()
-> *mut LeanObject {
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    v___x_3856_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11;
    v___x_3857_ = l_Lean_stringToMessageData(v___x_3856_);
    return v___x_3857_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    v___x_3858_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1;
    v___x_3859_ = l_Lean_stringToMessageData(v___x_3858_);
    return v___x_3859_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14()
-> *mut LeanObject {
    let mut v_cls_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    v_cls_3860_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8;
    v___x_3861_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17;
    v___x_3862_ = l_Lean_Name_append(v___x_3861_, v_cls_3860_);
    return v___x_3862_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16()
-> *mut LeanObject {
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    v___x_3864_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15;
    v___x_3865_ = l_Lean_stringToMessageData(v___x_3864_);
    return v___x_3865_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18()
-> *mut LeanObject {
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    v___x_3867_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17;
    v___x_3868_ = l_Lean_stringToMessageData(v___x_3867_);
    return v___x_3868_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(
    mut v_mod_3873_: *mut LeanObject,
    mut v_isMeta_3874_: u8,
    mut v_hint_3875_: *mut LeanObject,
    mut v___y_3876_: *mut LeanObject,
    mut v___y_3877_: *mut LeanObject,
    mut v___y_3878_: *mut LeanObject,
    mut v___y_3879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3883_: u8 = 0;
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v_asyncMode_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3928_: u8 = 0;
    let mut v_unused_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3931_: u8 = 0;
    let mut v_unused_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v_options_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3936_: u8 = 0;
    let mut v_inheritedTraceOptions_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: u8 = 0;
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3881_ = lean_st_ref_get(v___y_3879_);
                v_env_3882_ = lean_ctor_get(v___x_3881_, 0);
                lean_inc_ref(v_env_3882_);
                lean_dec(v___x_3881_);
                v_isExporting_3883_ = lean_ctor_get_uint8(
                    v_env_3882_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_3882_);
                v___x_3884_ = lean_st_ref_get(v___y_3879_);
                v_env_3885_ = lean_ctor_get(v___x_3884_, 0);
                lean_inc_ref(v_env_3885_);
                lean_dec(v___x_3884_);
                v___x_3886_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2);
                lean_inc(v_mod_3873_);
                v_entry_3887_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_3887_, 0, v_mod_3873_);
                lean_ctor_set_uint8(
                    v_entry_3887_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_3883_,
                );
                lean_ctor_set_uint8(
                    v_entry_3887_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_3874_,
                );
                v___x_3888_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_3889_ = lean_box(1);
                v___x_3890_ = lean_box(0);
                v___x_3933_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_3886_,
                    v___x_3888_,
                    v_env_3885_,
                    v___x_3889_,
                    v___x_3890_,
                );
                v___x_3934_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v___x_3933_, v_entry_3887_);
                lean_dec(v___x_3933_);
                if v___x_3934_ == 0 {
                    v_options_3935_ = lean_ctor_get(v___y_3878_, 2);
                    v_hasTrace_3936_ = lean_ctor_get_uint8(
                        v_options_3935_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3936_ == 0 {
                        lean_dec(v_hint_3875_);
                        lean_dec(v_mod_3873_);
                        v___y_3892_ = v___y_3877_;
                        v___y_3893_ = v___y_3879_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_3937_ = lean_ctor_get(v___y_3878_, 13);
                        v_cls_3938_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8;
                        v___x_3958_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14);
                        v___x_3959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3937_,
                            v_options_3935_,
                            v___x_3958_,
                        );
                        if v___x_3959_ == 0 {
                            lean_dec(v_hint_3875_);
                            lean_dec(v_mod_3873_);
                            v___y_3892_ = v___y_3877_;
                            v___y_3893_ = v___y_3879_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3960_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16);
                            if v_isExporting_3883_ == 0 {
                                v___x_3969_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21;
                                v___y_3962_ = v___x_3969_;
                                state = 8;
                                continue;
                            } else {
                                v___x_3970_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22;
                                v___y_3962_ = v___x_3970_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v_entry_3887_, 1);
                    lean_dec(v_hint_3875_);
                    lean_dec(v_mod_3873_);
                    v___x_3971_ = lean_box(0);
                    v___x_3972_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3972_, 0, v___x_3971_);
                    return v___x_3972_;
                }
            }
            1 => {
                v___x_3894_ = lean_st_ref_take(v___y_3893_);
                v_toEnvExtension_3895_ = lean_ctor_get(v___x_3888_, 0);
                v_env_3896_ = lean_ctor_get(v___x_3894_, 0);
                v_nextMacroScope_3897_ = lean_ctor_get(v___x_3894_, 1);
                v_ngen_3898_ = lean_ctor_get(v___x_3894_, 2);
                v_auxDeclNGen_3899_ = lean_ctor_get(v___x_3894_, 3);
                v_traceState_3900_ = lean_ctor_get(v___x_3894_, 4);
                v_messages_3901_ = lean_ctor_get(v___x_3894_, 6);
                v_infoState_3902_ = lean_ctor_get(v___x_3894_, 7);
                v_snapshotTasks_3903_ = lean_ctor_get(v___x_3894_, 8);
                v_isSharedCheck_3931_ = (!lean_is_exclusive(v___x_3894_)) as u8;
                if v_isSharedCheck_3931_ == 0 {
                    v_unused_3932_ = lean_ctor_get(v___x_3894_, 5);
                    lean_dec(v_unused_3932_);
                    v___x_3905_ = v___x_3894_;
                    v_isShared_3906_ = v_isSharedCheck_3931_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3903_);
                    lean_inc(v_infoState_3902_);
                    lean_inc(v_messages_3901_);
                    lean_inc(v_traceState_3900_);
                    lean_inc(v_auxDeclNGen_3899_);
                    lean_inc(v_ngen_3898_);
                    lean_inc(v_nextMacroScope_3897_);
                    lean_inc(v_env_3896_);
                    lean_dec(v___x_3894_);
                    v___x_3905_ = lean_box(0);
                    v_isShared_3906_ = v_isSharedCheck_3931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_3907_ = lean_ctor_get(v_toEnvExtension_3895_, 2);
                v___x_3908_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3888_,
                    v_env_3896_,
                    v_entry_3887_,
                    v_asyncMode_3907_,
                    v___x_3890_,
                );
                v___x_3909_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5);
                if v_isShared_3906_ == 0 {
                    lean_ctor_set(v___x_3905_, 5, v___x_3909_);
                    lean_ctor_set(v___x_3905_, 0, v___x_3908_);
                    v___x_3911_ = v___x_3905_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3908_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_nextMacroScope_3897_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 2, v_ngen_3898_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 3, v_auxDeclNGen_3899_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 4, v_traceState_3900_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 5, v___x_3909_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 6, v_messages_3901_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 7, v_infoState_3902_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 8, v_snapshotTasks_3903_);
                    v___x_3911_ = v_reuseFailAlloc_3930_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3912_ = lean_st_ref_set(v___y_3893_, v___x_3911_);
                v___x_3913_ = lean_st_ref_take(v___y_3892_);
                v_mctx_3914_ = lean_ctor_get(v___x_3913_, 0);
                v_zetaDeltaFVarIds_3915_ = lean_ctor_get(v___x_3913_, 2);
                v_postponed_3916_ = lean_ctor_get(v___x_3913_, 3);
                v_diag_3917_ = lean_ctor_get(v___x_3913_, 4);
                v_isSharedCheck_3928_ = (!lean_is_exclusive(v___x_3913_)) as u8;
                if v_isSharedCheck_3928_ == 0 {
                    v_unused_3929_ = lean_ctor_get(v___x_3913_, 1);
                    lean_dec(v_unused_3929_);
                    v___x_3919_ = v___x_3913_;
                    v_isShared_3920_ = v_isSharedCheck_3928_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_diag_3917_);
                    lean_inc(v_postponed_3916_);
                    lean_inc(v_zetaDeltaFVarIds_3915_);
                    lean_inc(v_mctx_3914_);
                    lean_dec(v___x_3913_);
                    v___x_3919_ = lean_box(0);
                    v_isShared_3920_ = v_isSharedCheck_3928_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3921_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6);
                if v_isShared_3920_ == 0 {
                    lean_ctor_set(v___x_3919_, 1, v___x_3921_);
                    v___x_3923_ = v___x_3919_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_mctx_3914_);
                    lean_ctor_set(v_reuseFailAlloc_3927_, 1, v___x_3921_);
                    lean_ctor_set(v_reuseFailAlloc_3927_, 2, v_zetaDeltaFVarIds_3915_);
                    lean_ctor_set(v_reuseFailAlloc_3927_, 3, v_postponed_3916_);
                    lean_ctor_set(v_reuseFailAlloc_3927_, 4, v_diag_3917_);
                    v___x_3923_ = v_reuseFailAlloc_3927_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3924_ = lean_st_ref_set(v___y_3892_, v___x_3923_);
                v___x_3925_ = lean_box(0);
                v___x_3926_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3926_, 0, v___x_3925_);
                return v___x_3926_;
            }
            6 => {
                v___x_3942_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3942_, 0, v___y_3940_);
                lean_ctor_set(v___x_3942_, 1, v___y_3941_);
                v___x_3943_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_cls_3938_, v___x_3942_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
                if lean_obj_tag(v___x_3943_) == 0 {
                    lean_dec_ref_known(v___x_3943_, 1);
                    v___y_3892_ = v___y_3877_;
                    v___y_3893_ = v___y_3879_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_3887_, 1);
                    return v___x_3943_;
                }
            }
            7 => {
                lean_inc_ref(v___y_3946_);
                v___x_3947_ = l_Lean_stringToMessageData(v___y_3946_);
                v___x_3948_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3948_, 0, v___y_3945_);
                lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                v___x_3949_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10);
                v___x_3950_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                lean_ctor_set(v___x_3950_, 1, v___x_3949_);
                v___x_3951_ = l_Lean_MessageData_ofName(v_mod_3873_);
                v___x_3952_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3952_, 0, v___x_3950_);
                lean_ctor_set(v___x_3952_, 1, v___x_3951_);
                v___x_3953_ = l_Lean_Name_isAnonymous(v_hint_3875_);
                if v___x_3953_ == 0 {
                    v___x_3954_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12);
                    v___x_3955_ = l_Lean_MessageData_ofName(v_hint_3875_);
                    v___x_3956_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3956_, 0, v___x_3954_);
                    lean_ctor_set(v___x_3956_, 1, v___x_3955_);
                    v___y_3940_ = v___x_3952_;
                    v___y_3941_ = v___x_3956_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v_hint_3875_);
                    v___x_3957_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13);
                    v___y_3940_ = v___x_3952_;
                    v___y_3941_ = v___x_3957_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                lean_inc_ref(v___y_3962_);
                v___x_3963_ = l_Lean_stringToMessageData(v___y_3962_);
                v___x_3964_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3964_, 0, v___x_3960_);
                lean_ctor_set(v___x_3964_, 1, v___x_3963_);
                v___x_3965_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18);
                v___x_3966_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3966_, 0, v___x_3964_);
                lean_ctor_set(v___x_3966_, 1, v___x_3965_);
                if v_isMeta_3874_ == 0 {
                    v___x_3967_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19;
                    v___y_3945_ = v___x_3966_;
                    v___y_3946_ = v___x_3967_;
                    state = 7;
                    continue;
                } else {
                    v___x_3968_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20;
                    v___y_3945_ = v___x_3966_;
                    v___y_3946_ = v___x_3968_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_mod_3973_: *mut LeanObject,
    mut v_isMeta_3974_: *mut LeanObject,
    mut v_hint_3975_: *mut LeanObject,
    mut v___y_3976_: *mut LeanObject,
    mut v___y_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
    mut v___y_3980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3981_: u8 = 0;
    let mut v_res_3982_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3981_ = (lean_unbox(v_isMeta_3974_) as u8);
    v_res_3982_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_mod_3973_, v_isMeta_boxed_3981_, v_hint_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
    lean_dec(v___y_3979_);
    lean_dec_ref(v___y_3978_);
    lean_dec(v___y_3977_);
    lean_dec_ref(v___y_3976_);
    return v_res_3982_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(
    mut v___x_3983_: *mut LeanObject,
    mut v_declName_3984_: *mut LeanObject,
    mut v_as_3985_: *mut LeanObject,
    mut v_sz_3986_: usize,
    mut v_i_3987_: usize,
    mut v_b_3988_: *mut LeanObject,
    mut v___y_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
    mut v___y_3991_: *mut LeanObject,
    mut v___y_3992_: *mut LeanObject,
    mut v___y_3993_: *mut LeanObject,
    mut v___y_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
    mut v___y_3996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3998_: u8 = 0;
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: usize = 0;
    let mut v___x_4011_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3998_ = lean_usize_dec_lt(v_i_3987_, v_sz_3986_);
                if v___x_3998_ == 0 {
                    lean_dec(v_declName_3984_);
                    v___x_3999_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3999_, 0, v_b_3988_);
                    return v___x_3999_;
                } else {
                    v___x_4000_ = l_Lean_Environment_header(v___x_3983_);
                    v_modules_4001_ = lean_ctor_get(v___x_4000_, 3);
                    lean_inc_ref(v_modules_4001_);
                    lean_dec_ref(v___x_4000_);
                    v___x_4002_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_4003_ = lean_array_uget_borrowed(v_as_3985_, v_i_3987_);
                    v___x_4004_ = lean_array_get(v___x_4002_, v_modules_4001_, v_a_4003_);
                    lean_dec_ref(v_modules_4001_);
                    v_toImport_4005_ = lean_ctor_get(v___x_4004_, 0);
                    lean_inc_ref(v_toImport_4005_);
                    lean_dec(v___x_4004_);
                    v_module_4006_ = lean_ctor_get(v_toImport_4005_, 0);
                    lean_inc(v_module_4006_);
                    lean_dec_ref(v_toImport_4005_);
                    v___x_4007_ = 0;
                    lean_inc(v_declName_3984_);
                    v___x_4008_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_module_4006_, v___x_4007_, v_declName_3984_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
                    if lean_obj_tag(v___x_4008_) == 0 {
                        lean_dec_ref_known(v___x_4008_, 1);
                        v___x_4009_ = lean_box(0);
                        v___x_4010_ = 1usize;
                        v___x_4011_ = lean_usize_add(v_i_3987_, v___x_4010_);
                        v_i_3987_ = v___x_4011_;
                        v_b_3988_ = v___x_4009_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_3984_);
                        return v___x_4008_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4___boxed(
    mut v___x_4013_: *mut LeanObject,
    mut v_declName_4014_: *mut LeanObject,
    mut v_as_4015_: *mut LeanObject,
    mut v_sz_4016_: *mut LeanObject,
    mut v_i_4017_: *mut LeanObject,
    mut v_b_4018_: *mut LeanObject,
    mut v___y_4019_: *mut LeanObject,
    mut v___y_4020_: *mut LeanObject,
    mut v___y_4021_: *mut LeanObject,
    mut v___y_4022_: *mut LeanObject,
    mut v___y_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
    mut v___y_4026_: *mut LeanObject,
    mut v___y_4027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4028_: usize = 0;
    let mut v_i_boxed_4029_: usize = 0;
    let mut v_res_4030_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4028_ = lean_unbox_usize(v_sz_4016_);
    lean_dec(v_sz_4016_);
    v_i_boxed_4029_ = lean_unbox_usize(v_i_4017_);
    lean_dec(v_i_4017_);
    v_res_4030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(v___x_4013_, v_declName_4014_, v_as_4015_, v_sz_boxed_4028_, v_i_boxed_4029_, v_b_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
    lean_dec(v___y_4026_);
    lean_dec_ref(v___y_4025_);
    lean_dec(v___y_4024_);
    lean_dec_ref(v___y_4023_);
    lean_dec(v___y_4022_);
    lean_dec_ref(v___y_4021_);
    lean_dec(v___y_4020_);
    lean_dec_ref(v___y_4019_);
    lean_dec_ref(v_as_4015_);
    lean_dec_ref(v___x_4013_);
    return v_res_4030_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    v___x_4033_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1;
    v___x_4034_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0;
    v___x_4035_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_4034_, v___x_4033_);
    return v___x_4035_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(
    mut v_declName_4038_: *mut LeanObject,
    mut v_isMeta_4039_: u8,
    mut v___y_4040_: *mut LeanObject,
    mut v___y_4041_: *mut LeanObject,
    mut v___y_4042_: *mut LeanObject,
    mut v___y_4043_: *mut LeanObject,
    mut v___y_4044_: *mut LeanObject,
    mut v___y_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
    mut v___y_4047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4057_: usize = 0;
    let mut v___x_4058_: usize = 0;
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut v_unused_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4079_: u8 = 0;
    let mut v_toImport_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4049_ = lean_st_ref_get(v___y_4047_);
                v_env_4053_ = lean_ctor_get(v___x_4049_, 0);
                lean_inc_ref(v_env_4053_);
                lean_dec(v___x_4049_);
                v___x_4068_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4053_, v_declName_4038_);
                if lean_obj_tag(v___x_4068_) == 0 {
                    lean_dec_ref(v_env_4053_);
                    lean_dec(v_declName_4038_);
                    state = 1;
                    continue;
                } else {
                    v_val_4069_ = lean_ctor_get(v___x_4068_, 0);
                    lean_inc(v_val_4069_);
                    lean_dec_ref_known(v___x_4068_, 1);
                    v___x_4070_ = l_Lean_Environment_header(v_env_4053_);
                    v_modules_4071_ = lean_ctor_get(v___x_4070_, 3);
                    lean_inc_ref(v_modules_4071_);
                    lean_dec_ref(v___x_4070_);
                    v___x_4072_ = lean_array_get_size(v_modules_4071_);
                    v___x_4073_ = lean_nat_dec_lt(v_val_4069_, v___x_4072_);
                    if v___x_4073_ == 0 {
                        lean_dec_ref(v_modules_4071_);
                        lean_dec(v_val_4069_);
                        lean_dec_ref(v_env_4053_);
                        lean_dec(v_declName_4038_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4074_ = lean_st_ref_get(v___y_4047_);
                        v_env_4075_ = lean_ctor_get(v___x_4074_, 0);
                        lean_inc_ref(v_env_4075_);
                        lean_dec(v___x_4074_);
                        v___x_4076_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2);
                        v___x_4077_ = lean_array_fget(v_modules_4071_, v_val_4069_);
                        lean_dec(v_val_4069_);
                        lean_dec_ref(v_modules_4071_);
                        if v_isMeta_4039_ == 0 {
                            lean_dec_ref(v_env_4075_);
                            v___y_4079_ = v_isMeta_4039_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_declName_4038_);
                            v___x_4090_ = l_Lean_isMarkedMeta(v_env_4075_, v_declName_4038_);
                            if v___x_4090_ == 0 {
                                v___y_4079_ = v_isMeta_4039_;
                                state = 5;
                                continue;
                            } else {
                                v___x_4091_ = 0;
                                v___y_4079_ = v___x_4091_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4051_ = lean_box(0);
                v___x_4052_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4052_, 0, v___x_4051_);
                return v___x_4052_;
            }
            2 => {
                v___x_4056_ = lean_box(0);
                v_sz_4057_ = lean_array_size(v___y_4055_);
                v___x_4058_ = 0usize;
                v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(v_env_4053_, v_declName_4038_, v___y_4055_, v_sz_4057_, v___x_4058_, v___x_4056_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
                lean_dec_ref(v___y_4055_);
                lean_dec_ref(v_env_4053_);
                if lean_obj_tag(v___x_4059_) == 0 {
                    v_isSharedCheck_4066_ = (!lean_is_exclusive(v___x_4059_)) as u8;
                    if v_isSharedCheck_4066_ == 0 {
                        v_unused_4067_ = lean_ctor_get(v___x_4059_, 0);
                        lean_dec(v_unused_4067_);
                        v___x_4061_ = v___x_4059_;
                        v_isShared_4062_ = v_isSharedCheck_4066_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_4059_);
                        v___x_4061_ = lean_box(0);
                        v_isShared_4062_ = v_isSharedCheck_4066_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_4059_;
                }
            }
            3 => {
                if v_isShared_4062_ == 0 {
                    lean_ctor_set(v___x_4061_, 0, v___x_4056_);
                    v___x_4064_ = v___x_4061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4056_);
                    v___x_4064_ = v_reuseFailAlloc_4065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4064_;
            }
            5 => {
                v_toImport_4080_ = lean_ctor_get(v___x_4077_, 0);
                lean_inc_ref(v_toImport_4080_);
                lean_dec(v___x_4077_);
                v_module_4081_ = lean_ctor_get(v_toImport_4080_, 0);
                lean_inc(v_module_4081_);
                lean_dec_ref(v_toImport_4080_);
                lean_inc(v_declName_4038_);
                v___x_4082_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_module_4081_, v___y_4079_, v_declName_4038_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
                if lean_obj_tag(v___x_4082_) == 0 {
                    lean_dec_ref_known(v___x_4082_, 1);
                    v___x_4083_ = l_Lean_indirectModUseExt;
                    v___x_4084_ = lean_box(1);
                    v___x_4085_ = lean_box(0);
                    lean_inc_ref(v_env_4053_);
                    v___x_4086_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4076_,
                        v___x_4083_,
                        v_env_4053_,
                        v___x_4084_,
                        v___x_4085_,
                    );
                    v___x_4087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v___x_4086_, v_declName_4038_);
                    lean_dec(v___x_4086_);
                    if lean_obj_tag(v___x_4087_) == 0 {
                        v___x_4088_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3;
                        v___y_4055_ = v___x_4088_;
                        state = 2;
                        continue;
                    } else {
                        v_val_4089_ = lean_ctor_get(v___x_4087_, 0);
                        lean_inc(v_val_4089_);
                        lean_dec_ref_known(v___x_4087_, 1);
                        v___y_4055_ = v_val_4089_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_4053_);
                    lean_dec(v_declName_4038_);
                    return v___x_4082_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___boxed(
    mut v_declName_4092_: *mut LeanObject,
    mut v_isMeta_4093_: *mut LeanObject,
    mut v___y_4094_: *mut LeanObject,
    mut v___y_4095_: *mut LeanObject,
    mut v___y_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
    mut v___y_4098_: *mut LeanObject,
    mut v___y_4099_: *mut LeanObject,
    mut v___y_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
    mut v___y_4102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_4103_: u8 = 0;
    let mut v_res_4104_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4103_ = (lean_unbox(v_isMeta_4093_) as u8);
    v_res_4104_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(v_declName_4092_, v_isMeta_boxed_4103_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
    lean_dec(v___y_4101_);
    lean_dec_ref(v___y_4100_);
    lean_dec(v___y_4099_);
    lean_dec_ref(v___y_4098_);
    lean_dec(v___y_4097_);
    lean_dec_ref(v___y_4096_);
    lean_dec(v___y_4095_);
    lean_dec_ref(v___y_4094_);
    return v_res_4104_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(
    mut v_as_x27_4105_: *mut LeanObject,
    mut v_b_4106_: *mut LeanObject,
    mut v___y_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
    mut v___y_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
    mut v___y_4112_: *mut LeanObject,
    mut v___y_4113_: *mut LeanObject,
    mut v___y_4114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: u8 = 0;
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4105_) == 0 {
                    v___x_4116_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4116_, 0, v_b_4106_);
                    return v___x_4116_;
                } else {
                    v_head_4117_ = lean_ctor_get(v_as_x27_4105_, 0);
                    v_tail_4118_ = lean_ctor_get(v_as_x27_4105_, 1);
                    v___x_4119_ = 1;
                    lean_inc(v_head_4117_);
                    v___x_4120_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(v_head_4117_, v___x_4119_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
                    if lean_obj_tag(v___x_4120_) == 0 {
                        lean_dec_ref_known(v___x_4120_, 1);
                        v___x_4121_ = lean_box(0);
                        v_as_x27_4105_ = v_tail_4118_;
                        v_b_4106_ = v___x_4121_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4120_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg___boxed(
    mut v_as_x27_4123_: *mut LeanObject,
    mut v_b_4124_: *mut LeanObject,
    mut v___y_4125_: *mut LeanObject,
    mut v___y_4126_: *mut LeanObject,
    mut v___y_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
    mut v___y_4129_: *mut LeanObject,
    mut v___y_4130_: *mut LeanObject,
    mut v___y_4131_: *mut LeanObject,
    mut v___y_4132_: *mut LeanObject,
    mut v___y_4133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4134_: *mut LeanObject = core::ptr::null_mut();
    v_res_4134_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_as_x27_4123_, v_b_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
    lean_dec(v___y_4132_);
    lean_dec_ref(v___y_4131_);
    lean_dec(v___y_4130_);
    lean_dec_ref(v___y_4129_);
    lean_dec(v___y_4128_);
    lean_dec_ref(v___y_4127_);
    lean_dec(v___y_4126_);
    lean_dec_ref(v___y_4125_);
    lean_dec(v_as_x27_4123_);
    return v_res_4134_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(
    mut v_currNamespace_4135_: *mut LeanObject,
    mut v___y_4136_: *mut LeanObject,
    mut v___y_4137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    v___x_4138_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4138_, 0, v_currNamespace_4135_);
    lean_ctor_set(v___x_4138_, 1, v___y_4137_);
    return v___x_4138_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed(
    mut v_currNamespace_4139_: *mut LeanObject,
    mut v___y_4140_: *mut LeanObject,
    mut v___y_4141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4142_: *mut LeanObject = core::ptr::null_mut();
    v_res_4142_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(v_currNamespace_4139_, v___y_4140_, v___y_4141_);
    lean_dec_ref(v___y_4140_);
    return v_res_4142_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(
    mut v_env_4143_: *mut LeanObject,
    mut v_options_4144_: *mut LeanObject,
    mut v_currNamespace_4145_: *mut LeanObject,
    mut v_openDecls_4146_: *mut LeanObject,
    mut v_n_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    v___x_4150_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_4143_,
        v_options_4144_,
        v_currNamespace_4145_,
        v_openDecls_4146_,
        v_n_4147_,
    );
    v___x_4151_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4151_, 0, v___x_4150_);
    lean_ctor_set(v___x_4151_, 1, v___y_4149_);
    return v___x_4151_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed(
    mut v_env_4152_: *mut LeanObject,
    mut v_options_4153_: *mut LeanObject,
    mut v_currNamespace_4154_: *mut LeanObject,
    mut v_openDecls_4155_: *mut LeanObject,
    mut v_n_4156_: *mut LeanObject,
    mut v___y_4157_: *mut LeanObject,
    mut v___y_4158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4159_: *mut LeanObject = core::ptr::null_mut();
    v_res_4159_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(v_env_4152_, v_options_4153_, v_currNamespace_4154_, v_openDecls_4155_, v_n_4156_, v___y_4157_, v___y_4158_);
    lean_dec_ref(v___y_4157_);
    lean_dec_ref(v_options_4153_);
    return v_res_4159_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(
    mut v_x_4160_: *mut LeanObject,
    mut v___y_4161_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4160_) == 0 {
        let mut v_a_4162_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
        v_a_4162_ = lean_ctor_get(v_x_4160_, 0);
        lean_inc(v_a_4162_);
        v___x_4163_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4163_, 0, v_a_4162_);
        lean_ctor_set(v___x_4163_, 1, v___y_4161_);
        return v___x_4163_;
    } else {
        let mut v_a_4164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
        v_a_4164_ = lean_ctor_get(v_x_4160_, 0);
        lean_inc(v_a_4164_);
        v___x_4165_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4165_, 0, v_a_4164_);
        lean_ctor_set(v___x_4165_, 1, v___y_4161_);
        return v___x_4165_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg___boxed(
    mut v_x_4166_: *mut LeanObject,
    mut v___y_4167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4168_: *mut LeanObject = core::ptr::null_mut();
    v_res_4168_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v_x_4166_, v___y_4167_);
    lean_dec_ref(v_x_4166_);
    return v_res_4168_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(
    mut v_env_4169_: *mut LeanObject,
    mut v_stx_4170_: *mut LeanObject,
    mut v___y_4171_: *mut LeanObject,
    mut v___y_4172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4178_: u8 = 0;
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4183_: u8 = 0;
    let mut v_unused_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4188_: u8 = 0;
    let mut v_snd_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4194_: u8 = 0;
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4199_: u8 = 0;
    let mut v_a_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut v_isSharedCheck_4213_: u8 = 0;
    let mut v_a_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4218_: u8 = 0;
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4173_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_4169_,
                    v_stx_4170_,
                    v___y_4171_,
                    v___y_4172_,
                );
                if lean_obj_tag(v___x_4173_) == 0 {
                    v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
                    lean_inc(v_a_4174_);
                    if lean_obj_tag(v_a_4174_) == 0 {
                        v_a_4175_ = lean_ctor_get(v___x_4173_, 1);
                        v_isSharedCheck_4183_ = (!lean_is_exclusive(v___x_4173_)) as u8;
                        if v_isSharedCheck_4183_ == 0 {
                            v_unused_4184_ = lean_ctor_get(v___x_4173_, 0);
                            lean_dec(v_unused_4184_);
                            v___x_4177_ = v___x_4173_;
                            v_isShared_4178_ = v_isSharedCheck_4183_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4175_);
                            lean_dec(v___x_4173_);
                            v___x_4177_ = lean_box(0);
                            v_isShared_4178_ = v_isSharedCheck_4183_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_4185_ = lean_ctor_get(v_a_4174_, 0);
                        v_isSharedCheck_4213_ = (!lean_is_exclusive(v_a_4174_)) as u8;
                        if v_isSharedCheck_4213_ == 0 {
                            v___x_4187_ = v_a_4174_;
                            v_isShared_4188_ = v_isSharedCheck_4213_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_4185_);
                            lean_dec(v_a_4174_);
                            v___x_4187_ = lean_box(0);
                            v_isShared_4188_ = v_isSharedCheck_4213_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_4214_ = lean_ctor_get(v___x_4173_, 0);
                    v_a_4215_ = lean_ctor_get(v___x_4173_, 1);
                    v_isSharedCheck_4222_ = (!lean_is_exclusive(v___x_4173_)) as u8;
                    if v_isSharedCheck_4222_ == 0 {
                        v___x_4217_ = v___x_4173_;
                        v_isShared_4218_ = v_isSharedCheck_4222_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4215_);
                        lean_inc(v_a_4214_);
                        lean_dec(v___x_4173_);
                        v___x_4217_ = lean_box(0);
                        v_isShared_4218_ = v_isSharedCheck_4222_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4179_ = lean_box(0);
                if v_isShared_4178_ == 0 {
                    lean_ctor_set(v___x_4177_, 0, v___x_4179_);
                    v___x_4181_ = v___x_4177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4179_);
                    lean_ctor_set(v_reuseFailAlloc_4182_, 1, v_a_4175_);
                    v___x_4181_ = v_reuseFailAlloc_4182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4181_;
            }
            3 => {
                v_snd_4189_ = lean_ctor_get(v_val_4185_, 1);
                lean_inc(v_snd_4189_);
                lean_dec(v_val_4185_);
                if lean_obj_tag(v_snd_4189_) == 0 {
                    lean_del_object(v___x_4187_);
                    v_a_4190_ = lean_ctor_get(v___x_4173_, 1);
                    lean_inc(v_a_4190_);
                    lean_dec_ref_known(v___x_4173_, 2);
                    v_a_4191_ = lean_ctor_get(v_snd_4189_, 0);
                    v_isSharedCheck_4199_ = (!lean_is_exclusive(v_snd_4189_)) as u8;
                    if v_isSharedCheck_4199_ == 0 {
                        v___x_4193_ = v_snd_4189_;
                        v_isShared_4194_ = v_isSharedCheck_4199_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4191_);
                        lean_dec(v_snd_4189_);
                        v___x_4193_ = lean_box(0);
                        v_isShared_4194_ = v_isSharedCheck_4199_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4200_ = lean_ctor_get(v___x_4173_, 1);
                    lean_inc(v_a_4200_);
                    lean_dec_ref_known(v___x_4173_, 2);
                    v_a_4201_ = lean_ctor_get(v_snd_4189_, 0);
                    v_isSharedCheck_4212_ = (!lean_is_exclusive(v_snd_4189_)) as u8;
                    if v_isSharedCheck_4212_ == 0 {
                        v___x_4203_ = v_snd_4189_;
                        v_isShared_4204_ = v_isSharedCheck_4212_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4201_);
                        lean_dec(v_snd_4189_);
                        v___x_4203_ = lean_box(0);
                        v_isShared_4204_ = v_isSharedCheck_4212_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4194_ == 0 {
                    v___x_4196_ = v___x_4193_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4191_);
                    v___x_4196_ = v_reuseFailAlloc_4198_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4197_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v___x_4196_, v_a_4190_);
                lean_dec_ref(v___x_4196_);
                return v___x_4197_;
            }
            6 => {
                if v_isShared_4188_ == 0 {
                    lean_ctor_set(v___x_4187_, 0, v_a_4201_);
                    v___x_4206_ = v___x_4187_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4201_);
                    v___x_4206_ = v_reuseFailAlloc_4211_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4204_ == 0 {
                    lean_ctor_set(v___x_4203_, 0, v___x_4206_);
                    v___x_4208_ = v___x_4203_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4210_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4206_);
                    v___x_4208_ = v_reuseFailAlloc_4210_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4209_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v___x_4208_, v_a_4200_);
                lean_dec_ref(v___x_4208_);
                return v___x_4209_;
            }
            9 => {
                if v_isShared_4218_ == 0 {
                    v___x_4220_ = v___x_4217_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4214_);
                    lean_ctor_set(v_reuseFailAlloc_4221_, 1, v_a_4215_);
                    v___x_4220_ = v_reuseFailAlloc_4221_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed(
    mut v_env_4223_: *mut LeanObject,
    mut v_stx_4224_: *mut LeanObject,
    mut v___y_4225_: *mut LeanObject,
    mut v___y_4226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4227_: *mut LeanObject = core::ptr::null_mut();
    v_res_4227_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(v_env_4223_, v_stx_4224_, v___y_4225_, v___y_4226_);
    lean_dec_ref(v___y_4225_);
    return v_res_4227_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(
    mut v_as_4228_: *mut LeanObject,
    mut v___y_4229_: *mut LeanObject,
    mut v___y_4230_: *mut LeanObject,
    mut v___y_4231_: *mut LeanObject,
    mut v___y_4232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4237_: u8 = 0;
    let mut v_tail_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: u8 = 0;
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_4228_) == 0 {
                    v___x_4234_ = lean_box(0);
                    v___x_4235_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4235_, 0, v___x_4234_);
                    return v___x_4235_;
                } else {
                    v_options_4236_ = lean_ctor_get(v___y_4231_, 2);
                    v_hasTrace_4237_ = lean_ctor_get_uint8(
                        v_options_4236_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4237_ == 0 {
                        v_tail_4238_ = lean_ctor_get(v_as_4228_, 1);
                        lean_inc(v_tail_4238_);
                        lean_dec_ref_known(v_as_4228_, 2);
                        v_as_4228_ = v_tail_4238_;
                        state = 0;
                        continue;
                    } else {
                        v_head_4240_ = lean_ctor_get(v_as_4228_, 0);
                        lean_inc(v_head_4240_);
                        v_tail_4241_ = lean_ctor_get(v_as_4228_, 1);
                        lean_inc(v_tail_4241_);
                        lean_dec_ref_known(v_as_4228_, 2);
                        v_fst_4242_ = lean_ctor_get(v_head_4240_, 0);
                        lean_inc_n(v_fst_4242_, 2);
                        v_snd_4243_ = lean_ctor_get(v_head_4240_, 1);
                        lean_inc(v_snd_4243_);
                        lean_dec(v_head_4240_);
                        v_inheritedTraceOptions_4244_ = lean_ctor_get(v___y_4231_, 13);
                        v___x_4245_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17;
                        v___x_4246_ = l_Lean_Name_append(v___x_4245_, v_fst_4242_);
                        v___x_4247_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4244_,
                            v_options_4236_,
                            v___x_4246_,
                        );
                        lean_dec(v___x_4246_);
                        if v___x_4247_ == 0 {
                            lean_dec(v_snd_4243_);
                            lean_dec(v_fst_4242_);
                            v_as_4228_ = v_tail_4241_;
                            state = 0;
                            continue;
                        } else {
                            v___x_4249_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_4249_, 0, v_snd_4243_);
                            v___x_4250_ = l_Lean_MessageData_ofFormat(v___x_4249_);
                            v___x_4251_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_fst_4242_, v___x_4250_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
                            if lean_obj_tag(v___x_4251_) == 0 {
                                lean_dec_ref_known(v___x_4251_, 1);
                                v_as_4228_ = v_tail_4241_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_tail_4241_);
                                return v___x_4251_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg___boxed(
    mut v_as_4253_: *mut LeanObject,
    mut v___y_4254_: *mut LeanObject,
    mut v___y_4255_: *mut LeanObject,
    mut v___y_4256_: *mut LeanObject,
    mut v___y_4257_: *mut LeanObject,
    mut v___y_4258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4259_: *mut LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v_as_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
    lean_dec(v___y_4257_);
    lean_dec_ref(v___y_4256_);
    lean_dec(v___y_4255_);
    lean_dec_ref(v___y_4254_);
    return v_res_4259_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(
    mut v_env_4260_: *mut LeanObject,
    mut v_declName_4261_: *mut LeanObject,
    mut v___y_4262_: *mut LeanObject,
    mut v___y_4263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4264_: u8 = 0;
    let mut v_env_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: u8 = 0;
    let mut v___x_4268_: u8 = 0;
    v___x_4264_ = 0;
    v_env_4265_ = l_Lean_Environment_setExporting(v_env_4260_, v___x_4264_);
    lean_inc(v_declName_4261_);
    v___x_4266_ = l_Lean_mkPrivateName(v_env_4265_, v_declName_4261_);
    v___x_4267_ = 1;
    lean_inc_ref(v_env_4265_);
    v___x_4268_ = l_Lean_Environment_contains(v_env_4265_, v___x_4266_, v___x_4267_);
    if v___x_4268_ == 0 {
        let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4270_: u8 = 0;
        let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
        v___x_4269_ = l_Lean_privateToUserName(v_declName_4261_);
        v___x_4270_ = l_Lean_Environment_contains(v_env_4265_, v___x_4269_, v___x_4267_);
        v___x_4271_ = lean_box((v___x_4270_) as usize);
        v___x_4272_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4272_, 0, v___x_4271_);
        lean_ctor_set(v___x_4272_, 1, v___y_4263_);
        return v___x_4272_;
    } else {
        let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_env_4265_);
        lean_dec(v_declName_4261_);
        v___x_4273_ = lean_box((v___x_4268_) as usize);
        v___x_4274_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4274_, 0, v___x_4273_);
        lean_ctor_set(v___x_4274_, 1, v___y_4263_);
        return v___x_4274_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed(
    mut v_env_4275_: *mut LeanObject,
    mut v_declName_4276_: *mut LeanObject,
    mut v___y_4277_: *mut LeanObject,
    mut v___y_4278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4279_: *mut LeanObject = core::ptr::null_mut();
    v_res_4279_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(v_env_4275_, v_declName_4276_, v___y_4277_, v___y_4278_);
    lean_dec_ref(v___y_4277_);
    return v_res_4279_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(
    mut v_env_4280_: *mut LeanObject,
    mut v_currNamespace_4281_: *mut LeanObject,
    mut v_openDecls_4282_: *mut LeanObject,
    mut v_n_4283_: *mut LeanObject,
    mut v___y_4284_: *mut LeanObject,
    mut v___y_4285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    v___x_4286_ = l_Lean_ResolveName_resolveNamespace(
        v_env_4280_,
        v_currNamespace_4281_,
        v_openDecls_4282_,
        v_n_4283_,
    );
    v___x_4287_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4287_, 0, v___x_4286_);
    lean_ctor_set(v___x_4287_, 1, v___y_4285_);
    return v___x_4287_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed(
    mut v_env_4288_: *mut LeanObject,
    mut v_currNamespace_4289_: *mut LeanObject,
    mut v_openDecls_4290_: *mut LeanObject,
    mut v_n_4291_: *mut LeanObject,
    mut v___y_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4294_: *mut LeanObject = core::ptr::null_mut();
    v_res_4294_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(v_env_4288_, v_currNamespace_4289_, v_openDecls_4290_, v_n_4291_, v___y_4292_, v___y_4293_);
    lean_dec_ref(v___y_4292_);
    return v_res_4294_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(
    mut v_x_4296_: *mut LeanObject,
    mut v___y_4297_: *mut LeanObject,
    mut v___y_4298_: *mut LeanObject,
    mut v___y_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
    mut v___y_4301_: *mut LeanObject,
    mut v___y_4302_: *mut LeanObject,
    mut v___y_4303_: *mut LeanObject,
    mut v___y_4304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroScope_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4354_: u8 = 0;
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4358_: u8 = 0;
    let mut v_unused_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4363_: u8 = 0;
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4367_: u8 = 0;
    let mut v_reuseFailAlloc_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4369_: u8 = 0;
    let mut v_unused_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4378_: u8 = 0;
    let mut v_a_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: u8 = 0;
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4306_ = lean_st_ref_get(v___y_4304_);
                v_env_4307_ = lean_ctor_get(v___x_4306_, 0);
                lean_inc_ref_n(v_env_4307_, 4);
                lean_dec(v___x_4306_);
                v_options_4308_ = lean_ctor_get(v___y_4303_, 2);
                v_currRecDepth_4309_ = lean_ctor_get(v___y_4303_, 3);
                v_maxRecDepth_4310_ = lean_ctor_get(v___y_4303_, 4);
                v_ref_4311_ = lean_ctor_get(v___y_4303_, 5);
                v_currNamespace_4312_ = lean_ctor_get(v___y_4303_, 6);
                v_openDecls_4313_ = lean_ctor_get(v___y_4303_, 7);
                v_quotContext_4314_ = lean_ctor_get(v___y_4303_, 10);
                v_currMacroScope_4315_ = lean_ctor_get(v___y_4303_, 11);
                v___x_4316_ = lean_st_ref_get(v___y_4304_);
                v_nextMacroScope_4317_ = lean_ctor_get(v___x_4316_, 1);
                lean_inc(v_nextMacroScope_4317_);
                lean_dec(v___x_4316_);
                v___f_4318_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                lean_closure_set(v___f_4318_, 0, v_env_4307_);
                v___f_4319_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                lean_closure_set(v___f_4319_, 0, v_env_4307_);
                lean_inc_n(v_openDecls_4313_, 2);
                lean_inc_n(v_currNamespace_4312_, 3);
                v___f_4320_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___f_4320_, 0, v_env_4307_);
                lean_closure_set(v___f_4320_, 1, v_currNamespace_4312_);
                lean_closure_set(v___f_4320_, 2, v_openDecls_4313_);
                v___f_4321_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_4321_, 0, v_currNamespace_4312_);
                lean_inc_ref(v_options_4308_);
                v___f_4322_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                lean_closure_set(v___f_4322_, 0, v_env_4307_);
                lean_closure_set(v___f_4322_, 1, v_options_4308_);
                lean_closure_set(v___f_4322_, 2, v_currNamespace_4312_);
                lean_closure_set(v___f_4322_, 3, v_openDecls_4313_);
                v_methods_4323_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v_methods_4323_, 0, v___f_4318_);
                lean_ctor_set(v_methods_4323_, 1, v___f_4321_);
                lean_ctor_set(v_methods_4323_, 2, v___f_4319_);
                lean_ctor_set(v_methods_4323_, 3, v___f_4320_);
                lean_ctor_set(v_methods_4323_, 4, v___f_4322_);
                lean_inc(v_ref_4311_);
                lean_inc(v_maxRecDepth_4310_);
                lean_inc(v_currRecDepth_4309_);
                lean_inc(v_currMacroScope_4315_);
                lean_inc(v_quotContext_4314_);
                v___x_4324_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_4324_, 0, v_methods_4323_);
                lean_ctor_set(v___x_4324_, 1, v_quotContext_4314_);
                lean_ctor_set(v___x_4324_, 2, v_currMacroScope_4315_);
                lean_ctor_set(v___x_4324_, 3, v_currRecDepth_4309_);
                lean_ctor_set(v___x_4324_, 4, v_maxRecDepth_4310_);
                lean_ctor_set(v___x_4324_, 5, v_ref_4311_);
                v___x_4325_ = lean_box(0);
                v___x_4326_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4326_, 0, v_nextMacroScope_4317_);
                lean_ctor_set(v___x_4326_, 1, v___x_4325_);
                lean_ctor_set(v___x_4326_, 2, v___x_4325_);
                v___x_4327_ = lean_apply_2(v_x_4296_, v___x_4324_, v___x_4326_);
                if lean_obj_tag(v___x_4327_) == 0 {
                    v_a_4328_ = lean_ctor_get(v___x_4327_, 1);
                    lean_inc(v_a_4328_);
                    v_a_4329_ = lean_ctor_get(v___x_4327_, 0);
                    lean_inc(v_a_4329_);
                    lean_dec_ref_known(v___x_4327_, 2);
                    v_macroScope_4330_ = lean_ctor_get(v_a_4328_, 0);
                    lean_inc(v_macroScope_4330_);
                    v_traceMsgs_4331_ = lean_ctor_get(v_a_4328_, 1);
                    lean_inc(v_traceMsgs_4331_);
                    v_expandedMacroDecls_4332_ = lean_ctor_get(v_a_4328_, 2);
                    lean_inc(v_expandedMacroDecls_4332_);
                    lean_dec(v_a_4328_);
                    v___x_4333_ = lean_box(0);
                    v___x_4334_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_expandedMacroDecls_4332_, v___x_4333_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
                    lean_dec(v_expandedMacroDecls_4332_);
                    if lean_obj_tag(v___x_4334_) == 0 {
                        lean_dec_ref_known(v___x_4334_, 1);
                        v___x_4335_ = lean_st_ref_take(v___y_4304_);
                        v_env_4336_ = lean_ctor_get(v___x_4335_, 0);
                        v_ngen_4337_ = lean_ctor_get(v___x_4335_, 2);
                        v_auxDeclNGen_4338_ = lean_ctor_get(v___x_4335_, 3);
                        v_traceState_4339_ = lean_ctor_get(v___x_4335_, 4);
                        v_cache_4340_ = lean_ctor_get(v___x_4335_, 5);
                        v_messages_4341_ = lean_ctor_get(v___x_4335_, 6);
                        v_infoState_4342_ = lean_ctor_get(v___x_4335_, 7);
                        v_snapshotTasks_4343_ = lean_ctor_get(v___x_4335_, 8);
                        v_isSharedCheck_4369_ = (!lean_is_exclusive(v___x_4335_)) as u8;
                        if v_isSharedCheck_4369_ == 0 {
                            v_unused_4370_ = lean_ctor_get(v___x_4335_, 1);
                            lean_dec(v_unused_4370_);
                            v___x_4345_ = v___x_4335_;
                            v_isShared_4346_ = v_isSharedCheck_4369_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_4343_);
                            lean_inc(v_infoState_4342_);
                            lean_inc(v_messages_4341_);
                            lean_inc(v_cache_4340_);
                            lean_inc(v_traceState_4339_);
                            lean_inc(v_auxDeclNGen_4338_);
                            lean_inc(v_ngen_4337_);
                            lean_inc(v_env_4336_);
                            lean_dec(v___x_4335_);
                            v___x_4345_ = lean_box(0);
                            v_isShared_4346_ = v_isSharedCheck_4369_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_traceMsgs_4331_);
                        lean_dec(v_macroScope_4330_);
                        lean_dec(v_a_4329_);
                        v_a_4371_ = lean_ctor_get(v___x_4334_, 0);
                        v_isSharedCheck_4378_ = (!lean_is_exclusive(v___x_4334_)) as u8;
                        if v_isSharedCheck_4378_ == 0 {
                            v___x_4373_ = v___x_4334_;
                            v_isShared_4374_ = v_isSharedCheck_4378_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_4371_);
                            lean_dec(v___x_4334_);
                            v___x_4373_ = lean_box(0);
                            v_isShared_4374_ = v_isSharedCheck_4378_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_4379_ = lean_ctor_get(v___x_4327_, 0);
                    lean_inc(v_a_4379_);
                    lean_dec_ref_known(v___x_4327_, 2);
                    if lean_obj_tag(v_a_4379_) == 0 {
                        v_a_4380_ = lean_ctor_get(v_a_4379_, 0);
                        lean_inc(v_a_4380_);
                        v_a_4381_ = lean_ctor_get(v_a_4379_, 1);
                        lean_inc_ref(v_a_4381_);
                        lean_dec_ref_known(v_a_4379_, 2);
                        v___x_4382_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0;
                        v___x_4383_ = lean_string_dec_eq(v_a_4381_, v___x_4382_);
                        if v___x_4383_ == 0 {
                            v___x_4384_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_4384_, 0, v_a_4381_);
                            v___x_4385_ = l_Lean_MessageData_ofFormat(v___x_4384_);
                            v___x_4386_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_a_4380_, v___x_4385_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
                            lean_dec(v_a_4380_);
                            return v___x_4386_;
                        } else {
                            lean_dec_ref(v_a_4381_);
                            v___x_4387_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_a_4380_);
                            return v___x_4387_;
                        }
                    } else {
                        v___x_4388_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
                        return v___x_4388_;
                    }
                }
            }
            1 => {
                if v_isShared_4346_ == 0 {
                    lean_ctor_set(v___x_4345_, 1, v_macroScope_4330_);
                    v___x_4348_ = v___x_4345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_env_4336_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 1, v_macroScope_4330_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 2, v_ngen_4337_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 3, v_auxDeclNGen_4338_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 4, v_traceState_4339_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 5, v_cache_4340_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 6, v_messages_4341_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 7, v_infoState_4342_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 8, v_snapshotTasks_4343_);
                    v___x_4348_ = v_reuseFailAlloc_4368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4349_ = lean_st_ref_set(v___y_4304_, v___x_4348_);
                v___x_4350_ = l_List_reverse___redArg(v_traceMsgs_4331_);
                v___x_4351_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v___x_4350_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
                if lean_obj_tag(v___x_4351_) == 0 {
                    v_isSharedCheck_4358_ = (!lean_is_exclusive(v___x_4351_)) as u8;
                    if v_isSharedCheck_4358_ == 0 {
                        v_unused_4359_ = lean_ctor_get(v___x_4351_, 0);
                        lean_dec(v_unused_4359_);
                        v___x_4353_ = v___x_4351_;
                        v_isShared_4354_ = v_isSharedCheck_4358_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_4351_);
                        v___x_4353_ = lean_box(0);
                        v_isShared_4354_ = v_isSharedCheck_4358_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4329_);
                    v_a_4360_ = lean_ctor_get(v___x_4351_, 0);
                    v_isSharedCheck_4367_ = (!lean_is_exclusive(v___x_4351_)) as u8;
                    if v_isSharedCheck_4367_ == 0 {
                        v___x_4362_ = v___x_4351_;
                        v_isShared_4363_ = v_isSharedCheck_4367_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4360_);
                        lean_dec(v___x_4351_);
                        v___x_4362_ = lean_box(0);
                        v_isShared_4363_ = v_isSharedCheck_4367_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4354_ == 0 {
                    lean_ctor_set(v___x_4353_, 0, v_a_4329_);
                    v___x_4356_ = v___x_4353_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4329_);
                    v___x_4356_ = v_reuseFailAlloc_4357_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4356_;
            }
            5 => {
                if v_isShared_4363_ == 0 {
                    v___x_4365_ = v___x_4362_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
                    v___x_4365_ = v_reuseFailAlloc_4366_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4365_;
            }
            7 => {
                if v_isShared_4374_ == 0 {
                    v___x_4376_ = v___x_4373_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
                    v___x_4376_ = v_reuseFailAlloc_4377_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___boxed(
    mut v_x_4389_: *mut LeanObject,
    mut v___y_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4399_: *mut LeanObject = core::ptr::null_mut();
    v_res_4399_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(
            v_x_4389_,
            v___y_4390_,
            v___y_4391_,
            v___y_4392_,
            v___y_4393_,
            v___y_4394_,
            v___y_4395_,
            v___y_4396_,
            v___y_4397_,
        );
    lean_dec(v___y_4397_);
    lean_dec_ref(v___y_4396_);
    lean_dec(v___y_4395_);
    lean_dec_ref(v___y_4394_);
    lean_dec(v___y_4393_);
    lean_dec_ref(v___y_4392_);
    lean_dec(v___y_4391_);
    lean_dec_ref(v___y_4390_);
    return v_res_4399_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(
    mut v_x_4410_: *mut LeanObject,
    mut v_a_4411_: *mut LeanObject,
    mut v_a_4412_: *mut LeanObject,
    mut v_a_4413_: *mut LeanObject,
    mut v_a_4414_: *mut LeanObject,
    mut v_a_4415_: *mut LeanObject,
    mut v_a_4416_: *mut LeanObject,
    mut v_a_4417_: *mut LeanObject,
    mut v_a_4418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pat_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4438_: u8 = 0;
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4442_: u8 = 0;
    let mut v_a_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4420_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
                lean_inc(v_x_4410_);
                v___x_4421_ = l_Lean_Syntax_isOfKind(v_x_4410_, v___x_4420_);
                if v___x_4421_ == 0 {
                    lean_dec(v_x_4410_);
                    v___x_4422_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
                    return v___x_4422_;
                } else {
                    v___x_4423_ = lean_unsigned_to_nat(1);
                    v_pat_4424_ = l_Lean_Syntax_getArg(v_x_4410_, v___x_4423_);
                    lean_dec(v_x_4410_);
                    v___x_4425_ = lean_alloc_closure(
                        l_Lean_Parser_Tactic_MRefinePat_parse___boxed as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___x_4425_, 0, v_pat_4424_);
                    v___x_4426_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(v___x_4425_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
                    if lean_obj_tag(v___x_4426_) == 0 {
                        v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
                        lean_inc(v_a_4427_);
                        lean_dec_ref_known(v___x_4426_, 1);
                        v___x_4428_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                            v_a_4412_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_,
                        );
                        if lean_obj_tag(v___x_4428_) == 0 {
                            v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
                            lean_inc(v_a_4429_);
                            lean_dec_ref_known(v___x_4428_, 1);
                            v_fst_4430_ = lean_ctor_get(v_a_4429_, 0);
                            lean_inc_n(v_fst_4430_, 2);
                            v_snd_4431_ = lean_ctor_get(v_a_4429_, 1);
                            lean_inc(v_snd_4431_);
                            lean_dec(v_a_4429_);
                            v___x_4432_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4;
                            v___f_4433_ = lean_alloc_closure(
                                l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                13,
                                4,
                            );
                            lean_closure_set(v___f_4433_, 0, v___x_4432_);
                            lean_closure_set(v___f_4433_, 1, v_snd_4431_);
                            lean_closure_set(v___f_4433_, 2, v_a_4427_);
                            lean_closure_set(v___f_4433_, 3, v_fst_4430_);
                            v___x_4434_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_fst_4430_, v___f_4433_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
                            return v___x_4434_;
                        } else {
                            lean_dec(v_a_4427_);
                            v_a_4435_ = lean_ctor_get(v___x_4428_, 0);
                            v_isSharedCheck_4442_ = (!lean_is_exclusive(v___x_4428_)) as u8;
                            if v_isSharedCheck_4442_ == 0 {
                                v___x_4437_ = v___x_4428_;
                                v_isShared_4438_ = v_isSharedCheck_4442_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_4435_);
                                lean_dec(v___x_4428_);
                                v___x_4437_ = lean_box(0);
                                v_isShared_4438_ = v_isSharedCheck_4442_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_4443_ = lean_ctor_get(v___x_4426_, 0);
                        v_isSharedCheck_4450_ = (!lean_is_exclusive(v___x_4426_)) as u8;
                        if v_isSharedCheck_4450_ == 0 {
                            v___x_4445_ = v___x_4426_;
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4443_);
                            lean_dec(v___x_4426_);
                            v___x_4445_ = lean_box(0);
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4438_ == 0 {
                    v___x_4440_ = v___x_4437_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
                    v___x_4440_ = v_reuseFailAlloc_4441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4440_;
            }
            3 => {
                if v_isShared_4446_ == 0 {
                    v___x_4448_ = v___x_4445_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
                    v___x_4448_ = v_reuseFailAlloc_4449_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___boxed(
    mut v_x_4451_: *mut LeanObject,
    mut v_a_4452_: *mut LeanObject,
    mut v_a_4453_: *mut LeanObject,
    mut v_a_4454_: *mut LeanObject,
    mut v_a_4455_: *mut LeanObject,
    mut v_a_4456_: *mut LeanObject,
    mut v_a_4457_: *mut LeanObject,
    mut v_a_4458_: *mut LeanObject,
    mut v_a_4459_: *mut LeanObject,
    mut v_a_4460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4461_: *mut LeanObject = core::ptr::null_mut();
    v_res_4461_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(
        v_x_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_,
        v_a_4459_,
    );
    lean_dec(v_a_4459_);
    lean_dec_ref(v_a_4458_);
    lean_dec(v_a_4457_);
    lean_dec_ref(v_a_4456_);
    lean_dec(v_a_4455_);
    lean_dec_ref(v_a_4454_);
    lean_dec(v_a_4453_);
    lean_dec_ref(v_a_4452_);
    return v_res_4461_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0(
    mut v_00_u03b1_4462_: *mut LeanObject,
    mut v_x_4463_: *mut LeanObject,
    mut v___y_4464_: *mut LeanObject,
    mut v___y_4465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    v___x_4466_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v_x_4463_, v___y_4465_);
    return v___x_4466_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___boxed(
    mut v_00_u03b1_4467_: *mut LeanObject,
    mut v_x_4468_: *mut LeanObject,
    mut v___y_4469_: *mut LeanObject,
    mut v___y_4470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4471_: *mut LeanObject = core::ptr::null_mut();
    v_res_4471_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0(v_00_u03b1_4467_, v_x_4468_, v___y_4469_, v___y_4470_);
    lean_dec_ref(v___y_4469_);
    lean_dec_ref(v_x_4468_);
    return v_res_4471_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5(
    mut v_00_u03b1_4472_: *mut LeanObject,
    mut v_ref_4473_: *mut LeanObject,
    mut v___y_4474_: *mut LeanObject,
    mut v___y_4475_: *mut LeanObject,
    mut v___y_4476_: *mut LeanObject,
    mut v___y_4477_: *mut LeanObject,
    mut v___y_4478_: *mut LeanObject,
    mut v___y_4479_: *mut LeanObject,
    mut v___y_4480_: *mut LeanObject,
    mut v___y_4481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    v___x_4483_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_ref_4473_);
    return v___x_4483_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___boxed(
    mut v_00_u03b1_4484_: *mut LeanObject,
    mut v_ref_4485_: *mut LeanObject,
    mut v___y_4486_: *mut LeanObject,
    mut v___y_4487_: *mut LeanObject,
    mut v___y_4488_: *mut LeanObject,
    mut v___y_4489_: *mut LeanObject,
    mut v___y_4490_: *mut LeanObject,
    mut v___y_4491_: *mut LeanObject,
    mut v___y_4492_: *mut LeanObject,
    mut v___y_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4495_: *mut LeanObject = core::ptr::null_mut();
    v_res_4495_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5(v_00_u03b1_4484_, v_ref_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
    lean_dec(v___y_4493_);
    lean_dec_ref(v___y_4492_);
    lean_dec(v___y_4491_);
    lean_dec_ref(v___y_4490_);
    lean_dec(v___y_4489_);
    lean_dec_ref(v___y_4488_);
    lean_dec(v___y_4487_);
    lean_dec_ref(v___y_4486_);
    return v_res_4495_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0(
    mut v_00_u03b1_4496_: *mut LeanObject,
    mut v_x_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
    mut v___y_4499_: *mut LeanObject,
    mut v___y_4500_: *mut LeanObject,
    mut v___y_4501_: *mut LeanObject,
    mut v___y_4502_: *mut LeanObject,
    mut v___y_4503_: *mut LeanObject,
    mut v___y_4504_: *mut LeanObject,
    mut v___y_4505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    v___x_4507_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(
            v_x_4497_,
            v___y_4498_,
            v___y_4499_,
            v___y_4500_,
            v___y_4501_,
            v___y_4502_,
            v___y_4503_,
            v___y_4504_,
            v___y_4505_,
        );
    return v___x_4507_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___boxed(
    mut v_00_u03b1_4508_: *mut LeanObject,
    mut v_x_4509_: *mut LeanObject,
    mut v___y_4510_: *mut LeanObject,
    mut v___y_4511_: *mut LeanObject,
    mut v___y_4512_: *mut LeanObject,
    mut v___y_4513_: *mut LeanObject,
    mut v___y_4514_: *mut LeanObject,
    mut v___y_4515_: *mut LeanObject,
    mut v___y_4516_: *mut LeanObject,
    mut v___y_4517_: *mut LeanObject,
    mut v___y_4518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4519_: *mut LeanObject = core::ptr::null_mut();
    v_res_4519_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0(
        v_00_u03b1_4508_,
        v_x_4509_,
        v___y_4510_,
        v___y_4511_,
        v___y_4512_,
        v___y_4513_,
        v___y_4514_,
        v___y_4515_,
        v___y_4516_,
        v___y_4517_,
    );
    lean_dec(v___y_4517_);
    lean_dec_ref(v___y_4516_);
    lean_dec(v___y_4515_);
    lean_dec_ref(v___y_4514_);
    lean_dec(v___y_4513_);
    lean_dec_ref(v___y_4512_);
    lean_dec(v___y_4511_);
    lean_dec_ref(v___y_4510_);
    return v_res_4519_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1(
    mut v_mvarId_4520_: *mut LeanObject,
    mut v_val_4521_: *mut LeanObject,
    mut v___y_4522_: *mut LeanObject,
    mut v___y_4523_: *mut LeanObject,
    mut v___y_4524_: *mut LeanObject,
    mut v___y_4525_: *mut LeanObject,
    mut v___y_4526_: *mut LeanObject,
    mut v___y_4527_: *mut LeanObject,
    mut v___y_4528_: *mut LeanObject,
    mut v___y_4529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    v___x_4531_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(
            v_mvarId_4520_,
            v_val_4521_,
            v___y_4527_,
        );
    return v___x_4531_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___boxed(
    mut v_mvarId_4532_: *mut LeanObject,
    mut v_val_4533_: *mut LeanObject,
    mut v___y_4534_: *mut LeanObject,
    mut v___y_4535_: *mut LeanObject,
    mut v___y_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
    mut v___y_4538_: *mut LeanObject,
    mut v___y_4539_: *mut LeanObject,
    mut v___y_4540_: *mut LeanObject,
    mut v___y_4541_: *mut LeanObject,
    mut v___y_4542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4543_: *mut LeanObject = core::ptr::null_mut();
    v_res_4543_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1(
        v_mvarId_4532_,
        v_val_4533_,
        v___y_4534_,
        v___y_4535_,
        v___y_4536_,
        v___y_4537_,
        v___y_4538_,
        v___y_4539_,
        v___y_4540_,
        v___y_4541_,
    );
    lean_dec(v___y_4541_);
    lean_dec_ref(v___y_4540_);
    lean_dec(v___y_4539_);
    lean_dec_ref(v___y_4538_);
    lean_dec(v___y_4537_);
    lean_dec_ref(v___y_4536_);
    lean_dec(v___y_4535_);
    lean_dec_ref(v___y_4534_);
    return v_res_4543_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2(
    mut v_as_4544_: *mut LeanObject,
    mut v_as_x27_4545_: *mut LeanObject,
    mut v_b_4546_: *mut LeanObject,
    mut v_a_4547_: *mut LeanObject,
    mut v___y_4548_: *mut LeanObject,
    mut v___y_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
    mut v___y_4552_: *mut LeanObject,
    mut v___y_4553_: *mut LeanObject,
    mut v___y_4554_: *mut LeanObject,
    mut v___y_4555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    v___x_4557_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_as_x27_4545_, v_b_4546_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
    return v___x_4557_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___boxed(
    mut v_as_4558_: *mut LeanObject,
    mut v_as_x27_4559_: *mut LeanObject,
    mut v_b_4560_: *mut LeanObject,
    mut v_a_4561_: *mut LeanObject,
    mut v___y_4562_: *mut LeanObject,
    mut v___y_4563_: *mut LeanObject,
    mut v___y_4564_: *mut LeanObject,
    mut v___y_4565_: *mut LeanObject,
    mut v___y_4566_: *mut LeanObject,
    mut v___y_4567_: *mut LeanObject,
    mut v___y_4568_: *mut LeanObject,
    mut v___y_4569_: *mut LeanObject,
    mut v___y_4570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4571_: *mut LeanObject = core::ptr::null_mut();
    v_res_4571_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2(v_as_4558_, v_as_x27_4559_, v_b_4560_, v_a_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
    lean_dec(v___y_4569_);
    lean_dec_ref(v___y_4568_);
    lean_dec(v___y_4567_);
    lean_dec_ref(v___y_4566_);
    lean_dec(v___y_4565_);
    lean_dec_ref(v___y_4564_);
    lean_dec(v___y_4563_);
    lean_dec_ref(v___y_4562_);
    lean_dec(v_as_x27_4559_);
    lean_dec(v_as_4558_);
    return v_res_4571_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3(
    mut v_as_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
    mut v___y_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
    mut v___y_4576_: *mut LeanObject,
    mut v___y_4577_: *mut LeanObject,
    mut v___y_4578_: *mut LeanObject,
    mut v___y_4579_: *mut LeanObject,
    mut v___y_4580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    v___x_4582_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v_as_4572_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
    return v___x_4582_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___boxed(
    mut v_as_4583_: *mut LeanObject,
    mut v___y_4584_: *mut LeanObject,
    mut v___y_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
    mut v___y_4588_: *mut LeanObject,
    mut v___y_4589_: *mut LeanObject,
    mut v___y_4590_: *mut LeanObject,
    mut v___y_4591_: *mut LeanObject,
    mut v___y_4592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4593_: *mut LeanObject = core::ptr::null_mut();
    v_res_4593_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3(v_as_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
    lean_dec(v___y_4591_);
    lean_dec_ref(v___y_4590_);
    lean_dec(v___y_4589_);
    lean_dec_ref(v___y_4588_);
    lean_dec(v___y_4587_);
    lean_dec_ref(v___y_4586_);
    lean_dec(v___y_4585_);
    lean_dec_ref(v___y_4584_);
    return v_res_4593_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4(
    mut v_00_u03b1_4594_: *mut LeanObject,
    mut v_ref_4595_: *mut LeanObject,
    mut v_msg_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
    mut v___y_4600_: *mut LeanObject,
    mut v___y_4601_: *mut LeanObject,
    mut v___y_4602_: *mut LeanObject,
    mut v___y_4603_: *mut LeanObject,
    mut v___y_4604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    v___x_4606_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_ref_4595_, v_msg_4596_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
    return v___x_4606_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___boxed(
    mut v_00_u03b1_4607_: *mut LeanObject,
    mut v_ref_4608_: *mut LeanObject,
    mut v_msg_4609_: *mut LeanObject,
    mut v___y_4610_: *mut LeanObject,
    mut v___y_4611_: *mut LeanObject,
    mut v___y_4612_: *mut LeanObject,
    mut v___y_4613_: *mut LeanObject,
    mut v___y_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
    mut v___y_4616_: *mut LeanObject,
    mut v___y_4617_: *mut LeanObject,
    mut v___y_4618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4619_: *mut LeanObject = core::ptr::null_mut();
    v_res_4619_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4(v_00_u03b1_4607_, v_ref_4608_, v_msg_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
    lean_dec(v___y_4617_);
    lean_dec_ref(v___y_4616_);
    lean_dec(v___y_4615_);
    lean_dec_ref(v___y_4614_);
    lean_dec(v___y_4613_);
    lean_dec_ref(v___y_4612_);
    lean_dec(v___y_4611_);
    lean_dec_ref(v___y_4610_);
    lean_dec(v_ref_4608_);
    return v_res_4619_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7(
    mut v_00_u03b2_4620_: *mut LeanObject,
    mut v_x_4621_: *mut LeanObject,
    mut v_x_4622_: *mut LeanObject,
    mut v_x_4623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    v___x_4624_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(v_x_4621_, v_x_4622_, v_x_4623_);
    return v___x_4624_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3(
    mut v_mod_4625_: *mut LeanObject,
    mut v_isMeta_4626_: u8,
    mut v_hint_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
    mut v___y_4629_: *mut LeanObject,
    mut v___y_4630_: *mut LeanObject,
    mut v___y_4631_: *mut LeanObject,
    mut v___y_4632_: *mut LeanObject,
    mut v___y_4633_: *mut LeanObject,
    mut v___y_4634_: *mut LeanObject,
    mut v___y_4635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    v___x_4637_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_mod_4625_, v_isMeta_4626_, v_hint_4627_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
    return v___x_4637_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___boxed(
    mut v_mod_4638_: *mut LeanObject,
    mut v_isMeta_4639_: *mut LeanObject,
    mut v_hint_4640_: *mut LeanObject,
    mut v___y_4641_: *mut LeanObject,
    mut v___y_4642_: *mut LeanObject,
    mut v___y_4643_: *mut LeanObject,
    mut v___y_4644_: *mut LeanObject,
    mut v___y_4645_: *mut LeanObject,
    mut v___y_4646_: *mut LeanObject,
    mut v___y_4647_: *mut LeanObject,
    mut v___y_4648_: *mut LeanObject,
    mut v___y_4649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_4650_: u8 = 0;
    let mut v_res_4651_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4650_ = (lean_unbox(v_isMeta_4639_) as u8);
    v_res_4651_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3(v_mod_4638_, v_isMeta_boxed_4650_, v_hint_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
    lean_dec(v___y_4648_);
    lean_dec_ref(v___y_4647_);
    lean_dec(v___y_4646_);
    lean_dec_ref(v___y_4645_);
    lean_dec(v___y_4644_);
    lean_dec_ref(v___y_4643_);
    lean_dec(v___y_4642_);
    lean_dec_ref(v___y_4641_);
    return v_res_4651_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5(
    mut v_00_u03b2_4652_: *mut LeanObject,
    mut v_m_4653_: *mut LeanObject,
    mut v_a_4654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    v___x_4655_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v_m_4653_, v_a_4654_);
    return v___x_4655_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b2_4656_: *mut LeanObject,
    mut v_m_4657_: *mut LeanObject,
    mut v_a_4658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4659_: *mut LeanObject = core::ptr::null_mut();
    v_res_4659_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5(v_00_u03b2_4656_, v_m_4657_, v_a_4658_);
    lean_dec(v_a_4658_);
    lean_dec_ref(v_m_4657_);
    return v_res_4659_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12(
    mut v_00_u03b2_4660_: *mut LeanObject,
    mut v_x_4661_: *mut LeanObject,
    mut v_x_4662_: usize,
    mut v_x_4663_: usize,
    mut v_x_4664_: *mut LeanObject,
    mut v_x_4665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    v___x_4666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_4661_, v_x_4662_, v_x_4663_, v_x_4664_, v_x_4665_);
    return v___x_4666_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___boxed(
    mut v_00_u03b2_4667_: *mut LeanObject,
    mut v_x_4668_: *mut LeanObject,
    mut v_x_4669_: *mut LeanObject,
    mut v_x_4670_: *mut LeanObject,
    mut v_x_4671_: *mut LeanObject,
    mut v_x_4672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_19703__boxed_4673_: usize = 0;
    let mut v_x_19704__boxed_4674_: usize = 0;
    let mut v_res_4675_: *mut LeanObject = core::ptr::null_mut();
    v_x_19703__boxed_4673_ = lean_unbox_usize(v_x_4669_);
    lean_dec(v_x_4669_);
    v_x_19704__boxed_4674_ = lean_unbox_usize(v_x_4670_);
    lean_dec(v_x_4670_);
    v_res_4675_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12(v_00_u03b2_4667_, v_x_4668_, v_x_19703__boxed_4673_, v_x_19704__boxed_4674_, v_x_4671_, v_x_4672_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_4676_: *mut LeanObject,
    mut v_x_4677_: *mut LeanObject,
    mut v_x_4678_: *mut LeanObject,
) -> u8 {
    let mut v___x_4679_: u8 = 0;
    v___x_4679_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v_x_4677_, v_x_4678_);
    return v___x_4679_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_4680_: *mut LeanObject,
    mut v_x_4681_: *mut LeanObject,
    mut v_x_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4683_: u8 = 0;
    let mut v_r_4684_: *mut LeanObject = core::ptr::null_mut();
    v_res_4683_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6(v_00_u03b2_4680_, v_x_4681_, v_x_4682_);
    lean_dec_ref(v_x_4682_);
    lean_dec_ref(v_x_4681_);
    v_r_4684_ = lean_box((v_res_4683_) as usize);
    return v_r_4684_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9(
    mut v_00_u03b2_4685_: *mut LeanObject,
    mut v_a_4686_: *mut LeanObject,
    mut v_x_4687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    v___x_4688_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_4686_, v_x_4687_);
    return v___x_4688_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___boxed(
    mut v_00_u03b2_4689_: *mut LeanObject,
    mut v_a_4690_: *mut LeanObject,
    mut v_x_4691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4692_: *mut LeanObject = core::ptr::null_mut();
    v_res_4692_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9(v_00_u03b2_4689_, v_a_4690_, v_x_4691_);
    lean_dec(v_x_4691_);
    lean_dec(v_a_4690_);
    return v_res_4692_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15(
    mut v_00_u03b2_4693_: *mut LeanObject,
    mut v_n_4694_: *mut LeanObject,
    mut v_k_4695_: *mut LeanObject,
    mut v_v_4696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    v___x_4697_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(v_n_4694_, v_k_4695_, v_v_4696_);
    return v___x_4697_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16(
    mut v_00_u03b2_4698_: *mut LeanObject,
    mut v_depth_4699_: usize,
    mut v_keys_4700_: *mut LeanObject,
    mut v_vals_4701_: *mut LeanObject,
    mut v_heq_4702_: *mut LeanObject,
    mut v_i_4703_: *mut LeanObject,
    mut v_entries_4704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    v___x_4705_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_depth_4699_, v_keys_4700_, v_vals_4701_, v_i_4703_, v_entries_4704_);
    return v___x_4705_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___boxed(
    mut v_00_u03b2_4706_: *mut LeanObject,
    mut v_depth_4707_: *mut LeanObject,
    mut v_keys_4708_: *mut LeanObject,
    mut v_vals_4709_: *mut LeanObject,
    mut v_heq_4710_: *mut LeanObject,
    mut v_i_4711_: *mut LeanObject,
    mut v_entries_4712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4713_: usize = 0;
    let mut v_res_4714_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4713_ = lean_unbox_usize(v_depth_4707_);
    lean_dec(v_depth_4707_);
    v_res_4714_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16(v_00_u03b2_4706_, v_depth_boxed_4713_, v_keys_4708_, v_vals_4709_, v_heq_4710_, v_i_4711_, v_entries_4712_);
    lean_dec_ref(v_vals_4709_);
    lean_dec_ref(v_keys_4708_);
    return v_res_4714_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(
    mut v_00_u03b2_4715_: *mut LeanObject,
    mut v_x_4716_: *mut LeanObject,
    mut v_x_4717_: usize,
    mut v_x_4718_: *mut LeanObject,
) -> u8 {
    let mut v___x_4719_: u8 = 0;
    v___x_4719_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_4716_, v_x_4717_, v_x_4718_);
    return v___x_4719_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___boxed(
    mut v_00_u03b2_4720_: *mut LeanObject,
    mut v_x_4721_: *mut LeanObject,
    mut v_x_4722_: *mut LeanObject,
    mut v_x_4723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_19737__boxed_4724_: usize = 0;
    let mut v_res_4725_: u8 = 0;
    let mut v_r_4726_: *mut LeanObject = core::ptr::null_mut();
    v_x_19737__boxed_4724_ = lean_unbox_usize(v_x_4722_);
    lean_dec(v_x_4722_);
    v_res_4725_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(v_00_u03b2_4720_, v_x_4721_, v_x_19737__boxed_4724_, v_x_4723_);
    lean_dec_ref(v_x_4723_);
    lean_dec_ref(v_x_4721_);
    v_r_4726_ = lean_box((v_res_4725_) as usize);
    return v_r_4726_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17(
    mut v_00_u03b2_4727_: *mut LeanObject,
    mut v_x_4728_: *mut LeanObject,
    mut v_x_4729_: *mut LeanObject,
    mut v_x_4730_: *mut LeanObject,
    mut v_x_4731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    v___x_4732_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(v_x_4728_, v_x_4729_, v_x_4730_, v_x_4731_);
    return v___x_4732_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15(
    mut v_00_u03b2_4733_: *mut LeanObject,
    mut v_keys_4734_: *mut LeanObject,
    mut v_vals_4735_: *mut LeanObject,
    mut v_heq_4736_: *mut LeanObject,
    mut v_i_4737_: *mut LeanObject,
    mut v_k_4738_: *mut LeanObject,
) -> u8 {
    let mut v___x_4739_: u8 = 0;
    v___x_4739_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_keys_4734_, v_i_4737_, v_k_4738_);
    return v___x_4739_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___boxed(
    mut v_00_u03b2_4740_: *mut LeanObject,
    mut v_keys_4741_: *mut LeanObject,
    mut v_vals_4742_: *mut LeanObject,
    mut v_heq_4743_: *mut LeanObject,
    mut v_i_4744_: *mut LeanObject,
    mut v_k_4745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4746_: u8 = 0;
    let mut v_r_4747_: *mut LeanObject = core::ptr::null_mut();
    v_res_4746_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15(v_00_u03b2_4740_, v_keys_4741_, v_vals_4742_, v_heq_4743_, v_i_4744_, v_k_4745_);
    lean_dec_ref(v_k_4745_);
    lean_dec_ref(v_vals_4742_);
    lean_dec_ref(v_keys_4741_);
    v_r_4747_ = lean_box((v_res_4746_) as usize);
    return v_r_4747_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1()
-> *mut LeanObject {
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    v___x_4759_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4760_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
    v___x_4761_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3;
    v___x_4762_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4763_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4759_,
        v___x_4760_,
        v___x_4761_,
        v___x_4762_,
    );
    return v___x_4763_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___boxed(
    mut v_a_4764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4765_: *mut LeanObject = core::ptr::null_mut();
    v_res_4765_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1();
    return v_res_4765_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(
    mut v_as_4784_: *mut LeanObject,
    mut v_i_4785_: usize,
    mut v_stop_4786_: usize,
    mut v_b_4787_: *mut LeanObject,
    mut v___y_4788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4790_: u8 = 0;
    let mut v_ref_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: usize = 0;
    let mut v___x_4794_: usize = 0;
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4790_ = lean_usize_dec_eq(v_i_4785_, v_stop_4786_);
                if v___x_4790_ == 0 {
                    v_ref_4791_ = lean_ctor_get(v___y_4788_, 5);
                    v___x_4792_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0;
                    v___x_4793_ = 1usize;
                    v___x_4794_ = lean_usize_sub(v_i_4785_, v___x_4793_);
                    v___x_4795_ = lean_array_uget_borrowed(v_as_4784_, v___x_4794_);
                    v___x_4796_ = l_Lean_SourceInfo_fromRef(v_ref_4791_, v___x_4790_);
                    v___x_4797_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2;
                    v___x_4798_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3;
                    lean_inc_n(v___x_4796_, 5);
                    v___x_4799_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4799_, 0, v___x_4796_);
                    lean_ctor_set(v___x_4799_, 1, v___x_4798_);
                    v___x_4800_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5;
                    v___x_4801_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7;
                    v___x_4802_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4802_, 0, v___x_4796_);
                    lean_ctor_set(v___x_4802_, 1, v___x_4792_);
                    lean_inc(v___x_4795_);
                    v___x_4803_ = l_Lean_Syntax_node3(
                        v___x_4796_,
                        v___x_4801_,
                        v___x_4795_,
                        v___x_4802_,
                        v_b_4787_,
                    );
                    v___x_4804_ = l_Lean_Syntax_node1(v___x_4796_, v___x_4800_, v___x_4803_);
                    v___x_4805_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8;
                    v___x_4806_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4806_, 0, v___x_4796_);
                    lean_ctor_set(v___x_4806_, 1, v___x_4805_);
                    v___x_4807_ = l_Lean_Syntax_node3(
                        v___x_4796_,
                        v___x_4797_,
                        v___x_4799_,
                        v___x_4804_,
                        v___x_4806_,
                    );
                    v_i_4785_ = v___x_4794_;
                    v_b_4787_ = v___x_4807_;
                    state = 0;
                    continue;
                } else {
                    v___x_4809_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4809_, 0, v_b_4787_);
                    return v___x_4809_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___boxed(
    mut v_as_4810_: *mut LeanObject,
    mut v_i_4811_: *mut LeanObject,
    mut v_stop_4812_: *mut LeanObject,
    mut v_b_4813_: *mut LeanObject,
    mut v___y_4814_: *mut LeanObject,
    mut v___y_4815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4816_: usize = 0;
    let mut v_stop_boxed_4817_: usize = 0;
    let mut v_res_4818_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4816_ = lean_unbox_usize(v_i_4811_);
    lean_dec(v_i_4811_);
    v_stop_boxed_4817_ = lean_unbox_usize(v_stop_4812_);
    lean_dec(v_stop_4812_);
    v_res_4818_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_4810_, v_i_boxed_4816_, v_stop_boxed_4817_, v_b_4813_, v___y_4814_);
    lean_dec_ref(v___y_4814_);
    lean_dec_ref(v_as_4810_);
    return v_res_4818_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(
    mut v_as_4819_: *mut LeanObject,
    mut v_i_4820_: usize,
    mut v_stop_4821_: usize,
    mut v_b_4822_: *mut LeanObject,
    mut v___y_4823_: *mut LeanObject,
    mut v___y_4824_: *mut LeanObject,
    mut v___y_4825_: *mut LeanObject,
    mut v___y_4826_: *mut LeanObject,
    mut v___y_4827_: *mut LeanObject,
    mut v___y_4828_: *mut LeanObject,
    mut v___y_4829_: *mut LeanObject,
    mut v___y_4830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4832_: u8 = 0;
    v___x_4832_ = lean_usize_dec_eq(v_i_4820_, v_stop_4821_);
    if v___x_4832_ == 0 {
        let mut v_ref_4833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4835_: usize = 0;
        let mut v___x_4836_: usize = 0;
        let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4833_ = lean_ctor_get(v___y_4829_, 5);
        v___x_4834_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0;
        v___x_4835_ = 1usize;
        v___x_4836_ = lean_usize_sub(v_i_4820_, v___x_4835_);
        v___x_4837_ = lean_array_uget_borrowed(v_as_4819_, v___x_4836_);
        v___x_4838_ = l_Lean_SourceInfo_fromRef(v_ref_4833_, v___x_4832_);
        v___x_4839_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2;
        v___x_4840_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3;
        lean_inc_n(v___x_4838_, 5);
        v___x_4841_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4841_, 0, v___x_4838_);
        lean_ctor_set(v___x_4841_, 1, v___x_4840_);
        v___x_4842_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5;
        v___x_4843_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7;
        v___x_4844_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4844_, 0, v___x_4838_);
        lean_ctor_set(v___x_4844_, 1, v___x_4834_);
        lean_inc(v___x_4837_);
        v___x_4845_ = l_Lean_Syntax_node3(
            v___x_4838_,
            v___x_4843_,
            v___x_4837_,
            v___x_4844_,
            v_b_4822_,
        );
        v___x_4846_ = l_Lean_Syntax_node1(v___x_4838_, v___x_4842_, v___x_4845_);
        v___x_4847_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8;
        v___x_4848_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4848_, 0, v___x_4838_);
        lean_ctor_set(v___x_4848_, 1, v___x_4847_);
        v___x_4849_ = l_Lean_Syntax_node3(
            v___x_4838_,
            v___x_4839_,
            v___x_4841_,
            v___x_4846_,
            v___x_4848_,
        );
        v___x_4850_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_4819_, v___x_4836_, v_stop_4821_, v___x_4849_, v___y_4829_);
        return v___x_4850_;
    } else {
        let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
        v___x_4851_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4851_, 0, v_b_4822_);
        return v___x_4851_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___boxed(
    mut v_as_4852_: *mut LeanObject,
    mut v_i_4853_: *mut LeanObject,
    mut v_stop_4854_: *mut LeanObject,
    mut v_b_4855_: *mut LeanObject,
    mut v___y_4856_: *mut LeanObject,
    mut v___y_4857_: *mut LeanObject,
    mut v___y_4858_: *mut LeanObject,
    mut v___y_4859_: *mut LeanObject,
    mut v___y_4860_: *mut LeanObject,
    mut v___y_4861_: *mut LeanObject,
    mut v___y_4862_: *mut LeanObject,
    mut v___y_4863_: *mut LeanObject,
    mut v___y_4864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4865_: usize = 0;
    let mut v_stop_boxed_4866_: usize = 0;
    let mut v_res_4867_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4865_ = lean_unbox_usize(v_i_4853_);
    lean_dec(v_i_4853_);
    v_stop_boxed_4866_ = lean_unbox_usize(v_stop_4854_);
    lean_dec(v_stop_4854_);
    v_res_4867_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(v_as_4852_, v_i_boxed_4865_, v_stop_boxed_4866_, v_b_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
    lean_dec(v___y_4863_);
    lean_dec_ref(v___y_4862_);
    lean_dec(v___y_4861_);
    lean_dec_ref(v___y_4860_);
    lean_dec(v___y_4859_);
    lean_dec_ref(v___y_4858_);
    lean_dec(v___y_4857_);
    lean_dec_ref(v___y_4856_);
    lean_dec_ref(v_as_4852_);
    return v_res_4867_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(
    mut v_sz_4876_: usize,
    mut v_i_4877_: usize,
    mut v_bs_4878_: *mut LeanObject,
    mut v___y_4879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4881_: u8 = 0;
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: u8 = 0;
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: usize = 0;
    let mut v___x_4896_: usize = 0;
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4881_ = lean_usize_dec_lt(v_i_4877_, v_sz_4876_);
                if v___x_4881_ == 0 {
                    v___x_4882_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4882_, 0, v_bs_4878_);
                    return v___x_4882_;
                } else {
                    v_ref_4883_ = lean_ctor_get(v___y_4879_, 5);
                    v_v_4884_ = lean_array_uget(v_bs_4878_, v_i_4877_);
                    v___x_4885_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4886_ = lean_array_uset(v_bs_4878_, v_i_4877_, v___x_4885_);
                    v___x_4887_ = 0;
                    v___x_4888_ = l_Lean_SourceInfo_fromRef(v_ref_4883_, v___x_4887_);
                    v___x_4889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1;
                    v___x_4890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2;
                    lean_inc_n(v___x_4888_, 2);
                    v___x_4891_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4891_, 0, v___x_4888_);
                    lean_ctor_set(v___x_4891_, 1, v___x_4890_);
                    v___x_4892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3;
                    v___x_4893_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4893_, 0, v___x_4888_);
                    lean_ctor_set(v___x_4893_, 1, v___x_4892_);
                    v___x_4894_ = l_Lean_Syntax_node3(
                        v___x_4888_,
                        v___x_4889_,
                        v___x_4891_,
                        v_v_4884_,
                        v___x_4893_,
                    );
                    v___x_4895_ = 1usize;
                    v___x_4896_ = lean_usize_add(v_i_4877_, v___x_4895_);
                    v___x_4897_ = lean_array_uset(v_bs_x27_4886_, v_i_4877_, v___x_4894_);
                    v_i_4877_ = v___x_4896_;
                    v_bs_4878_ = v___x_4897_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___boxed(
    mut v_sz_4899_: *mut LeanObject,
    mut v_i_4900_: *mut LeanObject,
    mut v_bs_4901_: *mut LeanObject,
    mut v___y_4902_: *mut LeanObject,
    mut v___y_4903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4904_: usize = 0;
    let mut v_i_boxed_4905_: usize = 0;
    let mut v_res_4906_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4904_ = lean_unbox_usize(v_sz_4899_);
    lean_dec(v_sz_4899_);
    v_i_boxed_4905_ = lean_unbox_usize(v_i_4900_);
    lean_dec(v_i_4900_);
    v_res_4906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_boxed_4904_, v_i_boxed_4905_, v_bs_4901_, v___y_4902_);
    lean_dec_ref(v___y_4902_);
    return v_res_4906_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(
    mut v_x_4962_: *mut LeanObject,
    mut v_a_4963_: *mut LeanObject,
    mut v_a_4964_: *mut LeanObject,
    mut v_a_4965_: *mut LeanObject,
    mut v_a_4966_: *mut LeanObject,
    mut v_a_4967_: *mut LeanObject,
    mut v_a_4968_: *mut LeanObject,
    mut v_a_4969_: *mut LeanObject,
    mut v_a_4970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: u8 = 0;
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4979_: usize = 0;
    let mut v___x_4980_: usize = 0;
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: u8 = 0;
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: u8 = 0;
    let mut v___x_5031_: usize = 0;
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5037_: u8 = 0;
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5041_: u8 = 0;
    let mut v_a_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5045_: u8 = 0;
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4972_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1;
                lean_inc(v_x_4962_);
                v___x_4973_ = l_Lean_Syntax_isOfKind(v_x_4962_, v___x_4972_);
                if v___x_4973_ == 0 {
                    lean_dec(v_x_4962_);
                    v___x_4974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
                    return v___x_4974_;
                } else {
                    v___x_4975_ = lean_unsigned_to_nat(1);
                    v___x_4976_ = l_Lean_Syntax_getArg(v_x_4962_, v___x_4975_);
                    lean_dec(v_x_4962_);
                    v_args_4977_ = l_Lean_Syntax_getArgs(v___x_4976_);
                    lean_dec(v___x_4976_);
                    v___x_4978_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_args_4977_);
                    lean_dec_ref(v_args_4977_);
                    v_sz_4979_ = lean_array_size(v___x_4978_);
                    v___x_4980_ = 0usize;
                    v___x_4981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_4979_, v___x_4980_, v___x_4978_, v_a_4969_);
                    if lean_obj_tag(v___x_4981_) == 0 {
                        v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
                        lean_inc(v_a_4982_);
                        lean_dec_ref_known(v___x_4981_, 1);
                        v_ref_4983_ = lean_ctor_get(v_a_4969_, 5);
                        v___x_4984_ = lean_unsigned_to_nat(0);
                        v___x_4985_ = 0;
                        v___x_4986_ = l_Lean_SourceInfo_fromRef(v_ref_4983_, v___x_4985_);
                        v___x_5019_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17;
                        v___x_5020_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18;
                        lean_inc_n(v___x_4986_, 5);
                        v___x_5021_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_5021_, 0, v___x_4986_);
                        lean_ctor_set(v___x_5021_, 1, v___x_5020_);
                        v___x_5022_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
                        v___x_5023_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21;
                        v___x_5024_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22;
                        v___x_5025_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_5025_, 0, v___x_4986_);
                        lean_ctor_set(v___x_5025_, 1, v___x_5024_);
                        v___x_5026_ = l_Lean_Syntax_node1(v___x_4986_, v___x_5023_, v___x_5025_);
                        v___x_5027_ = l_Lean_Syntax_node1(v___x_4986_, v___x_5022_, v___x_5026_);
                        v___x_5028_ =
                            l_Lean_Syntax_node2(v___x_4986_, v___x_5019_, v___x_5021_, v___x_5027_);
                        v___x_5029_ = lean_array_get_size(v_a_4982_);
                        v___x_5030_ = lean_nat_dec_lt(v___x_4984_, v___x_5029_);
                        if v___x_5030_ == 0 {
                            lean_dec(v_a_4982_);
                            v_a_4988_ = v___x_5028_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5031_ = lean_usize_of_nat(v___x_5029_);
                            v___x_5032_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(v_a_4982_, v___x_5031_, v___x_4980_, v___x_5028_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
                            lean_dec(v_a_4982_);
                            if lean_obj_tag(v___x_5032_) == 0 {
                                v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
                                lean_inc(v_a_5033_);
                                lean_dec_ref_known(v___x_5032_, 1);
                                v_a_4988_ = v_a_5033_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_4986_);
                                v_a_5034_ = lean_ctor_get(v___x_5032_, 0);
                                v_isSharedCheck_5041_ = (!lean_is_exclusive(v___x_5032_)) as u8;
                                if v_isSharedCheck_5041_ == 0 {
                                    v___x_5036_ = v___x_5032_;
                                    v_isShared_5037_ = v_isSharedCheck_5041_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_5034_);
                                    lean_dec(v___x_5032_);
                                    v___x_5036_ = lean_box(0);
                                    v_isShared_5037_ = v_isSharedCheck_5041_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_5042_ = lean_ctor_get(v___x_4981_, 0);
                        v_isSharedCheck_5049_ = (!lean_is_exclusive(v___x_4981_)) as u8;
                        if v_isSharedCheck_5049_ == 0 {
                            v___x_5044_ = v___x_4981_;
                            v_isShared_5045_ = v_isSharedCheck_5049_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5042_);
                            lean_dec(v___x_4981_);
                            v___x_5044_ = lean_box(0);
                            v_isShared_5045_ = v_isSharedCheck_5049_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4989_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3;
                v___x_4990_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4;
                lean_inc_n(v___x_4986_, 15);
                v___x_4991_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4991_, 0, v___x_4986_);
                lean_ctor_set(v___x_4991_, 1, v___x_4990_);
                v___x_4992_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6;
                v___x_4993_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8;
                v___x_4994_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7;
                v___x_4995_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2;
                v___x_4996_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
                v___x_4997_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4997_, 0, v___x_4986_);
                lean_ctor_set(v___x_4997_, 1, v___x_4995_);
                v___x_4998_ = l_Lean_Syntax_node2(v___x_4986_, v___x_4996_, v___x_4997_, v_a_4988_);
                v___x_4999_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9;
                v___x_5000_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5000_, 0, v___x_4986_);
                lean_ctor_set(v___x_5000_, 1, v___x_4999_);
                v___x_5001_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11;
                v___x_5002_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12;
                v___x_5003_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5003_, 0, v___x_4986_);
                lean_ctor_set(v___x_5003_, 1, v___x_5002_);
                v___x_5004_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13;
                v___x_5005_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14;
                v___x_5006_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5006_, 0, v___x_4986_);
                lean_ctor_set(v___x_5006_, 1, v___x_5004_);
                v___x_5007_ = l_Lean_Syntax_node1(v___x_4986_, v___x_5005_, v___x_5006_);
                v___x_5008_ = l_Lean_Syntax_node1(v___x_4986_, v___x_4994_, v___x_5007_);
                v___x_5009_ = l_Lean_Syntax_node1(v___x_4986_, v___x_4993_, v___x_5008_);
                v___x_5010_ = l_Lean_Syntax_node1(v___x_4986_, v___x_4992_, v___x_5009_);
                v___x_5011_ =
                    l_Lean_Syntax_node2(v___x_4986_, v___x_5001_, v___x_5003_, v___x_5010_);
                v___x_5012_ = l_Lean_Syntax_node3(
                    v___x_4986_,
                    v___x_4994_,
                    v___x_4998_,
                    v___x_5000_,
                    v___x_5011_,
                );
                v___x_5013_ = l_Lean_Syntax_node1(v___x_4986_, v___x_4993_, v___x_5012_);
                v___x_5014_ = l_Lean_Syntax_node1(v___x_4986_, v___x_4992_, v___x_5013_);
                v___x_5015_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15;
                v___x_5016_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5016_, 0, v___x_4986_);
                lean_ctor_set(v___x_5016_, 1, v___x_5015_);
                v___x_5017_ = l_Lean_Syntax_node3(
                    v___x_4986_,
                    v___x_4989_,
                    v___x_4991_,
                    v___x_5014_,
                    v___x_5016_,
                );
                v___x_5018_ = l_Lean_Elab_Tactic_evalTactic(
                    v___x_5017_,
                    v_a_4963_,
                    v_a_4964_,
                    v_a_4965_,
                    v_a_4966_,
                    v_a_4967_,
                    v_a_4968_,
                    v_a_4969_,
                    v_a_4970_,
                );
                return v___x_5018_;
            }
            2 => {
                if v_isShared_5037_ == 0 {
                    v___x_5039_ = v___x_5036_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
                    v___x_5039_ = v_reuseFailAlloc_5040_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5039_;
            }
            4 => {
                if v_isShared_5045_ == 0 {
                    v___x_5047_ = v___x_5044_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5042_);
                    v___x_5047_ = v_reuseFailAlloc_5048_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___boxed(
    mut v_x_5050_: *mut LeanObject,
    mut v_a_5051_: *mut LeanObject,
    mut v_a_5052_: *mut LeanObject,
    mut v_a_5053_: *mut LeanObject,
    mut v_a_5054_: *mut LeanObject,
    mut v_a_5055_: *mut LeanObject,
    mut v_a_5056_: *mut LeanObject,
    mut v_a_5057_: *mut LeanObject,
    mut v_a_5058_: *mut LeanObject,
    mut v_a_5059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5060_: *mut LeanObject = core::ptr::null_mut();
    v_res_5060_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(
        v_x_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_,
        v_a_5058_,
    );
    lean_dec(v_a_5058_);
    lean_dec_ref(v_a_5057_);
    lean_dec(v_a_5056_);
    lean_dec_ref(v_a_5055_);
    lean_dec(v_a_5054_);
    lean_dec_ref(v_a_5053_);
    lean_dec(v_a_5052_);
    lean_dec_ref(v_a_5051_);
    return v_res_5060_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(
    mut v_sz_5061_: usize,
    mut v_i_5062_: usize,
    mut v_bs_5063_: *mut LeanObject,
    mut v___y_5064_: *mut LeanObject,
    mut v___y_5065_: *mut LeanObject,
    mut v___y_5066_: *mut LeanObject,
    mut v___y_5067_: *mut LeanObject,
    mut v___y_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
    mut v___y_5070_: *mut LeanObject,
    mut v___y_5071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    v___x_5073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_5061_, v_i_5062_, v_bs_5063_, v___y_5070_);
    return v___x_5073_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___boxed(
    mut v_sz_5074_: *mut LeanObject,
    mut v_i_5075_: *mut LeanObject,
    mut v_bs_5076_: *mut LeanObject,
    mut v___y_5077_: *mut LeanObject,
    mut v___y_5078_: *mut LeanObject,
    mut v___y_5079_: *mut LeanObject,
    mut v___y_5080_: *mut LeanObject,
    mut v___y_5081_: *mut LeanObject,
    mut v___y_5082_: *mut LeanObject,
    mut v___y_5083_: *mut LeanObject,
    mut v___y_5084_: *mut LeanObject,
    mut v___y_5085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5086_: usize = 0;
    let mut v_i_boxed_5087_: usize = 0;
    let mut v_res_5088_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5086_ = lean_unbox_usize(v_sz_5074_);
    lean_dec(v_sz_5074_);
    v_i_boxed_5087_ = lean_unbox_usize(v_i_5075_);
    lean_dec(v_i_5075_);
    v_res_5088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(v_sz_boxed_5086_, v_i_boxed_5087_, v_bs_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
    lean_dec(v___y_5084_);
    lean_dec_ref(v___y_5083_);
    lean_dec(v___y_5082_);
    lean_dec_ref(v___y_5081_);
    lean_dec(v___y_5080_);
    lean_dec_ref(v___y_5079_);
    lean_dec(v___y_5078_);
    lean_dec_ref(v___y_5077_);
    return v_res_5088_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1(
    mut v_as_5089_: *mut LeanObject,
    mut v_i_5090_: usize,
    mut v_stop_5091_: usize,
    mut v_b_5092_: *mut LeanObject,
    mut v___y_5093_: *mut LeanObject,
    mut v___y_5094_: *mut LeanObject,
    mut v___y_5095_: *mut LeanObject,
    mut v___y_5096_: *mut LeanObject,
    mut v___y_5097_: *mut LeanObject,
    mut v___y_5098_: *mut LeanObject,
    mut v___y_5099_: *mut LeanObject,
    mut v___y_5100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    v___x_5102_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_5089_, v_i_5090_, v_stop_5091_, v_b_5092_, v___y_5099_);
    return v___x_5102_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___boxed(
    mut v_as_5103_: *mut LeanObject,
    mut v_i_5104_: *mut LeanObject,
    mut v_stop_5105_: *mut LeanObject,
    mut v_b_5106_: *mut LeanObject,
    mut v___y_5107_: *mut LeanObject,
    mut v___y_5108_: *mut LeanObject,
    mut v___y_5109_: *mut LeanObject,
    mut v___y_5110_: *mut LeanObject,
    mut v___y_5111_: *mut LeanObject,
    mut v___y_5112_: *mut LeanObject,
    mut v___y_5113_: *mut LeanObject,
    mut v___y_5114_: *mut LeanObject,
    mut v___y_5115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5116_: usize = 0;
    let mut v_stop_boxed_5117_: usize = 0;
    let mut v_res_5118_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5116_ = lean_unbox_usize(v_i_5104_);
    lean_dec(v_i_5104_);
    v_stop_boxed_5117_ = lean_unbox_usize(v_stop_5105_);
    lean_dec(v_stop_5105_);
    v_res_5118_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1(v_as_5103_, v_i_boxed_5116_, v_stop_boxed_5117_, v_b_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
    lean_dec(v___y_5114_);
    lean_dec_ref(v___y_5113_);
    lean_dec(v___y_5112_);
    lean_dec_ref(v___y_5111_);
    lean_dec(v___y_5110_);
    lean_dec_ref(v___y_5109_);
    lean_dec(v___y_5108_);
    lean_dec_ref(v___y_5107_);
    lean_dec_ref(v_as_5103_);
    return v_res_5118_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1()
-> *mut LeanObject {
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    v___x_5128_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5129_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1;
    v___x_5130_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1;
    v___x_5131_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5132_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5128_,
        v___x_5129_,
        v___x_5130_,
        v___x_5131_,
    );
    return v___x_5132_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___boxed(
    mut v_a_5133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5134_: *mut LeanObject = core::ptr::null_mut();
    v_res_5134_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1();
    return v_res_5134_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
}
