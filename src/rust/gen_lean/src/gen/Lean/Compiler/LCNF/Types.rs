// Lean compiler output
// Module: Lean.Compiler.LCNF.Types
// Imports: Lean.Compiler.BorrowedAnnotation Lean.Meta.InferType Init.Omega Lean.OriginalConstKind
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_set, lean_array_size, lean_array_to_list, lean_array_uget_borrowed,
    lean_expr_abstract, lean_expr_eqv, lean_expr_instantiate_rev, lean_expr_instantiate1,
    lean_infer_type, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq, lean_uint64_lor, lean_uint64_of_nat,
    lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Class::lean_is_class;
use crate::r#gen::Lean::Compiler::BorrowedAnnotation::{
    initialize_Lean_Compiler_BorrowedAnnotation, l_Lean_isMarkedBorrowed, l_Lean_markBorrowed,
    runtime_initialize_Lean_Compiler_BorrowedAnnotation,
};
use crate::r#gen::Lean::CoreM::{l_Lean_Exception_isRuntime, l_Lean_diagnostics};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_InductiveVal_numCtors;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_eta,
    l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_headBeta, l_Lean_Expr_isAppOf, l_Lean_Expr_lam___override,
    l_Lean_Expr_sort___override, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_joinSep, l_Lean_MessageData_note, l_Lean_MessageData_ofConstName,
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::InferType::{
    initialize_Lean_Meta_InferType, l_Lean_Meta_isProp, l_Lean_Meta_isTypeFormer,
    runtime_initialize_Lean_Meta_InferType,
};
use crate::r#gen::Lean::OriginalConstKind::{
    initialize_Lean_OriginalConstKind, l_Lean_getOriginalConstKind_x3f,
    runtime_initialize_Lean_OriginalConstKind,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
pub static l_Lean_Compiler_term_u25fe___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Compiler_term_u25fe___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_term_u25fe___closed__1_value: leanh::LeanStringObject<9> =
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
        m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0],
    };
static mut l_Lean_Compiler_term_u25fe___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_term_u25fe___closed__2_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 5,
        m_data: [116, 101, 114, 109, 226, 151, 190, 0],
    };
static mut l_Lean_Compiler_term_u25fe___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_term_u25fe___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Compiler_term_u25fe___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__1_value)
                as *mut leanh::LeanObject,
            8543197020067251012 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Compiler_term_u25fe___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__2_value)
                as *mut leanh::LeanObject,
            5316518735284633940 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_term_u25fe___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_term_u25fe___closed__4_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 151, 190, 0],
    };
static mut l_Lean_Compiler_term_u25fe___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_term_u25fe___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_term_u25fe___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_term_u25fe___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__3_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_term_u25fe___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_term_u25fe: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_term_u25fe___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 99, 69, 114, 97, 115, 101, 100, 0]};
static mut l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__0_value) as *mut leanh::LeanObject,381462102099548843 as *mut leanh::LeanObject] };
static mut l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_erasedExpr___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_erasedExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_erasedExpr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_anyExpr___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [108, 99, 65, 110, 121, 0],
    };
static mut l_Lean_Compiler_LCNF_anyExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyExpr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_anyExpr___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyExpr___closed__0_value)
                as *mut leanh::LeanObject,
            9493731432054108642 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_anyExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyExpr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_anyExpr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_anyExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_anyExpr: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_isVoid___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [108, 99, 86, 111, 105, 100, 0],
    };
static mut l_Lean_Expr_isVoid___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isVoid___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Expr_isVoid___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_isVoid___closed__0_value)
                as *mut leanh::LeanObject,
            12548675615898448964 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_isVoid___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isVoid___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0: u64 = 0;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [83, 117, 98, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [86, 111, 105, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 111, 110, 101, 109, 112, 116, 121, 84, 121, 112, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0_value: leanh::LeanStringObject<43> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 101, 114, 114, 111, 114, 58, 32, 112, 114, 105, 118, 97, 116, 101, 32, 105, 110, 32, 112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0: u64 = 0;
pub static l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [32, 226, 134, 166, 32, 0]};
static mut l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0_value
) as *mut leanh::LeanObject;
static mut l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toLCNFType___closed__0_value: leanh::LeanStringObject<34> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            108, 111, 99, 97, 108, 108, 121, 32, 105, 110, 102, 101, 114, 114, 101, 100, 32, 99,
            111, 109, 112, 105, 108, 97, 116, 105, 111, 110, 32, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toLCNFType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toLCNFType___closed__2_value: leanh::LeanStringObject<19> =
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
            10, 100, 105, 102, 102, 101, 114, 115, 32, 102, 114, 111, 109, 32, 116, 121, 112, 101,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toLCNFType___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toLCNFType___closed__4_value: leanh::LeanStringObject<147> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 147,
        m_capacity: 147,
        m_length: 146,
        m_data: [
            10, 116, 104, 97, 116, 32, 119, 111, 117, 108, 100, 32, 98, 101, 32, 105, 110, 102,
            101, 114, 114, 101, 100, 32, 105, 110, 32, 111, 116, 104, 101, 114, 32, 109, 111, 100,
            117, 108, 101, 115, 46, 32, 84, 104, 105, 115, 32, 117, 115, 117, 97, 108, 108, 121,
            32, 109, 101, 97, 110, 115, 32, 116, 104, 97, 116, 32, 97, 32, 116, 121, 112, 101, 32,
            96, 100, 101, 102, 96, 32, 105, 110, 118, 111, 108, 118, 101, 100, 32, 119, 105, 116,
            104, 32, 116, 104, 101, 32, 109, 101, 110, 116, 105, 111, 110, 101, 100, 32, 100, 101,
            99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 110, 101, 101, 100, 115, 32, 116,
            111, 32, 98, 101, 32, 96, 64, 91, 101, 120, 112, 111, 115, 101, 93, 96, 100, 46, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toLCNFType___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toLCNFType___closed__6_value: leanh::LeanStringObject<21> =
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
            67, 111, 109, 112, 105, 108, 97, 116, 105, 111, 110, 32, 102, 97, 105, 108, 101, 100,
            44, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toLCNFType___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toLCNFType___closed__8_value: leanh::LeanStringObject<86> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 86,
        m_capacity: 86,
        m_length: 85,
        m_data: [
            84, 104, 105, 115, 32, 105, 115, 32, 97, 32, 99, 117, 114, 114, 101, 110, 116, 32, 99,
            111, 109, 112, 105, 108, 101, 114, 32, 108, 105, 109, 105, 116, 97, 116, 105, 111, 110,
            32, 102, 111, 114, 32, 96, 109, 111, 100, 117, 108, 101, 96, 115, 32, 116, 104, 97,
            116, 32, 109, 97, 121, 32, 98, 101, 32, 108, 105, 102, 116, 101, 100, 32, 105, 110, 32,
            116, 104, 101, 32, 102, 117, 116, 117, 114, 101, 46, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toLCNFType___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toLCNFType___closed__10_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toLCNFType___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_toLCNFType___closed__11_value: leanh::LeanStringObject<178> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 178,
        m_capacity: 178,
        m_length: 177,
        m_data: [
            108, 111, 99, 97, 108, 108, 121, 32, 105, 110, 102, 101, 114, 114, 101, 100, 32, 99,
            111, 109, 112, 105, 108, 97, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 100, 105,
            102, 102, 101, 114, 115, 32, 102, 114, 111, 109, 32, 116, 121, 112, 101, 32, 116, 104,
            97, 116, 32, 119, 111, 117, 108, 100, 32, 98, 101, 32, 105, 110, 102, 101, 114, 114,
            101, 100, 32, 105, 110, 32, 111, 116, 104, 101, 114, 32, 109, 111, 100, 117, 108, 101,
            115, 46, 32, 83, 111, 109, 101, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 108,
            108, 111, 119, 105, 110, 103, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110,
            115, 32, 109, 97, 121, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 96, 64,
            91, 101, 120, 112, 111, 115, 101, 93, 96, 100, 32, 116, 111, 32, 102, 105, 120, 32,
            116, 104, 105, 115, 32, 109, 105, 115, 109, 97, 116, 99, 104, 58, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toLCNFType___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toLCNFType___closed__14_value: leanh::LeanStringObject<2> =
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
        m_data: [10, 0],
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toLCNFType___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toLCNFType___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0_value: leanh::LeanStringObject<47> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 70, 111, 114, 97, 108, 108, 44, 32, 116, 111, 111, 32, 109, 97, 110, 121, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_mkBoxedName___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [95, 98, 111, 120, 101, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_mkBoxedName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkBoxedName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ImpureType_float___closed__0_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [70, 108, 111, 97, 116, 0],
};
static mut l_Lean_Compiler_LCNF_ImpureType_float___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_float___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ImpureType_float___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_float___closed__0_value)
            as *mut leanh::LeanObject,
        4889978610488853816 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ImpureType_float___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_float___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_ImpureType_float___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_float___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_float: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ImpureType_float32___closed__0_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [70, 108, 111, 97, 116, 51, 50, 0],
};
static mut l_Lean_Compiler_LCNF_ImpureType_float32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ImpureType_float32___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_float32___closed__0_value)
            as *mut leanh::LeanObject,
        16690552700474419446 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ImpureType_float32___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_float32___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_ImpureType_float32___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_float32___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_float32: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [85, 73, 110, 116, 56, 0],
};
static mut l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0_value)
            as *mut leanh::LeanObject,
        15764114953608429200 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_uint8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [85, 73, 110, 116, 49, 54, 0],
};
static mut l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0_value)
            as *mut leanh::LeanObject,
        9755723410228041222 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_uint16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [85, 73, 110, 116, 51, 50, 0],
};
static mut l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0_value)
            as *mut leanh::LeanObject,
        13474504806189678690 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_uint32: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [85, 73, 110, 116, 54, 52, 0],
};
static mut l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0_value)
            as *mut leanh::LeanObject,
        2954612489107370298 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_uint64: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ImpureType_usize___closed__0_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [85, 83, 105, 122, 101, 0],
};
static mut l_Lean_Compiler_LCNF_ImpureType_usize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_usize___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ImpureType_usize___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_usize___closed__0_value)
            as *mut leanh::LeanObject,
        17712594561405737325 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ImpureType_usize___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_usize___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_ImpureType_usize___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_usize___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_usize: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_ImpureType_erased___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_erased___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_erased: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ImpureType_object___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [111, 98, 106, 0],
};
static mut l_Lean_Compiler_LCNF_ImpureType_object___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_object___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ImpureType_object___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_object___closed__0_value)
            as *mut leanh::LeanObject,
        6552590064380865520 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ImpureType_object___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_object___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_object___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_object: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 111, 98, 106, 0],
};
static mut l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0_value)
            as *mut leanh::LeanObject,
        930430701391226905 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_tobject: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [116, 97, 103, 103, 101, 100, 0],
};
static mut l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0_value)
            as *mut leanh::LeanObject,
        13921617720798624167 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_tagged: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_ImpureType_void___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ImpureType_void___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_ImpureType_void: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2503_ = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__0;
    v___x_2504_ = l_String_toRawSubstring_x27(v___x_2503_);
    return v___x_2504_;
}
pub unsafe fn l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1(
    mut v_x_2513_: *mut leanh::LeanObject,
    mut v_a_2514_: *mut leanh::LeanObject,
    mut v_a_2515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: u8 = 0;
    v___x_2516_ = l_Lean_Compiler_term_u25fe___closed__3;
    v___x_2517_ = l_Lean_Syntax_isOfKind(v_x_2513_, v___x_2516_);
    if v___x_2517_ == 0 {
        let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2518_ = leanh::lean_box(1);
        v___x_2519_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2519_, 0, v___x_2518_);
        leanh::lean_ctor_set(v___x_2519_, 1, v_a_2515_);
        return v___x_2519_;
    } else {
        let mut v_quotContext_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2523_: u8 = 0;
        let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2520_ = leanh::lean_ctor_get(v_a_2514_, 1);
        v_currMacroScope_2521_ = leanh::lean_ctor_get(v_a_2514_, 2);
        v_ref_2522_ = leanh::lean_ctor_get(v_a_2514_, 5);
        v___x_2523_ = 0;
        v___x_2524_ = l_Lean_SourceInfo_fromRef(v_ref_2522_, v___x_2523_);
        v___x_2525_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1_once), _init_l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__1);
        v___x_2526_ = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2;
        leanh::lean_inc(v_currMacroScope_2521_);
        leanh::lean_inc(v_quotContext_2520_);
        v___x_2527_ =
            l_Lean_addMacroScope(v_quotContext_2520_, v___x_2526_, v_currMacroScope_2521_);
        v___x_2528_ = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__4;
        v___x_2529_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2529_, 0, v___x_2524_);
        leanh::lean_ctor_set(v___x_2529_, 1, v___x_2525_);
        leanh::lean_ctor_set(v___x_2529_, 2, v___x_2527_);
        leanh::lean_ctor_set(v___x_2529_, 3, v___x_2528_);
        v___x_2530_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2530_, 0, v___x_2529_);
        leanh::lean_ctor_set(v___x_2530_, 1, v_a_2515_);
        return v___x_2530_;
    }
}
pub unsafe fn l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___boxed(
    mut v_x_2531_: *mut leanh::LeanObject,
    mut v_a_2532_: *mut leanh::LeanObject,
    mut v_a_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2534_ = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1(v_x_2531_, v_a_2532_, v_a_2533_);
    leanh::lean_dec_ref(v_a_2532_);
    return v_res_2534_;
}
pub unsafe fn l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1(
    mut v_x_2538_: *mut leanh::LeanObject,
    mut v_a_2539_: *mut leanh::LeanObject,
    mut v_a_2540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: u8 = 0;
    v___x_2541_ =
        l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___closed__1;
    leanh::lean_inc(v_x_2538_);
    v___x_2542_ = l_Lean_Syntax_isOfKind(v_x_2538_, v___x_2541_);
    if v___x_2542_ == 0 {
        let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2538_);
        v___x_2543_ = leanh::lean_box(0);
        v___x_2544_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2544_, 0, v___x_2543_);
        leanh::lean_ctor_set(v___x_2544_, 1, v_a_2540_);
        return v___x_2544_;
    } else {
        let mut v_ref_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2546_: u8 = 0;
        let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_2545_ = l_Lean_replaceRef(v_x_2538_, v_a_2539_);
        leanh::lean_dec(v_x_2538_);
        v___x_2546_ = 0;
        v___x_2547_ = l_Lean_SourceInfo_fromRef(v_ref_2545_, v___x_2546_);
        leanh::lean_dec(v_ref_2545_);
        v___x_2548_ = l_Lean_Compiler_term_u25fe___closed__3;
        v___x_2549_ = l_Lean_Compiler_term_u25fe___closed__4;
        leanh::lean_inc(v___x_2547_);
        v___x_2550_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2550_, 0, v___x_2547_);
        leanh::lean_ctor_set(v___x_2550_, 1, v___x_2549_);
        v___x_2551_ = l_Lean_Syntax_node1(v___x_2547_, v___x_2548_, v___x_2550_);
        v___x_2552_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2552_, 0, v___x_2551_);
        leanh::lean_ctor_set(v___x_2552_, 1, v_a_2540_);
        return v___x_2552_;
    }
}
pub unsafe fn l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1___boxed(
    mut v_x_2553_: *mut leanh::LeanObject,
    mut v_a_2554_: *mut leanh::LeanObject,
    mut v_a_2555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______unexpand__lcErased__1(
        v_x_2553_, v_a_2554_, v_a_2555_,
    );
    leanh::lean_dec(v_a_2554_);
    return v_res_2556_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_erasedExpr___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2557_ = leanh::lean_box(0);
    v___x_2558_ = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2;
    v___x_2559_ = l_Lean_mkConst(v___x_2558_, v___x_2557_);
    return v___x_2559_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_erasedExpr() -> *mut leanh::LeanObject {
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2560_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_erasedExpr___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_erasedExpr___closed__0_once),
        _init_l_Lean_Compiler_LCNF_erasedExpr___closed__0,
    );
    return v___x_2560_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_anyExpr___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2564_ = leanh::lean_box(0);
    v___x_2565_ = l_Lean_Compiler_LCNF_anyExpr___closed__1;
    v___x_2566_ = l_Lean_mkConst(v___x_2565_, v___x_2564_);
    return v___x_2566_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_anyExpr() -> *mut leanh::LeanObject {
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2567_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_anyExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_anyExpr___closed__2_once),
        _init_l_Lean_Compiler_LCNF_anyExpr___closed__2,
    );
    return v___x_2567_;
}
pub unsafe fn l_Lean_Expr_isVoid(mut v_e_2571_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u8 = 0;
    v___x_2572_ = l_Lean_Expr_isVoid___closed__1;
    v___x_2573_ = l_Lean_Expr_isAppOf(v_e_2571_, v___x_2572_);
    return v___x_2573_;
}
pub unsafe fn l_Lean_Expr_isVoid___boxed(
    mut v_e_2574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2575_: u8 = 0;
    let mut v_r_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2575_ = l_Lean_Expr_isVoid(v_e_2574_);
    leanh::lean_dec_ref(v_e_2574_);
    v_r_2576_ = leanh::lean_box((v_res_2575_) as usize);
    return v_r_2576_;
}
pub unsafe fn l_Lean_Expr_isErased(mut v_e_2577_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    v___x_2578_ = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2;
    v___x_2579_ = l_Lean_Expr_isAppOf(v_e_2577_, v___x_2578_);
    return v___x_2579_;
}
pub unsafe fn l_Lean_Expr_isErased___boxed(
    mut v_e_2580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2581_: u8 = 0;
    let mut v_r_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2581_ = l_Lean_Expr_isErased(v_e_2580_);
    leanh::lean_dec_ref(v_e_2580_);
    v_r_2582_ = leanh::lean_box((v_res_2581_) as usize);
    return v_r_2582_;
}
pub unsafe fn l_Lean_Expr_isAny(mut v_e_2583_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    v___x_2584_ = l_Lean_Compiler_LCNF_anyExpr___closed__1;
    v___x_2585_ = l_Lean_Expr_isAppOf(v_e_2583_, v___x_2584_);
    return v___x_2585_;
}
pub unsafe fn l_Lean_Expr_isAny___boxed(
    mut v_e_2586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2587_: u8 = 0;
    let mut v_r_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2587_ = l_Lean_Expr_isAny(v_e_2586_);
    leanh::lean_dec_ref(v_e_2586_);
    v_r_2588_ = leanh::lean_box((v_res_2587_) as usize);
    return v_r_2588_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isPropFormerTypeQuick(
    mut v_x_2589_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_body_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    let mut v___x_2594_: u8 = 0;
    let mut v___x_2595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2589_) {
                7 => {
                    v_body_2590_ = leanh::lean_ctor_get(v_x_2589_, 2);
                    v_x_2589_ = v_body_2590_;
                    state = 0;
                    continue;
                }
                3 => {
                    v_u_2592_ = leanh::lean_ctor_get(v_x_2589_, 0);
                    if leanh::lean_obj_tag(v_u_2592_) == 0 {
                        v___x_2593_ = 1;
                        return v___x_2593_;
                    } else {
                        v___x_2594_ = 0;
                        return v___x_2594_;
                    }
                }
                _ => {
                    v___x_2595_ = 0;
                    return v___x_2595_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isPropFormerTypeQuick___boxed(
    mut v_x_2596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2597_: u8 = 0;
    let mut v_r_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2597_ = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(v_x_2596_);
    leanh::lean_dec_ref(v_x_2596_);
    v_r_2598_ = leanh::lean_box((v_res_2597_) as usize);
    return v_r_2598_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(
    mut v_k_2599_: *mut leanh::LeanObject,
    mut v_b_2600_: *mut leanh::LeanObject,
    mut v___y_2601_: *mut leanh::LeanObject,
    mut v___y_2602_: *mut leanh::LeanObject,
    mut v___y_2603_: *mut leanh::LeanObject,
    mut v___y_2604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2604_);
    leanh::lean_inc_ref(v___y_2603_);
    leanh::lean_inc(v___y_2602_);
    leanh::lean_inc_ref(v___y_2601_);
    v___x_2606_ = leanh::lean_apply_6(
        v_k_2599_,
        v_b_2600_,
        v___y_2601_,
        v___y_2602_,
        v___y_2603_,
        v___y_2604_,
        leanh::lean_box(0),
    );
    return v___x_2606_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0___boxed(
    mut v_k_2607_: *mut leanh::LeanObject,
    mut v_b_2608_: *mut leanh::LeanObject,
    mut v___y_2609_: *mut leanh::LeanObject,
    mut v___y_2610_: *mut leanh::LeanObject,
    mut v___y_2611_: *mut leanh::LeanObject,
    mut v___y_2612_: *mut leanh::LeanObject,
    mut v___y_2613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2614_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0(v_k_2607_, v_b_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
    leanh::lean_dec(v___y_2612_);
    leanh::lean_dec_ref(v___y_2611_);
    leanh::lean_dec(v___y_2610_);
    leanh::lean_dec_ref(v___y_2609_);
    return v_res_2614_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(
    mut v_name_2615_: *mut leanh::LeanObject,
    mut v_bi_2616_: u8,
    mut v_type_2617_: *mut leanh::LeanObject,
    mut v_k_2618_: *mut leanh::LeanObject,
    mut v_kind_2619_: u8,
    mut v___y_2620_: *mut leanh::LeanObject,
    mut v___y_2621_: *mut leanh::LeanObject,
    mut v___y_2622_: *mut leanh::LeanObject,
    mut v___y_2623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut v_a_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2638_: u8 = 0;
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2625_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_2625_, 0, v_k_2618_);
                v___x_2626_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_2615_,
                    v_bi_2616_,
                    v_type_2617_,
                    v___f_2625_,
                    v_kind_2619_,
                    v___y_2620_,
                    v___y_2621_,
                    v___y_2622_,
                    v___y_2623_,
                );
                if leanh::lean_obj_tag(v___x_2626_) == 0 {
                    v_a_2627_ = leanh::lean_ctor_get(v___x_2626_, 0);
                    v_isSharedCheck_2634_ = (!leanh::lean_is_exclusive(v___x_2626_)) as u8;
                    if v_isSharedCheck_2634_ == 0 {
                        v___x_2629_ = v___x_2626_;
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2627_);
                        leanh::lean_dec(v___x_2626_);
                        v___x_2629_ = leanh::lean_box(0);
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2635_ = leanh::lean_ctor_get(v___x_2626_, 0);
                    v_isSharedCheck_2642_ = (!leanh::lean_is_exclusive(v___x_2626_)) as u8;
                    if v_isSharedCheck_2642_ == 0 {
                        v___x_2637_ = v___x_2626_;
                        v_isShared_2638_ = v_isSharedCheck_2642_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2635_);
                        leanh::lean_dec(v___x_2626_);
                        v___x_2637_ = leanh::lean_box(0);
                        v_isShared_2638_ = v_isSharedCheck_2642_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2630_ == 0 {
                    v___x_2632_ = v___x_2629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
                    v___x_2632_ = v_reuseFailAlloc_2633_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2632_;
            }
            3 => {
                if v_isShared_2638_ == 0 {
                    v___x_2640_ = v___x_2637_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2641_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
                    v___x_2640_ = v_reuseFailAlloc_2641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2640_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg___boxed(
    mut v_name_2643_: *mut leanh::LeanObject,
    mut v_bi_2644_: *mut leanh::LeanObject,
    mut v_type_2645_: *mut leanh::LeanObject,
    mut v_k_2646_: *mut leanh::LeanObject,
    mut v_kind_2647_: *mut leanh::LeanObject,
    mut v___y_2648_: *mut leanh::LeanObject,
    mut v___y_2649_: *mut leanh::LeanObject,
    mut v___y_2650_: *mut leanh::LeanObject,
    mut v___y_2651_: *mut leanh::LeanObject,
    mut v___y_2652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_2653_: u8 = 0;
    let mut v_kind_boxed_2654_: u8 = 0;
    let mut v_res_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2653_ = (leanh::lean_unbox(v_bi_2644_) as u8);
    v_kind_boxed_2654_ = (leanh::lean_unbox(v_kind_2647_) as u8);
    v_res_2655_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_name_2643_, v_bi_boxed_2653_, v_type_2645_, v_k_2646_, v_kind_boxed_2654_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
    leanh::lean_dec(v___y_2651_);
    leanh::lean_dec_ref(v___y_2650_);
    leanh::lean_dec(v___y_2649_);
    leanh::lean_dec_ref(v___y_2648_);
    return v_res_2655_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0(
    mut v_00_u03b1_2656_: *mut leanh::LeanObject,
    mut v_name_2657_: *mut leanh::LeanObject,
    mut v_bi_2658_: u8,
    mut v_type_2659_: *mut leanh::LeanObject,
    mut v_k_2660_: *mut leanh::LeanObject,
    mut v_kind_2661_: u8,
    mut v___y_2662_: *mut leanh::LeanObject,
    mut v___y_2663_: *mut leanh::LeanObject,
    mut v___y_2664_: *mut leanh::LeanObject,
    mut v___y_2665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2667_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_name_2657_, v_bi_2658_, v_type_2659_, v_k_2660_, v_kind_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
    return v___x_2667_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___boxed(
    mut v_00_u03b1_2668_: *mut leanh::LeanObject,
    mut v_name_2669_: *mut leanh::LeanObject,
    mut v_bi_2670_: *mut leanh::LeanObject,
    mut v_type_2671_: *mut leanh::LeanObject,
    mut v_k_2672_: *mut leanh::LeanObject,
    mut v_kind_2673_: *mut leanh::LeanObject,
    mut v___y_2674_: *mut leanh::LeanObject,
    mut v___y_2675_: *mut leanh::LeanObject,
    mut v___y_2676_: *mut leanh::LeanObject,
    mut v___y_2677_: *mut leanh::LeanObject,
    mut v___y_2678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_2679_: u8 = 0;
    let mut v_kind_boxed_2680_: u8 = 0;
    let mut v_res_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2679_ = (leanh::lean_unbox(v_bi_2670_) as u8);
    v_kind_boxed_2680_ = (leanh::lean_unbox(v_kind_2673_) as u8);
    v_res_2681_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0(v_00_u03b1_2668_, v_name_2669_, v_bi_boxed_2679_, v_type_2671_, v_k_2672_, v_kind_boxed_2680_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
    leanh::lean_dec(v___y_2677_);
    leanh::lean_dec_ref(v___y_2676_);
    leanh::lean_dec(v___y_2675_);
    leanh::lean_dec_ref(v___y_2674_);
    return v_res_2681_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed(
    mut v_xs_2684_: *mut leanh::LeanObject,
    mut v_body_2685_: *mut leanh::LeanObject,
    mut v_x_2686_: *mut leanh::LeanObject,
    mut v___y_2687_: *mut leanh::LeanObject,
    mut v___y_2688_: *mut leanh::LeanObject,
    mut v___y_2689_: *mut leanh::LeanObject,
    mut v___y_2690_: *mut leanh::LeanObject,
    mut v___y_2691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2692_ =
        l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(
            v_xs_2684_,
            v_body_2685_,
            v_x_2686_,
            v___y_2687_,
            v___y_2688_,
            v___y_2689_,
            v___y_2690_,
        );
    leanh::lean_dec(v___y_2690_);
    leanh::lean_dec_ref(v___y_2689_);
    leanh::lean_dec(v___y_2688_);
    leanh::lean_dec_ref(v___y_2687_);
    return v_res_2692_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(
    mut v_type_2693_: *mut leanh::LeanObject,
    mut v_xs_2694_: *mut leanh::LeanObject,
    mut v_a_2695_: *mut leanh::LeanObject,
    mut v_a_2696_: *mut leanh::LeanObject,
    mut v_a_2697_: *mut leanh::LeanObject,
    mut v_a_2698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2701_: u8 = 0;
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2714_: u8 = 0;
    let mut v_u_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: u8 = 0;
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2723_: u8 = 0;
    let mut v_a_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v_u_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: u8 = 0;
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2739_: u8 = 0;
    let mut v___f_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: u8 = 0;
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_type_2693_) {
                3 => {
                    v_u_2732_ = leanh::lean_ctor_get(v_type_2693_, 0);
                    if leanh::lean_obj_tag(v_u_2732_) == 0 {
                        leanh::lean_dec_ref_known(v_type_2693_, 1);
                        leanh::lean_dec_ref(v_xs_2694_);
                        v___x_2733_ = 1;
                        v___x_2734_ = leanh::lean_box((v___x_2733_) as usize);
                        v___x_2735_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2735_, 0, v___x_2734_);
                        return v___x_2735_;
                    } else {
                        v___y_2705_ = v_a_2695_;
                        v___y_2706_ = v_a_2696_;
                        v___y_2707_ = v_a_2697_;
                        v___y_2708_ = v_a_2698_;
                        state = 2;
                        continue;
                    }
                }
                7 => {
                    v_binderName_2736_ = leanh::lean_ctor_get(v_type_2693_, 0);
                    leanh::lean_inc(v_binderName_2736_);
                    v_binderType_2737_ = leanh::lean_ctor_get(v_type_2693_, 1);
                    leanh::lean_inc_ref(v_binderType_2737_);
                    v_body_2738_ = leanh::lean_ctor_get(v_type_2693_, 2);
                    leanh::lean_inc_ref(v_body_2738_);
                    v_binderInfo_2739_ = leanh::lean_ctor_get_uint8(
                        v_type_2693_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_dec_ref_known(v_type_2693_, 3);
                    leanh::lean_inc_ref(v_xs_2694_);
                    v___f_2740_ = leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                    leanh::lean_closure_set(v___f_2740_, 0, v_xs_2694_);
                    leanh::lean_closure_set(v___f_2740_, 1, v_body_2738_);
                    v___x_2741_ = lean_expr_instantiate_rev(v_binderType_2737_, v_xs_2694_);
                    leanh::lean_dec_ref(v_xs_2694_);
                    leanh::lean_dec_ref(v_binderType_2737_);
                    v___x_2742_ = 0;
                    v___x_2743_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_2736_, v_binderInfo_2739_, v___x_2741_, v___f_2740_, v___x_2742_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
                    return v___x_2743_;
                }
                _ => {
                    v___y_2705_ = v_a_2695_;
                    v___y_2706_ = v_a_2696_;
                    v___y_2707_ = v_a_2697_;
                    v___y_2708_ = v_a_2698_;
                    state = 2;
                    continue;
                }
            },
            1 => {
                v___x_2701_ = 0;
                v___x_2702_ = leanh::lean_box((v___x_2701_) as usize);
                v___x_2703_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2703_, 0, v___x_2702_);
                return v___x_2703_;
            }
            2 => {
                v___x_2709_ = lean_expr_instantiate_rev(v_type_2693_, v_xs_2694_);
                leanh::lean_dec_ref(v_xs_2694_);
                leanh::lean_dec_ref(v_type_2693_);
                v___x_2710_ = l_Lean_Meta_whnfD(
                    v___x_2709_,
                    v___y_2705_,
                    v___y_2706_,
                    v___y_2707_,
                    v___y_2708_,
                );
                if leanh::lean_obj_tag(v___x_2710_) == 0 {
                    v_a_2711_ = leanh::lean_ctor_get(v___x_2710_, 0);
                    v_isSharedCheck_2723_ = (!leanh::lean_is_exclusive(v___x_2710_)) as u8;
                    if v_isSharedCheck_2723_ == 0 {
                        v___x_2713_ = v___x_2710_;
                        v_isShared_2714_ = v_isSharedCheck_2723_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2711_);
                        leanh::lean_dec(v___x_2710_);
                        v___x_2713_ = leanh::lean_box(0);
                        v_isShared_2714_ = v_isSharedCheck_2723_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2724_ = leanh::lean_ctor_get(v___x_2710_, 0);
                    v_isSharedCheck_2731_ = (!leanh::lean_is_exclusive(v___x_2710_)) as u8;
                    if v_isSharedCheck_2731_ == 0 {
                        v___x_2726_ = v___x_2710_;
                        v_isShared_2727_ = v_isSharedCheck_2731_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2724_);
                        leanh::lean_dec(v___x_2710_);
                        v___x_2726_ = leanh::lean_box(0);
                        v_isShared_2727_ = v_isSharedCheck_2731_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => match leanh::lean_obj_tag(v_a_2711_) {
                3 => {
                    v_u_2715_ = leanh::lean_ctor_get(v_a_2711_, 0);
                    leanh::lean_inc(v_u_2715_);
                    leanh::lean_dec_ref_known(v_a_2711_, 1);
                    if leanh::lean_obj_tag(v_u_2715_) == 0 {
                        v___x_2716_ = 1;
                        v___x_2717_ = leanh::lean_box((v___x_2716_) as usize);
                        if v_isShared_2714_ == 0 {
                            leanh::lean_ctor_set(v___x_2713_, 0, v___x_2717_);
                            v___x_2719_ = v___x_2713_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2720_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2717_);
                            v___x_2719_ = v_reuseFailAlloc_2720_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_u_2715_);
                        leanh::lean_del_object(v___x_2713_);
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    leanh::lean_del_object(v___x_2713_);
                    v___x_2721_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0;
                    v_type_2693_ = v_a_2711_;
                    v_xs_2694_ = v___x_2721_;
                    v_a_2695_ = v___y_2705_;
                    v_a_2696_ = v___y_2706_;
                    v_a_2697_ = v___y_2707_;
                    v_a_2698_ = v___y_2708_;
                    state = 0;
                    continue;
                }
                _ => {
                    leanh::lean_del_object(v___x_2713_);
                    leanh::lean_dec(v_a_2711_);
                    state = 1;
                    continue;
                }
            },
            4 => {
                return v___x_2719_;
            }
            5 => {
                if v_isShared_2727_ == 0 {
                    v___x_2729_ = v___x_2726_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2730_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
                    v___x_2729_ = v_reuseFailAlloc_2730_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___lam__0(
    mut v_xs_2744_: *mut leanh::LeanObject,
    mut v_body_2745_: *mut leanh::LeanObject,
    mut v_x_2746_: *mut leanh::LeanObject,
    mut v___y_2747_: *mut leanh::LeanObject,
    mut v___y_2748_: *mut leanh::LeanObject,
    mut v___y_2749_: *mut leanh::LeanObject,
    mut v___y_2750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2752_ = lean_array_push(v_xs_2744_, v_x_2746_);
    v___x_2753_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(
        v_body_2745_,
        v___x_2752_,
        v___y_2747_,
        v___y_2748_,
        v___y_2749_,
        v___y_2750_,
    );
    return v___x_2753_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___boxed(
    mut v_type_2754_: *mut leanh::LeanObject,
    mut v_xs_2755_: *mut leanh::LeanObject,
    mut v_a_2756_: *mut leanh::LeanObject,
    mut v_a_2757_: *mut leanh::LeanObject,
    mut v_a_2758_: *mut leanh::LeanObject,
    mut v_a_2759_: *mut leanh::LeanObject,
    mut v_a_2760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2761_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(
        v_type_2754_,
        v_xs_2755_,
        v_a_2756_,
        v_a_2757_,
        v_a_2758_,
        v_a_2759_,
    );
    leanh::lean_dec(v_a_2759_);
    leanh::lean_dec_ref(v_a_2758_);
    leanh::lean_dec(v_a_2757_);
    leanh::lean_dec_ref(v_a_2756_);
    return v_res_2761_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isPropFormerType(
    mut v_type_2762_: *mut leanh::LeanObject,
    mut v_a_2763_: *mut leanh::LeanObject,
    mut v_a_2764_: *mut leanh::LeanObject,
    mut v_a_2765_: *mut leanh::LeanObject,
    mut v_a_2766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2768_: u8 = 0;
    v___x_2768_ = l_Lean_Compiler_LCNF_isPropFormerTypeQuick(v_type_2762_);
    if v___x_2768_ == 0 {
        let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2769_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0;
        v___x_2770_ =
            l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go(
                v_type_2762_,
                v___x_2769_,
                v_a_2763_,
                v_a_2764_,
                v_a_2765_,
                v_a_2766_,
            );
        return v___x_2770_;
    } else {
        let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_type_2762_);
        v___x_2771_ = leanh::lean_box((v___x_2768_) as usize);
        v___x_2772_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2772_, 0, v___x_2771_);
        return v___x_2772_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isPropFormerType___boxed(
    mut v_type_2773_: *mut leanh::LeanObject,
    mut v_a_2774_: *mut leanh::LeanObject,
    mut v_a_2775_: *mut leanh::LeanObject,
    mut v_a_2776_: *mut leanh::LeanObject,
    mut v_a_2777_: *mut leanh::LeanObject,
    mut v_a_2778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2779_ = l_Lean_Compiler_LCNF_isPropFormerType(
        v_type_2773_,
        v_a_2774_,
        v_a_2775_,
        v_a_2776_,
        v_a_2777_,
    );
    leanh::lean_dec(v_a_2777_);
    leanh::lean_dec_ref(v_a_2776_);
    leanh::lean_dec(v_a_2775_);
    leanh::lean_dec_ref(v_a_2774_);
    return v_res_2779_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isPropFormer(
    mut v_e_2780_: *mut leanh::LeanObject,
    mut v_a_2781_: *mut leanh::LeanObject,
    mut v_a_2782_: *mut leanh::LeanObject,
    mut v_a_2783_: *mut leanh::LeanObject,
    mut v_a_2784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2792_: u8 = 0;
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_2784_);
                leanh::lean_inc_ref(v_a_2783_);
                leanh::lean_inc(v_a_2782_);
                leanh::lean_inc_ref(v_a_2781_);
                v___x_2786_ =
                    lean_infer_type(v_e_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
                if leanh::lean_obj_tag(v___x_2786_) == 0 {
                    v_a_2787_ = leanh::lean_ctor_get(v___x_2786_, 0);
                    leanh::lean_inc(v_a_2787_);
                    leanh::lean_dec_ref_known(v___x_2786_, 1);
                    v___x_2788_ = l_Lean_Compiler_LCNF_isPropFormerType(
                        v_a_2787_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_,
                    );
                    return v___x_2788_;
                } else {
                    v_a_2789_ = leanh::lean_ctor_get(v___x_2786_, 0);
                    v_isSharedCheck_2796_ = (!leanh::lean_is_exclusive(v___x_2786_)) as u8;
                    if v_isSharedCheck_2796_ == 0 {
                        v___x_2791_ = v___x_2786_;
                        v_isShared_2792_ = v_isSharedCheck_2796_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2789_);
                        leanh::lean_dec(v___x_2786_);
                        v___x_2791_ = leanh::lean_box(0);
                        v_isShared_2792_ = v_isSharedCheck_2796_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2792_ == 0 {
                    v___x_2794_ = v___x_2791_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2795_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
                    v___x_2794_ = v_reuseFailAlloc_2795_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isPropFormer___boxed(
    mut v_e_2797_: *mut leanh::LeanObject,
    mut v_a_2798_: *mut leanh::LeanObject,
    mut v_a_2799_: *mut leanh::LeanObject,
    mut v_a_2800_: *mut leanh::LeanObject,
    mut v_a_2801_: *mut leanh::LeanObject,
    mut v_a_2802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2803_ =
        l_Lean_Compiler_LCNF_isPropFormer(v_e_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
    leanh::lean_dec(v_a_2801_);
    leanh::lean_dec_ref(v_a_2800_);
    leanh::lean_dec(v_a_2799_);
    leanh::lean_dec_ref(v_a_2798_);
    return v_res_2803_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0()
-> u64 {
    let mut v___x_2804_: u8 = 0;
    let mut v___x_2805_: u64 = 0;
    v___x_2804_ = 0;
    v___x_2805_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2804_);
    return v___x_2805_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(
    mut v_type_2806_: *mut leanh::LeanObject,
    mut v_a_2807_: *mut leanh::LeanObject,
    mut v_a_2808_: *mut leanh::LeanObject,
    mut v_a_2809_: *mut leanh::LeanObject,
    mut v_a_2810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2813_: u8 = 0;
    let mut v_ctxApprox_2814_: u8 = 0;
    let mut v_quasiPatternApprox_2815_: u8 = 0;
    let mut v_constApprox_2816_: u8 = 0;
    let mut v_isDefEqStuckEx_2817_: u8 = 0;
    let mut v_unificationHints_2818_: u8 = 0;
    let mut v_proofIrrelevance_2819_: u8 = 0;
    let mut v_assignSyntheticOpaque_2820_: u8 = 0;
    let mut v_offsetCnstrs_2821_: u8 = 0;
    let mut v_etaStruct_2822_: u8 = 0;
    let mut v_univApprox_2823_: u8 = 0;
    let mut v_iota_2824_: u8 = 0;
    let mut v_beta_2825_: u8 = 0;
    let mut v_proj_2826_: u8 = 0;
    let mut v_zeta_2827_: u8 = 0;
    let mut v_zetaDelta_2828_: u8 = 0;
    let mut v_zetaUnused_2829_: u8 = 0;
    let mut v_zetaHave_2830_: u8 = 0;
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2833_: u8 = 0;
    let mut v_trackZetaDelta_2834_: u8 = 0;
    let mut v_zetaDeltaSet_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2841_: u8 = 0;
    let mut v_inTypeClassResolution_2842_: u8 = 0;
    let mut v_cacheInferType_2843_: u8 = 0;
    let mut v___x_2844_: u8 = 0;
    let mut v_config_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: u64 = 0;
    let mut v___x_2848_: u64 = 0;
    let mut v___x_2849_: u64 = 0;
    let mut v___x_2850_: u64 = 0;
    let mut v___x_2851_: u64 = 0;
    let mut v_key_2852_: u64 = 0;
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: u8 = 0;
    let mut v_reuseFailAlloc_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2812_ = l_Lean_Meta_Context_config(v_a_2807_);
                v_foApprox_2813_ = leanh::lean_ctor_get_uint8(v___x_2812_, 0 as u32);
                v_ctxApprox_2814_ = leanh::lean_ctor_get_uint8(v___x_2812_, 1 as u32);
                v_quasiPatternApprox_2815_ =
                    leanh::lean_ctor_get_uint8(v___x_2812_, 2 as u32);
                v_constApprox_2816_ = leanh::lean_ctor_get_uint8(v___x_2812_, 3 as u32);
                v_isDefEqStuckEx_2817_ = leanh::lean_ctor_get_uint8(v___x_2812_, 4 as u32);
                v_unificationHints_2818_ = leanh::lean_ctor_get_uint8(v___x_2812_, 5 as u32);
                v_proofIrrelevance_2819_ = leanh::lean_ctor_get_uint8(v___x_2812_, 6 as u32);
                v_assignSyntheticOpaque_2820_ =
                    leanh::lean_ctor_get_uint8(v___x_2812_, 7 as u32);
                v_offsetCnstrs_2821_ = leanh::lean_ctor_get_uint8(v___x_2812_, 8 as u32);
                v_etaStruct_2822_ = leanh::lean_ctor_get_uint8(v___x_2812_, 10 as u32);
                v_univApprox_2823_ = leanh::lean_ctor_get_uint8(v___x_2812_, 11 as u32);
                v_iota_2824_ = leanh::lean_ctor_get_uint8(v___x_2812_, 12 as u32);
                v_beta_2825_ = leanh::lean_ctor_get_uint8(v___x_2812_, 13 as u32);
                v_proj_2826_ = leanh::lean_ctor_get_uint8(v___x_2812_, 14 as u32);
                v_zeta_2827_ = leanh::lean_ctor_get_uint8(v___x_2812_, 15 as u32);
                v_zetaDelta_2828_ = leanh::lean_ctor_get_uint8(v___x_2812_, 16 as u32);
                v_zetaUnused_2829_ = leanh::lean_ctor_get_uint8(v___x_2812_, 17 as u32);
                v_zetaHave_2830_ = leanh::lean_ctor_get_uint8(v___x_2812_, 18 as u32);
                v_isSharedCheck_2861_ = (!leanh::lean_is_exclusive(v___x_2812_)) as u8;
                if v_isSharedCheck_2861_ == 0 {
                    v___x_2832_ = v___x_2812_;
                    v_isShared_2833_ = v_isSharedCheck_2861_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2812_);
                    v___x_2832_ = leanh::lean_box(0);
                    v_isShared_2833_ = v_isSharedCheck_2861_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_2834_ = leanh::lean_ctor_get_uint8(
                    v_a_2807_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2835_ = leanh::lean_ctor_get(v_a_2807_, 1);
                v_lctx_2836_ = leanh::lean_ctor_get(v_a_2807_, 2);
                v_localInstances_2837_ = leanh::lean_ctor_get(v_a_2807_, 3);
                v_defEqCtx_x3f_2838_ = leanh::lean_ctor_get(v_a_2807_, 4);
                v_synthPendingDepth_2839_ = leanh::lean_ctor_get(v_a_2807_, 5);
                v_canUnfold_x3f_2840_ = leanh::lean_ctor_get(v_a_2807_, 6);
                v_univApprox_2841_ = leanh::lean_ctor_get_uint8(
                    v_a_2807_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2842_ = leanh::lean_ctor_get_uint8(
                    v_a_2807_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2843_ = leanh::lean_ctor_get_uint8(
                    v_a_2807_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2844_ = 0;
                if v_isShared_2833_ == 0 {
                    v_config_2846_ = v___x_2832_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        0 as u32,
                        v_foApprox_2813_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        1 as u32,
                        v_ctxApprox_2814_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        2 as u32,
                        v_quasiPatternApprox_2815_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        3 as u32,
                        v_constApprox_2816_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        4 as u32,
                        v_isDefEqStuckEx_2817_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        5 as u32,
                        v_unificationHints_2818_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        6 as u32,
                        v_proofIrrelevance_2819_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        7 as u32,
                        v_assignSyntheticOpaque_2820_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        8 as u32,
                        v_offsetCnstrs_2821_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        10 as u32,
                        v_etaStruct_2822_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        11 as u32,
                        v_univApprox_2823_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        12 as u32,
                        v_iota_2824_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        13 as u32,
                        v_beta_2825_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        14 as u32,
                        v_proj_2826_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        15 as u32,
                        v_zeta_2827_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        16 as u32,
                        v_zetaDelta_2828_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        17 as u32,
                        v_zetaUnused_2829_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2860_,
                        18 as u32,
                        v_zetaHave_2830_,
                    );
                    v_config_2846_ = v_reuseFailAlloc_2860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_2846_, 9 as u32, v___x_2844_);
                v___x_2847_ = l_Lean_Meta_Context_configKey(v_a_2807_);
                v___x_2848_ = 3u64;
                v___x_2849_ = lean_uint64_shift_right(v___x_2847_, v___x_2848_);
                v___x_2850_ = lean_uint64_shift_left(v___x_2849_, v___x_2848_);
                v___x_2851_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0_once), _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___closed__0);
                v_key_2852_ = lean_uint64_lor(v___x_2850_, v___x_2851_);
                v___x_2853_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2853_, 0, v_config_2846_);
                leanh::lean_ctor_set_uint64(
                    v___x_2853_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2852_,
                );
                leanh::lean_inc(v_canUnfold_x3f_2840_);
                leanh::lean_inc(v_synthPendingDepth_2839_);
                leanh::lean_inc(v_defEqCtx_x3f_2838_);
                leanh::lean_inc_ref(v_localInstances_2837_);
                leanh::lean_inc_ref(v_lctx_2836_);
                leanh::lean_inc(v_zetaDeltaSet_2835_);
                v___x_2854_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2854_, 0, v___x_2853_);
                leanh::lean_ctor_set(v___x_2854_, 1, v_zetaDeltaSet_2835_);
                leanh::lean_ctor_set(v___x_2854_, 2, v_lctx_2836_);
                leanh::lean_ctor_set(v___x_2854_, 3, v_localInstances_2837_);
                leanh::lean_ctor_set(v___x_2854_, 4, v_defEqCtx_x3f_2838_);
                leanh::lean_ctor_set(v___x_2854_, 5, v_synthPendingDepth_2839_);
                leanh::lean_ctor_set(v___x_2854_, 6, v_canUnfold_x3f_2840_);
                leanh::lean_ctor_set_uint8(
                    v___x_2854_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2834_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2854_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2841_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2854_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2842_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2854_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2843_,
                );
                leanh::lean_inc(v_a_2810_);
                leanh::lean_inc_ref(v_a_2809_);
                leanh::lean_inc(v_a_2808_);
                v___x_2855_ = lean_whnf(v_type_2806_, v___x_2854_, v_a_2808_, v_a_2809_, v_a_2810_);
                if leanh::lean_obj_tag(v___x_2855_) == 0 {
                    v_a_2856_ = leanh::lean_ctor_get(v___x_2855_, 0);
                    leanh::lean_inc_n(v_a_2856_, 2);
                    v___x_2857_ = l_Lean_Expr_eta(v_a_2856_);
                    v___x_2858_ = lean_expr_eqv(v___x_2857_, v_a_2856_);
                    leanh::lean_dec(v_a_2856_);
                    if v___x_2858_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2855_, 1);
                        v_type_2806_ = v___x_2857_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_2857_);
                        return v___x_2855_;
                    }
                } else {
                    return v___x_2855_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta___boxed(
    mut v_type_2862_: *mut leanh::LeanObject,
    mut v_a_2863_: *mut leanh::LeanObject,
    mut v_a_2864_: *mut leanh::LeanObject,
    mut v_a_2865_: *mut leanh::LeanObject,
    mut v_a_2866_: *mut leanh::LeanObject,
    mut v_a_2867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2868_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(
        v_type_2862_,
        v_a_2863_,
        v_a_2864_,
        v_a_2865_,
        v_a_2866_,
    );
    leanh::lean_dec(v_a_2866_);
    leanh::lean_dec_ref(v_a_2865_);
    leanh::lean_dec(v_a_2864_);
    leanh::lean_dec_ref(v_a_2863_);
    return v_res_2868_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(
    mut v_msgData_2869_: *mut leanh::LeanObject,
    mut v___y_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2875_ = lean_st_ref_get(v___y_2873_);
    v_env_2876_ = leanh::lean_ctor_get(v___x_2875_, 0);
    leanh::lean_inc_ref(v_env_2876_);
    leanh::lean_dec(v___x_2875_);
    v___x_2877_ = lean_st_ref_get(v___y_2871_);
    v_mctx_2878_ = leanh::lean_ctor_get(v___x_2877_, 0);
    leanh::lean_inc_ref(v_mctx_2878_);
    leanh::lean_dec(v___x_2877_);
    v_lctx_2879_ = leanh::lean_ctor_get(v___y_2870_, 2);
    v_options_2880_ = leanh::lean_ctor_get(v___y_2872_, 2);
    leanh::lean_inc_ref(v_options_2880_);
    leanh::lean_inc_ref(v_lctx_2879_);
    v___x_2881_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2881_, 0, v_env_2876_);
    leanh::lean_ctor_set(v___x_2881_, 1, v_mctx_2878_);
    leanh::lean_ctor_set(v___x_2881_, 2, v_lctx_2879_);
    leanh::lean_ctor_set(v___x_2881_, 3, v_options_2880_);
    v___x_2882_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2882_, 0, v___x_2881_);
    leanh::lean_ctor_set(v___x_2882_, 1, v_msgData_2869_);
    v___x_2883_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2883_, 0, v___x_2882_);
    return v___x_2883_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6___boxed(
    mut v_msgData_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
    mut v___y_2888_: *mut leanh::LeanObject,
    mut v___y_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2890_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msgData_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
    leanh::lean_dec(v___y_2888_);
    leanh::lean_dec_ref(v___y_2887_);
    leanh::lean_dec(v___y_2886_);
    leanh::lean_dec_ref(v___y_2885_);
    return v_res_2890_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(
    mut v_msg_2891_: *mut leanh::LeanObject,
    mut v___y_2892_: *mut leanh::LeanObject,
    mut v___y_2893_: *mut leanh::LeanObject,
    mut v___y_2894_: *mut leanh::LeanObject,
    mut v___y_2895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2897_ = leanh::lean_ctor_get(v___y_2894_, 5);
                v___x_2898_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5_spec__6(v_msg_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
                v_a_2899_ = leanh::lean_ctor_get(v___x_2898_, 0);
                v_isSharedCheck_2907_ = (!leanh::lean_is_exclusive(v___x_2898_)) as u8;
                if v_isSharedCheck_2907_ == 0 {
                    v___x_2901_ = v___x_2898_;
                    v_isShared_2902_ = v_isSharedCheck_2907_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2899_);
                    leanh::lean_dec(v___x_2898_);
                    v___x_2901_ = leanh::lean_box(0);
                    v_isShared_2902_ = v_isSharedCheck_2907_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2897_);
                v___x_2903_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2903_, 0, v_ref_2897_);
                leanh::lean_ctor_set(v___x_2903_, 1, v_a_2899_);
                if v_isShared_2902_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2901_, 1);
                    leanh::lean_ctor_set(v___x_2901_, 0, v___x_2903_);
                    v___x_2905_ = v___x_2901_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2906_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2903_);
                    v___x_2905_ = v_reuseFailAlloc_2906_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg___boxed(
    mut v_msg_2908_: *mut leanh::LeanObject,
    mut v___y_2909_: *mut leanh::LeanObject,
    mut v___y_2910_: *mut leanh::LeanObject,
    mut v___y_2911_: *mut leanh::LeanObject,
    mut v___y_2912_: *mut leanh::LeanObject,
    mut v___y_2913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2914_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
    leanh::lean_dec(v___y_2912_);
    leanh::lean_dec_ref(v___y_2911_);
    leanh::lean_dec(v___y_2910_);
    leanh::lean_dec_ref(v___y_2909_);
    return v_res_2914_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(
    mut v_ref_2915_: *mut leanh::LeanObject,
    mut v_msg_2916_: *mut leanh::LeanObject,
    mut v___y_2917_: *mut leanh::LeanObject,
    mut v___y_2918_: *mut leanh::LeanObject,
    mut v___y_2919_: *mut leanh::LeanObject,
    mut v___y_2920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2934_: u8 = 0;
    let mut v_cancelTk_x3f_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2936_: u8 = 0;
    let mut v_inheritedTraceOptions_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2922_ = leanh::lean_ctor_get(v___y_2919_, 0);
    v_fileMap_2923_ = leanh::lean_ctor_get(v___y_2919_, 1);
    v_options_2924_ = leanh::lean_ctor_get(v___y_2919_, 2);
    v_currRecDepth_2925_ = leanh::lean_ctor_get(v___y_2919_, 3);
    v_maxRecDepth_2926_ = leanh::lean_ctor_get(v___y_2919_, 4);
    v_ref_2927_ = leanh::lean_ctor_get(v___y_2919_, 5);
    v_currNamespace_2928_ = leanh::lean_ctor_get(v___y_2919_, 6);
    v_openDecls_2929_ = leanh::lean_ctor_get(v___y_2919_, 7);
    v_initHeartbeats_2930_ = leanh::lean_ctor_get(v___y_2919_, 8);
    v_maxHeartbeats_2931_ = leanh::lean_ctor_get(v___y_2919_, 9);
    v_quotContext_2932_ = leanh::lean_ctor_get(v___y_2919_, 10);
    v_currMacroScope_2933_ = leanh::lean_ctor_get(v___y_2919_, 11);
    v_diag_2934_ = leanh::lean_ctor_get_uint8(
        v___y_2919_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2935_ = leanh::lean_ctor_get(v___y_2919_, 12);
    v_suppressElabErrors_2936_ = leanh::lean_ctor_get_uint8(
        v___y_2919_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2937_ = leanh::lean_ctor_get(v___y_2919_, 13);
    v_ref_2938_ = l_Lean_replaceRef(v_ref_2915_, v_ref_2927_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_2937_);
    leanh::lean_inc(v_cancelTk_x3f_2935_);
    leanh::lean_inc(v_currMacroScope_2933_);
    leanh::lean_inc(v_quotContext_2932_);
    leanh::lean_inc(v_maxHeartbeats_2931_);
    leanh::lean_inc(v_initHeartbeats_2930_);
    leanh::lean_inc(v_openDecls_2929_);
    leanh::lean_inc(v_currNamespace_2928_);
    leanh::lean_inc(v_maxRecDepth_2926_);
    leanh::lean_inc(v_currRecDepth_2925_);
    leanh::lean_inc_ref(v_options_2924_);
    leanh::lean_inc_ref(v_fileMap_2923_);
    leanh::lean_inc_ref(v_fileName_2922_);
    v___x_2939_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_2939_, 0, v_fileName_2922_);
    leanh::lean_ctor_set(v___x_2939_, 1, v_fileMap_2923_);
    leanh::lean_ctor_set(v___x_2939_, 2, v_options_2924_);
    leanh::lean_ctor_set(v___x_2939_, 3, v_currRecDepth_2925_);
    leanh::lean_ctor_set(v___x_2939_, 4, v_maxRecDepth_2926_);
    leanh::lean_ctor_set(v___x_2939_, 5, v_ref_2938_);
    leanh::lean_ctor_set(v___x_2939_, 6, v_currNamespace_2928_);
    leanh::lean_ctor_set(v___x_2939_, 7, v_openDecls_2929_);
    leanh::lean_ctor_set(v___x_2939_, 8, v_initHeartbeats_2930_);
    leanh::lean_ctor_set(v___x_2939_, 9, v_maxHeartbeats_2931_);
    leanh::lean_ctor_set(v___x_2939_, 10, v_quotContext_2932_);
    leanh::lean_ctor_set(v___x_2939_, 11, v_currMacroScope_2933_);
    leanh::lean_ctor_set(v___x_2939_, 12, v_cancelTk_x3f_2935_);
    leanh::lean_ctor_set(v___x_2939_, 13, v_inheritedTraceOptions_2937_);
    leanh::lean_ctor_set_uint8(
        v___x_2939_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_2934_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2939_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2936_,
    );
    v___x_2940_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_2916_, v___y_2917_, v___y_2918_, v___x_2939_, v___y_2920_);
    leanh::lean_dec_ref_known(v___x_2939_, 14);
    return v___x_2940_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg___boxed(
    mut v_ref_2941_: *mut leanh::LeanObject,
    mut v_msg_2942_: *mut leanh::LeanObject,
    mut v___y_2943_: *mut leanh::LeanObject,
    mut v___y_2944_: *mut leanh::LeanObject,
    mut v___y_2945_: *mut leanh::LeanObject,
    mut v___y_2946_: *mut leanh::LeanObject,
    mut v___y_2947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2948_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_2941_, v_msg_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
    leanh::lean_dec(v___y_2946_);
    leanh::lean_dec_ref(v___y_2945_);
    leanh::lean_dec(v___y_2944_);
    leanh::lean_dec_ref(v___y_2943_);
    leanh::lean_dec(v_ref_2941_);
    return v_res_2948_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2949_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2949_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2950_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__0);
    v___x_2951_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2951_, 0, v___x_2950_);
    return v___x_2951_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2952_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
    v___x_2953_ = leanh::lean_unsigned_to_nat(0);
    v___x_2954_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2954_, 0, v___x_2953_);
    leanh::lean_ctor_set(v___x_2954_, 1, v___x_2953_);
    leanh::lean_ctor_set(v___x_2954_, 2, v___x_2953_);
    leanh::lean_ctor_set(v___x_2954_, 3, v___x_2953_);
    leanh::lean_ctor_set(v___x_2954_, 4, v___x_2952_);
    leanh::lean_ctor_set(v___x_2954_, 5, v___x_2952_);
    leanh::lean_ctor_set(v___x_2954_, 6, v___x_2952_);
    leanh::lean_ctor_set(v___x_2954_, 7, v___x_2952_);
    leanh::lean_ctor_set(v___x_2954_, 8, v___x_2952_);
    leanh::lean_ctor_set(v___x_2954_, 9, v___x_2952_);
    return v___x_2954_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2955_ = leanh::lean_unsigned_to_nat(32);
    v___x_2956_ = lean_mk_empty_array_with_capacity(v___x_2955_);
    v___x_2957_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2957_, 0, v___x_2956_);
    return v___x_2957_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2958_: usize = 0;
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2958_ = 5usize;
    v___x_2959_ = leanh::lean_unsigned_to_nat(0);
    v___x_2960_ = leanh::lean_unsigned_to_nat(32);
    v___x_2961_ = lean_mk_empty_array_with_capacity(v___x_2960_);
    v___x_2962_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__3);
    v___x_2963_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2963_, 0, v___x_2962_);
    leanh::lean_ctor_set(v___x_2963_, 1, v___x_2961_);
    leanh::lean_ctor_set(v___x_2963_, 2, v___x_2959_);
    leanh::lean_ctor_set(v___x_2963_, 3, v___x_2959_);
    leanh::lean_ctor_set_usize(v___x_2963_, 4, v___x_2958_);
    return v___x_2963_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2964_ = leanh::lean_box(1);
    v___x_2965_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__4);
    v___x_2966_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__1);
    v___x_2967_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2967_, 0, v___x_2966_);
    leanh::lean_ctor_set(v___x_2967_, 1, v___x_2965_);
    leanh::lean_ctor_set(v___x_2967_, 2, v___x_2964_);
    return v___x_2967_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2969_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__6;
    v___x_2970_ = l_Lean_stringToMessageData(v___x_2969_);
    return v___x_2970_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2972_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__8;
    v___x_2973_ = l_Lean_stringToMessageData(v___x_2972_);
    return v___x_2973_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2975_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__10;
    v___x_2976_ = l_Lean_stringToMessageData(v___x_2975_);
    return v___x_2976_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2978_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__12;
    v___x_2979_ = l_Lean_stringToMessageData(v___x_2978_);
    return v___x_2979_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2981_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__14;
    v___x_2982_ = l_Lean_stringToMessageData(v___x_2981_);
    return v___x_2982_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2984_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__16;
    v___x_2985_ = l_Lean_stringToMessageData(v___x_2984_);
    return v___x_2985_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2987_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__18;
    v___x_2988_ = l_Lean_stringToMessageData(v___x_2987_);
    return v___x_2988_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(
    mut v_msg_2989_: *mut leanh::LeanObject,
    mut v_declHint_2990_: *mut leanh::LeanObject,
    mut v___y_2991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: u8 = 0;
    let mut v_isExporting_2996_: u8 = 0;
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: u8 = 0;
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: u8 = 0;
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2993_ = lean_st_ref_get(v___y_2991_);
                v_env_2994_ = leanh::lean_ctor_get(v___x_2993_, 0);
                leanh::lean_inc_ref(v_env_2994_);
                leanh::lean_dec(v___x_2993_);
                v___x_2995_ = l_Lean_Name_isAnonymous(v_declHint_2990_);
                if v___x_2995_ == 0 {
                    v_isExporting_2996_ = leanh::lean_ctor_get_uint8(
                        v_env_2994_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2996_ == 0 {
                        leanh::lean_dec_ref(v_env_2994_);
                        leanh::lean_dec(v_declHint_2990_);
                        v___x_2997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2997_, 0, v_msg_2989_);
                        return v___x_2997_;
                    } else {
                        leanh::lean_inc_ref(v_env_2994_);
                        v___x_2998_ = l_Lean_Environment_setExporting(v_env_2994_, v___x_2995_);
                        leanh::lean_inc(v_declHint_2990_);
                        leanh::lean_inc_ref(v___x_2998_);
                        v___x_2999_ = l_Lean_Environment_contains(
                            v___x_2998_,
                            v_declHint_2990_,
                            v_isExporting_2996_,
                        );
                        if v___x_2999_ == 0 {
                            leanh::lean_dec_ref(v___x_2998_);
                            leanh::lean_dec_ref(v_env_2994_);
                            leanh::lean_dec(v_declHint_2990_);
                            v___x_3000_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3000_, 0, v_msg_2989_);
                            return v___x_3000_;
                        } else {
                            v___x_3001_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
                            v___x_3002_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
                            v___x_3003_ = l_Lean_Options_empty;
                            v___x_3004_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3004_, 0, v___x_2998_);
                            leanh::lean_ctor_set(v___x_3004_, 1, v___x_3001_);
                            leanh::lean_ctor_set(v___x_3004_, 2, v___x_3002_);
                            leanh::lean_ctor_set(v___x_3004_, 3, v___x_3003_);
                            leanh::lean_inc(v_declHint_2990_);
                            v___x_3005_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2990_, v___x_2995_);
                            v_c_3006_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3006_, 0, v___x_3004_);
                            leanh::lean_ctor_set(v_c_3006_, 1, v___x_3005_);
                            v___x_3007_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2994_,
                                v_declHint_2990_,
                            );
                            if leanh::lean_obj_tag(v___x_3007_) == 0 {
                                leanh::lean_dec_ref(v_env_2994_);
                                leanh::lean_dec(v_declHint_2990_);
                                v___x_3008_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
                                v___x_3009_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3009_, 0, v___x_3008_);
                                leanh::lean_ctor_set(v___x_3009_, 1, v_c_3006_);
                                v___x_3010_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__9);
                                v___x_3011_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3011_, 0, v___x_3009_);
                                leanh::lean_ctor_set(v___x_3011_, 1, v___x_3010_);
                                v___x_3012_ = l_Lean_MessageData_note(v___x_3011_);
                                v___x_3013_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3013_, 0, v_msg_2989_);
                                leanh::lean_ctor_set(v___x_3013_, 1, v___x_3012_);
                                v___x_3014_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3014_, 0, v___x_3013_);
                                return v___x_3014_;
                            } else {
                                v_val_3015_ = leanh::lean_ctor_get(v___x_3007_, 0);
                                v_isSharedCheck_3050_ =
                                    (!leanh::lean_is_exclusive(v___x_3007_)) as u8;
                                if v_isSharedCheck_3050_ == 0 {
                                    v___x_3017_ = v___x_3007_;
                                    v_isShared_3018_ = v_isSharedCheck_3050_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3015_);
                                    leanh::lean_dec(v___x_3007_);
                                    v___x_3017_ = leanh::lean_box(0);
                                    v_isShared_3018_ = v_isSharedCheck_3050_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2994_);
                    leanh::lean_dec(v_declHint_2990_);
                    v___x_3051_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3051_, 0, v_msg_2989_);
                    return v___x_3051_;
                }
            }
            1 => {
                v___x_3019_ = leanh::lean_box(0);
                v___x_3020_ = l_Lean_Environment_header(v_env_2994_);
                leanh::lean_dec_ref(v_env_2994_);
                v___x_3021_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3020_);
                v_mod_3022_ = lean_array_get(v___x_3019_, v___x_3021_, v_val_3015_);
                leanh::lean_dec(v_val_3015_);
                leanh::lean_dec_ref(v___x_3021_);
                v___x_3023_ = l_Lean_isPrivateName(v_declHint_2990_);
                leanh::lean_dec(v_declHint_2990_);
                if v___x_3023_ == 0 {
                    v___x_3024_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__11);
                    v___x_3025_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3025_, 0, v___x_3024_);
                    leanh::lean_ctor_set(v___x_3025_, 1, v_c_3006_);
                    v___x_3026_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__13);
                    v___x_3027_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3027_, 0, v___x_3025_);
                    leanh::lean_ctor_set(v___x_3027_, 1, v___x_3026_);
                    v___x_3028_ = l_Lean_MessageData_ofName(v_mod_3022_);
                    v___x_3029_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3029_, 0, v___x_3027_);
                    leanh::lean_ctor_set(v___x_3029_, 1, v___x_3028_);
                    v___x_3030_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__15);
                    v___x_3031_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3031_, 0, v___x_3029_);
                    leanh::lean_ctor_set(v___x_3031_, 1, v___x_3030_);
                    v___x_3032_ = l_Lean_MessageData_note(v___x_3031_);
                    v___x_3033_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3033_, 0, v_msg_2989_);
                    leanh::lean_ctor_set(v___x_3033_, 1, v___x_3032_);
                    if v_isShared_3018_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3017_, 0);
                        leanh::lean_ctor_set(v___x_3017_, 0, v___x_3033_);
                        v___x_3035_ = v___x_3017_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3036_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
                        v___x_3035_ = v_reuseFailAlloc_3036_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3037_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__7);
                    v___x_3038_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3038_, 0, v___x_3037_);
                    leanh::lean_ctor_set(v___x_3038_, 1, v_c_3006_);
                    v___x_3039_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__17);
                    v___x_3040_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3040_, 0, v___x_3038_);
                    leanh::lean_ctor_set(v___x_3040_, 1, v___x_3039_);
                    v___x_3041_ = l_Lean_MessageData_ofName(v_mod_3022_);
                    v___x_3042_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3042_, 0, v___x_3040_);
                    leanh::lean_ctor_set(v___x_3042_, 1, v___x_3041_);
                    v___x_3043_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__19);
                    v___x_3044_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3044_, 0, v___x_3042_);
                    leanh::lean_ctor_set(v___x_3044_, 1, v___x_3043_);
                    v___x_3045_ = l_Lean_MessageData_note(v___x_3044_);
                    v___x_3046_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3046_, 0, v_msg_2989_);
                    leanh::lean_ctor_set(v___x_3046_, 1, v___x_3045_);
                    if v_isShared_3018_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3017_, 0);
                        leanh::lean_ctor_set(v___x_3017_, 0, v___x_3046_);
                        v___x_3048_ = v___x_3017_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3049_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
                        v___x_3048_ = v_reuseFailAlloc_3049_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3035_;
            }
            3 => {
                return v___x_3048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___boxed(
    mut v_msg_3052_: *mut leanh::LeanObject,
    mut v_declHint_3053_: *mut leanh::LeanObject,
    mut v___y_3054_: *mut leanh::LeanObject,
    mut v___y_3055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_3052_, v_declHint_3053_, v___y_3054_);
    leanh::lean_dec(v___y_3054_);
    return v_res_3056_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(
    mut v_msg_3057_: *mut leanh::LeanObject,
    mut v_declHint_3058_: *mut leanh::LeanObject,
    mut v___y_3059_: *mut leanh::LeanObject,
    mut v___y_3060_: *mut leanh::LeanObject,
    mut v___y_3061_: *mut leanh::LeanObject,
    mut v___y_3062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3068_: u8 = 0;
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3064_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_3057_, v_declHint_3058_, v___y_3062_);
                v_a_3065_ = leanh::lean_ctor_get(v___x_3064_, 0);
                v_isSharedCheck_3074_ = (!leanh::lean_is_exclusive(v___x_3064_)) as u8;
                if v_isSharedCheck_3074_ == 0 {
                    v___x_3067_ = v___x_3064_;
                    v_isShared_3068_ = v_isSharedCheck_3074_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3065_);
                    leanh::lean_dec(v___x_3064_);
                    v___x_3067_ = leanh::lean_box(0);
                    v_isShared_3068_ = v_isSharedCheck_3074_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3069_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3070_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3070_, 0, v___x_3069_);
                leanh::lean_ctor_set(v___x_3070_, 1, v_a_3065_);
                if v_isShared_3068_ == 0 {
                    leanh::lean_ctor_set(v___x_3067_, 0, v___x_3070_);
                    v___x_3072_ = v___x_3067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3073_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3070_);
                    v___x_3072_ = v_reuseFailAlloc_3073_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9___boxed(
    mut v_msg_3075_: *mut leanh::LeanObject,
    mut v_declHint_3076_: *mut leanh::LeanObject,
    mut v___y_3077_: *mut leanh::LeanObject,
    mut v___y_3078_: *mut leanh::LeanObject,
    mut v___y_3079_: *mut leanh::LeanObject,
    mut v___y_3080_: *mut leanh::LeanObject,
    mut v___y_3081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3082_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_3075_, v_declHint_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
    leanh::lean_dec(v___y_3080_);
    leanh::lean_dec_ref(v___y_3079_);
    leanh::lean_dec(v___y_3078_);
    leanh::lean_dec_ref(v___y_3077_);
    return v_res_3082_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(
    mut v_ref_3083_: *mut leanh::LeanObject,
    mut v_msg_3084_: *mut leanh::LeanObject,
    mut v_declHint_3085_: *mut leanh::LeanObject,
    mut v___y_3086_: *mut leanh::LeanObject,
    mut v___y_3087_: *mut leanh::LeanObject,
    mut v___y_3088_: *mut leanh::LeanObject,
    mut v___y_3089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3091_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9(v_msg_3084_, v_declHint_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
    v_a_3092_ = leanh::lean_ctor_get(v___x_3091_, 0);
    leanh::lean_inc(v_a_3092_);
    leanh::lean_dec_ref(v___x_3091_);
    v___x_3093_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_3083_, v_a_3092_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg___boxed(
    mut v_ref_3094_: *mut leanh::LeanObject,
    mut v_msg_3095_: *mut leanh::LeanObject,
    mut v_declHint_3096_: *mut leanh::LeanObject,
    mut v___y_3097_: *mut leanh::LeanObject,
    mut v___y_3098_: *mut leanh::LeanObject,
    mut v___y_3099_: *mut leanh::LeanObject,
    mut v___y_3100_: *mut leanh::LeanObject,
    mut v___y_3101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3102_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_3094_, v_msg_3095_, v_declHint_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
    leanh::lean_dec(v___y_3100_);
    leanh::lean_dec_ref(v___y_3099_);
    leanh::lean_dec(v___y_3098_);
    leanh::lean_dec_ref(v___y_3097_);
    leanh::lean_dec(v_ref_3094_);
    return v_res_3102_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3104_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__0;
    v___x_3105_ = l_Lean_stringToMessageData(v___x_3104_);
    return v___x_3105_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3107_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__2;
    v___x_3108_ = l_Lean_stringToMessageData(v___x_3107_);
    return v___x_3108_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(
    mut v_ref_3109_: *mut leanh::LeanObject,
    mut v_constName_3110_: *mut leanh::LeanObject,
    mut v___y_3111_: *mut leanh::LeanObject,
    mut v___y_3112_: *mut leanh::LeanObject,
    mut v___y_3113_: *mut leanh::LeanObject,
    mut v___y_3114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3116_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__1);
    v___x_3117_ = 0;
    leanh::lean_inc(v_constName_3110_);
    v___x_3118_ = l_Lean_MessageData_ofConstName(v_constName_3110_, v___x_3117_);
    v___x_3119_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3119_, 0, v___x_3116_);
    leanh::lean_ctor_set(v___x_3119_, 1, v___x_3118_);
    v___x_3120_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___closed__3);
    v___x_3121_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3121_, 0, v___x_3119_);
    leanh::lean_ctor_set(v___x_3121_, 1, v___x_3120_);
    v___x_3122_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_3109_, v___x_3121_, v_constName_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
    return v___x_3122_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg___boxed(
    mut v_ref_3123_: *mut leanh::LeanObject,
    mut v_constName_3124_: *mut leanh::LeanObject,
    mut v___y_3125_: *mut leanh::LeanObject,
    mut v___y_3126_: *mut leanh::LeanObject,
    mut v___y_3127_: *mut leanh::LeanObject,
    mut v___y_3128_: *mut leanh::LeanObject,
    mut v___y_3129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3130_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_3123_, v_constName_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
    leanh::lean_dec(v___y_3128_);
    leanh::lean_dec_ref(v___y_3127_);
    leanh::lean_dec(v___y_3126_);
    leanh::lean_dec_ref(v___y_3125_);
    leanh::lean_dec(v_ref_3123_);
    return v_res_3130_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(
    mut v_constName_3131_: *mut leanh::LeanObject,
    mut v___y_3132_: *mut leanh::LeanObject,
    mut v___y_3133_: *mut leanh::LeanObject,
    mut v___y_3134_: *mut leanh::LeanObject,
    mut v___y_3135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_3137_ = leanh::lean_ctor_get(v___y_3134_, 5);
    v___x_3138_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_3137_, v_constName_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
    return v___x_3138_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg___boxed(
    mut v_constName_3139_: *mut leanh::LeanObject,
    mut v___y_3140_: *mut leanh::LeanObject,
    mut v___y_3141_: *mut leanh::LeanObject,
    mut v___y_3142_: *mut leanh::LeanObject,
    mut v___y_3143_: *mut leanh::LeanObject,
    mut v___y_3144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3145_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
    leanh::lean_dec(v___y_3143_);
    leanh::lean_dec_ref(v___y_3142_);
    leanh::lean_dec(v___y_3141_);
    leanh::lean_dec_ref(v___y_3140_);
    return v_res_3145_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(
    mut v_constName_3146_: *mut leanh::LeanObject,
    mut v___y_3147_: *mut leanh::LeanObject,
    mut v___y_3148_: *mut leanh::LeanObject,
    mut v___y_3149_: *mut leanh::LeanObject,
    mut v___y_3150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: u8 = 0;
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3160_: u8 = 0;
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3152_ = lean_st_ref_get(v___y_3150_);
                v_env_3153_ = leanh::lean_ctor_get(v___x_3152_, 0);
                leanh::lean_inc_ref(v_env_3153_);
                leanh::lean_dec(v___x_3152_);
                v___x_3154_ = 0;
                leanh::lean_inc(v_constName_3146_);
                v___x_3155_ =
                    l_Lean_Environment_find_x3f(v_env_3153_, v_constName_3146_, v___x_3154_);
                if leanh::lean_obj_tag(v___x_3155_) == 0 {
                    v___x_3156_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
                    return v___x_3156_;
                } else {
                    leanh::lean_dec(v_constName_3146_);
                    v_val_3157_ = leanh::lean_ctor_get(v___x_3155_, 0);
                    v_isSharedCheck_3164_ = (!leanh::lean_is_exclusive(v___x_3155_)) as u8;
                    if v_isSharedCheck_3164_ == 0 {
                        v___x_3159_ = v___x_3155_;
                        v_isShared_3160_ = v_isSharedCheck_3164_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3157_);
                        leanh::lean_dec(v___x_3155_);
                        v___x_3159_ = leanh::lean_box(0);
                        v_isShared_3160_ = v_isSharedCheck_3164_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3160_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3159_, 0);
                    v___x_3162_ = v___x_3159_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3163_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_val_3157_);
                    v___x_3162_ = v_reuseFailAlloc_3163_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4___boxed(
    mut v_constName_3165_: *mut leanh::LeanObject,
    mut v___y_3166_: *mut leanh::LeanObject,
    mut v___y_3167_: *mut leanh::LeanObject,
    mut v___y_3168_: *mut leanh::LeanObject,
    mut v___y_3169_: *mut leanh::LeanObject,
    mut v___y_3170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3171_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_constName_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
    leanh::lean_dec(v___y_3169_);
    leanh::lean_dec_ref(v___y_3168_);
    leanh::lean_dec(v___y_3167_);
    leanh::lean_dec_ref(v___y_3166_);
    return v_res_3171_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(
    mut v_binderType_3172_: *mut leanh::LeanObject,
    mut v_body_3173_: *mut leanh::LeanObject,
    mut v_binderName_3174_: *mut leanh::LeanObject,
    mut v_binderInfo_3175_: u8,
    mut v_x_3176_: *mut leanh::LeanObject,
    mut v___y_3177_: *mut leanh::LeanObject,
    mut v___y_3178_: *mut leanh::LeanObject,
    mut v___y_3179_: *mut leanh::LeanObject,
    mut v___y_3180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u8 = 0;
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut v_unused_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3182_ =
                    l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(
                        v_binderType_3172_,
                        v___y_3177_,
                        v___y_3178_,
                        v___y_3179_,
                        v___y_3180_,
                    );
                if leanh::lean_obj_tag(v___x_3182_) == 0 {
                    v_a_3183_ = leanh::lean_ctor_get(v___x_3182_, 0);
                    leanh::lean_inc(v_a_3183_);
                    leanh::lean_dec_ref_known(v___x_3182_, 1);
                    v___x_3184_ = lean_expr_instantiate1(v_body_3173_, v_x_3176_);
                    v___x_3185_ =
                        l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(
                            v___x_3184_,
                            v___y_3177_,
                            v___y_3178_,
                            v___y_3179_,
                            v___y_3180_,
                        );
                    if leanh::lean_obj_tag(v___x_3185_) == 0 {
                        v_a_3186_ = leanh::lean_ctor_get(v___x_3185_, 0);
                        leanh::lean_inc(v_a_3186_);
                        v___x_3187_ = l_Lean_Expr_isErased(v_a_3186_);
                        if v___x_3187_ == 0 {
                            v_isSharedCheck_3199_ =
                                (!leanh::lean_is_exclusive(v___x_3185_)) as u8;
                            if v_isSharedCheck_3199_ == 0 {
                                v_unused_3200_ = leanh::lean_ctor_get(v___x_3185_, 0);
                                leanh::lean_dec(v_unused_3200_);
                                v___x_3189_ = v___x_3185_;
                                v_isShared_3190_ = v_isSharedCheck_3199_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3185_);
                                v___x_3189_ = leanh::lean_box(0);
                                v_isShared_3190_ = v_isSharedCheck_3199_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3186_);
                            leanh::lean_dec(v_a_3183_);
                            leanh::lean_dec_ref(v_x_3176_);
                            leanh::lean_dec(v_binderName_3174_);
                            return v___x_3185_;
                        }
                    } else {
                        leanh::lean_dec(v_a_3183_);
                        leanh::lean_dec_ref(v_x_3176_);
                        leanh::lean_dec(v_binderName_3174_);
                        return v___x_3185_;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_3176_);
                    leanh::lean_dec(v_binderName_3174_);
                    return v___x_3182_;
                }
            }
            1 => {
                v___x_3191_ = leanh::lean_unsigned_to_nat(1);
                v___x_3192_ = lean_mk_empty_array_with_capacity(v___x_3191_);
                v___x_3193_ = lean_array_push(v___x_3192_, v_x_3176_);
                v___x_3194_ = lean_expr_abstract(v_a_3186_, v___x_3193_);
                leanh::lean_dec_ref(v___x_3193_);
                leanh::lean_dec(v_a_3186_);
                v___x_3195_ = l_Lean_Expr_lam___override(
                    v_binderName_3174_,
                    v_a_3183_,
                    v___x_3194_,
                    v_binderInfo_3175_,
                );
                if v_isShared_3190_ == 0 {
                    leanh::lean_ctor_set(v___x_3189_, 0, v___x_3195_);
                    v___x_3197_ = v___x_3189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3198_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
                    v___x_3197_ = v_reuseFailAlloc_3198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed(
    mut v_binderType_3201_: *mut leanh::LeanObject,
    mut v_body_3202_: *mut leanh::LeanObject,
    mut v_binderName_3203_: *mut leanh::LeanObject,
    mut v_binderInfo_3204_: *mut leanh::LeanObject,
    mut v_x_3205_: *mut leanh::LeanObject,
    mut v___y_3206_: *mut leanh::LeanObject,
    mut v___y_3207_: *mut leanh::LeanObject,
    mut v___y_3208_: *mut leanh::LeanObject,
    mut v___y_3209_: *mut leanh::LeanObject,
    mut v___y_3210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_9702__boxed_3211_: u8 = 0;
    let mut v_res_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_9702__boxed_3211_ = (leanh::lean_unbox(v_binderInfo_3204_) as u8);
    v_res_3212_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0(
        v_binderType_3201_,
        v_body_3202_,
        v_binderName_3203_,
        v_binderInfo_9702__boxed_3211_,
        v_x_3205_,
        v___y_3206_,
        v___y_3207_,
        v___y_3208_,
        v___y_3209_,
    );
    leanh::lean_dec(v___y_3209_);
    leanh::lean_dec_ref(v___y_3208_);
    leanh::lean_dec(v___y_3207_);
    leanh::lean_dec_ref(v___y_3206_);
    leanh::lean_dec_ref(v_body_3202_);
    return v_res_3212_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(
    mut v_d_3213_: *mut leanh::LeanObject,
    mut v_xs_3214_: *mut leanh::LeanObject,
    mut v_body_3215_: *mut leanh::LeanObject,
    mut v_binderName_3216_: *mut leanh::LeanObject,
    mut v_binderInfo_3217_: u8,
    mut v_x_3218_: *mut leanh::LeanObject,
    mut v___y_3219_: *mut leanh::LeanObject,
    mut v___y_3220_: *mut leanh::LeanObject,
    mut v___y_3221_: *mut leanh::LeanObject,
    mut v___y_3222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isBorrowed_3224_: u8 = 0;
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3238_: u8 = 0;
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3243_: u8 = 0;
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isBorrowed_3224_ = l_Lean_isMarkedBorrowed(v_d_3213_);
                v___x_3225_ =
                    l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(
                        v_d_3213_,
                        v___y_3219_,
                        v___y_3220_,
                        v___y_3221_,
                        v___y_3222_,
                    );
                if leanh::lean_obj_tag(v___x_3225_) == 0 {
                    v_a_3226_ = leanh::lean_ctor_get(v___x_3225_, 0);
                    leanh::lean_inc(v_a_3226_);
                    leanh::lean_dec_ref_known(v___x_3225_, 1);
                    v___x_3244_ = lean_expr_abstract(v_a_3226_, v_xs_3214_);
                    leanh::lean_dec(v_a_3226_);
                    if v_isBorrowed_3224_ == 0 {
                        v_d_3228_ = v___x_3244_;
                        v___y_3229_ = v___y_3219_;
                        v___y_3230_ = v___y_3220_;
                        v___y_3231_ = v___y_3221_;
                        v___y_3232_ = v___y_3222_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3245_ = l_Lean_markBorrowed(v___x_3244_);
                        v_d_3228_ = v___x_3245_;
                        v___y_3229_ = v___y_3219_;
                        v___y_3230_ = v___y_3220_;
                        v___y_3231_ = v___y_3221_;
                        v___y_3232_ = v___y_3222_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_3218_);
                    leanh::lean_dec(v_binderName_3216_);
                    leanh::lean_dec_ref(v_body_3215_);
                    leanh::lean_dec_ref(v_xs_3214_);
                    return v___x_3225_;
                }
            }
            1 => {
                v___x_3233_ = lean_array_push(v_xs_3214_, v_x_3218_);
                v___x_3234_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_body_3215_, v___x_3233_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
                if leanh::lean_obj_tag(v___x_3234_) == 0 {
                    v_a_3235_ = leanh::lean_ctor_get(v___x_3234_, 0);
                    v_isSharedCheck_3243_ = (!leanh::lean_is_exclusive(v___x_3234_)) as u8;
                    if v_isSharedCheck_3243_ == 0 {
                        v___x_3237_ = v___x_3234_;
                        v_isShared_3238_ = v_isSharedCheck_3243_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3235_);
                        leanh::lean_dec(v___x_3234_);
                        v___x_3237_ = leanh::lean_box(0);
                        v_isShared_3238_ = v_isSharedCheck_3243_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_d_3228_);
                    leanh::lean_dec(v_binderName_3216_);
                    return v___x_3234_;
                }
            }
            2 => {
                v___x_3239_ = l_Lean_Expr_forallE___override(
                    v_binderName_3216_,
                    v_d_3228_,
                    v_a_3235_,
                    v_binderInfo_3217_,
                );
                if v_isShared_3238_ == 0 {
                    leanh::lean_ctor_set(v___x_3237_, 0, v___x_3239_);
                    v___x_3241_ = v___x_3237_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3242_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
                    v___x_3241_ = v_reuseFailAlloc_3242_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed(
    mut v_d_3246_: *mut leanh::LeanObject,
    mut v_xs_3247_: *mut leanh::LeanObject,
    mut v_body_3248_: *mut leanh::LeanObject,
    mut v_binderName_3249_: *mut leanh::LeanObject,
    mut v_binderInfo_3250_: *mut leanh::LeanObject,
    mut v_x_3251_: *mut leanh::LeanObject,
    mut v___y_3252_: *mut leanh::LeanObject,
    mut v___y_3253_: *mut leanh::LeanObject,
    mut v___y_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
    mut v___y_3256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_9724__boxed_3257_: u8 = 0;
    let mut v_res_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_9724__boxed_3257_ = (leanh::lean_unbox(v_binderInfo_3250_) as u8);
    v_res_3258_ =
        l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0(
            v_d_3246_,
            v_xs_3247_,
            v_body_3248_,
            v_binderName_3249_,
            v_binderInfo_9724__boxed_3257_,
            v_x_3251_,
            v___y_3252_,
            v___y_3253_,
            v___y_3254_,
            v___y_3255_,
        );
    leanh::lean_dec(v___y_3255_);
    leanh::lean_dec_ref(v___y_3254_);
    leanh::lean_dec(v___y_3253_);
    leanh::lean_dec_ref(v___y_3252_);
    return v_res_3258_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(
    mut v_e_3259_: *mut leanh::LeanObject,
    mut v_xs_3260_: *mut leanh::LeanObject,
    mut v_a_3261_: *mut leanh::LeanObject,
    mut v_a_3262_: *mut leanh::LeanObject,
    mut v_a_3263_: *mut leanh::LeanObject,
    mut v_a_3264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderName_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3269_: u8 = 0;
    let mut v_d_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: u8 = 0;
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3280_: u8 = 0;
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_3259_) == 7 {
                    v_binderName_3266_ = leanh::lean_ctor_get(v_e_3259_, 0);
                    leanh::lean_inc_n(v_binderName_3266_, 2);
                    v_binderType_3267_ = leanh::lean_ctor_get(v_e_3259_, 1);
                    leanh::lean_inc_ref(v_binderType_3267_);
                    v_body_3268_ = leanh::lean_ctor_get(v_e_3259_, 2);
                    leanh::lean_inc_ref(v_body_3268_);
                    v_binderInfo_3269_ = leanh::lean_ctor_get_uint8(
                        v_e_3259_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_dec_ref_known(v_e_3259_, 3);
                    v_d_3270_ = lean_expr_instantiate_rev(v_binderType_3267_, v_xs_3260_);
                    leanh::lean_dec_ref(v_binderType_3267_);
                    v___x_3271_ = leanh::lean_box((v_binderInfo_3269_) as usize);
                    leanh::lean_inc_ref(v_d_3270_);
                    v___f_3272_ = leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                    leanh::lean_closure_set(v___f_3272_, 0, v_d_3270_);
                    leanh::lean_closure_set(v___f_3272_, 1, v_xs_3260_);
                    leanh::lean_closure_set(v___f_3272_, 2, v_body_3268_);
                    leanh::lean_closure_set(v___f_3272_, 3, v_binderName_3266_);
                    leanh::lean_closure_set(v___f_3272_, 4, v___x_3271_);
                    v___x_3273_ = 0;
                    v___x_3274_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_3266_, v_binderInfo_3269_, v_d_3270_, v___f_3272_, v___x_3273_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
                    return v___x_3274_;
                } else {
                    v___x_3275_ = lean_expr_instantiate_rev(v_e_3259_, v_xs_3260_);
                    leanh::lean_dec_ref(v_e_3259_);
                    v___x_3276_ =
                        l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(
                            v___x_3275_,
                            v_a_3261_,
                            v_a_3262_,
                            v_a_3263_,
                            v_a_3264_,
                        );
                    if leanh::lean_obj_tag(v___x_3276_) == 0 {
                        v_a_3277_ = leanh::lean_ctor_get(v___x_3276_, 0);
                        v_isSharedCheck_3285_ =
                            (!leanh::lean_is_exclusive(v___x_3276_)) as u8;
                        if v_isSharedCheck_3285_ == 0 {
                            v___x_3279_ = v___x_3276_;
                            v_isShared_3280_ = v_isSharedCheck_3285_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3277_);
                            leanh::lean_dec(v___x_3276_);
                            v___x_3279_ = leanh::lean_box(0);
                            v_isShared_3280_ = v_isSharedCheck_3285_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_xs_3260_);
                        return v___x_3276_;
                    }
                }
            }
            1 => {
                v___x_3281_ = lean_expr_abstract(v_a_3277_, v_xs_3260_);
                leanh::lean_dec_ref(v_xs_3260_);
                leanh::lean_dec(v_a_3277_);
                if v_isShared_3280_ == 0 {
                    leanh::lean_ctor_set(v___x_3279_, 0, v___x_3281_);
                    v___x_3283_ = v___x_3279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
                    v___x_3283_ = v_reuseFailAlloc_3284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3283_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3286_ = leanh::lean_box(0);
    v_dummy_3287_ = l_Lean_Expr_sort___override(v___x_3286_);
    return v_dummy_3287_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(
    mut v_type_3291_: *mut leanh::LeanObject,
    mut v_a_3292_: *mut leanh::LeanObject,
    mut v_a_3293_: *mut leanh::LeanObject,
    mut v_a_3294_: *mut leanh::LeanObject,
    mut v_a_3295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3301_: u8 = 0;
    let mut v___x_3302_: u8 = 0;
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3315_: u8 = 0;
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: u8 = 0;
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3332_: u8 = 0;
    let mut v_typeName_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: u8 = 0;
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v_fn_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: u8 = 0;
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3358_: u8 = 0;
    let mut v_unused_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_a_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3372_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_type_3291_);
                v___x_3297_ =
                    l_Lean_Meta_isProp(v_type_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
                if leanh::lean_obj_tag(v___x_3297_) == 0 {
                    v_a_3298_ = leanh::lean_ctor_get(v___x_3297_, 0);
                    v_isSharedCheck_3364_ = (!leanh::lean_is_exclusive(v___x_3297_)) as u8;
                    if v_isSharedCheck_3364_ == 0 {
                        v___x_3300_ = v___x_3297_;
                        v_isShared_3301_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3298_);
                        leanh::lean_dec(v___x_3297_);
                        v___x_3300_ = leanh::lean_box(0);
                        v_isShared_3301_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_type_3291_);
                    v_a_3365_ = leanh::lean_ctor_get(v___x_3297_, 0);
                    v_isSharedCheck_3372_ = (!leanh::lean_is_exclusive(v___x_3297_)) as u8;
                    if v_isSharedCheck_3372_ == 0 {
                        v___x_3367_ = v___x_3297_;
                        v_isShared_3368_ = v_isSharedCheck_3372_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3365_);
                        leanh::lean_dec(v___x_3297_);
                        v___x_3367_ = leanh::lean_box(0);
                        v_isShared_3368_ = v_isSharedCheck_3372_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3302_ = (leanh::lean_unbox(v_a_3298_) as u8);
                leanh::lean_dec(v_a_3298_);
                if v___x_3302_ == 0 {
                    v___x_3303_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_whnfEta(v_type_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
                    if leanh::lean_obj_tag(v___x_3303_) == 0 {
                        v_a_3304_ = leanh::lean_ctor_get(v___x_3303_, 0);
                        leanh::lean_inc(v_a_3304_);
                        match leanh::lean_obj_tag(v_a_3304_) {
                            3 => {
                                leanh::lean_dec_ref_known(v_a_3304_, 1);
                                leanh::lean_del_object(v___x_3300_);
                                return v___x_3303_;
                            }
                            4 => {
                                leanh::lean_dec_ref_known(v___x_3303_, 1);
                                leanh::lean_del_object(v___x_3300_);
                                v___x_3310_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0;
                                v___x_3311_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_3304_, v___x_3310_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
                                return v___x_3311_;
                            }
                            6 => {
                                leanh::lean_dec_ref_known(v___x_3303_, 1);
                                leanh::lean_del_object(v___x_3300_);
                                v_binderName_3312_ = leanh::lean_ctor_get(v_a_3304_, 0);
                                leanh::lean_inc_n(v_binderName_3312_, 2);
                                v_binderType_3313_ = leanh::lean_ctor_get(v_a_3304_, 1);
                                leanh::lean_inc_ref_n(v_binderType_3313_, 2);
                                v_body_3314_ = leanh::lean_ctor_get(v_a_3304_, 2);
                                leanh::lean_inc_ref(v_body_3314_);
                                v_binderInfo_3315_ = leanh::lean_ctor_get_uint8(
                                    v_a_3304_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                        as u32,
                                );
                                leanh::lean_dec_ref_known(v_a_3304_, 3);
                                v___x_3316_ = leanh::lean_box((v_binderInfo_3315_) as usize);
                                v___f_3317_ = leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                                leanh::lean_closure_set(v___f_3317_, 0, v_binderType_3313_);
                                leanh::lean_closure_set(v___f_3317_, 1, v_body_3314_);
                                leanh::lean_closure_set(v___f_3317_, 2, v_binderName_3312_);
                                leanh::lean_closure_set(v___f_3317_, 3, v___x_3316_);
                                v___x_3318_ = 0;
                                v___x_3319_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go_spec__0___redArg(v_binderName_3312_, v_binderInfo_3315_, v_binderType_3313_, v___f_3317_, v___x_3318_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
                                return v___x_3319_;
                            }
                            7 => {
                                leanh::lean_dec_ref_known(v___x_3303_, 1);
                                leanh::lean_del_object(v___x_3300_);
                                v___x_3320_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0;
                                v___x_3321_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(v_a_3304_, v___x_3320_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
                                return v___x_3321_;
                            }
                            5 => {
                                leanh::lean_dec_ref_known(v___x_3303_, 1);
                                leanh::lean_del_object(v___x_3300_);
                                v_dummy_3322_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0_once), _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__0);
                                v_nargs_3323_ = l_Lean_Expr_getAppNumArgs(v_a_3304_);
                                leanh::lean_inc(v_nargs_3323_);
                                v___x_3324_ = lean_mk_array(v_nargs_3323_, v_dummy_3322_);
                                v___x_3325_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3326_ = lean_nat_sub(v_nargs_3323_, v___x_3325_);
                                leanh::lean_dec(v_nargs_3323_);
                                v___x_3327_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_a_3304_, v___x_3324_, v___x_3326_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
                                return v___x_3327_;
                            }
                            1 => {
                                leanh::lean_dec_ref_known(v___x_3303_, 1);
                                leanh::lean_del_object(v___x_3300_);
                                v___x_3328_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_isPropFormerType_go___closed__0;
                                v___x_3329_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_a_3304_, v___x_3328_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
                                return v___x_3329_;
                            }
                            11 => {
                                v_isSharedCheck_3358_ =
                                    (!leanh::lean_is_exclusive(v___x_3303_)) as u8;
                                if v_isSharedCheck_3358_ == 0 {
                                    v_unused_3359_ = leanh::lean_ctor_get(v___x_3303_, 0);
                                    leanh::lean_dec(v_unused_3359_);
                                    v___x_3331_ = v___x_3303_;
                                    v_isShared_3332_ = v_isSharedCheck_3358_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_3303_);
                                    v___x_3331_ = leanh::lean_box(0);
                                    v_isShared_3332_ = v_isSharedCheck_3358_;
                                    state = 4;
                                    continue;
                                }
                            }
                            _ => {
                                leanh::lean_dec_ref_known(v___x_3303_, 1);
                                leanh::lean_dec(v_a_3304_);
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_3300_);
                        return v___x_3303_;
                    }
                } else {
                    leanh::lean_dec_ref(v_type_3291_);
                    v___x_3360_ = l_Lean_Compiler_LCNF_erasedExpr;
                    if v_isShared_3301_ == 0 {
                        leanh::lean_ctor_set(v___x_3300_, 0, v___x_3360_);
                        v___x_3362_ = v___x_3300_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3363_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
                        v___x_3362_ = v_reuseFailAlloc_3363_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3306_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_anyExpr___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_anyExpr___closed__2_once),
                    _init_l_Lean_Compiler_LCNF_anyExpr___closed__2,
                );
                if v_isShared_3301_ == 0 {
                    leanh::lean_ctor_set(v___x_3300_, 0, v___x_3306_);
                    v___x_3308_ = v___x_3300_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3309_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
                    v___x_3308_ = v_reuseFailAlloc_3309_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3308_;
            }
            4 => {
                v_typeName_3333_ = leanh::lean_ctor_get(v_a_3304_, 0);
                leanh::lean_inc(v_typeName_3333_);
                if leanh::lean_obj_tag(v_typeName_3333_) == 1 {
                    v_pre_3334_ = leanh::lean_ctor_get(v_typeName_3333_, 0);
                    if leanh::lean_obj_tag(v_pre_3334_) == 0 {
                        v_idx_3335_ = leanh::lean_ctor_get(v_a_3304_, 1);
                        leanh::lean_inc(v_idx_3335_);
                        v_struct_3336_ = leanh::lean_ctor_get(v_a_3304_, 2);
                        leanh::lean_inc_ref(v_struct_3336_);
                        leanh::lean_dec_ref_known(v_a_3304_, 3);
                        v_str_3337_ = leanh::lean_ctor_get(v_typeName_3333_, 1);
                        leanh::lean_inc_ref(v_str_3337_);
                        leanh::lean_dec_ref_known(v_typeName_3333_, 2);
                        v___x_3338_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__1;
                        v___x_3339_ = lean_string_dec_eq(v_str_3337_, v___x_3338_);
                        leanh::lean_dec_ref(v_str_3337_);
                        if v___x_3339_ == 0 {
                            leanh::lean_dec_ref(v_struct_3336_);
                            leanh::lean_dec(v_idx_3335_);
                            leanh::lean_del_object(v___x_3331_);
                            state = 2;
                            continue;
                        } else {
                            v___x_3340_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3341_ = lean_nat_dec_eq(v_idx_3335_, v___x_3340_);
                            leanh::lean_dec(v_idx_3335_);
                            if v___x_3341_ == 0 {
                                leanh::lean_dec_ref(v_struct_3336_);
                                leanh::lean_del_object(v___x_3331_);
                                state = 2;
                                continue;
                            } else {
                                if leanh::lean_obj_tag(v_struct_3336_) == 5 {
                                    v_fn_3342_ = leanh::lean_ctor_get(v_struct_3336_, 0);
                                    leanh::lean_inc_ref(v_fn_3342_);
                                    leanh::lean_dec_ref_known(v_struct_3336_, 2);
                                    if leanh::lean_obj_tag(v_fn_3342_) == 4 {
                                        v_declName_3343_ =
                                            leanh::lean_ctor_get(v_fn_3342_, 0);
                                        leanh::lean_inc(v_declName_3343_);
                                        if leanh::lean_obj_tag(v_declName_3343_) == 1 {
                                            v_pre_3344_ =
                                                leanh::lean_ctor_get(v_declName_3343_, 0);
                                            leanh::lean_inc(v_pre_3344_);
                                            if leanh::lean_obj_tag(v_pre_3344_) == 1 {
                                                v_pre_3345_ =
                                                    leanh::lean_ctor_get(v_pre_3344_, 0);
                                                if leanh::lean_obj_tag(v_pre_3345_) == 0 {
                                                    v_us_3346_ =
                                                        leanh::lean_ctor_get(v_fn_3342_, 1);
                                                    leanh::lean_inc(v_us_3346_);
                                                    leanh::lean_dec_ref_known(v_fn_3342_, 2);
                                                    v_str_3347_ = leanh::lean_ctor_get(
                                                        v_declName_3343_,
                                                        1,
                                                    );
                                                    leanh::lean_inc_ref(v_str_3347_);
                                                    leanh::lean_dec_ref_known(
                                                        v_declName_3343_,
                                                        2,
                                                    );
                                                    v_str_3348_ =
                                                        leanh::lean_ctor_get(v_pre_3344_, 1);
                                                    leanh::lean_inc_ref(v_str_3348_);
                                                    leanh::lean_dec_ref_known(
                                                        v_pre_3344_,
                                                        2,
                                                    );
                                                    v___x_3349_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__2;
                                                    v___x_3350_ = lean_string_dec_eq(
                                                        v_str_3348_,
                                                        v___x_3349_,
                                                    );
                                                    leanh::lean_dec_ref(v_str_3348_);
                                                    if v___x_3350_ == 0 {
                                                        leanh::lean_dec_ref(v_str_3347_);
                                                        leanh::lean_dec(v_us_3346_);
                                                        leanh::lean_del_object(v___x_3331_);
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        v___x_3351_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___closed__3;
                                                        v___x_3352_ = lean_string_dec_eq(
                                                            v_str_3347_,
                                                            v___x_3351_,
                                                        );
                                                        leanh::lean_dec_ref(v_str_3347_);
                                                        if v___x_3352_ == 0 {
                                                            leanh::lean_dec(v_us_3346_);
                                                            leanh::lean_del_object(
                                                                v___x_3331_,
                                                            );
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            if leanh::lean_obj_tag(
                                                                v_us_3346_,
                                                            ) == 0
                                                            {
                                                                leanh::lean_del_object(
                                                                    v___x_3300_,
                                                                );
                                                                v___x_3353_ =
                                                                    l_Lean_Expr_isVoid___closed__1;
                                                                v___x_3354_ = l_Lean_mkConst(
                                                                    v___x_3353_,
                                                                    v_us_3346_,
                                                                );
                                                                if v_isShared_3332_ == 0 {
                                                                    leanh::lean_ctor_set(
                                                                        v___x_3331_,
                                                                        0,
                                                                        v___x_3354_,
                                                                    );
                                                                    v___x_3356_ = v___x_3331_;
                                                                    state = 5;
                                                                    continue;
                                                                } else {
                                                                    v_reuseFailAlloc_3357_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v_reuseFailAlloc_3357_,
                                                                        0,
                                                                        v___x_3354_,
                                                                    );
                                                                    v___x_3356_ =
                                                                        v_reuseFailAlloc_3357_;
                                                                    state = 5;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec(v_us_3346_);
                                                                leanh::lean_del_object(
                                                                    v___x_3331_,
                                                                );
                                                                state = 2;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref_known(
                                                        v_pre_3344_,
                                                        2,
                                                    );
                                                    leanh::lean_dec_ref_known(
                                                        v_declName_3343_,
                                                        2,
                                                    );
                                                    leanh::lean_dec_ref_known(v_fn_3342_, 2);
                                                    leanh::lean_del_object(v___x_3331_);
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec(v_pre_3344_);
                                                leanh::lean_dec_ref_known(
                                                    v_declName_3343_,
                                                    2,
                                                );
                                                leanh::lean_dec_ref_known(v_fn_3342_, 2);
                                                leanh::lean_del_object(v___x_3331_);
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v_fn_3342_, 2);
                                            leanh::lean_dec(v_declName_3343_);
                                            leanh::lean_del_object(v___x_3331_);
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_fn_3342_);
                                        leanh::lean_del_object(v___x_3331_);
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_struct_3336_);
                                    leanh::lean_del_object(v___x_3331_);
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_typeName_3333_, 2);
                        leanh::lean_del_object(v___x_3331_);
                        leanh::lean_dec_ref_known(v_a_3304_, 3);
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_typeName_3333_);
                    leanh::lean_del_object(v___x_3331_);
                    leanh::lean_dec_ref_known(v_a_3304_, 3);
                    state = 2;
                    continue;
                }
            }
            5 => {
                return v___x_3356_;
            }
            6 => {
                return v___x_3362_;
            }
            7 => {
                if v_isShared_3368_ == 0 {
                    v___x_3370_ = v___x_3367_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3371_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
                    v___x_3370_ = v_reuseFailAlloc_3371_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(
    mut v_as_3373_: *mut leanh::LeanObject,
    mut v_sz_3374_: usize,
    mut v_i_3375_: usize,
    mut v_b_3376_: *mut leanh::LeanObject,
    mut v___y_3377_: *mut leanh::LeanObject,
    mut v___y_3378_: *mut leanh::LeanObject,
    mut v___y_3379_: *mut leanh::LeanObject,
    mut v___y_3380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: usize = 0;
    let mut v___x_3385_: usize = 0;
    let mut v___x_3387_: u8 = 0;
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3405_: u8 = 0;
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3409_: u8 = 0;
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3415_: u8 = 0;
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3419_: u8 = 0;
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: u8 = 0;
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3387_ = lean_usize_dec_lt(v_i_3375_, v_sz_3374_);
                if v___x_3387_ == 0 {
                    v___x_3388_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3388_, 0, v_b_3376_);
                    return v___x_3388_;
                } else {
                    v_a_3389_ = lean_array_uget_borrowed(v_as_3373_, v_i_3375_);
                    leanh::lean_inc(v_a_3389_);
                    v___x_3420_ = l_Lean_Meta_isProp(
                        v_a_3389_,
                        v___y_3377_,
                        v___y_3378_,
                        v___y_3379_,
                        v___y_3380_,
                    );
                    if leanh::lean_obj_tag(v___x_3420_) == 0 {
                        v_a_3421_ = leanh::lean_ctor_get(v___x_3420_, 0);
                        leanh::lean_inc(v_a_3421_);
                        v___x_3422_ = (leanh::lean_unbox(v_a_3421_) as u8);
                        leanh::lean_dec(v_a_3421_);
                        if v___x_3422_ == 0 {
                            leanh::lean_dec_ref_known(v___x_3420_, 1);
                            leanh::lean_inc(v_a_3389_);
                            v___x_3423_ = l_Lean_Compiler_LCNF_isPropFormer(
                                v_a_3389_,
                                v___y_3377_,
                                v___y_3378_,
                                v___y_3379_,
                                v___y_3380_,
                            );
                            v___y_3391_ = v___x_3423_;
                            state = 2;
                            continue;
                        } else {
                            v___y_3391_ = v___x_3420_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_3391_ = v___x_3420_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3384_ = 1usize;
                v___x_3385_ = lean_usize_add(v_i_3375_, v___x_3384_);
                v_i_3375_ = v___x_3385_;
                v_b_3376_ = v_a_3383_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_3391_) == 0 {
                    v_a_3392_ = leanh::lean_ctor_get(v___y_3391_, 0);
                    leanh::lean_inc(v_a_3392_);
                    leanh::lean_dec_ref_known(v___y_3391_, 1);
                    v___x_3393_ = (leanh::lean_unbox(v_a_3392_) as u8);
                    leanh::lean_dec(v_a_3392_);
                    if v___x_3393_ == 0 {
                        leanh::lean_inc(v_a_3389_);
                        v___x_3394_ = l_Lean_Meta_isTypeFormer(
                            v_a_3389_,
                            v___y_3377_,
                            v___y_3378_,
                            v___y_3379_,
                            v___y_3380_,
                        );
                        if leanh::lean_obj_tag(v___x_3394_) == 0 {
                            v_a_3395_ = leanh::lean_ctor_get(v___x_3394_, 0);
                            leanh::lean_inc(v_a_3395_);
                            leanh::lean_dec_ref_known(v___x_3394_, 1);
                            v___x_3396_ = (leanh::lean_unbox(v_a_3395_) as u8);
                            leanh::lean_dec(v_a_3395_);
                            if v___x_3396_ == 0 {
                                v___x_3397_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_anyExpr___closed__2
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_anyExpr___closed__2_once
                                    ),
                                    _init_l_Lean_Compiler_LCNF_anyExpr___closed__2,
                                );
                                v___x_3398_ = l_Lean_Expr_app___override(v_b_3376_, v___x_3397_);
                                v_a_3383_ = v___x_3398_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3389_);
                                v___x_3399_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(v_a_3389_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
                                if leanh::lean_obj_tag(v___x_3399_) == 0 {
                                    v_a_3400_ = leanh::lean_ctor_get(v___x_3399_, 0);
                                    leanh::lean_inc(v_a_3400_);
                                    leanh::lean_dec_ref_known(v___x_3399_, 1);
                                    v___x_3401_ = l_Lean_Expr_app___override(v_b_3376_, v_a_3400_);
                                    v_a_3383_ = v___x_3401_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_b_3376_);
                                    return v___x_3399_;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_3376_);
                            v_a_3402_ = leanh::lean_ctor_get(v___x_3394_, 0);
                            v_isSharedCheck_3409_ =
                                (!leanh::lean_is_exclusive(v___x_3394_)) as u8;
                            if v_isSharedCheck_3409_ == 0 {
                                v___x_3404_ = v___x_3394_;
                                v_isShared_3405_ = v_isSharedCheck_3409_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3402_);
                                leanh::lean_dec(v___x_3394_);
                                v___x_3404_ = leanh::lean_box(0);
                                v_isShared_3405_ = v_isSharedCheck_3409_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_3410_ = l_Lean_Compiler_LCNF_erasedExpr;
                        v___x_3411_ = l_Lean_Expr_app___override(v_b_3376_, v___x_3410_);
                        v_a_3383_ = v___x_3411_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_3376_);
                    v_a_3412_ = leanh::lean_ctor_get(v___y_3391_, 0);
                    v_isSharedCheck_3419_ = (!leanh::lean_is_exclusive(v___y_3391_)) as u8;
                    if v_isSharedCheck_3419_ == 0 {
                        v___x_3414_ = v___y_3391_;
                        v_isShared_3415_ = v_isSharedCheck_3419_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3412_);
                        leanh::lean_dec(v___y_3391_);
                        v___x_3414_ = leanh::lean_box(0);
                        v_isShared_3415_ = v_isSharedCheck_3419_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3405_ == 0 {
                    v___x_3407_ = v___x_3404_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3408_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
                    v___x_3407_ = v_reuseFailAlloc_3408_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3407_;
            }
            5 => {
                if v_isShared_3415_ == 0 {
                    v___x_3417_ = v___x_3414_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
                    v___x_3417_ = v_reuseFailAlloc_3418_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3425_ =
        l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__0;
    v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
    return v___x_3426_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(
    mut v_f_3427_: *mut leanh::LeanObject,
    mut v_args_3428_: *mut leanh::LeanObject,
    mut v_a_3429_: *mut leanh::LeanObject,
    mut v_a_3430_: *mut leanh::LeanObject,
    mut v_a_3431_: *mut leanh::LeanObject,
    mut v_a_3432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fNew_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3440_: usize = 0;
    let mut v___x_3441_: usize = 0;
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3453_: u8 = 0;
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3458_: u8 = 0;
    let mut v_a_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3466_: u8 = 0;
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3469_: u8 = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3480_: u8 = 0;
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_f_3427_) {
                4 => {
                    v_declName_3443_ = leanh::lean_ctor_get(v_f_3427_, 0);
                    v___x_3467_ = lean_st_ref_get(v_a_3432_);
                    v_env_3468_ = leanh::lean_ctor_get(v___x_3467_, 0);
                    leanh::lean_inc_ref(v_env_3468_);
                    leanh::lean_dec(v___x_3467_);
                    v_isExporting_3469_ = leanh::lean_ctor_get_uint8(
                        v_env_3468_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    leanh::lean_dec_ref(v_env_3468_);
                    if v_isExporting_3469_ == 0 {
                        v___y_3445_ = v_a_3429_;
                        v___y_3446_ = v_a_3430_;
                        v___y_3447_ = v_a_3431_;
                        v___y_3448_ = v_a_3432_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3470_ = l_Lean_isPrivateName(v_declName_3443_);
                        if v___x_3470_ == 0 {
                            v___y_3445_ = v_a_3429_;
                            v___y_3446_ = v_a_3430_;
                            v___y_3447_ = v_a_3431_;
                            v___y_3448_ = v_a_3432_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3471_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1_once), _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___closed__1);
                            v___x_3472_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_3471_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_);
                            if leanh::lean_obj_tag(v___x_3472_) == 0 {
                                leanh::lean_dec_ref_known(v___x_3472_, 1);
                                v___y_3445_ = v_a_3429_;
                                v___y_3446_ = v_a_3430_;
                                v___y_3447_ = v_a_3431_;
                                v___y_3448_ = v_a_3432_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_f_3427_, 2);
                                v_a_3473_ = leanh::lean_ctor_get(v___x_3472_, 0);
                                v_isSharedCheck_3480_ =
                                    (!leanh::lean_is_exclusive(v___x_3472_)) as u8;
                                if v_isSharedCheck_3480_ == 0 {
                                    v___x_3475_ = v___x_3472_;
                                    v_isShared_3476_ = v_isSharedCheck_3480_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3473_);
                                    leanh::lean_dec(v___x_3472_);
                                    v___x_3475_ = leanh::lean_box(0);
                                    v_isShared_3476_ = v_isSharedCheck_3480_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                }
                1 => {
                    v_fNew_3435_ = v_f_3427_;
                    v___y_3436_ = v_a_3429_;
                    v___y_3437_ = v_a_3430_;
                    v___y_3438_ = v_a_3431_;
                    v___y_3439_ = v_a_3432_;
                    state = 1;
                    continue;
                }
                _ => {
                    leanh::lean_dec_ref(v_f_3427_);
                    v___x_3481_ = l_Lean_Compiler_LCNF_anyExpr;
                    v___x_3482_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3482_, 0, v___x_3481_);
                    return v___x_3482_;
                }
            },
            1 => {
                v_sz_3440_ = lean_array_size(v_args_3428_);
                v___x_3441_ = 0usize;
                v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_args_3428_, v_sz_3440_, v___x_3441_, v_fNew_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
                return v___x_3442_;
            }
            2 => {
                leanh::lean_inc(v_declName_3443_);
                v___x_3449_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4(v_declName_3443_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
                if leanh::lean_obj_tag(v___x_3449_) == 0 {
                    v_a_3450_ = leanh::lean_ctor_get(v___x_3449_, 0);
                    v_isSharedCheck_3458_ = (!leanh::lean_is_exclusive(v___x_3449_)) as u8;
                    if v_isSharedCheck_3458_ == 0 {
                        v___x_3452_ = v___x_3449_;
                        v_isShared_3453_ = v_isSharedCheck_3458_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3450_);
                        leanh::lean_dec(v___x_3449_);
                        v___x_3452_ = leanh::lean_box(0);
                        v_isShared_3453_ = v_isSharedCheck_3458_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_f_3427_, 2);
                    v_a_3459_ = leanh::lean_ctor_get(v___x_3449_, 0);
                    v_isSharedCheck_3466_ = (!leanh::lean_is_exclusive(v___x_3449_)) as u8;
                    if v_isSharedCheck_3466_ == 0 {
                        v___x_3461_ = v___x_3449_;
                        v_isShared_3462_ = v_isSharedCheck_3466_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3459_);
                        leanh::lean_dec(v___x_3449_);
                        v___x_3461_ = leanh::lean_box(0);
                        v_isShared_3462_ = v_isSharedCheck_3466_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_3450_) == 5 {
                    leanh::lean_dec_ref_known(v_a_3450_, 1);
                    leanh::lean_del_object(v___x_3452_);
                    v_fNew_3435_ = v_f_3427_;
                    v___y_3436_ = v___y_3445_;
                    v___y_3437_ = v___y_3446_;
                    v___y_3438_ = v___y_3447_;
                    v___y_3439_ = v___y_3448_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_3450_);
                    leanh::lean_dec_ref_known(v_f_3427_, 2);
                    v___x_3454_ = l_Lean_Compiler_LCNF_anyExpr;
                    if v_isShared_3453_ == 0 {
                        leanh::lean_ctor_set(v___x_3452_, 0, v___x_3454_);
                        v___x_3456_ = v___x_3452_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3457_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3454_);
                        v___x_3456_ = v_reuseFailAlloc_3457_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3456_;
            }
            5 => {
                if v_isShared_3462_ == 0 {
                    v___x_3464_ = v___x_3461_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3465_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
                    v___x_3464_ = v_reuseFailAlloc_3465_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3464_;
            }
            7 => {
                if v_isShared_3476_ == 0 {
                    v___x_3478_ = v___x_3475_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3479_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
                    v___x_3478_ = v_reuseFailAlloc_3479_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3478_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(
    mut v_x_3483_: *mut leanh::LeanObject,
    mut v_x_3484_: *mut leanh::LeanObject,
    mut v_x_3485_: *mut leanh::LeanObject,
    mut v___y_3486_: *mut leanh::LeanObject,
    mut v___y_3487_: *mut leanh::LeanObject,
    mut v___y_3488_: *mut leanh::LeanObject,
    mut v___y_3489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3483_) == 5 {
                    v_fn_3491_ = leanh::lean_ctor_get(v_x_3483_, 0);
                    leanh::lean_inc_ref(v_fn_3491_);
                    v_arg_3492_ = leanh::lean_ctor_get(v_x_3483_, 1);
                    leanh::lean_inc_ref(v_arg_3492_);
                    leanh::lean_dec_ref_known(v_x_3483_, 2);
                    v___x_3493_ = lean_array_set(v_x_3484_, v_x_3485_, v_arg_3492_);
                    v___x_3494_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3495_ = lean_nat_sub(v_x_3485_, v___x_3494_);
                    leanh::lean_dec(v_x_3485_);
                    v_x_3483_ = v_fn_3491_;
                    v_x_3484_ = v___x_3493_;
                    v_x_3485_ = v___x_3495_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_3485_);
                    v___x_3497_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(v_x_3483_, v_x_3484_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
                    leanh::lean_dec_ref(v_x_3484_);
                    return v___x_3497_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0___boxed(
    mut v_x_3498_: *mut leanh::LeanObject,
    mut v_x_3499_: *mut leanh::LeanObject,
    mut v_x_3500_: *mut leanh::LeanObject,
    mut v___y_3501_: *mut leanh::LeanObject,
    mut v___y_3502_: *mut leanh::LeanObject,
    mut v___y_3503_: *mut leanh::LeanObject,
    mut v___y_3504_: *mut leanh::LeanObject,
    mut v___y_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3506_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go_spec__0(v_x_3498_, v_x_3499_, v_x_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
    leanh::lean_dec(v___y_3504_);
    leanh::lean_dec_ref(v___y_3503_);
    leanh::lean_dec(v___y_3502_);
    leanh::lean_dec_ref(v___y_3501_);
    return v_res_3506_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall___boxed(
    mut v_e_3507_: *mut leanh::LeanObject,
    mut v_xs_3508_: *mut leanh::LeanObject,
    mut v_a_3509_: *mut leanh::LeanObject,
    mut v_a_3510_: *mut leanh::LeanObject,
    mut v_a_3511_: *mut leanh::LeanObject,
    mut v_a_3512_: *mut leanh::LeanObject,
    mut v_a_3513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3514_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall(
        v_e_3507_, v_xs_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_,
    );
    leanh::lean_dec(v_a_3512_);
    leanh::lean_dec_ref(v_a_3511_);
    leanh::lean_dec(v_a_3510_);
    leanh::lean_dec_ref(v_a_3509_);
    return v_res_3514_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp___boxed(
    mut v_f_3515_: *mut leanh::LeanObject,
    mut v_args_3516_: *mut leanh::LeanObject,
    mut v_a_3517_: *mut leanh::LeanObject,
    mut v_a_3518_: *mut leanh::LeanObject,
    mut v_a_3519_: *mut leanh::LeanObject,
    mut v_a_3520_: *mut leanh::LeanObject,
    mut v_a_3521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3522_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp(
        v_f_3515_,
        v_args_3516_,
        v_a_3517_,
        v_a_3518_,
        v_a_3519_,
        v_a_3520_,
    );
    leanh::lean_dec(v_a_3520_);
    leanh::lean_dec_ref(v_a_3519_);
    leanh::lean_dec(v_a_3518_);
    leanh::lean_dec_ref(v_a_3517_);
    leanh::lean_dec_ref(v_args_3516_);
    return v_res_3522_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3___boxed(
    mut v_as_3523_: *mut leanh::LeanObject,
    mut v_sz_3524_: *mut leanh::LeanObject,
    mut v_i_3525_: *mut leanh::LeanObject,
    mut v_b_3526_: *mut leanh::LeanObject,
    mut v___y_3527_: *mut leanh::LeanObject,
    mut v___y_3528_: *mut leanh::LeanObject,
    mut v___y_3529_: *mut leanh::LeanObject,
    mut v___y_3530_: *mut leanh::LeanObject,
    mut v___y_3531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3532_: usize = 0;
    let mut v_i_boxed_3533_: usize = 0;
    let mut v_res_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3532_ = leanh::lean_unbox_usize(v_sz_3524_);
    leanh::lean_dec(v_sz_3524_);
    v_i_boxed_3533_ = leanh::lean_unbox_usize(v_i_3525_);
    leanh::lean_dec(v_i_3525_);
    v_res_3534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__3(v_as_3523_, v_sz_boxed_3532_, v_i_boxed_3533_, v_b_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
    leanh::lean_dec(v___y_3530_);
    leanh::lean_dec_ref(v___y_3529_);
    leanh::lean_dec(v___y_3528_);
    leanh::lean_dec_ref(v___y_3527_);
    leanh::lean_dec_ref(v_as_3523_);
    return v_res_3534_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed(
    mut v_type_3535_: *mut leanh::LeanObject,
    mut v_a_3536_: *mut leanh::LeanObject,
    mut v_a_3537_: *mut leanh::LeanObject,
    mut v_a_3538_: *mut leanh::LeanObject,
    mut v_a_3539_: *mut leanh::LeanObject,
    mut v_a_3540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3541_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(
        v_type_3535_,
        v_a_3536_,
        v_a_3537_,
        v_a_3538_,
        v_a_3539_,
    );
    leanh::lean_dec(v_a_3539_);
    leanh::lean_dec_ref(v_a_3538_);
    leanh::lean_dec(v_a_3537_);
    leanh::lean_dec_ref(v_a_3536_);
    return v_res_3541_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(
    mut v_00_u03b1_3542_: *mut leanh::LeanObject,
    mut v_msg_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
    mut v___y_3545_: *mut leanh::LeanObject,
    mut v___y_3546_: *mut leanh::LeanObject,
    mut v___y_3547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3549_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v_msg_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
    return v___x_3549_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___boxed(
    mut v_00_u03b1_3550_: *mut leanh::LeanObject,
    mut v_msg_3551_: *mut leanh::LeanObject,
    mut v___y_3552_: *mut leanh::LeanObject,
    mut v___y_3553_: *mut leanh::LeanObject,
    mut v___y_3554_: *mut leanh::LeanObject,
    mut v___y_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3557_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5(v_00_u03b1_3550_, v_msg_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
    leanh::lean_dec(v___y_3555_);
    leanh::lean_dec_ref(v___y_3554_);
    leanh::lean_dec(v___y_3553_);
    leanh::lean_dec_ref(v___y_3552_);
    return v_res_3557_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(
    mut v_00_u03b1_3558_: *mut leanh::LeanObject,
    mut v_constName_3559_: *mut leanh::LeanObject,
    mut v___y_3560_: *mut leanh::LeanObject,
    mut v___y_3561_: *mut leanh::LeanObject,
    mut v___y_3562_: *mut leanh::LeanObject,
    mut v___y_3563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3565_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___redArg(v_constName_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
    return v___x_3565_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4___boxed(
    mut v_00_u03b1_3566_: *mut leanh::LeanObject,
    mut v_constName_3567_: *mut leanh::LeanObject,
    mut v___y_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
    mut v___y_3571_: *mut leanh::LeanObject,
    mut v___y_3572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3573_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4(v_00_u03b1_3566_, v_constName_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
    leanh::lean_dec(v___y_3571_);
    leanh::lean_dec_ref(v___y_3570_);
    leanh::lean_dec(v___y_3569_);
    leanh::lean_dec_ref(v___y_3568_);
    return v_res_3573_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(
    mut v_00_u03b1_3574_: *mut leanh::LeanObject,
    mut v_ref_3575_: *mut leanh::LeanObject,
    mut v_constName_3576_: *mut leanh::LeanObject,
    mut v___y_3577_: *mut leanh::LeanObject,
    mut v___y_3578_: *mut leanh::LeanObject,
    mut v___y_3579_: *mut leanh::LeanObject,
    mut v___y_3580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3582_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___redArg(v_ref_3575_, v_constName_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
    return v___x_3582_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5___boxed(
    mut v_00_u03b1_3583_: *mut leanh::LeanObject,
    mut v_ref_3584_: *mut leanh::LeanObject,
    mut v_constName_3585_: *mut leanh::LeanObject,
    mut v___y_3586_: *mut leanh::LeanObject,
    mut v___y_3587_: *mut leanh::LeanObject,
    mut v___y_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3591_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5(v_00_u03b1_3583_, v_ref_3584_, v_constName_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
    leanh::lean_dec(v___y_3589_);
    leanh::lean_dec_ref(v___y_3588_);
    leanh::lean_dec(v___y_3587_);
    leanh::lean_dec_ref(v___y_3586_);
    leanh::lean_dec(v_ref_3584_);
    return v_res_3591_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(
    mut v_00_u03b1_3592_: *mut leanh::LeanObject,
    mut v_ref_3593_: *mut leanh::LeanObject,
    mut v_msg_3594_: *mut leanh::LeanObject,
    mut v_declHint_3595_: *mut leanh::LeanObject,
    mut v___y_3596_: *mut leanh::LeanObject,
    mut v___y_3597_: *mut leanh::LeanObject,
    mut v___y_3598_: *mut leanh::LeanObject,
    mut v___y_3599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3601_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___redArg(v_ref_3593_, v_msg_3594_, v_declHint_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
    return v___x_3601_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8___boxed(
    mut v_00_u03b1_3602_: *mut leanh::LeanObject,
    mut v_ref_3603_: *mut leanh::LeanObject,
    mut v_msg_3604_: *mut leanh::LeanObject,
    mut v_declHint_3605_: *mut leanh::LeanObject,
    mut v___y_3606_: *mut leanh::LeanObject,
    mut v___y_3607_: *mut leanh::LeanObject,
    mut v___y_3608_: *mut leanh::LeanObject,
    mut v___y_3609_: *mut leanh::LeanObject,
    mut v___y_3610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3611_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8(v_00_u03b1_3602_, v_ref_3603_, v_msg_3604_, v_declHint_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
    leanh::lean_dec(v___y_3609_);
    leanh::lean_dec_ref(v___y_3608_);
    leanh::lean_dec(v___y_3607_);
    leanh::lean_dec_ref(v___y_3606_);
    leanh::lean_dec(v_ref_3603_);
    return v_res_3611_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(
    mut v_msg_3612_: *mut leanh::LeanObject,
    mut v_declHint_3613_: *mut leanh::LeanObject,
    mut v___y_3614_: *mut leanh::LeanObject,
    mut v___y_3615_: *mut leanh::LeanObject,
    mut v___y_3616_: *mut leanh::LeanObject,
    mut v___y_3617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3619_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg(v_msg_3612_, v_declHint_3613_, v___y_3617_);
    return v___x_3619_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___boxed(
    mut v_msg_3620_: *mut leanh::LeanObject,
    mut v_declHint_3621_: *mut leanh::LeanObject,
    mut v___y_3622_: *mut leanh::LeanObject,
    mut v___y_3623_: *mut leanh::LeanObject,
    mut v___y_3624_: *mut leanh::LeanObject,
    mut v___y_3625_: *mut leanh::LeanObject,
    mut v___y_3626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3627_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10(v_msg_3620_, v_declHint_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
    leanh::lean_dec(v___y_3625_);
    leanh::lean_dec_ref(v___y_3624_);
    leanh::lean_dec(v___y_3623_);
    leanh::lean_dec_ref(v___y_3622_);
    return v_res_3627_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(
    mut v_00_u03b1_3628_: *mut leanh::LeanObject,
    mut v_ref_3629_: *mut leanh::LeanObject,
    mut v_msg_3630_: *mut leanh::LeanObject,
    mut v___y_3631_: *mut leanh::LeanObject,
    mut v___y_3632_: *mut leanh::LeanObject,
    mut v___y_3633_: *mut leanh::LeanObject,
    mut v___y_3634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3636_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___redArg(v_ref_3629_, v_msg_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
    return v___x_3636_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10___boxed(
    mut v_00_u03b1_3637_: *mut leanh::LeanObject,
    mut v_ref_3638_: *mut leanh::LeanObject,
    mut v_msg_3639_: *mut leanh::LeanObject,
    mut v___y_3640_: *mut leanh::LeanObject,
    mut v___y_3641_: *mut leanh::LeanObject,
    mut v___y_3642_: *mut leanh::LeanObject,
    mut v___y_3643_: *mut leanh::LeanObject,
    mut v___y_3644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3645_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__10(v_00_u03b1_3637_, v_ref_3638_, v_msg_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
    leanh::lean_dec(v___y_3643_);
    leanh::lean_dec_ref(v___y_3642_);
    leanh::lean_dec(v___y_3641_);
    leanh::lean_dec_ref(v___y_3640_);
    leanh::lean_dec(v_ref_3638_);
    return v_res_3645_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(
    mut v___y_3646_: *mut leanh::LeanObject,
    mut v_isExporting_3647_: u8,
    mut v___x_3648_: *mut leanh::LeanObject,
    mut v___y_3649_: *mut leanh::LeanObject,
    mut v___x_3650_: *mut leanh::LeanObject,
    mut v_a_x3f_3651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3664_: u8 = 0;
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3683_: u8 = 0;
    let mut v_unused_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_unused_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3653_ = lean_st_ref_take(v___y_3646_);
                v_env_3654_ = leanh::lean_ctor_get(v___x_3653_, 0);
                v_nextMacroScope_3655_ = leanh::lean_ctor_get(v___x_3653_, 1);
                v_ngen_3656_ = leanh::lean_ctor_get(v___x_3653_, 2);
                v_auxDeclNGen_3657_ = leanh::lean_ctor_get(v___x_3653_, 3);
                v_traceState_3658_ = leanh::lean_ctor_get(v___x_3653_, 4);
                v_messages_3659_ = leanh::lean_ctor_get(v___x_3653_, 6);
                v_infoState_3660_ = leanh::lean_ctor_get(v___x_3653_, 7);
                v_snapshotTasks_3661_ = leanh::lean_ctor_get(v___x_3653_, 8);
                v_isSharedCheck_3686_ = (!leanh::lean_is_exclusive(v___x_3653_)) as u8;
                if v_isSharedCheck_3686_ == 0 {
                    v_unused_3687_ = leanh::lean_ctor_get(v___x_3653_, 5);
                    leanh::lean_dec(v_unused_3687_);
                    v___x_3663_ = v___x_3653_;
                    v_isShared_3664_ = v_isSharedCheck_3686_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3661_);
                    leanh::lean_inc(v_infoState_3660_);
                    leanh::lean_inc(v_messages_3659_);
                    leanh::lean_inc(v_traceState_3658_);
                    leanh::lean_inc(v_auxDeclNGen_3657_);
                    leanh::lean_inc(v_ngen_3656_);
                    leanh::lean_inc(v_nextMacroScope_3655_);
                    leanh::lean_inc(v_env_3654_);
                    leanh::lean_dec(v___x_3653_);
                    v___x_3663_ = leanh::lean_box(0);
                    v_isShared_3664_ = v_isSharedCheck_3686_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3665_ = l_Lean_Environment_setExporting(v_env_3654_, v_isExporting_3647_);
                if v_isShared_3664_ == 0 {
                    leanh::lean_ctor_set(v___x_3663_, 5, v___x_3648_);
                    leanh::lean_ctor_set(v___x_3663_, 0, v___x_3665_);
                    v___x_3667_ = v___x_3663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_nextMacroScope_3655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 2, v_ngen_3656_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 3, v_auxDeclNGen_3657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 4, v_traceState_3658_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 5, v___x_3648_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 6, v_messages_3659_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 7, v_infoState_3660_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 8, v_snapshotTasks_3661_);
                    v___x_3667_ = v_reuseFailAlloc_3685_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3668_ = lean_st_ref_set(v___y_3646_, v___x_3667_);
                v___x_3669_ = lean_st_ref_take(v___y_3649_);
                v_mctx_3670_ = leanh::lean_ctor_get(v___x_3669_, 0);
                v_zetaDeltaFVarIds_3671_ = leanh::lean_ctor_get(v___x_3669_, 2);
                v_postponed_3672_ = leanh::lean_ctor_get(v___x_3669_, 3);
                v_diag_3673_ = leanh::lean_ctor_get(v___x_3669_, 4);
                v_isSharedCheck_3683_ = (!leanh::lean_is_exclusive(v___x_3669_)) as u8;
                if v_isSharedCheck_3683_ == 0 {
                    v_unused_3684_ = leanh::lean_ctor_get(v___x_3669_, 1);
                    leanh::lean_dec(v_unused_3684_);
                    v___x_3675_ = v___x_3669_;
                    v_isShared_3676_ = v_isSharedCheck_3683_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3673_);
                    leanh::lean_inc(v_postponed_3672_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3671_);
                    leanh::lean_inc(v_mctx_3670_);
                    leanh::lean_dec(v___x_3669_);
                    v___x_3675_ = leanh::lean_box(0);
                    v_isShared_3676_ = v_isSharedCheck_3683_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3676_ == 0 {
                    leanh::lean_ctor_set(v___x_3675_, 1, v___x_3650_);
                    v___x_3678_ = v___x_3675_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3682_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_mctx_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3682_, 1, v___x_3650_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3682_,
                        2,
                        v_zetaDeltaFVarIds_3671_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3682_, 3, v_postponed_3672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3682_, 4, v_diag_3673_);
                    v___x_3678_ = v_reuseFailAlloc_3682_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3679_ = lean_st_ref_set(v___y_3649_, v___x_3678_);
                v___x_3680_ = leanh::lean_box(0);
                v___x_3681_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3681_, 0, v___x_3680_);
                return v___x_3681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0___boxed(
    mut v___y_3688_: *mut leanh::LeanObject,
    mut v_isExporting_3689_: *mut leanh::LeanObject,
    mut v___x_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
    mut v___x_3692_: *mut leanh::LeanObject,
    mut v_a_x3f_3693_: *mut leanh::LeanObject,
    mut v___y_3694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_3695_: u8 = 0;
    let mut v_res_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3695_ = (leanh::lean_unbox(v_isExporting_3689_) as u8);
    v_res_3696_ =
        l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(
            v___y_3688_,
            v_isExporting_boxed_3695_,
            v___x_3690_,
            v___y_3691_,
            v___x_3692_,
            v_a_x3f_3693_,
        );
    leanh::lean_dec(v_a_x3f_3693_);
    leanh::lean_dec(v___y_3691_);
    leanh::lean_dec(v___y_3688_);
    return v_res_3696_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3697_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3697_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3698_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__0);
    v___x_3699_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3699_, 0, v___x_3698_);
    return v___x_3699_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
    v___x_3701_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3701_, 0, v___x_3700_);
    leanh::lean_ctor_set(v___x_3701_, 1, v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3702_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__1);
    v___x_3703_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_3703_, 0, v___x_3702_);
    leanh::lean_ctor_set(v___x_3703_, 1, v___x_3702_);
    leanh::lean_ctor_set(v___x_3703_, 2, v___x_3702_);
    leanh::lean_ctor_set(v___x_3703_, 3, v___x_3702_);
    leanh::lean_ctor_set(v___x_3703_, 4, v___x_3702_);
    leanh::lean_ctor_set(v___x_3703_, 5, v___x_3702_);
    return v___x_3703_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(
    mut v_x_3704_: *mut leanh::LeanObject,
    mut v_isExporting_3705_: u8,
    mut v___y_3706_: *mut leanh::LeanObject,
    mut v___y_3707_: *mut leanh::LeanObject,
    mut v___y_3708_: *mut leanh::LeanObject,
    mut v___y_3709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3713_: u8 = 0;
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3725_: u8 = 0;
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3747_: u8 = 0;
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3753_: u8 = 0;
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3757_: u8 = 0;
    let mut v_unused_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3760_: u8 = 0;
    let mut v_a_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v_unused_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3773_: u8 = 0;
    let mut v_unused_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_unused_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3711_ = lean_st_ref_get(v___y_3709_);
                v_env_3712_ = leanh::lean_ctor_get(v___x_3711_, 0);
                leanh::lean_inc_ref(v_env_3712_);
                leanh::lean_dec(v___x_3711_);
                v_isExporting_3713_ = leanh::lean_ctor_get_uint8(
                    v_env_3712_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_3712_);
                v___x_3714_ = lean_st_ref_take(v___y_3709_);
                v_env_3715_ = leanh::lean_ctor_get(v___x_3714_, 0);
                v_nextMacroScope_3716_ = leanh::lean_ctor_get(v___x_3714_, 1);
                v_ngen_3717_ = leanh::lean_ctor_get(v___x_3714_, 2);
                v_auxDeclNGen_3718_ = leanh::lean_ctor_get(v___x_3714_, 3);
                v_traceState_3719_ = leanh::lean_ctor_get(v___x_3714_, 4);
                v_messages_3720_ = leanh::lean_ctor_get(v___x_3714_, 6);
                v_infoState_3721_ = leanh::lean_ctor_get(v___x_3714_, 7);
                v_snapshotTasks_3722_ = leanh::lean_ctor_get(v___x_3714_, 8);
                v_isSharedCheck_3776_ = (!leanh::lean_is_exclusive(v___x_3714_)) as u8;
                if v_isSharedCheck_3776_ == 0 {
                    v_unused_3777_ = leanh::lean_ctor_get(v___x_3714_, 5);
                    leanh::lean_dec(v_unused_3777_);
                    v___x_3724_ = v___x_3714_;
                    v_isShared_3725_ = v_isSharedCheck_3776_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3722_);
                    leanh::lean_inc(v_infoState_3721_);
                    leanh::lean_inc(v_messages_3720_);
                    leanh::lean_inc(v_traceState_3719_);
                    leanh::lean_inc(v_auxDeclNGen_3718_);
                    leanh::lean_inc(v_ngen_3717_);
                    leanh::lean_inc(v_nextMacroScope_3716_);
                    leanh::lean_inc(v_env_3715_);
                    leanh::lean_dec(v___x_3714_);
                    v___x_3724_ = leanh::lean_box(0);
                    v_isShared_3725_ = v_isSharedCheck_3776_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3726_ = l_Lean_Environment_setExporting(v_env_3715_, v_isExporting_3705_);
                v___x_3727_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
                if v_isShared_3725_ == 0 {
                    leanh::lean_ctor_set(v___x_3724_, 5, v___x_3727_);
                    leanh::lean_ctor_set(v___x_3724_, 0, v___x_3726_);
                    v___x_3729_ = v___x_3724_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3775_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3726_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_nextMacroScope_3716_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 2, v_ngen_3717_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 3, v_auxDeclNGen_3718_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 4, v_traceState_3719_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 5, v___x_3727_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 6, v_messages_3720_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 7, v_infoState_3721_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 8, v_snapshotTasks_3722_);
                    v___x_3729_ = v_reuseFailAlloc_3775_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3730_ = lean_st_ref_set(v___y_3709_, v___x_3729_);
                v___x_3731_ = lean_st_ref_take(v___y_3707_);
                v_mctx_3732_ = leanh::lean_ctor_get(v___x_3731_, 0);
                v_zetaDeltaFVarIds_3733_ = leanh::lean_ctor_get(v___x_3731_, 2);
                v_postponed_3734_ = leanh::lean_ctor_get(v___x_3731_, 3);
                v_diag_3735_ = leanh::lean_ctor_get(v___x_3731_, 4);
                v_isSharedCheck_3773_ = (!leanh::lean_is_exclusive(v___x_3731_)) as u8;
                if v_isSharedCheck_3773_ == 0 {
                    v_unused_3774_ = leanh::lean_ctor_get(v___x_3731_, 1);
                    leanh::lean_dec(v_unused_3774_);
                    v___x_3737_ = v___x_3731_;
                    v_isShared_3738_ = v_isSharedCheck_3773_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3735_);
                    leanh::lean_inc(v_postponed_3734_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3733_);
                    leanh::lean_inc(v_mctx_3732_);
                    leanh::lean_dec(v___x_3731_);
                    v___x_3737_ = leanh::lean_box(0);
                    v_isShared_3738_ = v_isSharedCheck_3773_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3739_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__3);
                if v_isShared_3738_ == 0 {
                    leanh::lean_ctor_set(v___x_3737_, 1, v___x_3739_);
                    v___x_3741_ = v___x_3737_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3772_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_mctx_3732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3772_, 1, v___x_3739_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3772_,
                        2,
                        v_zetaDeltaFVarIds_3733_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3772_, 3, v_postponed_3734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3772_, 4, v_diag_3735_);
                    v___x_3741_ = v_reuseFailAlloc_3772_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3742_ = lean_st_ref_set(v___y_3707_, v___x_3741_);
                leanh::lean_inc(v___y_3709_);
                leanh::lean_inc_ref(v___y_3708_);
                leanh::lean_inc(v___y_3707_);
                leanh::lean_inc_ref(v___y_3706_);
                v_r_3743_ = leanh::lean_apply_5(
                    v_x_3704_,
                    v___y_3706_,
                    v___y_3707_,
                    v___y_3708_,
                    v___y_3709_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_3743_) == 0 {
                    v_a_3744_ = leanh::lean_ctor_get(v_r_3743_, 0);
                    v_isSharedCheck_3760_ = (!leanh::lean_is_exclusive(v_r_3743_)) as u8;
                    if v_isSharedCheck_3760_ == 0 {
                        v___x_3746_ = v_r_3743_;
                        v_isShared_3747_ = v_isSharedCheck_3760_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3744_);
                        leanh::lean_dec(v_r_3743_);
                        v___x_3746_ = leanh::lean_box(0);
                        v_isShared_3747_ = v_isSharedCheck_3760_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3761_ = leanh::lean_ctor_get(v_r_3743_, 0);
                    leanh::lean_inc(v_a_3761_);
                    leanh::lean_dec_ref_known(v_r_3743_, 1);
                    v___x_3762_ = leanh::lean_box(0);
                    v___x_3763_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_3709_, v_isExporting_3713_, v___x_3727_, v___y_3707_, v___x_3739_, v___x_3762_);
                    v_isSharedCheck_3770_ = (!leanh::lean_is_exclusive(v___x_3763_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v_unused_3771_ = leanh::lean_ctor_get(v___x_3763_, 0);
                        leanh::lean_dec(v_unused_3771_);
                        v___x_3765_ = v___x_3763_;
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3763_);
                        v___x_3765_ = leanh::lean_box(0);
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc(v_a_3744_);
                if v_isShared_3747_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3746_, 1);
                    v___x_3749_ = v___x_3746_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3759_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3744_);
                    v___x_3749_ = v_reuseFailAlloc_3759_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3750_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___lam__0(v___y_3709_, v_isExporting_3713_, v___x_3727_, v___y_3707_, v___x_3739_, v___x_3749_);
                leanh::lean_dec_ref(v___x_3749_);
                v_isSharedCheck_3757_ = (!leanh::lean_is_exclusive(v___x_3750_)) as u8;
                if v_isSharedCheck_3757_ == 0 {
                    v_unused_3758_ = leanh::lean_ctor_get(v___x_3750_, 0);
                    leanh::lean_dec(v_unused_3758_);
                    v___x_3752_ = v___x_3750_;
                    v_isShared_3753_ = v_isSharedCheck_3757_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3750_);
                    v___x_3752_ = leanh::lean_box(0);
                    v_isShared_3753_ = v_isSharedCheck_3757_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3753_ == 0 {
                    leanh::lean_ctor_set(v___x_3752_, 0, v_a_3744_);
                    v___x_3755_ = v___x_3752_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3756_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3744_);
                    v___x_3755_ = v_reuseFailAlloc_3756_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3755_;
            }
            9 => {
                if v_isShared_3766_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3765_, 1);
                    leanh::lean_ctor_set(v___x_3765_, 0, v_a_3761_);
                    v___x_3768_ = v___x_3765_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3761_);
                    v___x_3768_ = v_reuseFailAlloc_3769_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___boxed(
    mut v_x_3778_: *mut leanh::LeanObject,
    mut v_isExporting_3779_: *mut leanh::LeanObject,
    mut v___y_3780_: *mut leanh::LeanObject,
    mut v___y_3781_: *mut leanh::LeanObject,
    mut v___y_3782_: *mut leanh::LeanObject,
    mut v___y_3783_: *mut leanh::LeanObject,
    mut v___y_3784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_3785_: u8 = 0;
    let mut v_res_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3785_ = (leanh::lean_unbox(v_isExporting_3779_) as u8);
    v_res_3786_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(
        v_x_3778_,
        v_isExporting_boxed_3785_,
        v___y_3780_,
        v___y_3781_,
        v___y_3782_,
        v___y_3783_,
    );
    leanh::lean_dec(v___y_3783_);
    leanh::lean_dec_ref(v___y_3782_);
    leanh::lean_dec(v___y_3781_);
    leanh::lean_dec_ref(v___y_3780_);
    return v_res_3786_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(
    mut v_00_u03b1_3787_: *mut leanh::LeanObject,
    mut v_x_3788_: *mut leanh::LeanObject,
    mut v_isExporting_3789_: u8,
    mut v___y_3790_: *mut leanh::LeanObject,
    mut v___y_3791_: *mut leanh::LeanObject,
    mut v___y_3792_: *mut leanh::LeanObject,
    mut v___y_3793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3795_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(
        v_x_3788_,
        v_isExporting_3789_,
        v___y_3790_,
        v___y_3791_,
        v___y_3792_,
        v___y_3793_,
    );
    return v___x_3795_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___boxed(
    mut v_00_u03b1_3796_: *mut leanh::LeanObject,
    mut v_x_3797_: *mut leanh::LeanObject,
    mut v_isExporting_3798_: *mut leanh::LeanObject,
    mut v___y_3799_: *mut leanh::LeanObject,
    mut v___y_3800_: *mut leanh::LeanObject,
    mut v___y_3801_: *mut leanh::LeanObject,
    mut v___y_3802_: *mut leanh::LeanObject,
    mut v___y_3803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_3804_: u8 = 0;
    let mut v_res_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3804_ = (leanh::lean_unbox(v_isExporting_3798_) as u8);
    v_res_3805_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0(
        v_00_u03b1_3796_,
        v_x_3797_,
        v_isExporting_boxed_3804_,
        v___y_3799_,
        v___y_3800_,
        v___y_3801_,
        v___y_3802_,
    );
    leanh::lean_dec(v___y_3802_);
    leanh::lean_dec_ref(v___y_3801_);
    leanh::lean_dec(v___y_3800_);
    leanh::lean_dec_ref(v___y_3799_);
    return v_res_3805_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(
    mut v_opts_3806_: *mut leanh::LeanObject,
    mut v_opt_3807_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3808_ = leanh::lean_ctor_get(v_opt_3807_, 0);
    v_defValue_3809_ = leanh::lean_ctor_get(v_opt_3807_, 1);
    v_map_3810_ = leanh::lean_ctor_get(v_opts_3806_, 0);
    v___x_3811_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3810_,
            v_name_3808_,
        );
    if leanh::lean_obj_tag(v___x_3811_) == 0 {
        let mut v___x_3812_: u8 = 0;
        v___x_3812_ = (leanh::lean_unbox(v_defValue_3809_) as u8);
        return v___x_3812_;
    } else {
        let mut v_val_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3813_ = leanh::lean_ctor_get(v___x_3811_, 0);
        leanh::lean_inc(v_val_3813_);
        leanh::lean_dec_ref_known(v___x_3811_, 1);
        if leanh::lean_obj_tag(v_val_3813_) == 1 {
            let mut v_v_3814_: u8 = 0;
            v_v_3814_ = leanh::lean_ctor_get_uint8(v_val_3813_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3813_, 0);
            return v_v_3814_;
        } else {
            let mut v___x_3815_: u8 = 0;
            leanh::lean_dec(v_val_3813_);
            v___x_3815_ = (leanh::lean_unbox(v_defValue_3809_) as u8);
            return v___x_3815_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5___boxed(
    mut v_opts_3816_: *mut leanh::LeanObject,
    mut v_opt_3817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3818_: u8 = 0;
    let mut v_r_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3818_ =
        l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(v_opts_3816_, v_opt_3817_);
    leanh::lean_dec_ref(v_opt_3817_);
    leanh::lean_dec_ref(v_opts_3816_);
    v_r_3819_ = leanh::lean_box((v_res_3818_) as usize);
    return v_r_3819_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(
    mut v_opts_3820_: *mut leanh::LeanObject,
    mut v_opt_3821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3822_ = leanh::lean_ctor_get(v_opt_3821_, 0);
    v_defValue_3823_ = leanh::lean_ctor_get(v_opt_3821_, 1);
    v_map_3824_ = leanh::lean_ctor_get(v_opts_3820_, 0);
    v___x_3825_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3824_,
            v_name_3822_,
        );
    if leanh::lean_obj_tag(v___x_3825_) == 0 {
        leanh::lean_inc(v_defValue_3823_);
        return v_defValue_3823_;
    } else {
        let mut v_val_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3826_ = leanh::lean_ctor_get(v___x_3825_, 0);
        leanh::lean_inc(v_val_3826_);
        leanh::lean_dec_ref_known(v___x_3825_, 1);
        if leanh::lean_obj_tag(v_val_3826_) == 3 {
            let mut v_v_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_3827_ = leanh::lean_ctor_get(v_val_3826_, 0);
            leanh::lean_inc(v_v_3827_);
            leanh::lean_dec_ref_known(v_val_3826_, 1);
            return v_v_3827_;
        } else {
            leanh::lean_dec(v_val_3826_);
            leanh::lean_inc(v_defValue_3823_);
            return v_defValue_3823_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6___boxed(
    mut v_opts_3828_: *mut leanh::LeanObject,
    mut v_opt_3829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3830_ =
        l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(v_opts_3828_, v_opt_3829_);
    leanh::lean_dec_ref(v_opt_3829_);
    leanh::lean_dec_ref(v_opts_3828_);
    return v_res_3830_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toLCNFType___lam__0(
    mut v_a_3831_: *mut leanh::LeanObject,
    mut v_diag_3832_: *mut leanh::LeanObject,
    mut v_a_x3f_3833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3842_: u8 = 0;
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3849_: u8 = 0;
    let mut v_unused_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3835_ = lean_st_ref_take(v_a_3831_);
                v_mctx_3836_ = leanh::lean_ctor_get(v___x_3835_, 0);
                v_cache_3837_ = leanh::lean_ctor_get(v___x_3835_, 1);
                v_zetaDeltaFVarIds_3838_ = leanh::lean_ctor_get(v___x_3835_, 2);
                v_postponed_3839_ = leanh::lean_ctor_get(v___x_3835_, 3);
                v_isSharedCheck_3849_ = (!leanh::lean_is_exclusive(v___x_3835_)) as u8;
                if v_isSharedCheck_3849_ == 0 {
                    v_unused_3850_ = leanh::lean_ctor_get(v___x_3835_, 4);
                    leanh::lean_dec(v_unused_3850_);
                    v___x_3841_ = v___x_3835_;
                    v_isShared_3842_ = v_isSharedCheck_3849_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_postponed_3839_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3838_);
                    leanh::lean_inc(v_cache_3837_);
                    leanh::lean_inc(v_mctx_3836_);
                    leanh::lean_dec(v___x_3835_);
                    v___x_3841_ = leanh::lean_box(0);
                    v_isShared_3842_ = v_isSharedCheck_3849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3842_ == 0 {
                    leanh::lean_ctor_set(v___x_3841_, 4, v_diag_3832_);
                    v___x_3844_ = v___x_3841_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_mctx_3836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_cache_3837_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3848_,
                        2,
                        v_zetaDeltaFVarIds_3838_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 3, v_postponed_3839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 4, v_diag_3832_);
                    v___x_3844_ = v_reuseFailAlloc_3848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3845_ = lean_st_ref_set(v_a_3831_, v___x_3844_);
                v___x_3846_ = leanh::lean_box(0);
                v___x_3847_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3847_, 0, v___x_3846_);
                return v___x_3847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_toLCNFType___lam__0___boxed(
    mut v_a_3851_: *mut leanh::LeanObject,
    mut v_diag_3852_: *mut leanh::LeanObject,
    mut v_a_x3f_3853_: *mut leanh::LeanObject,
    mut v___y_3854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3855_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_3851_, v_diag_3852_, v_a_x3f_3853_);
    leanh::lean_dec(v_a_x3f_3853_);
    leanh::lean_dec(v_a_3851_);
    return v_res_3855_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___lam__0(
    mut v_ps_3856_: *mut leanh::LeanObject,
    mut v_k_3857_: *mut leanh::LeanObject,
    mut v_v_3858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3859_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3859_, 0, v_k_3857_);
    leanh::lean_ctor_set(v___x_3859_, 1, v_v_3858_);
    v___x_3860_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3860_, 0, v___x_3859_);
    leanh::lean_ctor_set(v___x_3860_, 1, v_ps_3856_);
    return v___x_3860_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(
    mut v_f_3861_: *mut leanh::LeanObject,
    mut v_keys_3862_: *mut leanh::LeanObject,
    mut v_vals_3863_: *mut leanh::LeanObject,
    mut v_i_3864_: *mut leanh::LeanObject,
    mut v_acc_3865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v_k_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3866_ = lean_array_get_size(v_keys_3862_);
                v___x_3867_ = lean_nat_dec_lt(v_i_3864_, v___x_3866_);
                if v___x_3867_ == 0 {
                    leanh::lean_dec(v_i_3864_);
                    leanh::lean_dec(v_f_3861_);
                    return v_acc_3865_;
                } else {
                    v_k_3868_ = lean_array_fget_borrowed(v_keys_3862_, v_i_3864_);
                    v_v_3869_ = lean_array_fget_borrowed(v_vals_3863_, v_i_3864_);
                    leanh::lean_inc(v_f_3861_);
                    leanh::lean_inc(v_v_3869_);
                    leanh::lean_inc(v_k_3868_);
                    v___x_3870_ =
                        leanh::lean_apply_3(v_f_3861_, v_acc_3865_, v_k_3868_, v_v_3869_);
                    v___x_3871_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3872_ = lean_nat_add(v_i_3864_, v___x_3871_);
                    leanh::lean_dec(v_i_3864_);
                    v_i_3864_ = v___x_3872_;
                    v_acc_3865_ = v___x_3870_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg___boxed(
    mut v_f_3874_: *mut leanh::LeanObject,
    mut v_keys_3875_: *mut leanh::LeanObject,
    mut v_vals_3876_: *mut leanh::LeanObject,
    mut v_i_3877_: *mut leanh::LeanObject,
    mut v_acc_3878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3879_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_3874_, v_keys_3875_, v_vals_3876_, v_i_3877_, v_acc_3878_);
    leanh::lean_dec_ref(v_vals_3876_);
    leanh::lean_dec_ref(v_keys_3875_);
    return v_res_3879_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(
    mut v_f_3880_: *mut leanh::LeanObject,
    mut v_x_3881_: *mut leanh::LeanObject,
    mut v_x_3882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3881_) == 0 {
        let mut v_es_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3886_: u8 = 0;
        v_es_3883_ = leanh::lean_ctor_get(v_x_3881_, 0);
        v___x_3884_ = leanh::lean_unsigned_to_nat(0);
        v___x_3885_ = lean_array_get_size(v_es_3883_);
        v___x_3886_ = lean_nat_dec_lt(v___x_3884_, v___x_3885_);
        if v___x_3886_ == 0 {
            leanh::lean_dec(v_f_3880_);
            return v_x_3882_;
        } else {
            let mut v___x_3887_: u8 = 0;
            v___x_3887_ = lean_nat_dec_le(v___x_3885_, v___x_3885_);
            if v___x_3887_ == 0 {
                if v___x_3886_ == 0 {
                    leanh::lean_dec(v_f_3880_);
                    return v_x_3882_;
                } else {
                    let mut v___x_3888_: usize = 0;
                    let mut v___x_3889_: usize = 0;
                    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_3888_ = 0usize;
                    v___x_3889_ = lean_usize_of_nat(v___x_3885_);
                    v___x_3890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_3880_, v_es_3883_, v___x_3888_, v___x_3889_, v_x_3882_);
                    return v___x_3890_;
                }
            } else {
                let mut v___x_3891_: usize = 0;
                let mut v___x_3892_: usize = 0;
                let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3891_ = 0usize;
                v___x_3892_ = lean_usize_of_nat(v___x_3885_);
                v___x_3893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_3880_, v_es_3883_, v___x_3891_, v___x_3892_, v_x_3882_);
                return v___x_3893_;
            }
        }
    } else {
        let mut v_ks_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ks_3894_ = leanh::lean_ctor_get(v_x_3881_, 0);
        v_vs_3895_ = leanh::lean_ctor_get(v_x_3881_, 1);
        v___x_3896_ = leanh::lean_unsigned_to_nat(0);
        v___x_3897_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_3880_, v_ks_3894_, v_vs_3895_, v___x_3896_, v_x_3882_);
        return v___x_3897_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(
    mut v_f_3898_: *mut leanh::LeanObject,
    mut v_as_3899_: *mut leanh::LeanObject,
    mut v_i_3900_: usize,
    mut v_stop_3901_: usize,
    mut v_b_3902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: usize = 0;
    let mut v___x_3906_: usize = 0;
    let mut v___x_3908_: u8 = 0;
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3908_ = lean_usize_dec_eq(v_i_3900_, v_stop_3901_);
                if v___x_3908_ == 0 {
                    v___x_3909_ = lean_array_uget_borrowed(v_as_3899_, v_i_3900_);
                    match leanh::lean_obj_tag(v___x_3909_) {
                        0 => {
                            v_key_3910_ = leanh::lean_ctor_get(v___x_3909_, 0);
                            v_val_3911_ = leanh::lean_ctor_get(v___x_3909_, 1);
                            leanh::lean_inc(v_f_3898_);
                            leanh::lean_inc(v_val_3911_);
                            leanh::lean_inc(v_key_3910_);
                            v___x_3912_ = leanh::lean_apply_3(
                                v_f_3898_,
                                v_b_3902_,
                                v_key_3910_,
                                v_val_3911_,
                            );
                            v___y_3904_ = v___x_3912_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_3913_ = leanh::lean_ctor_get(v___x_3909_, 0);
                            leanh::lean_inc(v_f_3898_);
                            v___x_3914_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_3898_, v_node_3913_, v_b_3902_);
                            v___y_3904_ = v___x_3914_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_3904_ = v_b_3902_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_f_3898_);
                    return v_b_3902_;
                }
            }
            1 => {
                v___x_3905_ = 1usize;
                v___x_3906_ = lean_usize_add(v_i_3900_, v___x_3905_);
                v_i_3900_ = v___x_3906_;
                v_b_3902_ = v___y_3904_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg___boxed(
    mut v_f_3915_: *mut leanh::LeanObject,
    mut v_as_3916_: *mut leanh::LeanObject,
    mut v_i_3917_: *mut leanh::LeanObject,
    mut v_stop_3918_: *mut leanh::LeanObject,
    mut v_b_3919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3920_: usize = 0;
    let mut v_stop_boxed_3921_: usize = 0;
    let mut v_res_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3920_ = leanh::lean_unbox_usize(v_i_3917_);
    leanh::lean_dec(v_i_3917_);
    v_stop_boxed_3921_ = leanh::lean_unbox_usize(v_stop_3918_);
    leanh::lean_dec(v_stop_3918_);
    v_res_3922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_3915_, v_as_3916_, v_i_boxed_3920_, v_stop_boxed_3921_, v_b_3919_);
    leanh::lean_dec_ref(v_as_3916_);
    return v_res_3922_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg___boxed(
    mut v_f_3923_: *mut leanh::LeanObject,
    mut v_x_3924_: *mut leanh::LeanObject,
    mut v_x_3925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3926_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_3923_, v_x_3924_, v_x_3925_);
    leanh::lean_dec_ref(v_x_3924_);
    return v_res_3926_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0(
    mut v_f_3927_: *mut leanh::LeanObject,
    mut v_x1_3928_: *mut leanh::LeanObject,
    mut v_x2_3929_: *mut leanh::LeanObject,
    mut v_x3_3930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3931_ = leanh::lean_apply_3(v_f_3927_, v_x1_3928_, v_x2_3929_, v_x3_3930_);
    return v___x_3931_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(
    mut v_map_3932_: *mut leanh::LeanObject,
    mut v_f_3933_: *mut leanh::LeanObject,
    mut v_init_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3935_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_3935_, 0, v_f_3933_);
    v___x_3936_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v___f_3935_, v_map_3932_, v_init_3934_);
    return v___x_3936_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg___boxed(
    mut v_map_3937_: *mut leanh::LeanObject,
    mut v_f_3938_: *mut leanh::LeanObject,
    mut v_init_3939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3940_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_3937_, v_f_3938_, v_init_3939_);
    leanh::lean_dec_ref(v_map_3937_);
    return v_res_3940_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(
    mut v_m_3942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3943_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___closed__0;
    v___x_3944_ = leanh::lean_box(0);
    v___x_3945_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_m_3942_, v___f_3943_, v___x_3944_);
    return v___x_3945_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg___boxed(
    mut v_m_3946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3947_ =
        l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(
            v_m_3946_,
        );
    leanh::lean_dec_ref(v_m_3946_);
    return v_res_3947_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(
    mut v_o_3951_: *mut leanh::LeanObject,
    mut v_k_3952_: *mut leanh::LeanObject,
    mut v_v_3953_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3955_: u8 = 0;
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3958_: u8 = 0;
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: u8 = 0;
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3969_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3954_ = leanh::lean_ctor_get(v_o_3951_, 0);
                v_hasTrace_3955_ = leanh::lean_ctor_get_uint8(
                    v_o_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3969_ = (!leanh::lean_is_exclusive(v_o_3951_)) as u8;
                if v_isSharedCheck_3969_ == 0 {
                    v___x_3957_ = v_o_3951_;
                    v_isShared_3958_ = v_isSharedCheck_3969_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_3954_);
                    leanh::lean_dec(v_o_3951_);
                    v___x_3957_ = leanh::lean_box(0);
                    v_isShared_3958_ = v_isSharedCheck_3969_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3959_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_3959_, 0 as u32, v_v_3953_);
                leanh::lean_inc(v_k_3952_);
                v___x_3960_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3952_, v___x_3959_, v_map_3954_);
                if v_hasTrace_3955_ == 0 {
                    v___x_3961_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___closed__1;
                    v___x_3962_ = l_Lean_Name_isPrefixOf(v___x_3961_, v_k_3952_);
                    leanh::lean_dec(v_k_3952_);
                    if v_isShared_3958_ == 0 {
                        leanh::lean_ctor_set(v___x_3957_, 0, v___x_3960_);
                        v___x_3964_ = v___x_3957_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3965_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3960_);
                        v___x_3964_ = v_reuseFailAlloc_3965_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_3952_);
                    if v_isShared_3958_ == 0 {
                        leanh::lean_ctor_set(v___x_3957_, 0, v___x_3960_);
                        v___x_3967_ = v___x_3957_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3968_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3960_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_3968_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_3955_,
                        );
                        v___x_3967_ = v_reuseFailAlloc_3968_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3964_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3962_,
                );
                return v___x_3964_;
            }
            3 => {
                return v___x_3967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6___boxed(
    mut v_o_3970_: *mut leanh::LeanObject,
    mut v_k_3971_: *mut leanh::LeanObject,
    mut v_v_3972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_3973_: u8 = 0;
    let mut v_res_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_3973_ = (leanh::lean_unbox(v_v_3972_) as u8);
    v_res_3974_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(v_o_3970_, v_k_3971_, v_v_boxed_3973_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(
    mut v_opts_3975_: *mut leanh::LeanObject,
    mut v_opt_3976_: *mut leanh::LeanObject,
    mut v_val_3977_: u8,
) -> *mut leanh::LeanObject {
    let mut v_name_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3978_ = leanh::lean_ctor_get(v_opt_3976_, 0);
    leanh::lean_inc(v_name_3978_);
    leanh::lean_dec_ref(v_opt_3976_);
    v___x_3979_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4_spec__6(v_opts_3975_, v_name_3978_, v_val_3977_);
    return v___x_3979_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4___boxed(
    mut v_opts_3980_: *mut leanh::LeanObject,
    mut v_opt_3981_: *mut leanh::LeanObject,
    mut v_val_3982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_3983_: u8 = 0;
    let mut v_res_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_3983_ = (leanh::lean_unbox(v_val_3982_) as u8);
    v_res_3984_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(
        v_opts_3980_,
        v_opt_3981_,
        v_val_boxed_3983_,
    );
    return v_res_3984_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(
    mut v_keys_3985_: *mut leanh::LeanObject,
    mut v_vals_3986_: *mut leanh::LeanObject,
    mut v_i_3987_: *mut leanh::LeanObject,
    mut v_k_3988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: u8 = 0;
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: u8 = 0;
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3989_ = lean_array_get_size(v_keys_3985_);
                v___x_3990_ = lean_nat_dec_lt(v_i_3987_, v___x_3989_);
                if v___x_3990_ == 0 {
                    leanh::lean_dec(v_i_3987_);
                    v___x_3991_ = leanh::lean_box(0);
                    return v___x_3991_;
                } else {
                    v_k_x27_3992_ = lean_array_fget_borrowed(v_keys_3985_, v_i_3987_);
                    v___x_3993_ = lean_name_eq(v_k_3988_, v_k_x27_3992_);
                    if v___x_3993_ == 0 {
                        v___x_3994_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3995_ = lean_nat_add(v_i_3987_, v___x_3994_);
                        leanh::lean_dec(v_i_3987_);
                        v_i_3987_ = v___x_3995_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3997_ = lean_array_fget_borrowed(v_vals_3986_, v_i_3987_);
                        leanh::lean_dec(v_i_3987_);
                        leanh::lean_inc(v___x_3997_);
                        v___x_3998_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3998_, 0, v___x_3997_);
                        return v___x_3998_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_keys_3999_: *mut leanh::LeanObject,
    mut v_vals_4000_: *mut leanh::LeanObject,
    mut v_i_4001_: *mut leanh::LeanObject,
    mut v_k_4002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4003_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_keys_3999_, v_vals_4000_, v_i_4001_, v_k_4002_);
    leanh::lean_dec(v_k_4002_);
    leanh::lean_dec_ref(v_vals_4000_);
    leanh::lean_dec_ref(v_keys_3999_);
    return v_res_4003_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_4004_: usize = 0;
    let mut v___x_4005_: usize = 0;
    let mut v___x_4006_: usize = 0;
    v___x_4004_ = 5usize;
    v___x_4005_ = 1usize;
    v___x_4006_ = lean_usize_shift_left(v___x_4005_, v___x_4004_);
    return v___x_4006_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_4007_: usize = 0;
    let mut v___x_4008_: usize = 0;
    let mut v___x_4009_: usize = 0;
    v___x_4007_ = 1usize;
    v___x_4008_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__0);
    v___x_4009_ = lean_usize_sub(v___x_4008_, v___x_4007_);
    return v___x_4009_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(
    mut v_x_4010_: *mut leanh::LeanObject,
    mut v_x_4011_: usize,
    mut v_x_4012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: usize = 0;
    let mut v___x_4016_: usize = 0;
    let mut v___x_4017_: usize = 0;
    let mut v_j_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: usize = 0;
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4010_) == 0 {
                    v_es_4013_ = leanh::lean_ctor_get(v_x_4010_, 0);
                    v___x_4014_ = leanh::lean_box(2);
                    v___x_4015_ = 5usize;
                    v___x_4016_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___closed__1);
                    v___x_4017_ = lean_usize_land(v_x_4011_, v___x_4016_);
                    v_j_4018_ = lean_usize_to_nat(v___x_4017_);
                    v___x_4019_ = lean_array_get_borrowed(v___x_4014_, v_es_4013_, v_j_4018_);
                    leanh::lean_dec(v_j_4018_);
                    match leanh::lean_obj_tag(v___x_4019_) {
                        0 => {
                            v_key_4020_ = leanh::lean_ctor_get(v___x_4019_, 0);
                            v_val_4021_ = leanh::lean_ctor_get(v___x_4019_, 1);
                            v___x_4022_ = lean_name_eq(v_x_4012_, v_key_4020_);
                            if v___x_4022_ == 0 {
                                v___x_4023_ = leanh::lean_box(0);
                                return v___x_4023_;
                            } else {
                                leanh::lean_inc(v_val_4021_);
                                v___x_4024_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4024_, 0, v_val_4021_);
                                return v___x_4024_;
                            }
                        }
                        1 => {
                            v_node_4025_ = leanh::lean_ctor_get(v___x_4019_, 0);
                            v___x_4026_ = lean_usize_shift_right(v_x_4011_, v___x_4015_);
                            v_x_4010_ = v_node_4025_;
                            v_x_4011_ = v___x_4026_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4028_ = leanh::lean_box(0);
                            return v___x_4028_;
                        }
                    }
                } else {
                    v_ks_4029_ = leanh::lean_ctor_get(v_x_4010_, 0);
                    v_vs_4030_ = leanh::lean_ctor_get(v_x_4010_, 1);
                    v___x_4031_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4032_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_ks_4029_, v_vs_4030_, v___x_4031_, v_x_4012_);
                    return v___x_4032_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg___boxed(
    mut v_x_4033_: *mut leanh::LeanObject,
    mut v_x_4034_: *mut leanh::LeanObject,
    mut v_x_4035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_18769__boxed_4036_: usize = 0;
    let mut v_res_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_18769__boxed_4036_ = leanh::lean_unbox_usize(v_x_4034_);
    leanh::lean_dec(v_x_4034_);
    v_res_4037_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_4033_, v_x_18769__boxed_4036_, v_x_4035_);
    leanh::lean_dec(v_x_4035_);
    leanh::lean_dec_ref(v_x_4033_);
    return v_res_4037_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0()
-> u64 {
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: u64 = 0;
    v___x_4038_ = leanh::lean_unsigned_to_nat(1723);
    v___x_4039_ = lean_uint64_of_nat(v___x_4038_);
    return v___x_4039_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(
    mut v_x_4040_: *mut leanh::LeanObject,
    mut v_x_4041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4043_: u64 = 0;
    let mut v___x_4044_: usize = 0;
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: u64 = 0;
    let mut v_hash_4047_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4041_) == 0 {
                    v___x_4046_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___closed__0);
                    v___y_4043_ = v___x_4046_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4047_ = leanh::lean_ctor_get_uint64(
                        v_x_4041_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4043_ = v_hash_4047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4044_ = lean_uint64_to_usize(v___y_4043_);
                v___x_4045_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_4040_, v___x_4044_, v_x_4041_);
                return v___x_4045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg___boxed(
    mut v_x_4048_: *mut leanh::LeanObject,
    mut v_x_4049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4050_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(
            v_x_4048_, v_x_4049_,
        );
    leanh::lean_dec(v_x_4049_);
    leanh::lean_dec_ref(v_x_4048_);
    return v_res_4050_;
}
pub unsafe fn _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4052_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__0;
    v___x_4053_ = l_Lean_stringToMessageData(v___x_4052_);
    return v___x_4053_;
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(
    mut v___x_4054_: *mut leanh::LeanObject,
    mut v___x_4055_: u8,
    mut v___x_4056_: *mut leanh::LeanObject,
    mut v_a_4057_: *mut leanh::LeanObject,
    mut v_a_4058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4064_: u8 = 0;
    let mut v_fst_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4069_: u8 = 0;
    let mut v___y_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4087_: u8 = 0;
    let mut v_unfoldAxiomCounter_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: u8 = 0;
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4100_: u8 = 0;
    let mut v_isSharedCheck_4101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4057_) == 0 {
                    leanh::lean_dec_ref(v___x_4056_);
                    v___x_4059_ = lean_array_to_list(v_a_4058_);
                    return v___x_4059_;
                } else {
                    v_head_4060_ = leanh::lean_ctor_get(v_a_4057_, 0);
                    v_tail_4061_ = leanh::lean_ctor_get(v_a_4057_, 1);
                    v_isSharedCheck_4101_ = (!leanh::lean_is_exclusive(v_a_4057_)) as u8;
                    if v_isSharedCheck_4101_ == 0 {
                        v___x_4063_ = v_a_4057_;
                        v_isShared_4064_ = v_isSharedCheck_4101_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4061_);
                        leanh::lean_inc(v_head_4060_);
                        leanh::lean_dec(v_a_4057_);
                        v___x_4063_ = leanh::lean_box(0);
                        v_isShared_4064_ = v_isSharedCheck_4101_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4065_ = leanh::lean_ctor_get(v_head_4060_, 0);
                v_snd_4066_ = leanh::lean_ctor_get(v_head_4060_, 1);
                v_isSharedCheck_4100_ = (!leanh::lean_is_exclusive(v_head_4060_)) as u8;
                if v_isSharedCheck_4100_ == 0 {
                    v___x_4068_ = v_head_4060_;
                    v_isShared_4069_ = v_isSharedCheck_4100_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4066_);
                    leanh::lean_inc(v_fst_4065_);
                    leanh::lean_dec(v_head_4060_);
                    v___x_4068_ = leanh::lean_box(0);
                    v_isShared_4069_ = v_isSharedCheck_4100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_unfoldAxiomCounter_4089_ = leanh::lean_ctor_get(v___x_4054_, 1);
                v___x_4090_ = leanh::lean_unsigned_to_nat(0);
                v___x_4098_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(v_unfoldAxiomCounter_4089_, v_fst_4065_);
                if leanh::lean_obj_tag(v___x_4098_) == 0 {
                    v___y_4092_ = v___x_4090_;
                    state = 7;
                    continue;
                } else {
                    v_val_4099_ = leanh::lean_ctor_get(v___x_4098_, 0);
                    leanh::lean_inc(v_val_4099_);
                    leanh::lean_dec_ref_known(v___x_4098_, 1);
                    v___y_4092_ = v_val_4099_;
                    state = 7;
                    continue;
                }
            }
            3 => {
                v___x_4072_ = l_Lean_MessageData_ofConstName(v_fst_4065_, v___x_4055_);
                v___x_4073_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1), core::ptr::addr_of_mut!(l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1_once), _init_l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___closed__1);
                if v_isShared_4069_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4068_, 7);
                    leanh::lean_ctor_set(v___x_4068_, 1, v___x_4073_);
                    leanh::lean_ctor_set(v___x_4068_, 0, v___x_4072_);
                    v___x_4075_ = v___x_4068_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4084_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 1, v___x_4073_);
                    v___x_4075_ = v_reuseFailAlloc_4084_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4076_ = l_Nat_reprFast(v___y_4071_);
                v___x_4077_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4077_, 0, v___x_4076_);
                v___x_4078_ = l_Lean_MessageData_ofFormat(v___x_4077_);
                if v_isShared_4064_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4063_, 7);
                    leanh::lean_ctor_set(v___x_4063_, 1, v___x_4078_);
                    leanh::lean_ctor_set(v___x_4063_, 0, v___x_4075_);
                    v___x_4080_ = v___x_4063_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4083_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4083_, 0, v___x_4075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4083_, 1, v___x_4078_);
                    v___x_4080_ = v_reuseFailAlloc_4083_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4081_ = lean_array_push(v_a_4058_, v___x_4080_);
                v_a_4057_ = v_tail_4061_;
                v_a_4058_ = v___x_4081_;
                state = 0;
                continue;
            }
            6 => {
                if v___y_4087_ == 0 {
                    leanh::lean_dec(v___y_4086_);
                    leanh::lean_del_object(v___x_4068_);
                    leanh::lean_dec(v_fst_4065_);
                    leanh::lean_del_object(v___x_4063_);
                    v_a_4057_ = v_tail_4061_;
                    state = 0;
                    continue;
                } else {
                    v___y_4071_ = v___y_4086_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_4093_ = lean_nat_sub(v_snd_4066_, v___y_4092_);
                leanh::lean_dec(v___y_4092_);
                leanh::lean_dec(v_snd_4066_);
                v___x_4094_ = lean_nat_dec_lt(v___x_4090_, v___x_4093_);
                if v___x_4094_ == 0 {
                    v___y_4086_ = v___x_4093_;
                    v___y_4087_ = v___x_4094_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_4065_);
                    leanh::lean_inc_ref(v___x_4056_);
                    v___x_4095_ = l_Lean_getOriginalConstKind_x3f(v___x_4056_, v_fst_4065_);
                    if leanh::lean_obj_tag(v___x_4095_) == 1 {
                        v_val_4096_ = leanh::lean_ctor_get(v___x_4095_, 0);
                        leanh::lean_inc(v_val_4096_);
                        leanh::lean_dec_ref_known(v___x_4095_, 1);
                        v___x_4097_ = (leanh::lean_unbox(v_val_4096_) as u8);
                        leanh::lean_dec(v_val_4096_);
                        if v___x_4097_ == 0 {
                            v___y_4071_ = v___x_4093_;
                            state = 3;
                            continue;
                        } else {
                            v___y_4086_ = v___x_4093_;
                            v___y_4087_ = v___x_4055_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4095_);
                        v___y_4086_ = v___x_4093_;
                        v___y_4087_ = v___x_4055_;
                        state = 6;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3___boxed(
    mut v___x_4102_: *mut leanh::LeanObject,
    mut v___x_4103_: *mut leanh::LeanObject,
    mut v___x_4104_: *mut leanh::LeanObject,
    mut v_a_4105_: *mut leanh::LeanObject,
    mut v_a_4106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_18850__boxed_4107_: u8 = 0;
    let mut v_res_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_18850__boxed_4107_ = (leanh::lean_unbox(v___x_4103_) as u8);
    v_res_4108_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(
        v___x_4102_,
        v___x_18850__boxed_4107_,
        v___x_4104_,
        v_a_4105_,
        v_a_4106_,
    );
    leanh::lean_dec_ref(v___x_4102_);
    return v_res_4108_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4110_ = l_Lean_Compiler_LCNF_toLCNFType___closed__0;
    v___x_4111_ = l_Lean_stringToMessageData(v___x_4110_);
    return v___x_4111_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4113_ = l_Lean_Compiler_LCNF_toLCNFType___closed__2;
    v___x_4114_ = l_Lean_stringToMessageData(v___x_4113_);
    return v___x_4114_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4116_ = l_Lean_Compiler_LCNF_toLCNFType___closed__4;
    v___x_4117_ = l_Lean_stringToMessageData(v___x_4116_);
    return v___x_4117_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4119_ = l_Lean_Compiler_LCNF_toLCNFType___closed__6;
    v___x_4120_ = l_Lean_stringToMessageData(v___x_4119_);
    return v___x_4120_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4122_ = l_Lean_Compiler_LCNF_toLCNFType___closed__8;
    v___x_4123_ = l_Lean_stringToMessageData(v___x_4122_);
    return v___x_4123_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12() -> *mut leanh::LeanObject
{
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_Compiler_LCNF_toLCNFType___closed__11;
    v___x_4128_ = l_Lean_stringToMessageData(v___x_4127_);
    return v___x_4128_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13() -> *mut leanh::LeanObject
{
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4129_ = leanh::lean_box(1);
    v___x_4130_ = l_Lean_MessageData_ofFormat(v___x_4129_);
    return v___x_4130_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15() -> *mut leanh::LeanObject
{
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4132_ = l_Lean_Compiler_LCNF_toLCNFType___closed__14;
    v___x_4133_ = l_Lean_stringToMessageData(v___x_4132_);
    return v___x_4133_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toLCNFType(
    mut v_type_4134_: *mut leanh::LeanObject,
    mut v_a_4135_: *mut leanh::LeanObject,
    mut v_a_4136_: *mut leanh::LeanObject,
    mut v_a_4137_: *mut leanh::LeanObject,
    mut v_a_4138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_4149_: u8 = 0;
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4157_: u8 = 0;
    let mut v___x_4158_: u8 = 0;
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4174_: u8 = 0;
    let mut v_inheritedTraceOptions_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4197_: u8 = 0;
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4207_: u8 = 0;
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4211_: u8 = 0;
    let mut v_reuseFailAlloc_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4213_: u8 = 0;
    let mut v_unused_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldAxiomCounter_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: u8 = 0;
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4238_: u8 = 0;
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4243_: u8 = 0;
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut v_unused_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: u8 = 0;
    let mut v_fileName_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4262_: u8 = 0;
    let mut v_inheritedTraceOptions_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: u8 = 0;
    let mut v___x_4271_: u8 = 0;
    let mut v___y_4273_: u8 = 0;
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4285_: u8 = 0;
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4292_: u8 = 0;
    let mut v_unused_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: u8 = 0;
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4298_: u8 = 0;
    let mut v_a_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4301_: u8 = 0;
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4304_: u8 = 0;
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4308_: u8 = 0;
    let mut v_unused_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: u8 = 0;
    let mut v___x_4311_: u8 = 0;
    let mut v_isSharedCheck_4312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_type_4134_);
                v___x_4140_ = leanh::lean_alloc_closure(
                    l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go___boxed
                        as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___x_4140_, 0, v_type_4134_);
                v___x_4141_ =
                    l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_go(
                        v_type_4134_,
                        v_a_4135_,
                        v_a_4136_,
                        v_a_4137_,
                        v_a_4138_,
                    );
                if leanh::lean_obj_tag(v___x_4141_) == 0 {
                    v_a_4142_ = leanh::lean_ctor_get(v___x_4141_, 0);
                    v_isSharedCheck_4312_ = (!leanh::lean_is_exclusive(v___x_4141_)) as u8;
                    if v_isSharedCheck_4312_ == 0 {
                        v___x_4144_ = v___x_4141_;
                        v_isShared_4145_ = v_isSharedCheck_4312_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4142_);
                        leanh::lean_dec(v___x_4141_);
                        v___x_4144_ = leanh::lean_box(0);
                        v_isShared_4145_ = v_isSharedCheck_4312_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4140_);
                    return v___x_4141_;
                }
            }
            1 => {
                v___x_4146_ = lean_st_ref_get(v_a_4138_);
                v_env_4147_ = leanh::lean_ctor_get(v___x_4146_, 0);
                leanh::lean_inc_ref(v_env_4147_);
                leanh::lean_dec(v___x_4146_);
                v___x_4148_ = l_Lean_Environment_header(v_env_4147_);
                leanh::lean_dec_ref(v_env_4147_);
                v_isModule_4149_ = leanh::lean_ctor_get_uint8(
                    v___x_4148_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                );
                leanh::lean_dec_ref(v___x_4148_);
                if v_isModule_4149_ == 0 {
                    leanh::lean_dec_ref(v___x_4140_);
                    if v_isShared_4145_ == 0 {
                        v___x_4151_ = v___x_4144_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4152_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4142_);
                        v___x_4151_ = v_reuseFailAlloc_4152_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4144_);
                    leanh::lean_inc_ref(v___x_4140_);
                    v___x_4153_ = l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(v___x_4140_, v_isModule_4149_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
                    if leanh::lean_obj_tag(v___x_4153_) == 0 {
                        v_a_4154_ = leanh::lean_ctor_get(v___x_4153_, 0);
                        v_isSharedCheck_4298_ =
                            (!leanh::lean_is_exclusive(v___x_4153_)) as u8;
                        if v_isSharedCheck_4298_ == 0 {
                            v___x_4156_ = v___x_4153_;
                            v_isShared_4157_ = v_isSharedCheck_4298_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4154_);
                            leanh::lean_dec(v___x_4153_);
                            v___x_4156_ = leanh::lean_box(0);
                            v_isShared_4157_ = v_isSharedCheck_4298_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_4140_);
                        v_a_4299_ = leanh::lean_ctor_get(v___x_4153_, 0);
                        leanh::lean_inc(v_a_4299_);
                        v___x_4310_ = l_Lean_Exception_isInterrupt(v_a_4299_);
                        if v___x_4310_ == 0 {
                            v___x_4311_ = l_Lean_Exception_isRuntime(v_a_4299_);
                            v___y_4301_ = v___x_4311_;
                            state = 18;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_4299_);
                            v___y_4301_ = v___x_4310_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4151_;
            }
            3 => {
                v___x_4158_ = lean_expr_eqv(v_a_4142_, v_a_4154_);
                if v___x_4158_ == 0 {
                    leanh::lean_del_object(v___x_4156_);
                    v___x_4159_ = lean_st_ref_get(v_a_4136_);
                    v___x_4160_ = lean_st_ref_get(v_a_4138_);
                    v_diag_4161_ = leanh::lean_ctor_get(v___x_4159_, 4);
                    leanh::lean_inc_ref(v_diag_4161_);
                    leanh::lean_dec(v___x_4159_);
                    v_fileName_4162_ = leanh::lean_ctor_get(v_a_4137_, 0);
                    v_fileMap_4163_ = leanh::lean_ctor_get(v_a_4137_, 1);
                    v_options_4164_ = leanh::lean_ctor_get(v_a_4137_, 2);
                    v_currRecDepth_4165_ = leanh::lean_ctor_get(v_a_4137_, 3);
                    v_ref_4166_ = leanh::lean_ctor_get(v_a_4137_, 5);
                    v_currNamespace_4167_ = leanh::lean_ctor_get(v_a_4137_, 6);
                    v_openDecls_4168_ = leanh::lean_ctor_get(v_a_4137_, 7);
                    v_initHeartbeats_4169_ = leanh::lean_ctor_get(v_a_4137_, 8);
                    v_maxHeartbeats_4170_ = leanh::lean_ctor_get(v_a_4137_, 9);
                    v_quotContext_4171_ = leanh::lean_ctor_get(v_a_4137_, 10);
                    v_currMacroScope_4172_ = leanh::lean_ctor_get(v_a_4137_, 11);
                    v_cancelTk_x3f_4173_ = leanh::lean_ctor_get(v_a_4137_, 12);
                    v_suppressElabErrors_4174_ = leanh::lean_ctor_get_uint8(
                        v_a_4137_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_4175_ = leanh::lean_ctor_get(v_a_4137_, 13);
                    v_env_4176_ = leanh::lean_ctor_get(v___x_4160_, 0);
                    leanh::lean_inc_ref(v_env_4176_);
                    leanh::lean_dec(v___x_4160_);
                    v___x_4177_ = l_Lean_diagnostics;
                    leanh::lean_inc_ref(v_options_4164_);
                    v___x_4178_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_toLCNFType_spec__4(
                        v_options_4164_,
                        v___x_4177_,
                        v_isModule_4149_,
                    );
                    v___x_4179_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_toLCNFType___closed__1,
                    );
                    v___x_4180_ = l_Lean_MessageData_ofExpr(v_a_4142_);
                    v___x_4181_ = l_Lean_indentD(v___x_4180_);
                    v___x_4182_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4182_, 0, v___x_4179_);
                    leanh::lean_ctor_set(v___x_4182_, 1, v___x_4181_);
                    v___x_4183_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__3_once),
                        _init_l_Lean_Compiler_LCNF_toLCNFType___closed__3,
                    );
                    v___x_4184_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4184_, 0, v___x_4182_);
                    leanh::lean_ctor_set(v___x_4184_, 1, v___x_4183_);
                    v___x_4185_ = l_Lean_MessageData_ofExpr(v_a_4154_);
                    v___x_4186_ = l_Lean_indentD(v___x_4185_);
                    v___x_4187_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4187_, 0, v___x_4184_);
                    leanh::lean_ctor_set(v___x_4187_, 1, v___x_4186_);
                    v___x_4188_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__5_once),
                        _init_l_Lean_Compiler_LCNF_toLCNFType___closed__5,
                    );
                    v___x_4189_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4189_, 0, v___x_4187_);
                    leanh::lean_ctor_set(v___x_4189_, 1, v___x_4188_);
                    v___x_4249_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__5(
                        v___x_4178_,
                        v___x_4177_,
                    );
                    v___x_4294_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4176_);
                    leanh::lean_dec_ref(v_env_4176_);
                    if v___x_4294_ == 0 {
                        if v___x_4249_ == 0 {
                            v_fileName_4251_ = v_fileName_4162_;
                            v_fileMap_4252_ = v_fileMap_4163_;
                            v_currRecDepth_4253_ = v_currRecDepth_4165_;
                            v_ref_4254_ = v_ref_4166_;
                            v_currNamespace_4255_ = v_currNamespace_4167_;
                            v_openDecls_4256_ = v_openDecls_4168_;
                            v_initHeartbeats_4257_ = v_initHeartbeats_4169_;
                            v_maxHeartbeats_4258_ = v_maxHeartbeats_4170_;
                            v_quotContext_4259_ = v_quotContext_4171_;
                            v_currMacroScope_4260_ = v_currMacroScope_4172_;
                            v_cancelTk_x3f_4261_ = v_cancelTk_x3f_4173_;
                            v_suppressElabErrors_4262_ = v_suppressElabErrors_4174_;
                            v_inheritedTraceOptions_4263_ = v_inheritedTraceOptions_4175_;
                            v___y_4264_ = v_a_4138_;
                            state = 13;
                            continue;
                        } else {
                            v___y_4273_ = v___x_4294_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___y_4273_ = v___x_4249_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4154_);
                    leanh::lean_dec_ref(v___x_4140_);
                    if v_isShared_4157_ == 0 {
                        leanh::lean_ctor_set(v___x_4156_, 0, v_a_4142_);
                        v___x_4296_ = v___x_4156_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_4297_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4142_);
                        v___x_4296_ = v_reuseFailAlloc_4297_;
                        state = 17;
                        continue;
                    }
                }
            }
            4 => {
                leanh::lean_inc_ref(v_a_4191_);
                v___x_4192_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4192_, 0, v_a_4191_);
                v___x_4193_ =
                    l_Lean_Compiler_LCNF_toLCNFType___lam__0(v_a_4136_, v_diag_4161_, v___x_4192_);
                leanh::lean_dec_ref_known(v___x_4192_, 1);
                leanh::lean_dec_ref(v___x_4193_);
                v_snd_4194_ = leanh::lean_ctor_get(v_a_4191_, 1);
                v_isSharedCheck_4213_ = (!leanh::lean_is_exclusive(v_a_4191_)) as u8;
                if v_isSharedCheck_4213_ == 0 {
                    v_unused_4214_ = leanh::lean_ctor_get(v_a_4191_, 0);
                    leanh::lean_dec(v_unused_4214_);
                    v___x_4196_ = v_a_4191_;
                    v_isShared_4197_ = v_isSharedCheck_4213_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4194_);
                    leanh::lean_dec(v_a_4191_);
                    v___x_4196_ = leanh::lean_box(0);
                    v_isShared_4197_ = v_isSharedCheck_4213_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4198_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__7_once),
                    _init_l_Lean_Compiler_LCNF_toLCNFType___closed__7,
                );
                if v_isShared_4197_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4196_, 7);
                    leanh::lean_ctor_set(v___x_4196_, 0, v___x_4198_);
                    v___x_4200_ = v___x_4196_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4212_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4198_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 1, v_snd_4194_);
                    v___x_4200_ = v_reuseFailAlloc_4212_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4201_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__9_once),
                    _init_l_Lean_Compiler_LCNF_toLCNFType___closed__9,
                );
                v___x_4202_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4202_, 0, v___x_4200_);
                leanh::lean_ctor_set(v___x_4202_, 1, v___x_4201_);
                v___x_4203_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__5___redArg(v___x_4202_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
                v_a_4204_ = leanh::lean_ctor_get(v___x_4203_, 0);
                v_isSharedCheck_4211_ = (!leanh::lean_is_exclusive(v___x_4203_)) as u8;
                if v_isSharedCheck_4211_ == 0 {
                    v___x_4206_ = v___x_4203_;
                    v_isShared_4207_ = v_isSharedCheck_4211_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4204_);
                    leanh::lean_dec(v___x_4203_);
                    v___x_4206_ = leanh::lean_box(0);
                    v_isShared_4207_ = v_isSharedCheck_4211_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4207_ == 0 {
                    v___x_4209_ = v___x_4206_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4210_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
                    v___x_4209_ = v_reuseFailAlloc_4210_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4209_;
            }
            9 => {
                v___x_4216_ = lean_st_ref_get(v_a_4138_);
                v___x_4217_ = lean_st_ref_get(v_a_4136_);
                v_diag_4218_ = leanh::lean_ctor_get(v___x_4217_, 4);
                leanh::lean_inc_ref(v_diag_4218_);
                leanh::lean_dec(v___x_4217_);
                v_env_4219_ = leanh::lean_ctor_get(v___x_4216_, 0);
                leanh::lean_inc_ref(v_env_4219_);
                leanh::lean_dec(v___x_4216_);
                v_unfoldAxiomCounter_4220_ = leanh::lean_ctor_get(v_diag_4218_, 1);
                leanh::lean_inc_ref(v_unfoldAxiomCounter_4220_);
                leanh::lean_dec_ref(v_diag_4218_);
                v___x_4221_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(v_unfoldAxiomCounter_4220_);
                leanh::lean_dec_ref(v_unfoldAxiomCounter_4220_);
                v___x_4222_ = l_Lean_Compiler_LCNF_toLCNFType___closed__10;
                v___x_4223_ = l_List_filterMapTR_go___at___00Lean_Compiler_LCNF_toLCNFType_spec__3(
                    v_diag_4161_,
                    v___x_4158_,
                    v_env_4219_,
                    v___x_4221_,
                    v___x_4222_,
                );
                v___x_4224_ = l_List_isEmpty___redArg(v___x_4223_);
                if v___x_4224_ == 0 {
                    leanh::lean_dec_ref_known(v___x_4189_, 2);
                    v___x_4225_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__12),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__12_once),
                        _init_l_Lean_Compiler_LCNF_toLCNFType___closed__12,
                    );
                    v___x_4226_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__13),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__13_once),
                        _init_l_Lean_Compiler_LCNF_toLCNFType___closed__13,
                    );
                    v___x_4227_ = l_Lean_MessageData_joinSep(v___x_4223_, v___x_4226_);
                    v___x_4228_ = l_Lean_indentD(v___x_4227_);
                    v___x_4229_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4229_, 0, v___x_4225_);
                    leanh::lean_ctor_set(v___x_4229_, 1, v___x_4228_);
                    v___x_4230_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__15),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toLCNFType___closed__15_once),
                        _init_l_Lean_Compiler_LCNF_toLCNFType___closed__15,
                    );
                    v___x_4231_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4231_, 0, v___x_4229_);
                    leanh::lean_ctor_set(v___x_4231_, 1, v___x_4230_);
                    v___x_4232_ = leanh::lean_box(0);
                    v___x_4233_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4233_, 0, v___x_4232_);
                    leanh::lean_ctor_set(v___x_4233_, 1, v___x_4231_);
                    v_a_4191_ = v___x_4233_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4223_);
                    v___x_4234_ = leanh::lean_box(0);
                    v___x_4235_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4235_, 0, v___x_4234_);
                    leanh::lean_ctor_set(v___x_4235_, 1, v___x_4189_);
                    v_a_4191_ = v___x_4235_;
                    state = 4;
                    continue;
                }
            }
            10 => {
                if v___y_4238_ == 0 {
                    leanh::lean_dec_ref(v___y_4237_);
                    state = 9;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_4189_, 2);
                    v___x_4239_ = leanh::lean_box(0);
                    v___x_4240_ = l_Lean_Compiler_LCNF_toLCNFType___lam__0(
                        v_a_4136_,
                        v_diag_4161_,
                        v___x_4239_,
                    );
                    v_isSharedCheck_4247_ = (!leanh::lean_is_exclusive(v___x_4240_)) as u8;
                    if v_isSharedCheck_4247_ == 0 {
                        v_unused_4248_ = leanh::lean_ctor_get(v___x_4240_, 0);
                        leanh::lean_dec(v_unused_4248_);
                        v___x_4242_ = v___x_4240_;
                        v_isShared_4243_ = v_isSharedCheck_4247_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4240_);
                        v___x_4242_ = leanh::lean_box(0);
                        v_isShared_4243_ = v_isSharedCheck_4247_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_4243_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4242_, 1);
                    leanh::lean_ctor_set(v___x_4242_, 0, v___y_4237_);
                    v___x_4245_ = v___x_4242_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4246_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___y_4237_);
                    v___x_4245_ = v_reuseFailAlloc_4246_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4245_;
            }
            13 => {
                v___x_4265_ = l_Lean_maxRecDepth;
                v___x_4266_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toLCNFType_spec__6(
                    v___x_4178_,
                    v___x_4265_,
                );
                leanh::lean_inc_ref(v_inheritedTraceOptions_4263_);
                leanh::lean_inc(v_cancelTk_x3f_4261_);
                leanh::lean_inc(v_currMacroScope_4260_);
                leanh::lean_inc(v_quotContext_4259_);
                leanh::lean_inc(v_maxHeartbeats_4258_);
                leanh::lean_inc(v_initHeartbeats_4257_);
                leanh::lean_inc(v_openDecls_4256_);
                leanh::lean_inc(v_currNamespace_4255_);
                leanh::lean_inc(v_ref_4254_);
                leanh::lean_inc(v_currRecDepth_4253_);
                leanh::lean_inc_ref(v_fileMap_4252_);
                leanh::lean_inc_ref(v_fileName_4251_);
                v___x_4267_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_4267_, 0, v_fileName_4251_);
                leanh::lean_ctor_set(v___x_4267_, 1, v_fileMap_4252_);
                leanh::lean_ctor_set(v___x_4267_, 2, v___x_4178_);
                leanh::lean_ctor_set(v___x_4267_, 3, v_currRecDepth_4253_);
                leanh::lean_ctor_set(v___x_4267_, 4, v___x_4266_);
                leanh::lean_ctor_set(v___x_4267_, 5, v_ref_4254_);
                leanh::lean_ctor_set(v___x_4267_, 6, v_currNamespace_4255_);
                leanh::lean_ctor_set(v___x_4267_, 7, v_openDecls_4256_);
                leanh::lean_ctor_set(v___x_4267_, 8, v_initHeartbeats_4257_);
                leanh::lean_ctor_set(v___x_4267_, 9, v_maxHeartbeats_4258_);
                leanh::lean_ctor_set(v___x_4267_, 10, v_quotContext_4259_);
                leanh::lean_ctor_set(v___x_4267_, 11, v_currMacroScope_4260_);
                leanh::lean_ctor_set(v___x_4267_, 12, v_cancelTk_x3f_4261_);
                leanh::lean_ctor_set(v___x_4267_, 13, v_inheritedTraceOptions_4263_);
                leanh::lean_ctor_set_uint8(
                    v___x_4267_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___x_4249_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4267_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4262_,
                );
                v___x_4268_ =
                    l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg(
                        v___x_4140_,
                        v_isModule_4149_,
                        v_a_4135_,
                        v_a_4136_,
                        v___x_4267_,
                        v___y_4264_,
                    );
                leanh::lean_dec_ref_known(v___x_4267_, 14);
                if leanh::lean_obj_tag(v___x_4268_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4268_, 1);
                    state = 9;
                    continue;
                } else {
                    v_a_4269_ = leanh::lean_ctor_get(v___x_4268_, 0);
                    leanh::lean_inc(v_a_4269_);
                    leanh::lean_dec_ref_known(v___x_4268_, 1);
                    v___x_4270_ = l_Lean_Exception_isInterrupt(v_a_4269_);
                    if v___x_4270_ == 0 {
                        leanh::lean_inc(v_a_4269_);
                        v___x_4271_ = l_Lean_Exception_isRuntime(v_a_4269_);
                        v___y_4237_ = v_a_4269_;
                        v___y_4238_ = v___x_4271_;
                        state = 10;
                        continue;
                    } else {
                        v___y_4237_ = v_a_4269_;
                        v___y_4238_ = v___x_4270_;
                        state = 10;
                        continue;
                    }
                }
            }
            14 => {
                if v___y_4273_ == 0 {
                    v___x_4274_ = lean_st_ref_take(v_a_4138_);
                    v_env_4275_ = leanh::lean_ctor_get(v___x_4274_, 0);
                    v_nextMacroScope_4276_ = leanh::lean_ctor_get(v___x_4274_, 1);
                    v_ngen_4277_ = leanh::lean_ctor_get(v___x_4274_, 2);
                    v_auxDeclNGen_4278_ = leanh::lean_ctor_get(v___x_4274_, 3);
                    v_traceState_4279_ = leanh::lean_ctor_get(v___x_4274_, 4);
                    v_messages_4280_ = leanh::lean_ctor_get(v___x_4274_, 6);
                    v_infoState_4281_ = leanh::lean_ctor_get(v___x_4274_, 7);
                    v_snapshotTasks_4282_ = leanh::lean_ctor_get(v___x_4274_, 8);
                    v_isSharedCheck_4292_ = (!leanh::lean_is_exclusive(v___x_4274_)) as u8;
                    if v_isSharedCheck_4292_ == 0 {
                        v_unused_4293_ = leanh::lean_ctor_get(v___x_4274_, 5);
                        leanh::lean_dec(v_unused_4293_);
                        v___x_4284_ = v___x_4274_;
                        v_isShared_4285_ = v_isSharedCheck_4292_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_4282_);
                        leanh::lean_inc(v_infoState_4281_);
                        leanh::lean_inc(v_messages_4280_);
                        leanh::lean_inc(v_traceState_4279_);
                        leanh::lean_inc(v_auxDeclNGen_4278_);
                        leanh::lean_inc(v_ngen_4277_);
                        leanh::lean_inc(v_nextMacroScope_4276_);
                        leanh::lean_inc(v_env_4275_);
                        leanh::lean_dec(v___x_4274_);
                        v___x_4284_ = leanh::lean_box(0);
                        v_isShared_4285_ = v_isSharedCheck_4292_;
                        state = 15;
                        continue;
                    }
                } else {
                    v_fileName_4251_ = v_fileName_4162_;
                    v_fileMap_4252_ = v_fileMap_4163_;
                    v_currRecDepth_4253_ = v_currRecDepth_4165_;
                    v_ref_4254_ = v_ref_4166_;
                    v_currNamespace_4255_ = v_currNamespace_4167_;
                    v_openDecls_4256_ = v_openDecls_4168_;
                    v_initHeartbeats_4257_ = v_initHeartbeats_4169_;
                    v_maxHeartbeats_4258_ = v_maxHeartbeats_4170_;
                    v_quotContext_4259_ = v_quotContext_4171_;
                    v_currMacroScope_4260_ = v_currMacroScope_4172_;
                    v_cancelTk_x3f_4261_ = v_cancelTk_x3f_4173_;
                    v_suppressElabErrors_4262_ = v_suppressElabErrors_4174_;
                    v_inheritedTraceOptions_4263_ = v_inheritedTraceOptions_4175_;
                    v___y_4264_ = v_a_4138_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_4286_ = l_Lean_Kernel_enableDiag(v_env_4275_, v___x_4249_);
                v___x_4287_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_Compiler_LCNF_toLCNFType_spec__0___redArg___closed__2);
                if v_isShared_4285_ == 0 {
                    leanh::lean_ctor_set(v___x_4284_, 5, v___x_4287_);
                    leanh::lean_ctor_set(v___x_4284_, 0, v___x_4286_);
                    v___x_4289_ = v___x_4284_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4291_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 1, v_nextMacroScope_4276_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 2, v_ngen_4277_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 3, v_auxDeclNGen_4278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 4, v_traceState_4279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 5, v___x_4287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 6, v_messages_4280_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 7, v_infoState_4281_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 8, v_snapshotTasks_4282_);
                    v___x_4289_ = v_reuseFailAlloc_4291_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4290_ = lean_st_ref_set(v_a_4138_, v___x_4289_);
                v_fileName_4251_ = v_fileName_4162_;
                v_fileMap_4252_ = v_fileMap_4163_;
                v_currRecDepth_4253_ = v_currRecDepth_4165_;
                v_ref_4254_ = v_ref_4166_;
                v_currNamespace_4255_ = v_currNamespace_4167_;
                v_openDecls_4256_ = v_openDecls_4168_;
                v_initHeartbeats_4257_ = v_initHeartbeats_4169_;
                v_maxHeartbeats_4258_ = v_maxHeartbeats_4170_;
                v_quotContext_4259_ = v_quotContext_4171_;
                v_currMacroScope_4260_ = v_currMacroScope_4172_;
                v_cancelTk_x3f_4261_ = v_cancelTk_x3f_4173_;
                v_suppressElabErrors_4262_ = v_suppressElabErrors_4174_;
                v_inheritedTraceOptions_4263_ = v_inheritedTraceOptions_4175_;
                v___y_4264_ = v_a_4138_;
                state = 13;
                continue;
            }
            17 => {
                return v___x_4296_;
            }
            18 => {
                if v___y_4301_ == 0 {
                    v_isSharedCheck_4308_ = (!leanh::lean_is_exclusive(v___x_4153_)) as u8;
                    if v_isSharedCheck_4308_ == 0 {
                        v_unused_4309_ = leanh::lean_ctor_get(v___x_4153_, 0);
                        leanh::lean_dec(v_unused_4309_);
                        v___x_4303_ = v___x_4153_;
                        v_isShared_4304_ = v_isSharedCheck_4308_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4153_);
                        v___x_4303_ = leanh::lean_box(0);
                        v_isShared_4304_ = v_isSharedCheck_4308_;
                        state = 19;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4142_);
                    return v___x_4153_;
                }
            }
            19 => {
                if v_isShared_4304_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4303_, 0);
                    leanh::lean_ctor_set(v___x_4303_, 0, v_a_4142_);
                    v___x_4306_ = v___x_4303_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4307_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4142_);
                    v___x_4306_ = v_reuseFailAlloc_4307_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_toLCNFType___boxed(
    mut v_type_4313_: *mut leanh::LeanObject,
    mut v_a_4314_: *mut leanh::LeanObject,
    mut v_a_4315_: *mut leanh::LeanObject,
    mut v_a_4316_: *mut leanh::LeanObject,
    mut v_a_4317_: *mut leanh::LeanObject,
    mut v_a_4318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4319_ =
        l_Lean_Compiler_LCNF_toLCNFType(v_type_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
    leanh::lean_dec(v_a_4317_);
    leanh::lean_dec_ref(v_a_4316_);
    leanh::lean_dec(v_a_4315_);
    leanh::lean_dec_ref(v_a_4314_);
    return v_res_4319_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(
    mut v_00_u03b2_4320_: *mut leanh::LeanObject,
    mut v_x_4321_: *mut leanh::LeanObject,
    mut v_x_4322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4323_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___redArg(
            v_x_4321_, v_x_4322_,
        );
    return v___x_4323_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1___boxed(
    mut v_00_u03b2_4324_: *mut leanh::LeanObject,
    mut v_x_4325_: *mut leanh::LeanObject,
    mut v_x_4326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4327_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1(
        v_00_u03b2_4324_,
        v_x_4325_,
        v_x_4326_,
    );
    leanh::lean_dec(v_x_4326_);
    leanh::lean_dec_ref(v_x_4325_);
    return v_res_4327_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(
    mut v_00_u03b2_4328_: *mut leanh::LeanObject,
    mut v_m_4329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4330_ =
        l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___redArg(
            v_m_4329_,
        );
    return v___x_4330_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2___boxed(
    mut v_00_u03b2_4331_: *mut leanh::LeanObject,
    mut v_m_4332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4333_ = l_Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2(
        v_00_u03b2_4331_,
        v_m_4332_,
    );
    leanh::lean_dec_ref(v_m_4332_);
    return v_res_4333_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(
    mut v_00_u03b2_4334_: *mut leanh::LeanObject,
    mut v_x_4335_: *mut leanh::LeanObject,
    mut v_x_4336_: usize,
    mut v_x_4337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4338_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___redArg(v_x_4335_, v_x_4336_, v_x_4337_);
    return v___x_4338_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1___boxed(
    mut v_00_u03b2_4339_: *mut leanh::LeanObject,
    mut v_x_4340_: *mut leanh::LeanObject,
    mut v_x_4341_: *mut leanh::LeanObject,
    mut v_x_4342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_19312__boxed_4343_: usize = 0;
    let mut v_res_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_19312__boxed_4343_ = leanh::lean_unbox_usize(v_x_4341_);
    leanh::lean_dec(v_x_4341_);
    v_res_4344_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1(v_00_u03b2_4339_, v_x_4340_, v_x_19312__boxed_4343_, v_x_4342_);
    leanh::lean_dec(v_x_4342_);
    leanh::lean_dec_ref(v_x_4340_);
    return v_res_4344_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(
    mut v_00_u03c3_4345_: *mut leanh::LeanObject,
    mut v_00_u03b2_4346_: *mut leanh::LeanObject,
    mut v_map_4347_: *mut leanh::LeanObject,
    mut v_f_4348_: *mut leanh::LeanObject,
    mut v_init_4349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4350_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___redArg(v_map_4347_, v_f_4348_, v_init_4349_);
    return v___x_4350_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3___boxed(
    mut v_00_u03c3_4351_: *mut leanh::LeanObject,
    mut v_00_u03b2_4352_: *mut leanh::LeanObject,
    mut v_map_4353_: *mut leanh::LeanObject,
    mut v_f_4354_: *mut leanh::LeanObject,
    mut v_init_4355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4356_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3(v_00_u03c3_4351_, v_00_u03b2_4352_, v_map_4353_, v_f_4354_, v_init_4355_);
    leanh::lean_dec_ref(v_map_4353_);
    return v_res_4356_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4(
    mut v_00_u03b2_4357_: *mut leanh::LeanObject,
    mut v_keys_4358_: *mut leanh::LeanObject,
    mut v_vals_4359_: *mut leanh::LeanObject,
    mut v_heq_4360_: *mut leanh::LeanObject,
    mut v_i_4361_: *mut leanh::LeanObject,
    mut v_k_4362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4363_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___redArg(v_keys_4358_, v_vals_4359_, v_i_4361_, v_k_4362_);
    return v___x_4363_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4___boxed(
    mut v_00_u03b2_4364_: *mut leanh::LeanObject,
    mut v_keys_4365_: *mut leanh::LeanObject,
    mut v_vals_4366_: *mut leanh::LeanObject,
    mut v_heq_4367_: *mut leanh::LeanObject,
    mut v_i_4368_: *mut leanh::LeanObject,
    mut v_k_4369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4370_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_toLCNFType_spec__1_spec__1_spec__4(v_00_u03b2_4364_, v_keys_4365_, v_vals_4366_, v_heq_4367_, v_i_4368_, v_k_4369_);
    leanh::lean_dec(v_k_4369_);
    leanh::lean_dec_ref(v_vals_4366_);
    leanh::lean_dec_ref(v_keys_4365_);
    return v_res_4370_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg(
    mut v_map_4371_: *mut leanh::LeanObject,
    mut v_f_4372_: *mut leanh::LeanObject,
    mut v_init_4373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4374_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_4372_, v_map_4371_, v_init_4373_);
    return v___x_4374_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg___boxed(
    mut v_map_4375_: *mut leanh::LeanObject,
    mut v_f_4376_: *mut leanh::LeanObject,
    mut v_init_4377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4378_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___redArg(v_map_4375_, v_f_4376_, v_init_4377_);
    leanh::lean_dec_ref(v_map_4375_);
    return v_res_4378_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7(
    mut v_00_u03c3_4379_: *mut leanh::LeanObject,
    mut v_00_u03b2_4380_: *mut leanh::LeanObject,
    mut v_map_4381_: *mut leanh::LeanObject,
    mut v_f_4382_: *mut leanh::LeanObject,
    mut v_init_4383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4384_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_4382_, v_map_4381_, v_init_4383_);
    return v___x_4384_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7___boxed(
    mut v_00_u03c3_4385_: *mut leanh::LeanObject,
    mut v_00_u03b2_4386_: *mut leanh::LeanObject,
    mut v_map_4387_: *mut leanh::LeanObject,
    mut v_f_4388_: *mut leanh::LeanObject,
    mut v_init_4389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4390_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7(v_00_u03c3_4385_, v_00_u03b2_4386_, v_map_4387_, v_f_4388_, v_init_4389_);
    leanh::lean_dec_ref(v_map_4387_);
    return v_res_4390_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11(
    mut v_00_u03c3_4391_: *mut leanh::LeanObject,
    mut v_00_u03b1_4392_: *mut leanh::LeanObject,
    mut v_00_u03b2_4393_: *mut leanh::LeanObject,
    mut v_f_4394_: *mut leanh::LeanObject,
    mut v_x_4395_: *mut leanh::LeanObject,
    mut v_x_4396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4397_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___redArg(v_f_4394_, v_x_4395_, v_x_4396_);
    return v___x_4397_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11___boxed(
    mut v_00_u03c3_4398_: *mut leanh::LeanObject,
    mut v_00_u03b1_4399_: *mut leanh::LeanObject,
    mut v_00_u03b2_4400_: *mut leanh::LeanObject,
    mut v_f_4401_: *mut leanh::LeanObject,
    mut v_x_4402_: *mut leanh::LeanObject,
    mut v_x_4403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4404_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11(v_00_u03c3_4398_, v_00_u03b1_4399_, v_00_u03b2_4400_, v_f_4401_, v_x_4402_, v_x_4403_);
    leanh::lean_dec_ref(v_x_4402_);
    return v_res_4404_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12(
    mut v_00_u03b1_4405_: *mut leanh::LeanObject,
    mut v_00_u03b2_4406_: *mut leanh::LeanObject,
    mut v_00_u03c3_4407_: *mut leanh::LeanObject,
    mut v_f_4408_: *mut leanh::LeanObject,
    mut v_as_4409_: *mut leanh::LeanObject,
    mut v_i_4410_: usize,
    mut v_stop_4411_: usize,
    mut v_b_4412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___redArg(v_f_4408_, v_as_4409_, v_i_4410_, v_stop_4411_, v_b_4412_);
    return v___x_4413_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12___boxed(
    mut v_00_u03b1_4414_: *mut leanh::LeanObject,
    mut v_00_u03b2_4415_: *mut leanh::LeanObject,
    mut v_00_u03c3_4416_: *mut leanh::LeanObject,
    mut v_f_4417_: *mut leanh::LeanObject,
    mut v_as_4418_: *mut leanh::LeanObject,
    mut v_i_4419_: *mut leanh::LeanObject,
    mut v_stop_4420_: *mut leanh::LeanObject,
    mut v_b_4421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4422_: usize = 0;
    let mut v_stop_boxed_4423_: usize = 0;
    let mut v_res_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4422_ = leanh::lean_unbox_usize(v_i_4419_);
    leanh::lean_dec(v_i_4419_);
    v_stop_boxed_4423_ = leanh::lean_unbox_usize(v_stop_4420_);
    leanh::lean_dec(v_stop_4420_);
    v_res_4424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__12(v_00_u03b1_4414_, v_00_u03b2_4415_, v_00_u03c3_4416_, v_f_4417_, v_as_4418_, v_i_boxed_4422_, v_stop_boxed_4423_, v_b_4421_);
    leanh::lean_dec_ref(v_as_4418_);
    return v_res_4424_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13(
    mut v_00_u03c3_4425_: *mut leanh::LeanObject,
    mut v_00_u03b1_4426_: *mut leanh::LeanObject,
    mut v_00_u03b2_4427_: *mut leanh::LeanObject,
    mut v_f_4428_: *mut leanh::LeanObject,
    mut v_keys_4429_: *mut leanh::LeanObject,
    mut v_vals_4430_: *mut leanh::LeanObject,
    mut v_heq_4431_: *mut leanh::LeanObject,
    mut v_i_4432_: *mut leanh::LeanObject,
    mut v_acc_4433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4434_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___redArg(v_f_4428_, v_keys_4429_, v_vals_4430_, v_i_4432_, v_acc_4433_);
    return v___x_4434_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13___boxed(
    mut v_00_u03c3_4435_: *mut leanh::LeanObject,
    mut v_00_u03b1_4436_: *mut leanh::LeanObject,
    mut v_00_u03b2_4437_: *mut leanh::LeanObject,
    mut v_f_4438_: *mut leanh::LeanObject,
    mut v_keys_4439_: *mut leanh::LeanObject,
    mut v_vals_4440_: *mut leanh::LeanObject,
    mut v_heq_4441_: *mut leanh::LeanObject,
    mut v_i_4442_: *mut leanh::LeanObject,
    mut v_acc_4443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4444_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Compiler_LCNF_toLCNFType_spec__2_spec__3_spec__7_spec__11_spec__13(v_00_u03c3_4435_, v_00_u03b1_4436_, v_00_u03b2_4437_, v_f_4438_, v_keys_4439_, v_vals_4440_, v_heq_4441_, v_i_4442_, v_acc_4443_);
    leanh::lean_dec_ref(v_vals_4440_);
    leanh::lean_dec_ref(v_keys_4439_);
    return v_res_4444_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4445_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_anyExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_anyExpr___closed__2_once),
        _init_l_Lean_Compiler_LCNF_anyExpr___closed__2,
    );
    v___x_4446_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4446_, 0, v___x_4445_);
    return v___x_4446_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4447_ = l_Lean_Compiler_LCNF_erasedExpr;
    v___x_4448_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4448_, 0, v___x_4447_);
    return v___x_4448_;
}
pub unsafe fn l_Lean_Compiler_LCNF_joinTypes_x3f(
    mut v_a_4449_: *mut leanh::LeanObject,
    mut v_b_4450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4457_: u8 = 0;
    let mut v___x_4458_: u8 = 0;
    let mut v_a_x27_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_x27_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: u8 = 0;
    let mut v___x_4463_: u8 = 0;
    let mut v_expr_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v_expr_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4497_: u8 = 0;
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: u8 = 0;
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4504_: u8 = 0;
    let mut v_expr_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4524_: u8 = 0;
    let mut v_expr_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: u8 = 0;
    let mut v___x_4531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4530_ = l_Lean_Expr_isErased(v_a_4449_);
                if v___x_4530_ == 0 {
                    v___x_4531_ = l_Lean_Expr_isErased(v_b_4450_);
                    v___y_4457_ = v___x_4531_;
                    state = 3;
                    continue;
                } else {
                    v___y_4457_ = v___x_4530_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_4452_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once),
                    _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0,
                );
                return v___x_4452_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_4454_) == 0 {
                    v___x_4455_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once
                        ),
                        _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0,
                    );
                    return v___x_4455_;
                } else {
                    return v___y_4454_;
                }
            }
            3 => {
                if v___y_4457_ == 0 {
                    v___x_4458_ = lean_expr_eqv(v_a_4449_, v_b_4450_);
                    if v___x_4458_ == 0 {
                        leanh::lean_inc_ref(v_a_4449_);
                        v_a_x27_4459_ = l_Lean_Expr_headBeta(v_a_4449_);
                        leanh::lean_inc_ref(v_b_4450_);
                        v_b_x27_4460_ = l_Lean_Expr_headBeta(v_b_4450_);
                        v___x_4461_ = lean_expr_eqv(v_a_4449_, v_a_x27_4459_);
                        if v___x_4461_ == 0 {
                            leanh::lean_dec_ref(v_b_4450_);
                            leanh::lean_dec_ref(v_a_4449_);
                            v_a_4449_ = v_a_x27_4459_;
                            v_b_4450_ = v_b_x27_4460_;
                            state = 0;
                            continue;
                        } else {
                            if v___x_4458_ == 0 {
                                v___x_4463_ = lean_expr_eqv(v_b_4450_, v_b_x27_4460_);
                                if v___x_4463_ == 0 {
                                    leanh::lean_dec_ref(v_b_4450_);
                                    leanh::lean_dec_ref(v_a_4449_);
                                    v_a_4449_ = v_a_x27_4459_;
                                    v_b_4450_ = v_b_x27_4460_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_b_x27_4460_);
                                    leanh::lean_dec_ref(v_a_x27_4459_);
                                    match leanh::lean_obj_tag(v_a_4449_) {
                                        10 => {
                                            v_expr_4465_ =
                                                leanh::lean_ctor_get(v_a_4449_, 1);
                                            leanh::lean_inc_ref(v_expr_4465_);
                                            leanh::lean_dec_ref_known(v_a_4449_, 2);
                                            v_a_4449_ = v_expr_4465_;
                                            state = 0;
                                            continue;
                                        }
                                        5 => match leanh::lean_obj_tag(v_b_4450_) {
                                            10 => {
                                                v_expr_4467_ =
                                                    leanh::lean_ctor_get(v_b_4450_, 1);
                                                leanh::lean_inc_ref(v_expr_4467_);
                                                leanh::lean_dec_ref_known(v_b_4450_, 2);
                                                v_b_4450_ = v_expr_4467_;
                                                state = 0;
                                                continue;
                                            }
                                            5 => {
                                                v_fn_4469_ =
                                                    leanh::lean_ctor_get(v_a_4449_, 0);
                                                leanh::lean_inc_ref(v_fn_4469_);
                                                v_arg_4470_ =
                                                    leanh::lean_ctor_get(v_a_4449_, 1);
                                                leanh::lean_inc_ref(v_arg_4470_);
                                                leanh::lean_dec_ref_known(v_a_4449_, 2);
                                                v_fn_4471_ =
                                                    leanh::lean_ctor_get(v_b_4450_, 0);
                                                leanh::lean_inc_ref(v_fn_4471_);
                                                v_arg_4472_ =
                                                    leanh::lean_ctor_get(v_b_4450_, 1);
                                                leanh::lean_inc_ref(v_arg_4472_);
                                                leanh::lean_dec_ref_known(v_b_4450_, 2);
                                                v___x_4473_ = l_Lean_Compiler_LCNF_joinTypes_x3f(
                                                    v_fn_4469_, v_fn_4471_,
                                                );
                                                if leanh::lean_obj_tag(v___x_4473_) == 0 {
                                                    leanh::lean_dec_ref(v_arg_4472_);
                                                    leanh::lean_dec_ref(v_arg_4470_);
                                                    v___y_4454_ = v___x_4473_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v_val_4474_ =
                                                        leanh::lean_ctor_get(v___x_4473_, 0);
                                                    leanh::lean_inc(v_val_4474_);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_4473_,
                                                        1,
                                                    );
                                                    v___x_4475_ =
                                                        l_Lean_Compiler_LCNF_joinTypes_x3f(
                                                            v_arg_4470_,
                                                            v_arg_4472_,
                                                        );
                                                    if leanh::lean_obj_tag(v___x_4475_) == 0
                                                    {
                                                        leanh::lean_dec(v_val_4474_);
                                                        v___y_4454_ = v___x_4475_;
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        v_val_4476_ = leanh::lean_ctor_get(
                                                            v___x_4475_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4484_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_4475_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_4484_ == 0 {
                                                            v___x_4478_ = v___x_4475_;
                                                            v_isShared_4479_ =
                                                                v_isSharedCheck_4484_;
                                                            state = 4;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_val_4476_);
                                                            leanh::lean_dec(v___x_4475_);
                                                            v___x_4478_ = leanh::lean_box(0);
                                                            v_isShared_4479_ =
                                                                v_isSharedCheck_4484_;
                                                            state = 4;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                            _ => {
                                                leanh::lean_dec_ref_known(v_a_4449_, 2);
                                                leanh::lean_dec_ref(v_b_4450_);
                                                state = 1;
                                                continue;
                                            }
                                        },
                                        7 => match leanh::lean_obj_tag(v_b_4450_) {
                                            10 => {
                                                v_expr_4485_ =
                                                    leanh::lean_ctor_get(v_b_4450_, 1);
                                                leanh::lean_inc_ref(v_expr_4485_);
                                                leanh::lean_dec_ref_known(v_b_4450_, 2);
                                                v_b_4450_ = v_expr_4485_;
                                                state = 0;
                                                continue;
                                            }
                                            7 => {
                                                v_binderName_4487_ =
                                                    leanh::lean_ctor_get(v_a_4449_, 0);
                                                leanh::lean_inc(v_binderName_4487_);
                                                v_binderType_4488_ =
                                                    leanh::lean_ctor_get(v_a_4449_, 1);
                                                leanh::lean_inc_ref(v_binderType_4488_);
                                                v_body_4489_ =
                                                    leanh::lean_ctor_get(v_a_4449_, 2);
                                                leanh::lean_inc_ref(v_body_4489_);
                                                leanh::lean_dec_ref_known(v_a_4449_, 3);
                                                v_binderType_4490_ =
                                                    leanh::lean_ctor_get(v_b_4450_, 1);
                                                leanh::lean_inc_ref(v_binderType_4490_);
                                                v_body_4491_ =
                                                    leanh::lean_ctor_get(v_b_4450_, 2);
                                                leanh::lean_inc_ref(v_body_4491_);
                                                leanh::lean_dec_ref_known(v_b_4450_, 3);
                                                v___x_4492_ = l_Lean_Compiler_LCNF_joinTypes_x3f(
                                                    v_binderType_4488_,
                                                    v_binderType_4490_,
                                                );
                                                if leanh::lean_obj_tag(v___x_4492_) == 0 {
                                                    leanh::lean_dec_ref(v_body_4491_);
                                                    leanh::lean_dec_ref(v_body_4489_);
                                                    leanh::lean_dec(v_binderName_4487_);
                                                    if leanh::lean_obj_tag(v___x_4492_) == 0
                                                    {
                                                        v___x_4493_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once), _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
                                                        return v___x_4493_;
                                                    } else {
                                                        return v___x_4492_;
                                                    }
                                                } else {
                                                    v_val_4494_ =
                                                        leanh::lean_ctor_get(v___x_4492_, 0);
                                                    v_isSharedCheck_4504_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_4492_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4504_ == 0 {
                                                        v___x_4496_ = v___x_4492_;
                                                        v_isShared_4497_ = v_isSharedCheck_4504_;
                                                        state = 6;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_val_4494_);
                                                        leanh::lean_dec(v___x_4492_);
                                                        v___x_4496_ = leanh::lean_box(0);
                                                        v_isShared_4497_ = v_isSharedCheck_4504_;
                                                        state = 6;
                                                        continue;
                                                    }
                                                }
                                            }
                                            _ => {
                                                leanh::lean_dec_ref_known(v_a_4449_, 3);
                                                leanh::lean_dec_ref(v_b_4450_);
                                                state = 1;
                                                continue;
                                            }
                                        },
                                        6 => match leanh::lean_obj_tag(v_b_4450_) {
                                            10 => {
                                                v_expr_4505_ =
                                                    leanh::lean_ctor_get(v_b_4450_, 1);
                                                leanh::lean_inc_ref(v_expr_4505_);
                                                leanh::lean_dec_ref_known(v_b_4450_, 2);
                                                v_b_4450_ = v_expr_4505_;
                                                state = 0;
                                                continue;
                                            }
                                            6 => {
                                                v_binderName_4507_ =
                                                    leanh::lean_ctor_get(v_a_4449_, 0);
                                                leanh::lean_inc(v_binderName_4507_);
                                                v_binderType_4508_ =
                                                    leanh::lean_ctor_get(v_a_4449_, 1);
                                                leanh::lean_inc_ref(v_binderType_4508_);
                                                v_body_4509_ =
                                                    leanh::lean_ctor_get(v_a_4449_, 2);
                                                leanh::lean_inc_ref(v_body_4509_);
                                                leanh::lean_dec_ref_known(v_a_4449_, 3);
                                                v_binderType_4510_ =
                                                    leanh::lean_ctor_get(v_b_4450_, 1);
                                                leanh::lean_inc_ref(v_binderType_4510_);
                                                v_body_4511_ =
                                                    leanh::lean_ctor_get(v_b_4450_, 2);
                                                leanh::lean_inc_ref(v_body_4511_);
                                                leanh::lean_dec_ref_known(v_b_4450_, 3);
                                                v___x_4512_ = l_Lean_Compiler_LCNF_joinTypes_x3f(
                                                    v_binderType_4508_,
                                                    v_binderType_4510_,
                                                );
                                                if leanh::lean_obj_tag(v___x_4512_) == 0 {
                                                    leanh::lean_dec_ref(v_body_4511_);
                                                    leanh::lean_dec_ref(v_body_4509_);
                                                    leanh::lean_dec(v_binderName_4507_);
                                                    if leanh::lean_obj_tag(v___x_4512_) == 0
                                                    {
                                                        v___x_4513_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0_once), _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__0);
                                                        return v___x_4513_;
                                                    } else {
                                                        return v___x_4512_;
                                                    }
                                                } else {
                                                    v_val_4514_ =
                                                        leanh::lean_ctor_get(v___x_4512_, 0);
                                                    v_isSharedCheck_4524_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_4512_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4524_ == 0 {
                                                        v___x_4516_ = v___x_4512_;
                                                        v_isShared_4517_ = v_isSharedCheck_4524_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_val_4514_);
                                                        leanh::lean_dec(v___x_4512_);
                                                        v___x_4516_ = leanh::lean_box(0);
                                                        v_isShared_4517_ = v_isSharedCheck_4524_;
                                                        state = 8;
                                                        continue;
                                                    }
                                                }
                                            }
                                            _ => {
                                                leanh::lean_dec_ref_known(v_a_4449_, 3);
                                                leanh::lean_dec_ref(v_b_4450_);
                                                state = 1;
                                                continue;
                                            }
                                        },
                                        _ => {
                                            if leanh::lean_obj_tag(v_b_4450_) == 10 {
                                                v_expr_4525_ =
                                                    leanh::lean_ctor_get(v_b_4450_, 1);
                                                leanh::lean_inc_ref(v_expr_4525_);
                                                leanh::lean_dec_ref_known(v_b_4450_, 2);
                                                v_b_4450_ = v_expr_4525_;
                                                state = 0;
                                                continue;
                                            } else {
                                                leanh::lean_dec_ref(v_b_4450_);
                                                leanh::lean_dec_ref(v_a_4449_);
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_b_4450_);
                                leanh::lean_dec_ref(v_a_4449_);
                                v_a_4449_ = v_a_x27_4459_;
                                v_b_4450_ = v_b_x27_4460_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_4450_);
                        v___x_4528_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4528_, 0, v_a_4449_);
                        return v___x_4528_;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_4450_);
                    leanh::lean_dec_ref(v_a_4449_);
                    v___x_4529_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_joinTypes_x3f___closed__1,
                    );
                    return v___x_4529_;
                }
            }
            4 => {
                v___x_4480_ = l_Lean_Expr_app___override(v_val_4474_, v_val_4476_);
                if v_isShared_4479_ == 0 {
                    leanh::lean_ctor_set(v___x_4478_, 0, v___x_4480_);
                    v___x_4482_ = v___x_4478_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4483_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
                    v___x_4482_ = v_reuseFailAlloc_4483_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4482_;
            }
            6 => {
                v___x_4498_ = l_Lean_Compiler_LCNF_joinTypes(v_body_4489_, v_body_4491_);
                v___x_4499_ = 0;
                v___x_4500_ = l_Lean_Expr_forallE___override(
                    v_binderName_4487_,
                    v_val_4494_,
                    v___x_4498_,
                    v___x_4499_,
                );
                if v_isShared_4497_ == 0 {
                    leanh::lean_ctor_set(v___x_4496_, 0, v___x_4500_);
                    v___x_4502_ = v___x_4496_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4503_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4500_);
                    v___x_4502_ = v_reuseFailAlloc_4503_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4502_;
            }
            8 => {
                v___x_4518_ = l_Lean_Compiler_LCNF_joinTypes(v_body_4509_, v_body_4511_);
                v___x_4519_ = 0;
                v___x_4520_ = l_Lean_Expr_lam___override(
                    v_binderName_4507_,
                    v_val_4514_,
                    v___x_4518_,
                    v___x_4519_,
                );
                if v_isShared_4517_ == 0 {
                    leanh::lean_ctor_set(v___x_4516_, 0, v___x_4520_);
                    v___x_4522_ = v___x_4516_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4523_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4520_);
                    v___x_4522_ = v_reuseFailAlloc_4523_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_joinTypes(
    mut v_a_4532_: *mut leanh::LeanObject,
    mut v_b_4533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4534_ = l_Lean_Compiler_LCNF_joinTypes_x3f(v_a_4532_, v_b_4533_);
    if leanh::lean_obj_tag(v___x_4534_) == 0 {
        let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4535_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_anyExpr___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_anyExpr___closed__2_once),
            _init_l_Lean_Compiler_LCNF_anyExpr___closed__2,
        );
        return v___x_4535_;
    } else {
        let mut v_val_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4536_ = leanh::lean_ctor_get(v___x_4534_, 0);
        leanh::lean_inc(v_val_4536_);
        leanh::lean_dec_ref_known(v___x_4534_, 1);
        return v_val_4536_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isTypeFormerType(
    mut v_type_4537_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: u8 = 0;
    let mut v_body_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4538_ = l_Lean_Expr_headBeta(v_type_4537_);
                match leanh::lean_obj_tag(v___x_4538_) {
                    3 => {
                        leanh::lean_dec_ref_known(v___x_4538_, 1);
                        v___x_4539_ = 1;
                        return v___x_4539_;
                    }
                    7 => {
                        v_body_4540_ = leanh::lean_ctor_get(v___x_4538_, 2);
                        leanh::lean_inc_ref(v_body_4540_);
                        leanh::lean_dec_ref_known(v___x_4538_, 3);
                        v_type_4537_ = v_body_4540_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        leanh::lean_dec_ref(v___x_4538_);
                        v___x_4542_ = 0;
                        return v___x_4542_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isTypeFormerType___boxed(
    mut v_type_4543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4544_: u8 = 0;
    let mut v_r_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4544_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_4543_);
    v_r_4545_ = leanh::lean_box((v_res_4544_) as usize);
    return v_r_4545_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(
    mut v_msgData_4546_: *mut leanh::LeanObject,
    mut v___y_4547_: *mut leanh::LeanObject,
    mut v___y_4548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4550_ = lean_st_ref_get(v___y_4548_);
    v_env_4551_ = leanh::lean_ctor_get(v___x_4550_, 0);
    leanh::lean_inc_ref(v_env_4551_);
    leanh::lean_dec(v___x_4550_);
    v_options_4552_ = leanh::lean_ctor_get(v___y_4547_, 2);
    v___x_4553_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__2);
    v___x_4554_ = leanh::lean_unsigned_to_nat(32);
    v___x_4555_ = lean_mk_empty_array_with_capacity(v___x_4554_);
    leanh::lean_dec_ref(v___x_4555_);
    v___x_4556_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitApp_spec__4_spec__4_spec__5_spec__8_spec__9_spec__10___redArg___closed__5);
    leanh::lean_inc_ref(v_options_4552_);
    v___x_4557_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4557_, 0, v_env_4551_);
    leanh::lean_ctor_set(v___x_4557_, 1, v___x_4553_);
    leanh::lean_ctor_set(v___x_4557_, 2, v___x_4556_);
    leanh::lean_ctor_set(v___x_4557_, 3, v_options_4552_);
    v___x_4558_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4558_, 0, v___x_4557_);
    leanh::lean_ctor_set(v___x_4558_, 1, v_msgData_4546_);
    v___x_4559_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4559_, 0, v___x_4558_);
    return v___x_4559_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0___boxed(
    mut v_msgData_4560_: *mut leanh::LeanObject,
    mut v___y_4561_: *mut leanh::LeanObject,
    mut v___y_4562_: *mut leanh::LeanObject,
    mut v___y_4563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4564_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msgData_4560_, v___y_4561_, v___y_4562_);
    leanh::lean_dec(v___y_4562_);
    leanh::lean_dec_ref(v___y_4561_);
    return v_res_4564_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(
    mut v_msg_4565_: *mut leanh::LeanObject,
    mut v___y_4566_: *mut leanh::LeanObject,
    mut v___y_4567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4574_: u8 = 0;
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4579_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4569_ = leanh::lean_ctor_get(v___y_4566_, 5);
                v___x_4570_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0_spec__0(v_msg_4565_, v___y_4566_, v___y_4567_);
                v_a_4571_ = leanh::lean_ctor_get(v___x_4570_, 0);
                v_isSharedCheck_4579_ = (!leanh::lean_is_exclusive(v___x_4570_)) as u8;
                if v_isSharedCheck_4579_ == 0 {
                    v___x_4573_ = v___x_4570_;
                    v_isShared_4574_ = v_isSharedCheck_4579_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4571_);
                    leanh::lean_dec(v___x_4570_);
                    v___x_4573_ = leanh::lean_box(0);
                    v_isShared_4574_ = v_isSharedCheck_4579_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_4569_);
                v___x_4575_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4575_, 0, v_ref_4569_);
                leanh::lean_ctor_set(v___x_4575_, 1, v_a_4571_);
                if v_isShared_4574_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4573_, 1);
                    leanh::lean_ctor_set(v___x_4573_, 0, v___x_4575_);
                    v___x_4577_ = v___x_4573_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4578_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4578_, 0, v___x_4575_);
                    v___x_4577_ = v_reuseFailAlloc_4578_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4577_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg___boxed(
    mut v_msg_4580_: *mut leanh::LeanObject,
    mut v___y_4581_: *mut leanh::LeanObject,
    mut v___y_4582_: *mut leanh::LeanObject,
    mut v___y_4583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4584_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_4580_, v___y_4581_, v___y_4582_);
    leanh::lean_dec(v___y_4582_);
    leanh::lean_dec_ref(v___y_4581_);
    return v_res_4584_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4586_ =
        l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__0;
    v___x_4587_ = l_Lean_stringToMessageData(v___x_4586_);
    return v___x_4587_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(
    mut v_ps_4588_: *mut leanh::LeanObject,
    mut v_i_4589_: *mut leanh::LeanObject,
    mut v_type_4590_: *mut leanh::LeanObject,
    mut v_a_4591_: *mut leanh::LeanObject,
    mut v_a_4592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: u8 = 0;
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4594_ = lean_array_get_size(v_ps_4588_);
                v___x_4595_ = lean_nat_dec_lt(v_i_4589_, v___x_4594_);
                if v___x_4595_ == 0 {
                    leanh::lean_dec(v_i_4589_);
                    v___x_4596_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4596_, 0, v_type_4590_);
                    return v___x_4596_;
                } else {
                    v___x_4597_ = l_Lean_Expr_headBeta(v_type_4590_);
                    if leanh::lean_obj_tag(v___x_4597_) == 7 {
                        v_body_4598_ = leanh::lean_ctor_get(v___x_4597_, 2);
                        leanh::lean_inc_ref(v_body_4598_);
                        leanh::lean_dec_ref_known(v___x_4597_, 3);
                        v___x_4599_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4600_ = lean_nat_add(v_i_4589_, v___x_4599_);
                        v___x_4601_ = lean_array_fget_borrowed(v_ps_4588_, v_i_4589_);
                        leanh::lean_dec(v_i_4589_);
                        v___x_4602_ = lean_expr_instantiate1(v_body_4598_, v___x_4601_);
                        leanh::lean_dec_ref(v_body_4598_);
                        v_i_4589_ = v___x_4600_;
                        v_type_4590_ = v___x_4602_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_4597_);
                        leanh::lean_dec(v_i_4589_);
                        v___x_4604_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1_once), _init_l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___closed__1);
                        v___x_4605_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v___x_4604_, v_a_4591_, v_a_4592_);
                        return v___x_4605_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go___boxed(
    mut v_ps_4606_: *mut leanh::LeanObject,
    mut v_i_4607_: *mut leanh::LeanObject,
    mut v_type_4608_: *mut leanh::LeanObject,
    mut v_a_4609_: *mut leanh::LeanObject,
    mut v_a_4610_: *mut leanh::LeanObject,
    mut v_a_4611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4612_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(
        v_ps_4606_,
        v_i_4607_,
        v_type_4608_,
        v_a_4609_,
        v_a_4610_,
    );
    leanh::lean_dec(v_a_4610_);
    leanh::lean_dec_ref(v_a_4609_);
    leanh::lean_dec_ref(v_ps_4606_);
    return v_res_4612_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(
    mut v_00_u03b1_4613_: *mut leanh::LeanObject,
    mut v_msg_4614_: *mut leanh::LeanObject,
    mut v___y_4615_: *mut leanh::LeanObject,
    mut v___y_4616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4618_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___redArg(v_msg_4614_, v___y_4615_, v___y_4616_);
    return v___x_4618_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0___boxed(
    mut v_00_u03b1_4619_: *mut leanh::LeanObject,
    mut v_msg_4620_: *mut leanh::LeanObject,
    mut v___y_4621_: *mut leanh::LeanObject,
    mut v___y_4622_: *mut leanh::LeanObject,
    mut v___y_4623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4624_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go_spec__0(v_00_u03b1_4619_, v_msg_4620_, v___y_4621_, v___y_4622_);
    leanh::lean_dec(v___y_4622_);
    leanh::lean_dec_ref(v___y_4621_);
    return v_res_4624_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter___redArg(
    mut v_e_4625_: *mut leanh::LeanObject,
    mut v_h__1_4626_: *mut leanh::LeanObject,
    mut v_h__2_4627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_4625_) == 7 {
        let mut v_binderName_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_4631_: u8 = 0;
        let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4627_);
        v_binderName_4628_ = leanh::lean_ctor_get(v_e_4625_, 0);
        leanh::lean_inc(v_binderName_4628_);
        v_binderType_4629_ = leanh::lean_ctor_get(v_e_4625_, 1);
        leanh::lean_inc_ref(v_binderType_4629_);
        v_body_4630_ = leanh::lean_ctor_get(v_e_4625_, 2);
        leanh::lean_inc_ref(v_body_4630_);
        v_binderInfo_4631_ = leanh::lean_ctor_get_uint8(
            v_e_4625_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_e_4625_, 3);
        v___x_4632_ = leanh::lean_box((v_binderInfo_4631_) as usize);
        v___x_4633_ = leanh::lean_apply_4(
            v_h__1_4626_,
            v_binderName_4628_,
            v_binderType_4629_,
            v_body_4630_,
            v___x_4632_,
        );
        return v___x_4633_;
    } else {
        let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4626_);
        v___x_4634_ =
            leanh::lean_apply_2(v_h__2_4627_, v_e_4625_, leanh::lean_box(0));
        return v___x_4634_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_toLCNFType_visitForall_match__9_splitter(
    mut v_motive_4635_: *mut leanh::LeanObject,
    mut v_e_4636_: *mut leanh::LeanObject,
    mut v_h__1_4637_: *mut leanh::LeanObject,
    mut v_h__2_4638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_4636_) == 7 {
        let mut v_binderName_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_4642_: u8 = 0;
        let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4638_);
        v_binderName_4639_ = leanh::lean_ctor_get(v_e_4636_, 0);
        leanh::lean_inc(v_binderName_4639_);
        v_binderType_4640_ = leanh::lean_ctor_get(v_e_4636_, 1);
        leanh::lean_inc_ref(v_binderType_4640_);
        v_body_4641_ = leanh::lean_ctor_get(v_e_4636_, 2);
        leanh::lean_inc_ref(v_body_4641_);
        v_binderInfo_4642_ = leanh::lean_ctor_get_uint8(
            v_e_4636_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_e_4636_, 3);
        v___x_4643_ = leanh::lean_box((v_binderInfo_4642_) as usize);
        v___x_4644_ = leanh::lean_apply_4(
            v_h__1_4637_,
            v_binderName_4639_,
            v_binderType_4640_,
            v_body_4641_,
            v___x_4643_,
        );
        return v___x_4644_;
    } else {
        let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4637_);
        v___x_4645_ =
            leanh::lean_apply_2(v_h__2_4638_, v_e_4636_, leanh::lean_box(0));
        return v___x_4645_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instantiateForall(
    mut v_type_4646_: *mut leanh::LeanObject,
    mut v_ps_4647_: *mut leanh::LeanObject,
    mut v_a_4648_: *mut leanh::LeanObject,
    mut v_a_4649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4651_ = leanh::lean_unsigned_to_nat(0);
    v___x_4652_ = l___private_Lean_Compiler_LCNF_Types_0__Lean_Compiler_LCNF_instantiateForall_go(
        v_ps_4647_,
        v___x_4651_,
        v_type_4646_,
        v_a_4648_,
        v_a_4649_,
    );
    return v___x_4652_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instantiateForall___boxed(
    mut v_type_4653_: *mut leanh::LeanObject,
    mut v_ps_4654_: *mut leanh::LeanObject,
    mut v_a_4655_: *mut leanh::LeanObject,
    mut v_a_4656_: *mut leanh::LeanObject,
    mut v_a_4657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4658_ =
        l_Lean_Compiler_LCNF_instantiateForall(v_type_4653_, v_ps_4654_, v_a_4655_, v_a_4656_);
    leanh::lean_dec(v_a_4656_);
    leanh::lean_dec_ref(v_a_4655_);
    leanh::lean_dec_ref(v_ps_4654_);
    return v_res_4658_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isPredicateType(
    mut v_type_4659_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: u8 = 0;
    let mut v___x_4663_: u8 = 0;
    let mut v_body_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4660_ = l_Lean_Expr_headBeta(v_type_4659_);
                match leanh::lean_obj_tag(v___x_4660_) {
                    3 => {
                        v_u_4661_ = leanh::lean_ctor_get(v___x_4660_, 0);
                        leanh::lean_inc(v_u_4661_);
                        leanh::lean_dec_ref_known(v___x_4660_, 1);
                        if leanh::lean_obj_tag(v_u_4661_) == 0 {
                            v___x_4662_ = 1;
                            return v___x_4662_;
                        } else {
                            leanh::lean_dec(v_u_4661_);
                            v___x_4663_ = 0;
                            return v___x_4663_;
                        }
                    }
                    7 => {
                        v_body_4664_ = leanh::lean_ctor_get(v___x_4660_, 2);
                        leanh::lean_inc_ref(v_body_4664_);
                        leanh::lean_dec_ref_known(v___x_4660_, 3);
                        v_type_4659_ = v_body_4664_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        leanh::lean_dec_ref(v___x_4660_);
                        v___x_4666_ = 0;
                        return v___x_4666_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isPredicateType___boxed(
    mut v_type_4667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4668_: u8 = 0;
    let mut v_r_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4668_ = l_Lean_Compiler_LCNF_isPredicateType(v_type_4667_);
    v_r_4669_ = leanh::lean_box((v_res_4668_) as usize);
    return v_r_4669_;
}
pub unsafe fn l_Lean_Compiler_LCNF_maybeTypeFormerType(
    mut v_type_4670_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: u8 = 0;
    let mut v_body_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_type_4670_);
                v___x_4671_ = l_Lean_Expr_headBeta(v_type_4670_);
                match leanh::lean_obj_tag(v___x_4671_) {
                    3 => {
                        leanh::lean_dec_ref_known(v___x_4671_, 1);
                        leanh::lean_dec_ref(v_type_4670_);
                        v___x_4672_ = 1;
                        return v___x_4672_;
                    }
                    7 => {
                        leanh::lean_dec_ref(v_type_4670_);
                        v_body_4673_ = leanh::lean_ctor_get(v___x_4671_, 2);
                        leanh::lean_inc_ref(v_body_4673_);
                        leanh::lean_dec_ref_known(v___x_4671_, 3);
                        v_type_4670_ = v_body_4673_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        leanh::lean_dec_ref(v___x_4671_);
                        v___x_4675_ = l_Lean_Expr_isErased(v_type_4670_);
                        leanh::lean_dec_ref(v_type_4670_);
                        return v___x_4675_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_maybeTypeFormerType___boxed(
    mut v_type_4676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4677_: u8 = 0;
    let mut v_r_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4677_ = l_Lean_Compiler_LCNF_maybeTypeFormerType(v_type_4676_);
    v_r_4678_ = leanh::lean_box((v_res_4677_) as usize);
    return v_r_4678_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isClass_x3f___redArg(
    mut v_type_4679_: *mut leanh::LeanObject,
    mut v_a_4680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4682_ = l_Lean_Expr_getAppFn(v_type_4679_);
    if leanh::lean_obj_tag(v___x_4682_) == 4 {
        let mut v_declName_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_env_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4686_: u8 = 0;
        v_declName_4683_ = leanh::lean_ctor_get(v___x_4682_, 0);
        leanh::lean_inc_n(v_declName_4683_, 2);
        leanh::lean_dec_ref_known(v___x_4682_, 2);
        v___x_4684_ = lean_st_ref_get(v_a_4680_);
        v_env_4685_ = leanh::lean_ctor_get(v___x_4684_, 0);
        leanh::lean_inc_ref(v_env_4685_);
        leanh::lean_dec(v___x_4684_);
        v___x_4686_ = lean_is_class(v_env_4685_, v_declName_4683_);
        if v___x_4686_ == 0 {
            let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_declName_4683_);
            v___x_4687_ = leanh::lean_box(0);
            v___x_4688_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_4688_, 0, v___x_4687_);
            return v___x_4688_;
        } else {
            let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4689_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_4689_, 0, v_declName_4683_);
            v___x_4690_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_4690_, 0, v___x_4689_);
            return v___x_4690_;
        }
    } else {
        let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_4682_);
        v___x_4691_ = leanh::lean_box(0);
        v___x_4692_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4692_, 0, v___x_4691_);
        return v___x_4692_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isClass_x3f___redArg___boxed(
    mut v_type_4693_: *mut leanh::LeanObject,
    mut v_a_4694_: *mut leanh::LeanObject,
    mut v_a_4695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4696_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_4693_, v_a_4694_);
    leanh::lean_dec(v_a_4694_);
    leanh::lean_dec_ref(v_type_4693_);
    return v_res_4696_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isClass_x3f(
    mut v_type_4697_: *mut leanh::LeanObject,
    mut v_a_4698_: *mut leanh::LeanObject,
    mut v_a_4699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4701_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_4697_, v_a_4699_);
    return v___x_4701_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isClass_x3f___boxed(
    mut v_type_4702_: *mut leanh::LeanObject,
    mut v_a_4703_: *mut leanh::LeanObject,
    mut v_a_4704_: *mut leanh::LeanObject,
    mut v_a_4705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4706_ = l_Lean_Compiler_LCNF_isClass_x3f(v_type_4702_, v_a_4703_, v_a_4704_);
    leanh::lean_dec(v_a_4704_);
    leanh::lean_dec_ref(v_a_4703_);
    leanh::lean_dec_ref(v_type_4702_);
    return v_res_4706_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(
    mut v_type_4707_: *mut leanh::LeanObject,
    mut v_a_4708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_type_4707_);
                v___x_4710_ = l_Lean_Expr_headBeta(v_type_4707_);
                if leanh::lean_obj_tag(v___x_4710_) == 7 {
                    leanh::lean_dec_ref(v_type_4707_);
                    v_body_4711_ = leanh::lean_ctor_get(v___x_4710_, 2);
                    leanh::lean_inc_ref(v_body_4711_);
                    leanh::lean_dec_ref_known(v___x_4710_, 3);
                    v_type_4707_ = v_body_4711_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___x_4710_);
                    v___x_4713_ =
                        l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_4707_, v_a_4708_);
                    leanh::lean_dec_ref(v_type_4707_);
                    return v___x_4713_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg___boxed(
    mut v_type_4714_: *mut leanh::LeanObject,
    mut v_a_4715_: *mut leanh::LeanObject,
    mut v_a_4716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4717_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_4714_, v_a_4715_);
    leanh::lean_dec(v_a_4715_);
    return v_res_4717_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isArrowClass_x3f(
    mut v_type_4718_: *mut leanh::LeanObject,
    mut v_a_4719_: *mut leanh::LeanObject,
    mut v_a_4720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4722_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_4718_, v_a_4720_);
    return v___x_4722_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isArrowClass_x3f___boxed(
    mut v_type_4723_: *mut leanh::LeanObject,
    mut v_a_4724_: *mut leanh::LeanObject,
    mut v_a_4725_: *mut leanh::LeanObject,
    mut v_a_4726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4727_ = l_Lean_Compiler_LCNF_isArrowClass_x3f(v_type_4723_, v_a_4724_, v_a_4725_);
    leanh::lean_dec(v_a_4725_);
    leanh::lean_dec_ref(v_a_4724_);
    return v_res_4727_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getArrowArity(
    mut v_e_4728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4729_ = l_Lean_Expr_headBeta(v_e_4728_);
    if leanh::lean_obj_tag(v___x_4729_) == 7 {
        let mut v_body_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_body_4730_ = leanh::lean_ctor_get(v___x_4729_, 2);
        leanh::lean_inc_ref(v_body_4730_);
        leanh::lean_dec_ref_known(v___x_4729_, 3);
        v___x_4731_ = l_Lean_Compiler_LCNF_getArrowArity(v_body_4730_);
        v___x_4732_ = leanh::lean_unsigned_to_nat(1);
        v___x_4733_ = lean_nat_add(v___x_4731_, v___x_4732_);
        leanh::lean_dec(v___x_4731_);
        return v___x_4733_;
    } else {
        let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_4729_);
        v___x_4734_ = leanh::lean_unsigned_to_nat(0);
        return v___x_4734_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(
    mut v_type_4735_: *mut leanh::LeanObject,
    mut v_a_4736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4739_: u8 = 0;
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: u8 = 0;
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4752_: u8 = 0;
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: u8 = 0;
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4760_: u8 = 0;
    let mut v___x_4761_: u8 = 0;
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4742_ = l_Lean_Expr_getAppFn(v_type_4735_);
                if leanh::lean_obj_tag(v___x_4742_) == 4 {
                    v_declName_4743_ = leanh::lean_ctor_get(v___x_4742_, 0);
                    leanh::lean_inc(v_declName_4743_);
                    leanh::lean_dec_ref_known(v___x_4742_, 2);
                    v___x_4744_ = lean_st_ref_get(v_a_4736_);
                    v_env_4745_ = leanh::lean_ctor_get(v___x_4744_, 0);
                    leanh::lean_inc_ref(v_env_4745_);
                    leanh::lean_dec(v___x_4744_);
                    v___x_4746_ = 0;
                    v___x_4747_ =
                        l_Lean_Environment_find_x3f(v_env_4745_, v_declName_4743_, v___x_4746_);
                    if leanh::lean_obj_tag(v___x_4747_) == 1 {
                        v_val_4748_ = leanh::lean_ctor_get(v___x_4747_, 0);
                        leanh::lean_inc(v_val_4748_);
                        leanh::lean_dec_ref_known(v___x_4747_, 1);
                        if leanh::lean_obj_tag(v_val_4748_) == 5 {
                            v_val_4749_ = leanh::lean_ctor_get(v_val_4748_, 0);
                            v_isSharedCheck_4760_ =
                                (!leanh::lean_is_exclusive(v_val_4748_)) as u8;
                            if v_isSharedCheck_4760_ == 0 {
                                v___x_4751_ = v_val_4748_;
                                v_isShared_4752_ = v_isSharedCheck_4760_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_4749_);
                                leanh::lean_dec(v_val_4748_);
                                v___x_4751_ = leanh::lean_box(0);
                                v_isShared_4752_ = v_isSharedCheck_4760_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_4748_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4747_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4742_);
                    v___x_4761_ = 0;
                    v___x_4762_ = leanh::lean_box((v___x_4761_) as usize);
                    v___x_4763_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4763_, 0, v___x_4762_);
                    return v___x_4763_;
                }
            }
            1 => {
                v___x_4739_ = 0;
                v___x_4740_ = leanh::lean_box((v___x_4739_) as usize);
                v___x_4741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4741_, 0, v___x_4740_);
                return v___x_4741_;
            }
            2 => {
                v___x_4753_ = l_Lean_InductiveVal_numCtors(v_val_4749_);
                leanh::lean_dec_ref(v_val_4749_);
                v___x_4754_ = leanh::lean_unsigned_to_nat(0);
                v___x_4755_ = lean_nat_dec_eq(v___x_4753_, v___x_4754_);
                leanh::lean_dec(v___x_4753_);
                v___x_4756_ = leanh::lean_box((v___x_4755_) as usize);
                if v_isShared_4752_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4751_, 0);
                    leanh::lean_ctor_set(v___x_4751_, 0, v___x_4756_);
                    v___x_4758_ = v___x_4751_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4759_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4759_, 0, v___x_4756_);
                    v___x_4758_ = v_reuseFailAlloc_4759_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg___boxed(
    mut v_type_4764_: *mut leanh::LeanObject,
    mut v_a_4765_: *mut leanh::LeanObject,
    mut v_a_4766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4767_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_4764_, v_a_4765_);
    leanh::lean_dec(v_a_4765_);
    leanh::lean_dec_ref(v_type_4764_);
    return v_res_4767_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isInductiveWithNoCtors(
    mut v_type_4768_: *mut leanh::LeanObject,
    mut v_a_4769_: *mut leanh::LeanObject,
    mut v_a_4770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4772_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_4768_, v_a_4770_);
    return v___x_4772_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isInductiveWithNoCtors___boxed(
    mut v_type_4773_: *mut leanh::LeanObject,
    mut v_a_4774_: *mut leanh::LeanObject,
    mut v_a_4775_: *mut leanh::LeanObject,
    mut v_a_4776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4777_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors(v_type_4773_, v_a_4774_, v_a_4775_);
    leanh::lean_dec(v_a_4775_);
    leanh::lean_dec_ref(v_a_4774_);
    leanh::lean_dec_ref(v_type_4773_);
    return v_res_4777_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkBoxedName(
    mut v_n_4779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4780_ = l_Lean_Compiler_LCNF_mkBoxedName___closed__0;
    v___x_4781_ = l_Lean_Name_str___override(v_n_4779_, v___x_4780_);
    return v___x_4781_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isBoxedName(
    mut v_name_4782_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_name_4782_) == 1 {
        let mut v_str_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4785_: u8 = 0;
        v_str_4783_ = leanh::lean_ctor_get(v_name_4782_, 1);
        v___x_4784_ = l_Lean_Compiler_LCNF_mkBoxedName___closed__0;
        v___x_4785_ = lean_string_dec_eq(v_str_4783_, v___x_4784_);
        return v___x_4785_;
    } else {
        let mut v___x_4786_: u8 = 0;
        v___x_4786_ = 0;
        return v___x_4786_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isBoxedName___boxed(
    mut v_name_4787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4788_: u8 = 0;
    let mut v_r_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4788_ = l_Lean_Compiler_LCNF_isBoxedName(v_name_4787_);
    leanh::lean_dec(v_name_4787_);
    v_r_4789_ = leanh::lean_box((v_res_4788_) as usize);
    return v_r_4789_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4793_ = leanh::lean_box(0);
    v___x_4794_ = l_Lean_Compiler_LCNF_ImpureType_float___closed__1;
    v___x_4795_ = l_Lean_Expr_const___override(v___x_4794_, v___x_4793_);
    return v___x_4795_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_float() -> *mut leanh::LeanObject {
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4796_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_float___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_float___closed__2_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_float___closed__2,
    );
    return v___x_4796_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4800_ = leanh::lean_box(0);
    v___x_4801_ = l_Lean_Compiler_LCNF_ImpureType_float32___closed__1;
    v___x_4802_ = l_Lean_Expr_const___override(v___x_4801_, v___x_4800_);
    return v___x_4802_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_float32() -> *mut leanh::LeanObject {
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4803_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_float32___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_float32___closed__2_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_float32___closed__2,
    );
    return v___x_4803_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4807_ = leanh::lean_box(0);
    v___x_4808_ = l_Lean_Compiler_LCNF_ImpureType_uint8___closed__1;
    v___x_4809_ = l_Lean_Expr_const___override(v___x_4808_, v___x_4807_);
    return v___x_4809_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_uint8() -> *mut leanh::LeanObject {
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4810_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_uint8___closed__2,
    );
    return v___x_4810_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4814_ = leanh::lean_box(0);
    v___x_4815_ = l_Lean_Compiler_LCNF_ImpureType_uint16___closed__1;
    v___x_4816_ = l_Lean_Expr_const___override(v___x_4815_, v___x_4814_);
    return v___x_4816_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_uint16() -> *mut leanh::LeanObject {
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4817_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_uint16___closed__2,
    );
    return v___x_4817_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4821_ = leanh::lean_box(0);
    v___x_4822_ = l_Lean_Compiler_LCNF_ImpureType_uint32___closed__1;
    v___x_4823_ = l_Lean_Expr_const___override(v___x_4822_, v___x_4821_);
    return v___x_4823_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_uint32() -> *mut leanh::LeanObject {
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4824_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_uint32___closed__2,
    );
    return v___x_4824_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4828_ = leanh::lean_box(0);
    v___x_4829_ = l_Lean_Compiler_LCNF_ImpureType_uint64___closed__1;
    v___x_4830_ = l_Lean_Expr_const___override(v___x_4829_, v___x_4828_);
    return v___x_4830_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_uint64() -> *mut leanh::LeanObject {
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_uint64___closed__2,
    );
    return v___x_4831_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4835_ = leanh::lean_box(0);
    v___x_4836_ = l_Lean_Compiler_LCNF_ImpureType_usize___closed__1;
    v___x_4837_ = l_Lean_Expr_const___override(v___x_4836_, v___x_4835_);
    return v___x_4837_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_usize() -> *mut leanh::LeanObject {
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4838_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_usize___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_usize___closed__2_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_usize___closed__2,
    );
    return v___x_4838_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4839_ = leanh::lean_box(0);
    v___x_4840_ = l_Lean_Compiler___aux__Lean__Compiler__LCNF__Types______macroRules__Lean__Compiler__term_u25fe__1___closed__2;
    v___x_4841_ = l_Lean_Expr_const___override(v___x_4840_, v___x_4839_);
    return v___x_4841_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_erased() -> *mut leanh::LeanObject {
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4842_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_erased___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_erased___closed__0_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_erased___closed__0,
    );
    return v___x_4842_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4846_ = leanh::lean_box(0);
    v___x_4847_ = l_Lean_Compiler_LCNF_ImpureType_object___closed__1;
    v___x_4848_ = l_Lean_Expr_const___override(v___x_4847_, v___x_4846_);
    return v___x_4848_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_object() -> *mut leanh::LeanObject {
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4849_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_object___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2,
    );
    return v___x_4849_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4853_ = leanh::lean_box(0);
    v___x_4854_ = l_Lean_Compiler_LCNF_ImpureType_tobject___closed__1;
    v___x_4855_ = l_Lean_Expr_const___override(v___x_4854_, v___x_4853_);
    return v___x_4855_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_tobject() -> *mut leanh::LeanObject {
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4856_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2,
    );
    return v___x_4856_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4860_ = leanh::lean_box(0);
    v___x_4861_ = l_Lean_Compiler_LCNF_ImpureType_tagged___closed__1;
    v___x_4862_ = l_Lean_Expr_const___override(v___x_4861_, v___x_4860_);
    return v___x_4862_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_tagged() -> *mut leanh::LeanObject {
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4863_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2,
    );
    return v___x_4863_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4864_ = leanh::lean_box(0);
    v___x_4865_ = l_Lean_Expr_isVoid___closed__1;
    v___x_4866_ = l_Lean_Expr_const___override(v___x_4865_, v___x_4864_);
    return v___x_4866_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ImpureType_void() -> *mut leanh::LeanObject {
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4867_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_void___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_void___closed__0_once),
        _init_l_Lean_Compiler_LCNF_ImpureType_void___closed__0,
    );
    return v___x_4867_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(
    mut v_x_4868_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4868_) == 4 {
        let mut v_declName_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_declName_4869_ = leanh::lean_ctor_get(v_x_4868_, 0);
        if leanh::lean_obj_tag(v_declName_4869_) == 1 {
            let mut v_pre_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_4870_ = leanh::lean_ctor_get(v_declName_4869_, 0);
            if leanh::lean_obj_tag(v_pre_4870_) == 0 {
                let mut v_us_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4874_: u8 = 0;
                v_us_4871_ = leanh::lean_ctor_get(v_x_4868_, 1);
                v_str_4872_ = leanh::lean_ctor_get(v_declName_4869_, 1);
                v___x_4873_ = l_Lean_Compiler_LCNF_ImpureType_float___closed__0;
                v___x_4874_ = lean_string_dec_eq(v_str_4872_, v___x_4873_);
                if v___x_4874_ == 0 {
                    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4876_: u8 = 0;
                    v___x_4875_ = l_Lean_Compiler_LCNF_ImpureType_float32___closed__0;
                    v___x_4876_ = lean_string_dec_eq(v_str_4872_, v___x_4875_);
                    if v___x_4876_ == 0 {
                        let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4878_: u8 = 0;
                        v___x_4877_ = l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0;
                        v___x_4878_ = lean_string_dec_eq(v_str_4872_, v___x_4877_);
                        if v___x_4878_ == 0 {
                            let mut v___x_4879_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4880_: u8 = 0;
                            v___x_4879_ = l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0;
                            v___x_4880_ = lean_string_dec_eq(v_str_4872_, v___x_4879_);
                            if v___x_4880_ == 0 {
                                let mut v___x_4881_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4882_: u8 = 0;
                                v___x_4881_ = l_Lean_Compiler_LCNF_ImpureType_uint32___closed__0;
                                v___x_4882_ = lean_string_dec_eq(v_str_4872_, v___x_4881_);
                                if v___x_4882_ == 0 {
                                    let mut v___x_4883_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4884_: u8 = 0;
                                    v___x_4883_ =
                                        l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0;
                                    v___x_4884_ = lean_string_dec_eq(v_str_4872_, v___x_4883_);
                                    if v___x_4884_ == 0 {
                                        let mut v___x_4885_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_4886_: u8 = 0;
                                        v___x_4885_ =
                                            l_Lean_Compiler_LCNF_ImpureType_usize___closed__0;
                                        v___x_4886_ = lean_string_dec_eq(v_str_4872_, v___x_4885_);
                                        if v___x_4886_ == 0 {
                                            return v___x_4886_;
                                        } else {
                                            if leanh::lean_obj_tag(v_us_4871_) == 0 {
                                                return v___x_4886_;
                                            } else {
                                                return v___x_4884_;
                                            }
                                        }
                                    } else {
                                        if leanh::lean_obj_tag(v_us_4871_) == 0 {
                                            return v___x_4884_;
                                        } else {
                                            return v___x_4882_;
                                        }
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v_us_4871_) == 0 {
                                        return v___x_4882_;
                                    } else {
                                        return v___x_4880_;
                                    }
                                }
                            } else {
                                if leanh::lean_obj_tag(v_us_4871_) == 0 {
                                    return v___x_4880_;
                                } else {
                                    return v___x_4878_;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v_us_4871_) == 0 {
                                return v___x_4878_;
                            } else {
                                return v___x_4876_;
                            }
                        }
                    } else {
                        if leanh::lean_obj_tag(v_us_4871_) == 0 {
                            return v___x_4876_;
                        } else {
                            return v___x_4874_;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_us_4871_) == 0 {
                        return v___x_4874_;
                    } else {
                        let mut v___x_4887_: u8 = 0;
                        v___x_4887_ = 0;
                        return v___x_4887_;
                    }
                }
            } else {
                let mut v___x_4888_: u8 = 0;
                v___x_4888_ = 0;
                return v___x_4888_;
            }
        } else {
            let mut v___x_4889_: u8 = 0;
            v___x_4889_ = 0;
            return v___x_4889_;
        }
    } else {
        let mut v___x_4890_: u8 = 0;
        v___x_4890_ = 0;
        return v___x_4890_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar___boxed(
    mut v_x_4891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4892_: u8 = 0;
    let mut v_r_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4892_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_x_4891_);
    leanh::lean_dec_ref(v_x_4891_);
    v_r_4893_ = leanh::lean_box((v_res_4892_) as usize);
    return v_r_4893_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(
    mut v_x_4894_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4894_) == 4 {
        let mut v_declName_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_declName_4895_ = leanh::lean_ctor_get(v_x_4894_, 0);
        if leanh::lean_obj_tag(v_declName_4895_) == 1 {
            let mut v_pre_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_4896_ = leanh::lean_ctor_get(v_declName_4895_, 0);
            if leanh::lean_obj_tag(v_pre_4896_) == 0 {
                let mut v_us_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4900_: u8 = 0;
                v_us_4897_ = leanh::lean_ctor_get(v_x_4894_, 1);
                v_str_4898_ = leanh::lean_ctor_get(v_declName_4895_, 1);
                v___x_4899_ = l_Lean_Compiler_LCNF_ImpureType_object___closed__0;
                v___x_4900_ = lean_string_dec_eq(v_str_4898_, v___x_4899_);
                if v___x_4900_ == 0 {
                    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4902_: u8 = 0;
                    v___x_4901_ = l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0;
                    v___x_4902_ = lean_string_dec_eq(v_str_4898_, v___x_4901_);
                    if v___x_4902_ == 0 {
                        let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4904_: u8 = 0;
                        v___x_4903_ = l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0;
                        v___x_4904_ = lean_string_dec_eq(v_str_4898_, v___x_4903_);
                        if v___x_4904_ == 0 {
                            let mut v___x_4905_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4906_: u8 = 0;
                            v___x_4905_ = l_Lean_Expr_isVoid___closed__0;
                            v___x_4906_ = lean_string_dec_eq(v_str_4898_, v___x_4905_);
                            if v___x_4906_ == 0 {
                                return v___x_4906_;
                            } else {
                                if leanh::lean_obj_tag(v_us_4897_) == 0 {
                                    return v___x_4906_;
                                } else {
                                    return v___x_4904_;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v_us_4897_) == 0 {
                                return v___x_4904_;
                            } else {
                                return v___x_4902_;
                            }
                        }
                    } else {
                        if leanh::lean_obj_tag(v_us_4897_) == 0 {
                            return v___x_4902_;
                        } else {
                            return v___x_4900_;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_us_4897_) == 0 {
                        return v___x_4900_;
                    } else {
                        let mut v___x_4907_: u8 = 0;
                        v___x_4907_ = 0;
                        return v___x_4907_;
                    }
                }
            } else {
                let mut v___x_4908_: u8 = 0;
                v___x_4908_ = 0;
                return v___x_4908_;
            }
        } else {
            let mut v___x_4909_: u8 = 0;
            v___x_4909_ = 0;
            return v___x_4909_;
        }
    } else {
        let mut v___x_4910_: u8 = 0;
        v___x_4910_ = 0;
        return v___x_4910_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj___boxed(
    mut v_x_4911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4912_: u8 = 0;
    let mut v_r_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4912_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isObj(v_x_4911_);
    leanh::lean_dec_ref(v_x_4911_);
    v_r_4913_ = leanh::lean_box((v_res_4912_) as usize);
    return v_r_4913_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(
    mut v_x_4914_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4914_) == 4 {
        let mut v_declName_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_declName_4915_ = leanh::lean_ctor_get(v_x_4914_, 0);
        if leanh::lean_obj_tag(v_declName_4915_) == 1 {
            let mut v_pre_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_4916_ = leanh::lean_ctor_get(v_declName_4915_, 0);
            if leanh::lean_obj_tag(v_pre_4916_) == 0 {
                let mut v_us_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4920_: u8 = 0;
                v_us_4917_ = leanh::lean_ctor_get(v_x_4914_, 1);
                v_str_4918_ = leanh::lean_ctor_get(v_declName_4915_, 1);
                v___x_4919_ = l_Lean_Compiler_LCNF_ImpureType_object___closed__0;
                v___x_4920_ = lean_string_dec_eq(v_str_4918_, v___x_4919_);
                if v___x_4920_ == 0 {
                    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4922_: u8 = 0;
                    v___x_4921_ = l_Lean_Compiler_LCNF_ImpureType_tobject___closed__0;
                    v___x_4922_ = lean_string_dec_eq(v_str_4918_, v___x_4921_);
                    if v___x_4922_ == 0 {
                        return v___x_4922_;
                    } else {
                        if leanh::lean_obj_tag(v_us_4917_) == 0 {
                            return v___x_4922_;
                        } else {
                            return v___x_4920_;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_us_4917_) == 0 {
                        return v___x_4920_;
                    } else {
                        let mut v___x_4923_: u8 = 0;
                        v___x_4923_ = 0;
                        return v___x_4923_;
                    }
                }
            } else {
                let mut v___x_4924_: u8 = 0;
                v___x_4924_ = 0;
                return v___x_4924_;
            }
        } else {
            let mut v___x_4925_: u8 = 0;
            v___x_4925_ = 0;
            return v___x_4925_;
        }
    } else {
        let mut v___x_4926_: u8 = 0;
        v___x_4926_ = 0;
        return v___x_4926_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef___boxed(
    mut v_x_4927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4928_: u8 = 0;
    let mut v_r_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4928_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_x_4927_);
    leanh::lean_dec_ref(v_x_4927_);
    v_r_4929_ = leanh::lean_box((v_res_4928_) as usize);
    return v_r_4929_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(
    mut v_x_4930_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4930_) == 4 {
        let mut v_declName_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_declName_4931_ = leanh::lean_ctor_get(v_x_4930_, 0);
        if leanh::lean_obj_tag(v_declName_4931_) == 1 {
            let mut v_pre_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_4932_ = leanh::lean_ctor_get(v_declName_4931_, 0);
            if leanh::lean_obj_tag(v_pre_4932_) == 0 {
                let mut v_us_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4936_: u8 = 0;
                v_us_4933_ = leanh::lean_ctor_get(v_x_4930_, 1);
                v_str_4934_ = leanh::lean_ctor_get(v_declName_4931_, 1);
                v___x_4935_ = l_Lean_Compiler_LCNF_ImpureType_object___closed__0;
                v___x_4936_ = lean_string_dec_eq(v_str_4934_, v___x_4935_);
                if v___x_4936_ == 0 {
                    return v___x_4936_;
                } else {
                    if leanh::lean_obj_tag(v_us_4933_) == 0 {
                        return v___x_4936_;
                    } else {
                        let mut v___x_4937_: u8 = 0;
                        v___x_4937_ = 0;
                        return v___x_4937_;
                    }
                }
            } else {
                let mut v___x_4938_: u8 = 0;
                v___x_4938_ = 0;
                return v___x_4938_;
            }
        } else {
            let mut v___x_4939_: u8 = 0;
            v___x_4939_ = 0;
            return v___x_4939_;
        }
    } else {
        let mut v___x_4940_: u8 = 0;
        v___x_4940_ = 0;
        return v___x_4940_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef___boxed(
    mut v_x_4941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4942_: u8 = 0;
    let mut v_r_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4942_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_x_4941_);
    leanh::lean_dec_ref(v_x_4941_);
    v_r_4943_ = leanh::lean_box((v_res_4942_) as usize);
    return v_r_4943_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(
    mut v_x_4944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: u8 = 0;
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: u8 = 0;
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: u8 = 0;
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: u8 = 0;
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: u8 = 0;
    let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: u8 = 0;
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: u8 = 0;
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4944_) == 4 {
                    v_declName_4951_ = leanh::lean_ctor_get(v_x_4944_, 0);
                    if leanh::lean_obj_tag(v_declName_4951_) == 1 {
                        v_pre_4952_ = leanh::lean_ctor_get(v_declName_4951_, 0);
                        if leanh::lean_obj_tag(v_pre_4952_) == 0 {
                            v_us_4953_ = leanh::lean_ctor_get(v_x_4944_, 1);
                            v_str_4954_ = leanh::lean_ctor_get(v_declName_4951_, 1);
                            v___x_4955_ = l_Lean_Compiler_LCNF_ImpureType_object___closed__0;
                            v___x_4956_ = lean_string_dec_eq(v_str_4954_, v___x_4955_);
                            if v___x_4956_ == 0 {
                                v___x_4957_ = l_Lean_Compiler_LCNF_ImpureType_float___closed__0;
                                v___x_4958_ = lean_string_dec_eq(v_str_4954_, v___x_4957_);
                                if v___x_4958_ == 0 {
                                    v___x_4959_ =
                                        l_Lean_Compiler_LCNF_ImpureType_float32___closed__0;
                                    v___x_4960_ = lean_string_dec_eq(v_str_4954_, v___x_4959_);
                                    if v___x_4960_ == 0 {
                                        v___x_4961_ =
                                            l_Lean_Compiler_LCNF_ImpureType_uint64___closed__0;
                                        v___x_4962_ = lean_string_dec_eq(v_str_4954_, v___x_4961_);
                                        if v___x_4962_ == 0 {
                                            v___x_4963_ = l_Lean_Expr_isVoid___closed__0;
                                            v___x_4964_ =
                                                lean_string_dec_eq(v_str_4954_, v___x_4963_);
                                            if v___x_4964_ == 0 {
                                                v___x_4965_ = l_Lean_Compiler_LCNF_ImpureType_tagged___closed__0;
                                                v___x_4966_ =
                                                    lean_string_dec_eq(v_str_4954_, v___x_4965_);
                                                if v___x_4966_ == 0 {
                                                    v___x_4967_ = l_Lean_Compiler_LCNF_ImpureType_uint8___closed__0;
                                                    v___x_4968_ = lean_string_dec_eq(
                                                        v_str_4954_,
                                                        v___x_4967_,
                                                    );
                                                    if v___x_4968_ == 0 {
                                                        v___x_4969_ = l_Lean_Compiler_LCNF_ImpureType_uint16___closed__0;
                                                        v___x_4970_ = lean_string_dec_eq(
                                                            v_str_4954_,
                                                            v___x_4969_,
                                                        );
                                                        if v___x_4970_ == 0 {
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            if leanh::lean_obj_tag(
                                                                v_us_4953_,
                                                            ) == 0
                                                            {
                                                                state = 3;
                                                                continue;
                                                            } else {
                                                                state = 1;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        if leanh::lean_obj_tag(v_us_4953_)
                                                            == 0
                                                        {
                                                            state = 3;
                                                            continue;
                                                        } else {
                                                            state = 1;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    if leanh::lean_obj_tag(v_us_4953_) == 0 {
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        state = 1;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                if leanh::lean_obj_tag(v_us_4953_) == 0 {
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    state = 1;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v_us_4953_) == 0 {
                                                state = 2;
                                                continue;
                                            } else {
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    } else {
                                        if leanh::lean_obj_tag(v_us_4953_) == 0 {
                                            state = 2;
                                            continue;
                                        } else {
                                            state = 1;
                                            continue;
                                        }
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v_us_4953_) == 0 {
                                        state = 2;
                                        continue;
                                    } else {
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                if leanh::lean_obj_tag(v_us_4953_) == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4946_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_ImpureType_tobject___closed__2,
                );
                return v___x_4946_;
            }
            2 => {
                v___x_4948_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_object___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_ImpureType_object___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_ImpureType_object___closed__2,
                );
                return v___x_4948_;
            }
            3 => {
                v___x_4950_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_ImpureType_tagged___closed__2,
                );
                return v___x_4950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed___boxed(
    mut v_x_4971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4972_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_x_4971_);
    leanh::lean_dec_ref(v_x_4971_);
    return v_res_4972_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_BorrowedAnnotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_OriginalConstKind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_erasedExpr = _init_l_Lean_Compiler_LCNF_erasedExpr();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_erasedExpr);
    l_Lean_Compiler_LCNF_anyExpr = _init_l_Lean_Compiler_LCNF_anyExpr();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_anyExpr);
    l_Lean_Compiler_LCNF_ImpureType_float = _init_l_Lean_Compiler_LCNF_ImpureType_float();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_float);
    l_Lean_Compiler_LCNF_ImpureType_float32 = _init_l_Lean_Compiler_LCNF_ImpureType_float32();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_float32);
    l_Lean_Compiler_LCNF_ImpureType_uint8 = _init_l_Lean_Compiler_LCNF_ImpureType_uint8();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_uint8);
    l_Lean_Compiler_LCNF_ImpureType_uint16 = _init_l_Lean_Compiler_LCNF_ImpureType_uint16();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_uint16);
    l_Lean_Compiler_LCNF_ImpureType_uint32 = _init_l_Lean_Compiler_LCNF_ImpureType_uint32();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_uint32);
    l_Lean_Compiler_LCNF_ImpureType_uint64 = _init_l_Lean_Compiler_LCNF_ImpureType_uint64();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_uint64);
    l_Lean_Compiler_LCNF_ImpureType_usize = _init_l_Lean_Compiler_LCNF_ImpureType_usize();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_usize);
    l_Lean_Compiler_LCNF_ImpureType_erased = _init_l_Lean_Compiler_LCNF_ImpureType_erased();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_erased);
    l_Lean_Compiler_LCNF_ImpureType_object = _init_l_Lean_Compiler_LCNF_ImpureType_object();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_object);
    l_Lean_Compiler_LCNF_ImpureType_tobject = _init_l_Lean_Compiler_LCNF_ImpureType_tobject();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_tobject);
    l_Lean_Compiler_LCNF_ImpureType_tagged = _init_l_Lean_Compiler_LCNF_ImpureType_tagged();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_tagged);
    l_Lean_Compiler_LCNF_ImpureType_void = _init_l_Lean_Compiler_LCNF_ImpureType_void();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_ImpureType_void);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Types(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Types(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_BorrowedAnnotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_OriginalConstKind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Types(builtin);
}