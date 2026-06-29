// Lean compiler output
// Module: Lean.Widget.Commands
// Imports: Lean.Widget.UserWidget Init.Notation Lean.Attributes
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_lt, lean_nat_mul,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_string_dec_eq,
    lean_string_intercalate, lean_uint64_dec_eq, lean_uint64_dec_lt, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f,
    l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_mkNameLit, l_Lean_TSyntax_getId,
    l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hash___override___boxed, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node5, l_Lean_Syntax_node6,
    l_Lean_addMacroScope, l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::AddDecl::l_Lean_addAndCompile;
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Attributes::l_Lean_Elab_toAttributeKind___boxed;
use crate::r#gen::Lean::Elab::Command::l_Lean_Elab_Command_liftTermElabM___redArg;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_elabTerm;
use crate::r#gen::Lean::Elab::Util::{
    l_Lean_Elab_expandMacroImpl_x3f, l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_mkConst};
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_addCore___redArg, l_Lean_ScopedEnvExtension_modifyState___redArg,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Lean::Widget::UserWidget::{
    initialize_Lean_Widget_UserWidget,
    l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe,
    l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe,
    l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt,
    l_Lean_Widget_savePanelWidgetInfo, runtime_initialize_Lean_Widget_UserWidget,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_maxView___redArg, l_Std_DTreeMap_Internal_Impl_minView___redArg,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
pub static l_Lean_Widget_widgetInstanceSpec___closed__0_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            119, 105, 100, 103, 101, 116, 73, 110, 115, 116, 97, 110, 99, 101, 83, 112, 101, 99, 0,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [87, 105, 100, 103, 101, 116, 0],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Widget_widgetInstanceSpec___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Widget_widgetInstanceSpec___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8308857172635824114 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Widget_widgetInstanceSpec___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13925169393008454587 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__4_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__4_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__6_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__6_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__9_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__9_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__11_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [119, 105, 116, 104, 32, 0],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__12_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__13_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__13_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__14_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__16_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__17_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__18_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetInstanceSpec___closed__19_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetInstanceSpec___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_widgetInstanceSpec: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__2_value) as *mut crate::leanh::LeanObject,2026475204632980274 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__5_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__8_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__8_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__8_value) as *mut crate::leanh::LeanObject,5018042693327868416 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__10_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__10_value) as *mut crate::leanh::LeanObject,6117808163008040242 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__12_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 76, 86, 97, 108, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__12_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__12_value) as *mut crate::leanh::LeanObject,14295752356045161913 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 100, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__14_value) as *mut crate::leanh::LeanObject,6041859491766292191 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__17_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__18_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__17_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__19_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 68, 101, 102, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__19_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__19_value) as *mut crate::leanh::LeanObject,7440505896048223825 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__21_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__22_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [106, 97, 118, 97, 115, 99, 114, 105, 112, 116, 72, 97, 115, 104, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__22_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__24_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__22_value) as *mut crate::leanh::LeanObject,341767172725632572 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__25_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__25_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__25_value) as *mut crate::leanh::LeanObject,5353940006376281447 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__27_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__27_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__27_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__29_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__29_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__29_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__31_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__32_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__33_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__32_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__2_value) as *mut crate::leanh::LeanObject,8308857172635824114 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__37_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__36_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__38_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__38_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__38_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__40_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__39_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__41_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__41_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__41_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__43_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__42_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__44_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__43_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__45_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__40_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__44_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__45_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__46_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__37_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__45_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__46_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__47_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__47_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__47_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__49_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [84, 111, 77, 111, 100, 117, 108, 101, 46, 116, 111, 77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__49_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__51_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 111, 77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__51_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__52_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__52_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__51_value) as *mut crate::leanh::LeanObject,13061281056160068605 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__52_value) as *mut crate::leanh::LeanObject,13826763611539437718 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__2_value) as *mut crate::leanh::LeanObject,8308857172635824114 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__51_value) as *mut crate::leanh::LeanObject,13835191317659186560 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__52_value) as *mut crate::leanh::LeanObject,16244922381413097087 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__55_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__54_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__55_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__55_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__57_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__57_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__59_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 114, 111, 112, 115, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__59_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__61_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__59_value) as *mut crate::leanh::LeanObject,1388899078119845201 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__62_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [83, 101, 114, 118, 101, 114, 46, 82, 112, 99, 69, 110, 99, 111, 100, 97, 98, 108, 101, 46, 114, 112, 99, 69, 110, 99, 111, 100, 101, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__62_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__64_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 101, 114, 118, 101, 114, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__64_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__65_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [82, 112, 99, 69, 110, 99, 111, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__65_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__66_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 112, 99, 69, 110, 99, 111, 100, 101, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__66_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__64_value) as *mut crate::leanh::LeanObject,1558204587275091866 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__65_value) as *mut crate::leanh::LeanObject,14205224002576139560 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__66_value) as *mut crate::leanh::LeanObject,1358420737987656218 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__64_value) as *mut crate::leanh::LeanObject,15371898625421214203 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__65_value) as *mut crate::leanh::LeanObject,9512484730448429213 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__66_value) as *mut crate::leanh::LeanObject,12194413601439834003 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__69_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__68_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__69: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__69_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__70_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__69_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__70: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__70_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__71_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [111, 112, 116, 69, 108, 108, 105, 112, 115, 105, 115, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__71: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__71_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__71_value) as *mut crate::leanh::LeanObject,11580369617518985485 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__73_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__73_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__74_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [87, 105, 100, 103, 101, 116, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__74: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__74_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__2_value) as *mut crate::leanh::LeanObject,8308857172635824114 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__74_value) as *mut crate::leanh::LeanObject,6368810086436444690 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__78_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__78: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__78_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__78_value) as *mut crate::leanh::LeanObject,9368229134555052249 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__80_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__80: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__80_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Widget_elabWidgetInstanceSpec___closed__0_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [74, 115, 111, 110, 46, 109, 107, 79, 98, 106, 0],
};
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Widget_elabWidgetInstanceSpec___closed__2_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [74, 115, 111, 110, 0],
};
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_elabWidgetInstanceSpec___closed__3_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [109, 107, 79, 98, 106, 0],
};
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Widget_elabWidgetInstanceSpec___closed__4_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__2_value)
            as *mut crate::leanh::LeanObject,
        1328561144935682750 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Widget_elabWidgetInstanceSpec___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__3_value)
                as *mut crate::leanh::LeanObject,
            466827370892149868 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__2_value)
            as *mut crate::leanh::LeanObject,
        849327805763387095 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__3_value)
                as *mut crate::leanh::LeanObject,
            1292069500323461113 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_elabWidgetInstanceSpec___closed__6_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_elabWidgetInstanceSpec___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__6_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_elabWidgetInstanceSpec___closed__8_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 101, 114, 109, 91, 95, 93, 0],
};
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_elabWidgetInstanceSpec___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__8_value)
                as *mut crate::leanh::LeanObject,
            11666683425613976406 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_elabWidgetInstanceSpec___closed__10_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [91, 0],
};
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_elabWidgetInstanceSpec___closed__11_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [93, 0],
};
static mut l_Lean_Widget_elabWidgetInstanceSpec___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_addWidgetSpec___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            97, 100, 100, 87, 105, 100, 103, 101, 116, 83, 112, 101, 99, 0,
        ],
    };
static mut l_Lean_Widget_addWidgetSpec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Widget_addWidgetSpec___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Widget_addWidgetSpec___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8308857172635824114 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Widget_addWidgetSpec___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6039569880997139036 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_addWidgetSpec___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_addWidgetSpec___closed__2_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0],
    };
static mut l_Lean_Widget_addWidgetSpec___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Widget_addWidgetSpec___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Widget_addWidgetSpec___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Widget_addWidgetSpec___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Widget_addWidgetSpec___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__3_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__2_value)
                as *mut crate::leanh::LeanObject,
            7983999284776576032 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_addWidgetSpec___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_addWidgetSpec___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_addWidgetSpec___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_addWidgetSpec___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_addWidgetSpec___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_addWidgetSpec___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_addWidgetSpec___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_addWidgetSpec: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_eraseWidgetSpec___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            101, 114, 97, 115, 101, 87, 105, 100, 103, 101, 116, 83, 112, 101, 99, 0,
        ],
    };
static mut l_Lean_Widget_eraseWidgetSpec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Widget_eraseWidgetSpec___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Widget_eraseWidgetSpec___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8308857172635824114 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Widget_eraseWidgetSpec___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            317594726881114870 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_eraseWidgetSpec___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_eraseWidgetSpec___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [45, 0],
    };
static mut l_Lean_Widget_eraseWidgetSpec___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_eraseWidgetSpec___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_eraseWidgetSpec___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_eraseWidgetSpec___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_eraseWidgetSpec___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_eraseWidgetSpec___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_eraseWidgetSpec___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_eraseWidgetSpec: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showWidgetSpec___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            115, 104, 111, 119, 87, 105, 100, 103, 101, 116, 83, 112, 101, 99, 0,
        ],
    };
static mut l_Lean_Widget_showWidgetSpec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Widget_showWidgetSpec___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Widget_showWidgetSpec___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8308857172635824114 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Widget_showWidgetSpec___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14834130175146174920 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showWidgetSpec___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showWidgetSpec___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [111, 114, 101, 108, 115, 101, 0],
    };
static mut l_Lean_Widget_showWidgetSpec___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showWidgetSpec___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__2_value)
                as *mut crate::leanh::LeanObject,
            393173242845875278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showWidgetSpec___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showWidgetSpec___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_addWidgetSpec___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_eraseWidgetSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showWidgetSpec___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showWidgetSpec___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showWidgetSpec___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_showWidgetSpec: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__0_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            115, 104, 111, 119, 80, 97, 110, 101, 108, 87, 105, 100, 103, 101, 116, 115, 67, 109,
            100, 0,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Widget_showPanelWidgetsCmd___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Widget_showPanelWidgetsCmd___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8308857172635824114 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13756061763304869835 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__2_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            115, 104, 111, 119, 95, 112, 97, 110, 101, 108, 95, 119, 105, 100, 103, 101, 116, 115,
            32, 0,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__6_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [44, 32, 0],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__8_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 11,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_showWidgetSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__7_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__10_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_elabWidgetInstanceSpec___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_showPanelWidgetsCmd___closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_showPanelWidgetsCmd___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_showPanelWidgetsCmd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_showPanelWidgetsCmd___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__3_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__17_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__18_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [95, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__0_value) as *mut crate::leanh::LeanObject,3246100636039109777 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3_value: crate::leanh::LeanStringObject<56> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 111, 109, 112, 105, 108, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 44, 32, 105, 116, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__5_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__2_value) as *mut crate::leanh::LeanObject,8308857172635824114 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__5_value) as *mut crate::leanh::LeanObject,2674240859200661470 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut crate::leanh::LeanObject)],
};
pub static mut l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetCmd___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [119, 105, 100, 103, 101, 116, 67, 109, 100, 0],
    };
static mut l_Lean_Widget_widgetCmd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Widget_widgetCmd___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Widget_widgetCmd___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8308857172635824114 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Widget_widgetCmd___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6403855130437285745 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetCmd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetCmd___closed__2_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [35, 119, 105, 100, 103, 101, 116, 32, 0],
    };
static mut l_Lean_Widget_widgetCmd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetCmd___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetCmd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetCmd___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetInstanceSpec___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetCmd___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_widgetCmd___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Widget_widgetCmd___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_widgetCmd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_widgetCmd___closed__5_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3424_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_3424_;
}
pub unsafe fn _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3444_ =
        l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__14;
    v___x_3445_ = l_String_toRawSubstring_x27(v___x_3444_);
    return v___x_3445_;
}
pub unsafe fn _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3462_ =
        l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__22;
    v___x_3463_ = l_String_toRawSubstring_x27(v___x_3462_);
    return v___x_3463_;
}
pub unsafe fn _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3489_ =
        l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34;
    v___x_3490_ = l_String_toRawSubstring_x27(v___x_3489_);
    return v___x_3490_;
}
pub unsafe fn _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3524_ =
        l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__49;
    v___x_3525_ = l_String_toRawSubstring_x27(v___x_3524_);
    return v___x_3525_;
}
pub unsafe fn _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3545_ =
        l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__59;
    v___x_3546_ = l_String_toRawSubstring_x27(v___x_3545_);
    return v___x_3546_;
}
pub unsafe fn _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3550_ =
        l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__62;
    v___x_3551_ = l_String_toRawSubstring_x27(v___x_3550_);
    return v___x_3551_;
}
pub unsafe fn _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3582_ = crate::leanh::lean_box(0);
    v___x_3583_ =
        l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75;
    v___x_3584_ = l_Lean_mkConst(v___x_3583_, v___x_3582_);
    return v___x_3584_;
}
pub unsafe fn _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3585_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76), core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76_once), _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__76);
    v___x_3586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3586_, 0, v___x_3585_);
    return v___x_3586_;
}
pub unsafe fn l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(
    mut v_mod_3594_: *mut crate::leanh::LeanObject,
    mut v_props_3595_: *mut crate::leanh::LeanObject,
    mut v_a_3596_: *mut crate::leanh::LeanObject,
    mut v_a_3597_: *mut crate::leanh::LeanObject,
    mut v_a_3598_: *mut crate::leanh::LeanObject,
    mut v_a_3599_: *mut crate::leanh::LeanObject,
    mut v_a_3600_: *mut crate::leanh::LeanObject,
    mut v_a_3601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: u8 = 0;
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: u8 = 0;
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3603_ = crate::leanh::lean_ctor_get(v_a_3600_, 5);
                v_quotContext_3604_ = crate::leanh::lean_ctor_get(v_a_3600_, 10);
                v_currMacroScope_3605_ = crate::leanh::lean_ctor_get(v_a_3600_, 11);
                v___x_3606_ = 0;
                v___x_3607_ = l_Lean_SourceInfo_fromRef(v_ref_3603_, v___x_3606_);
                v___x_3608_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__3;
                v___x_3609_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__4;
                crate::leanh::lean_inc_n(v___x_3607_, 5);
                v___x_3610_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3610_, 1, v___x_3609_);
                v___x_3611_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6;
                v___x_3612_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7_once), _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7);
                v___x_3613_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3613_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3613_, 1, v___x_3611_);
                crate::leanh::lean_ctor_set(v___x_3613_, 2, v___x_3612_);
                v___x_3614_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__9;
                v___x_3615_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__11;
                v___x_3616_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__13;
                v___x_3617_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15_once), _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__15);
                v___x_3618_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__16;
                crate::leanh::lean_inc(v_currMacroScope_3605_);
                crate::leanh::lean_inc(v_quotContext_3604_);
                v___x_3619_ =
                    l_Lean_addMacroScope(v_quotContext_3604_, v___x_3618_, v_currMacroScope_3605_);
                v___x_3620_ = crate::leanh::lean_box(0);
                v___x_3621_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__18;
                v___x_3622_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3622_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3622_, 1, v___x_3617_);
                crate::leanh::lean_ctor_set(v___x_3622_, 2, v___x_3619_);
                crate::leanh::lean_ctor_set(v___x_3622_, 3, v___x_3621_);
                crate::leanh::lean_inc_ref(v___x_3613_);
                v___x_3623_ =
                    l_Lean_Syntax_node2(v___x_3607_, v___x_3616_, v___x_3622_, v___x_3613_);
                v___x_3624_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__20;
                v___x_3625_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__21;
                v___x_3626_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3626_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3626_, 1, v___x_3625_);
                v___x_3692_ = l_Lean_TSyntax_getId(v_mod_3594_);
                crate::leanh::lean_inc(v___x_3692_);
                v___x_3693_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_3620_,
                    v___x_3692_,
                );
                if crate::leanh::lean_obj_tag(v___x_3693_) == 0 {
                    v___x_3694_ = l_Lean_quoteNameMk(v___x_3692_);
                    v___y_3628_ = v___x_3694_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3692_);
                    v_val_3695_ = crate::leanh::lean_ctor_get(v___x_3693_, 0);
                    crate::leanh::lean_inc(v_val_3695_);
                    crate::leanh::lean_dec_ref_known(v___x_3693_, 1);
                    v___x_3696_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__79;
                    v___x_3697_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__80;
                    v___x_3698_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58;
                    v___x_3699_ = lean_string_intercalate(v___x_3698_, v_val_3695_);
                    v___x_3700_ = lean_string_append(v___x_3697_, v___x_3699_);
                    crate::leanh::lean_dec_ref(v___x_3699_);
                    v___x_3701_ = crate::leanh::lean_box(2);
                    v___x_3702_ = l_Lean_Syntax_mkNameLit(v___x_3700_, v___x_3701_);
                    v___x_3703_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3704_ = lean_mk_empty_array_with_capacity(v___x_3703_);
                    v___x_3705_ = lean_array_push(v___x_3704_, v___x_3702_);
                    v___x_3706_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3706_, 0, v___x_3701_);
                    crate::leanh::lean_ctor_set(v___x_3706_, 1, v___x_3696_);
                    crate::leanh::lean_ctor_set(v___x_3706_, 2, v___x_3705_);
                    v___y_3628_ = v___x_3706_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v___x_3613_, 15);
                crate::leanh::lean_inc_ref_n(v___x_3626_, 2);
                crate::leanh::lean_inc_n(v___x_3607_, 31);
                v___x_3629_ = l_Lean_Syntax_node3(
                    v___x_3607_,
                    v___x_3624_,
                    v___x_3626_,
                    v___x_3613_,
                    v___y_3628_,
                );
                v___x_3630_ = l_Lean_Syntax_node3(
                    v___x_3607_,
                    v___x_3611_,
                    v___x_3613_,
                    v___x_3613_,
                    v___x_3629_,
                );
                v___x_3631_ =
                    l_Lean_Syntax_node2(v___x_3607_, v___x_3615_, v___x_3623_, v___x_3630_);
                v___x_3632_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23_once), _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__23);
                v___x_3633_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__24;
                crate::leanh::lean_inc_n(v_currMacroScope_3605_, 5);
                crate::leanh::lean_inc_n(v_quotContext_3604_, 5);
                v___x_3634_ =
                    l_Lean_addMacroScope(v_quotContext_3604_, v___x_3633_, v_currMacroScope_3605_);
                v___x_3635_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3635_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3635_, 1, v___x_3632_);
                crate::leanh::lean_ctor_set(v___x_3635_, 2, v___x_3634_);
                crate::leanh::lean_ctor_set(v___x_3635_, 3, v___x_3620_);
                crate::leanh::lean_inc_ref(v___x_3635_);
                v___x_3636_ =
                    l_Lean_Syntax_node2(v___x_3607_, v___x_3616_, v___x_3635_, v___x_3613_);
                v___x_3637_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__26;
                v___x_3638_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__28;
                v___x_3639_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__30;
                v___x_3640_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__31;
                v___x_3641_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3641_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3641_, 1, v___x_3640_);
                v___x_3642_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__33;
                v___x_3643_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35), core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35_once), _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__35);
                v___x_3644_ = crate::leanh::lean_box(0);
                v___x_3645_ =
                    l_Lean_addMacroScope(v_quotContext_3604_, v___x_3644_, v_currMacroScope_3605_);
                v___x_3646_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__46;
                v___x_3647_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3647_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3647_, 1, v___x_3643_);
                crate::leanh::lean_ctor_set(v___x_3647_, 2, v___x_3645_);
                crate::leanh::lean_ctor_set(v___x_3647_, 3, v___x_3646_);
                v___x_3648_ = l_Lean_Syntax_node1(v___x_3607_, v___x_3642_, v___x_3647_);
                v___x_3649_ =
                    l_Lean_Syntax_node2(v___x_3607_, v___x_3639_, v___x_3641_, v___x_3648_);
                v___x_3650_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48;
                v___x_3651_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50), core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once), _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
                v___x_3652_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53;
                v___x_3653_ =
                    l_Lean_addMacroScope(v_quotContext_3604_, v___x_3652_, v_currMacroScope_3605_);
                v___x_3654_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56;
                v___x_3655_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3655_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3655_, 1, v___x_3651_);
                crate::leanh::lean_ctor_set(v___x_3655_, 2, v___x_3653_);
                crate::leanh::lean_ctor_set(v___x_3655_, 3, v___x_3654_);
                v___x_3656_ = l_Lean_Syntax_node1(v___x_3607_, v___x_3611_, v_mod_3594_);
                v___x_3657_ =
                    l_Lean_Syntax_node2(v___x_3607_, v___x_3650_, v___x_3655_, v___x_3656_);
                v___x_3658_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__57;
                v___x_3659_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3659_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3659_, 1, v___x_3658_);
                v___x_3660_ = l_Lean_Syntax_node3(
                    v___x_3607_,
                    v___x_3638_,
                    v___x_3649_,
                    v___x_3657_,
                    v___x_3659_,
                );
                v___x_3661_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__58;
                v___x_3662_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3662_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3662_, 1, v___x_3661_);
                v___x_3663_ = l_Lean_Syntax_node3(
                    v___x_3607_,
                    v___x_3637_,
                    v___x_3660_,
                    v___x_3662_,
                    v___x_3635_,
                );
                v___x_3664_ = l_Lean_Syntax_node3(
                    v___x_3607_,
                    v___x_3624_,
                    v___x_3626_,
                    v___x_3613_,
                    v___x_3663_,
                );
                v___x_3665_ = l_Lean_Syntax_node3(
                    v___x_3607_,
                    v___x_3611_,
                    v___x_3613_,
                    v___x_3613_,
                    v___x_3664_,
                );
                v___x_3666_ =
                    l_Lean_Syntax_node2(v___x_3607_, v___x_3615_, v___x_3636_, v___x_3665_);
                v___x_3667_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60), core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60_once), _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__60);
                v___x_3668_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__61;
                v___x_3669_ =
                    l_Lean_addMacroScope(v_quotContext_3604_, v___x_3668_, v_currMacroScope_3605_);
                v___x_3670_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3670_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3670_, 1, v___x_3667_);
                crate::leanh::lean_ctor_set(v___x_3670_, 2, v___x_3669_);
                crate::leanh::lean_ctor_set(v___x_3670_, 3, v___x_3620_);
                v___x_3671_ =
                    l_Lean_Syntax_node2(v___x_3607_, v___x_3616_, v___x_3670_, v___x_3613_);
                v___x_3672_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63), core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63_once), _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__63);
                v___x_3673_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__67;
                v___x_3674_ =
                    l_Lean_addMacroScope(v_quotContext_3604_, v___x_3673_, v_currMacroScope_3605_);
                v___x_3675_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__70;
                v___x_3676_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3676_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3676_, 1, v___x_3672_);
                crate::leanh::lean_ctor_set(v___x_3676_, 2, v___x_3674_);
                crate::leanh::lean_ctor_set(v___x_3676_, 3, v___x_3675_);
                v___x_3677_ = l_Lean_Syntax_node1(v___x_3607_, v___x_3611_, v_props_3595_);
                v___x_3678_ =
                    l_Lean_Syntax_node2(v___x_3607_, v___x_3650_, v___x_3676_, v___x_3677_);
                v___x_3679_ = l_Lean_Syntax_node3(
                    v___x_3607_,
                    v___x_3624_,
                    v___x_3626_,
                    v___x_3613_,
                    v___x_3678_,
                );
                v___x_3680_ = l_Lean_Syntax_node3(
                    v___x_3607_,
                    v___x_3611_,
                    v___x_3613_,
                    v___x_3613_,
                    v___x_3679_,
                );
                v___x_3681_ =
                    l_Lean_Syntax_node2(v___x_3607_, v___x_3615_, v___x_3671_, v___x_3680_);
                v___x_3682_ = l_Lean_Syntax_node5(
                    v___x_3607_,
                    v___x_3611_,
                    v___x_3631_,
                    v___x_3613_,
                    v___x_3666_,
                    v___x_3613_,
                    v___x_3681_,
                );
                v___x_3683_ = l_Lean_Syntax_node1(v___x_3607_, v___x_3614_, v___x_3682_);
                v___x_3684_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__72;
                v___x_3685_ = l_Lean_Syntax_node1(v___x_3607_, v___x_3684_, v___x_3613_);
                v___x_3686_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__73;
                v___x_3687_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3687_, 0, v___x_3607_);
                crate::leanh::lean_ctor_set(v___x_3687_, 1, v___x_3686_);
                v___x_3688_ = l_Lean_Syntax_node6(
                    v___x_3607_,
                    v___x_3608_,
                    v___x_3610_,
                    v___x_3613_,
                    v___x_3683_,
                    v___x_3685_,
                    v___x_3613_,
                    v___x_3687_,
                );
                v___x_3689_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77), core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77_once), _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__77);
                v___x_3690_ = 1;
                v___x_3691_ = l_Lean_Elab_Term_elabTerm(
                    v___x_3688_,
                    v___x_3689_,
                    v___x_3690_,
                    v___x_3690_,
                    v_a_3596_,
                    v_a_3597_,
                    v_a_3598_,
                    v_a_3599_,
                    v_a_3600_,
                    v_a_3601_,
                );
                return v___x_3691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___boxed(
    mut v_mod_3707_: *mut crate::leanh::LeanObject,
    mut v_props_3708_: *mut crate::leanh::LeanObject,
    mut v_a_3709_: *mut crate::leanh::LeanObject,
    mut v_a_3710_: *mut crate::leanh::LeanObject,
    mut v_a_3711_: *mut crate::leanh::LeanObject,
    mut v_a_3712_: *mut crate::leanh::LeanObject,
    mut v_a_3713_: *mut crate::leanh::LeanObject,
    mut v_a_3714_: *mut crate::leanh::LeanObject,
    mut v_a_3715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3716_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(
        v_mod_3707_,
        v_props_3708_,
        v_a_3709_,
        v_a_3710_,
        v_a_3711_,
        v_a_3712_,
        v_a_3713_,
        v_a_3714_,
    );
    crate::leanh::lean_dec(v_a_3714_);
    crate::leanh::lean_dec_ref(v_a_3713_);
    crate::leanh::lean_dec(v_a_3712_);
    crate::leanh::lean_dec_ref(v_a_3711_);
    crate::leanh::lean_dec(v_a_3710_);
    crate::leanh::lean_dec_ref(v_a_3709_);
    return v_res_3716_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3717_ = crate::leanh::lean_box(0);
    v___x_3718_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3719_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3719_, 0, v___x_3718_);
    crate::leanh::lean_ctor_set(v___x_3719_, 1, v___x_3717_);
    return v___x_3719_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3721_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0);
    v___x_3722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3722_, 0, v___x_3721_);
    return v___x_3722_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___boxed(
    mut v___y_3723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3724_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
    return v_res_3724_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(
    mut v_00_u03b1_3725_: *mut crate::leanh::LeanObject,
    mut v___y_3726_: *mut crate::leanh::LeanObject,
    mut v___y_3727_: *mut crate::leanh::LeanObject,
    mut v___y_3728_: *mut crate::leanh::LeanObject,
    mut v___y_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3733_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
    return v___x_3733_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___boxed(
    mut v_00_u03b1_3734_: *mut crate::leanh::LeanObject,
    mut v___y_3735_: *mut crate::leanh::LeanObject,
    mut v___y_3736_: *mut crate::leanh::LeanObject,
    mut v___y_3737_: *mut crate::leanh::LeanObject,
    mut v___y_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
    mut v___y_3741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3742_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0(
            v_00_u03b1_3734_,
            v___y_3735_,
            v___y_3736_,
            v___y_3737_,
            v___y_3738_,
            v___y_3739_,
            v___y_3740_,
        );
    crate::leanh::lean_dec(v___y_3740_);
    crate::leanh::lean_dec_ref(v___y_3739_);
    crate::leanh::lean_dec(v___y_3738_);
    crate::leanh::lean_dec_ref(v___y_3737_);
    crate::leanh::lean_dec(v___y_3736_);
    crate::leanh::lean_dec_ref(v___y_3735_);
    return v_res_3742_;
}
pub unsafe fn _init_l_Lean_Widget_elabWidgetInstanceSpec___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3744_ = l_Lean_Widget_elabWidgetInstanceSpec___closed__0;
    v___x_3745_ = l_String_toRawSubstring_x27(v___x_3744_);
    return v___x_3745_;
}
pub unsafe fn l_Lean_Widget_elabWidgetInstanceSpec(
    mut v_x_3766_: *mut crate::leanh::LeanObject,
    mut v_a_3767_: *mut crate::leanh::LeanObject,
    mut v_a_3768_: *mut crate::leanh::LeanObject,
    mut v_a_3769_: *mut crate::leanh::LeanObject,
    mut v_a_3770_: *mut crate::leanh::LeanObject,
    mut v_a_3771_: *mut crate::leanh::LeanObject,
    mut v_a_3772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: u8 = 0;
    v___x_3774_ = l_Lean_Widget_widgetInstanceSpec___closed__3;
    crate::leanh::lean_inc(v_x_3766_);
    v___x_3775_ = l_Lean_Syntax_isOfKind(v_x_3766_, v___x_3774_);
    if v___x_3775_ == 0 {
        let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3766_);
        v___x_3776_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
        return v___x_3776_;
    } else {
        let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_mod_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3780_: u8 = 0;
        v___x_3777_ = crate::leanh::lean_unsigned_to_nat(0);
        v_mod_3778_ = l_Lean_Syntax_getArg(v_x_3766_, v___x_3777_);
        v___x_3779_ = l_Lean_Widget_widgetInstanceSpec___closed__7;
        crate::leanh::lean_inc(v_mod_3778_);
        v___x_3780_ = l_Lean_Syntax_isOfKind(v_mod_3778_, v___x_3779_);
        if v___x_3780_ == 0 {
            let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_mod_3778_);
            crate::leanh::lean_dec(v_x_3766_);
            v___x_3781_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
            return v___x_3781_;
        } else {
            let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3784_: u8 = 0;
            v___x_3782_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_3783_ = l_Lean_Syntax_getArg(v_x_3766_, v___x_3782_);
            crate::leanh::lean_dec(v_x_3766_);
            crate::leanh::lean_inc(v___x_3783_);
            v___x_3784_ = l_Lean_Syntax_matchesNull(v___x_3783_, v___x_3777_);
            if v___x_3784_ == 0 {
                let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3786_: u8 = 0;
                v___x_3785_ = crate::leanh::lean_unsigned_to_nat(2);
                crate::leanh::lean_inc(v___x_3783_);
                v___x_3786_ = l_Lean_Syntax_matchesNull(v___x_3783_, v___x_3785_);
                if v___x_3786_ == 0 {
                    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_3783_);
                    crate::leanh::lean_dec(v_mod_3778_);
                    v___x_3787_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
                    return v___x_3787_;
                } else {
                    let mut v_props_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_props_3788_ = l_Lean_Syntax_getArg(v___x_3783_, v___x_3782_);
                    crate::leanh::lean_dec(v___x_3783_);
                    v___x_3789_ =
                        l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(
                            v_mod_3778_,
                            v_props_3788_,
                            v_a_3767_,
                            v_a_3768_,
                            v_a_3769_,
                            v_a_3770_,
                            v_a_3771_,
                            v_a_3772_,
                        );
                    return v___x_3789_;
                }
            } else {
                let mut v_ref_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_quotContext_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_currMacroScope_3792_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v___x_3793_: u8 = 0;
                let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_3783_);
                v_ref_3790_ = crate::leanh::lean_ctor_get(v_a_3771_, 5);
                v_quotContext_3791_ = crate::leanh::lean_ctor_get(v_a_3771_, 10);
                v_currMacroScope_3792_ = crate::leanh::lean_ctor_get(v_a_3771_, 11);
                v___x_3793_ = 0;
                v___x_3794_ = l_Lean_SourceInfo_fromRef(v_ref_3790_, v___x_3793_);
                v___x_3795_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48;
                v___x_3796_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Widget_elabWidgetInstanceSpec___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Widget_elabWidgetInstanceSpec___closed__1_once),
                    _init_l_Lean_Widget_elabWidgetInstanceSpec___closed__1,
                );
                v___x_3797_ = l_Lean_Widget_elabWidgetInstanceSpec___closed__4;
                crate::leanh::lean_inc(v_currMacroScope_3792_);
                crate::leanh::lean_inc(v_quotContext_3791_);
                v___x_3798_ =
                    l_Lean_addMacroScope(v_quotContext_3791_, v___x_3797_, v_currMacroScope_3792_);
                v___x_3799_ = l_Lean_Widget_elabWidgetInstanceSpec___closed__7;
                crate::leanh::lean_inc_n(v___x_3794_, 6);
                v___x_3800_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3800_, 0, v___x_3794_);
                crate::leanh::lean_ctor_set(v___x_3800_, 1, v___x_3796_);
                crate::leanh::lean_ctor_set(v___x_3800_, 2, v___x_3798_);
                crate::leanh::lean_ctor_set(v___x_3800_, 3, v___x_3799_);
                v___x_3801_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6;
                v___x_3802_ = l_Lean_Widget_elabWidgetInstanceSpec___closed__9;
                v___x_3803_ = l_Lean_Widget_elabWidgetInstanceSpec___closed__10;
                v___x_3804_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3804_, 0, v___x_3794_);
                crate::leanh::lean_ctor_set(v___x_3804_, 1, v___x_3803_);
                v___x_3805_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7_once), _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__7);
                v___x_3806_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3806_, 0, v___x_3794_);
                crate::leanh::lean_ctor_set(v___x_3806_, 1, v___x_3801_);
                crate::leanh::lean_ctor_set(v___x_3806_, 2, v___x_3805_);
                v___x_3807_ = l_Lean_Widget_elabWidgetInstanceSpec___closed__11;
                v___x_3808_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3808_, 0, v___x_3794_);
                crate::leanh::lean_ctor_set(v___x_3808_, 1, v___x_3807_);
                v___x_3809_ = l_Lean_Syntax_node3(
                    v___x_3794_,
                    v___x_3802_,
                    v___x_3804_,
                    v___x_3806_,
                    v___x_3808_,
                );
                v___x_3810_ = l_Lean_Syntax_node1(v___x_3794_, v___x_3801_, v___x_3809_);
                v___x_3811_ =
                    l_Lean_Syntax_node2(v___x_3794_, v___x_3795_, v___x_3800_, v___x_3810_);
                v___x_3812_ =
                    l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux(
                        v_mod_3778_,
                        v___x_3811_,
                        v_a_3767_,
                        v_a_3768_,
                        v_a_3769_,
                        v_a_3770_,
                        v_a_3771_,
                        v_a_3772_,
                    );
                return v___x_3812_;
            }
        }
    }
}
pub unsafe fn l_Lean_Widget_elabWidgetInstanceSpec___boxed(
    mut v_x_3813_: *mut crate::leanh::LeanObject,
    mut v_a_3814_: *mut crate::leanh::LeanObject,
    mut v_a_3815_: *mut crate::leanh::LeanObject,
    mut v_a_3816_: *mut crate::leanh::LeanObject,
    mut v_a_3817_: *mut crate::leanh::LeanObject,
    mut v_a_3818_: *mut crate::leanh::LeanObject,
    mut v_a_3819_: *mut crate::leanh::LeanObject,
    mut v_a_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3821_ = l_Lean_Widget_elabWidgetInstanceSpec(
        v_x_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_,
    );
    crate::leanh::lean_dec(v_a_3819_);
    crate::leanh::lean_dec_ref(v_a_3818_);
    crate::leanh::lean_dec(v_a_3817_);
    crate::leanh::lean_dec_ref(v_a_3816_);
    crate::leanh::lean_dec(v_a_3815_);
    crate::leanh::lean_dec_ref(v_a_3814_);
    return v_res_3821_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3916_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg___closed__0);
    v___x_3917_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3917_, 0, v___x_3916_);
    return v___x_3917_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg___boxed(
    mut v___y_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
    return v_res_3919_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(
    mut v_00_u03b1_3920_: *mut crate::leanh::LeanObject,
    mut v___y_3921_: *mut crate::leanh::LeanObject,
    mut v___y_3922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3924_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
    return v___x_3924_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___boxed(
    mut v_00_u03b1_3925_: *mut crate::leanh::LeanObject,
    mut v___y_3926_: *mut crate::leanh::LeanObject,
    mut v___y_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3929_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0(
            v_00_u03b1_3925_,
            v___y_3926_,
            v___y_3927_,
        );
    crate::leanh::lean_dec(v___y_3927_);
    crate::leanh::lean_dec_ref(v___y_3926_);
    return v_res_3929_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(
    mut v_e_3930_: *mut crate::leanh::LeanObject,
    mut v___y_3931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3947_: u8 = 0;
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3953_: u8 = 0;
    let mut v_unused_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3933_ = l_Lean_Expr_hasMVar(v_e_3930_);
                if v___x_3933_ == 0 {
                    v___x_3934_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3934_, 0, v_e_3930_);
                    return v___x_3934_;
                } else {
                    v___x_3935_ = lean_st_ref_get(v___y_3931_);
                    v_mctx_3936_ = crate::leanh::lean_ctor_get(v___x_3935_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_3936_);
                    crate::leanh::lean_dec(v___x_3935_);
                    v___x_3937_ = l_Lean_instantiateMVarsCore(v_mctx_3936_, v_e_3930_);
                    v_fst_3938_ = crate::leanh::lean_ctor_get(v___x_3937_, 0);
                    crate::leanh::lean_inc(v_fst_3938_);
                    v_snd_3939_ = crate::leanh::lean_ctor_get(v___x_3937_, 1);
                    crate::leanh::lean_inc(v_snd_3939_);
                    crate::leanh::lean_dec_ref(v___x_3937_);
                    v___x_3940_ = lean_st_ref_take(v___y_3931_);
                    v_cache_3941_ = crate::leanh::lean_ctor_get(v___x_3940_, 1);
                    v_zetaDeltaFVarIds_3942_ = crate::leanh::lean_ctor_get(v___x_3940_, 2);
                    v_postponed_3943_ = crate::leanh::lean_ctor_get(v___x_3940_, 3);
                    v_diag_3944_ = crate::leanh::lean_ctor_get(v___x_3940_, 4);
                    v_isSharedCheck_3953_ = (!crate::leanh::lean_is_exclusive(v___x_3940_)) as u8;
                    if v_isSharedCheck_3953_ == 0 {
                        v_unused_3954_ = crate::leanh::lean_ctor_get(v___x_3940_, 0);
                        crate::leanh::lean_dec(v_unused_3954_);
                        v___x_3946_ = v___x_3940_;
                        v_isShared_3947_ = v_isSharedCheck_3953_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_3944_);
                        crate::leanh::lean_inc(v_postponed_3943_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_3942_);
                        crate::leanh::lean_inc(v_cache_3941_);
                        crate::leanh::lean_dec(v___x_3940_);
                        v___x_3946_ = crate::leanh::lean_box(0);
                        v_isShared_3947_ = v_isSharedCheck_3953_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3947_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3946_, 0, v_snd_3939_);
                    v___x_3949_ = v___x_3946_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3952_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_snd_3939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3952_, 1, v_cache_3941_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3952_,
                        2,
                        v_zetaDeltaFVarIds_3942_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3952_, 3, v_postponed_3943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3952_, 4, v_diag_3944_);
                    v___x_3949_ = v_reuseFailAlloc_3952_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3950_ = lean_st_ref_set(v___y_3931_, v___x_3949_);
                v___x_3951_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3951_, 0, v_fst_3938_);
                return v___x_3951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg___boxed(
    mut v_e_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
    mut v___y_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3958_ =
        l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(
            v_e_3955_,
            v___y_3956_,
        );
    crate::leanh::lean_dec(v___y_3956_);
    return v_res_3958_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(
    mut v_e_3959_: *mut crate::leanh::LeanObject,
    mut v___y_3960_: *mut crate::leanh::LeanObject,
    mut v___y_3961_: *mut crate::leanh::LeanObject,
    mut v___y_3962_: *mut crate::leanh::LeanObject,
    mut v___y_3963_: *mut crate::leanh::LeanObject,
    mut v___y_3964_: *mut crate::leanh::LeanObject,
    mut v___y_3965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3967_ =
        l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(
            v_e_3959_,
            v___y_3963_,
        );
    return v___x_3967_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___boxed(
    mut v_e_3968_: *mut crate::leanh::LeanObject,
    mut v___y_3969_: *mut crate::leanh::LeanObject,
    mut v___y_3970_: *mut crate::leanh::LeanObject,
    mut v___y_3971_: *mut crate::leanh::LeanObject,
    mut v___y_3972_: *mut crate::leanh::LeanObject,
    mut v___y_3973_: *mut crate::leanh::LeanObject,
    mut v___y_3974_: *mut crate::leanh::LeanObject,
    mut v___y_3975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3976_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3(
        v_e_3968_,
        v___y_3969_,
        v___y_3970_,
        v___y_3971_,
        v___y_3972_,
        v___y_3973_,
        v___y_3974_,
    );
    crate::leanh::lean_dec(v___y_3974_);
    crate::leanh::lean_dec_ref(v___y_3973_);
    crate::leanh::lean_dec(v___y_3972_);
    crate::leanh::lean_dec_ref(v___y_3971_);
    crate::leanh::lean_dec(v___y_3970_);
    crate::leanh::lean_dec_ref(v___y_3969_);
    return v_res_3976_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(
    mut v_k_3977_: u64,
    mut v_t_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3985_: u8 = 0;
    let mut v___x_3986_: u64 = 0;
    let mut v___x_3987_: u8 = 0;
    let mut v___x_3988_: u64 = 0;
    let mut v___x_3989_: u8 = 0;
    let mut v_impl_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: u8 = 0;
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4008_: u8 = 0;
    let mut v_size_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4020_: u8 = 0;
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4046_: u8 = 0;
    let mut v_unused_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4064_: u8 = 0;
    let mut v_unused_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4071_: u8 = 0;
    let mut v_unused_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4089_: u8 = 0;
    let mut v_size_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4099_: u8 = 0;
    let mut v_unused_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4106_: u8 = 0;
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut v_unused_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4123_: u8 = 0;
    let mut v_k_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4128_: u8 = 0;
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4139_: u8 = 0;
    let mut v_unused_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4143_: u8 = 0;
    let mut v_unused_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: u8 = 0;
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4168_: u8 = 0;
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: u8 = 0;
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4184_: u8 = 0;
    let mut v_size_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: u8 = 0;
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4196_: u8 = 0;
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v_unused_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4236_: u8 = 0;
    let mut v_unused_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4244_: u8 = 0;
    let mut v_k_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4262_: u8 = 0;
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4273_: u8 = 0;
    let mut v_unused_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4295_: u8 = 0;
    let mut v_unused_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v_unused_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4309_: u8 = 0;
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: u8 = 0;
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v_size_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: u8 = 0;
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4337_: u8 = 0;
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4349_: u8 = 0;
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4353_: u8 = 0;
    let mut v_unused_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4372_: u8 = 0;
    let mut v_unused_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4388_: u8 = 0;
    let mut v_unused_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4396_: u8 = 0;
    let mut v_k_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4417_: u8 = 0;
    let mut v_unused_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4425_: u8 = 0;
    let mut v_k_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4443_: u8 = 0;
    let mut v_unused_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4447_: u8 = 0;
    let mut v_unused_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4459_: u8 = 0;
    let mut v_unused_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4483_: u8 = 0;
    let mut v_size_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: u8 = 0;
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4495_: u8 = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4520_: u8 = 0;
    let mut v_unused_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4533_: u8 = 0;
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4537_: u8 = 0;
    let mut v_unused_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4544_: u8 = 0;
    let mut v_unused_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v_size_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4572_: u8 = 0;
    let mut v_unused_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4579_: u8 = 0;
    let mut v_k_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4584_: u8 = 0;
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4595_: u8 = 0;
    let mut v_unused_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4599_: u8 = 0;
    let mut v_unused_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4608_: u8 = 0;
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4616_: u8 = 0;
    let mut v_unused_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4625_: u8 = 0;
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4633_: u8 = 0;
    let mut v_unused_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4639_: u8 = 0;
    let mut v_unused_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3978_) == 0 {
                    v_k_3979_ = crate::leanh::lean_ctor_get(v_t_3978_, 1);
                    v_v_3980_ = crate::leanh::lean_ctor_get(v_t_3978_, 2);
                    v_l_3981_ = crate::leanh::lean_ctor_get(v_t_3978_, 3);
                    v_r_3982_ = crate::leanh::lean_ctor_get(v_t_3978_, 4);
                    v_isSharedCheck_4639_ = (!crate::leanh::lean_is_exclusive(v_t_3978_)) as u8;
                    if v_isSharedCheck_4639_ == 0 {
                        v_unused_4640_ = crate::leanh::lean_ctor_get(v_t_3978_, 0);
                        crate::leanh::lean_dec(v_unused_4640_);
                        v___x_3984_ = v_t_3978_;
                        v_isShared_3985_ = v_isSharedCheck_4639_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_3982_);
                        crate::leanh::lean_inc(v_l_3981_);
                        crate::leanh::lean_inc(v_v_3980_);
                        crate::leanh::lean_inc(v_k_3979_);
                        crate::leanh::lean_dec(v_t_3978_);
                        v___x_3984_ = crate::leanh::lean_box(0);
                        v_isShared_3985_ = v_isSharedCheck_4639_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_3978_;
                }
            }
            1 => {
                v___x_3986_ = crate::leanh::lean_unbox_uint64(v_k_3979_);
                v___x_3987_ = lean_uint64_dec_lt(v_k_3977_, v___x_3986_);
                if v___x_3987_ == 0 {
                    v___x_3988_ = crate::leanh::lean_unbox_uint64(v_k_3979_);
                    v___x_3989_ = lean_uint64_dec_eq(v_k_3977_, v___x_3988_);
                    if v___x_3989_ == 0 {
                        v_impl_3990_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_3977_, v_r_3982_);
                        v___x_3991_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_3990_) == 0 {
                            if crate::leanh::lean_obj_tag(v_l_3981_) == 0 {
                                v_size_3992_ = crate::leanh::lean_ctor_get(v_impl_3990_, 0);
                                crate::leanh::lean_inc(v_size_3992_);
                                v_size_3993_ = crate::leanh::lean_ctor_get(v_l_3981_, 0);
                                v_k_3994_ = crate::leanh::lean_ctor_get(v_l_3981_, 1);
                                v_v_3995_ = crate::leanh::lean_ctor_get(v_l_3981_, 2);
                                v_l_3996_ = crate::leanh::lean_ctor_get(v_l_3981_, 3);
                                v_r_3997_ = crate::leanh::lean_ctor_get(v_l_3981_, 4);
                                crate::leanh::lean_inc(v_r_3997_);
                                v___x_3998_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_3999_ = lean_nat_mul(v___x_3998_, v_size_3992_);
                                v___x_4000_ = lean_nat_dec_lt(v___x_3999_, v_size_3993_);
                                crate::leanh::lean_dec(v___x_3999_);
                                if v___x_4000_ == 0 {
                                    crate::leanh::lean_dec(v_r_3997_);
                                    v___x_4001_ = lean_nat_add(v___x_3991_, v_size_3993_);
                                    v___x_4002_ = lean_nat_add(v___x_4001_, v_size_3992_);
                                    crate::leanh::lean_dec(v_size_3992_);
                                    crate::leanh::lean_dec(v___x_4001_);
                                    if v_isShared_3985_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3984_, 4, v_impl_3990_);
                                        crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4002_);
                                        v___x_4004_ = v___x_3984_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4005_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4005_,
                                            0,
                                            v___x_4002_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4005_,
                                            1,
                                            v_k_3979_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4005_,
                                            2,
                                            v_v_3980_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4005_,
                                            3,
                                            v_l_3981_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4005_,
                                            4,
                                            v_impl_3990_,
                                        );
                                        v___x_4004_ = v_reuseFailAlloc_4005_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_l_3996_);
                                    crate::leanh::lean_inc(v_v_3995_);
                                    crate::leanh::lean_inc(v_k_3994_);
                                    crate::leanh::lean_inc(v_size_3993_);
                                    v_isSharedCheck_4071_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_3981_)) as u8;
                                    if v_isSharedCheck_4071_ == 0 {
                                        v_unused_4072_ = crate::leanh::lean_ctor_get(v_l_3981_, 4);
                                        crate::leanh::lean_dec(v_unused_4072_);
                                        v_unused_4073_ = crate::leanh::lean_ctor_get(v_l_3981_, 3);
                                        crate::leanh::lean_dec(v_unused_4073_);
                                        v_unused_4074_ = crate::leanh::lean_ctor_get(v_l_3981_, 2);
                                        crate::leanh::lean_dec(v_unused_4074_);
                                        v_unused_4075_ = crate::leanh::lean_ctor_get(v_l_3981_, 1);
                                        crate::leanh::lean_dec(v_unused_4075_);
                                        v_unused_4076_ = crate::leanh::lean_ctor_get(v_l_3981_, 0);
                                        crate::leanh::lean_dec(v_unused_4076_);
                                        v___x_4007_ = v_l_3981_;
                                        v_isShared_4008_ = v_isSharedCheck_4071_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_3981_);
                                        v___x_4007_ = crate::leanh::lean_box(0);
                                        v_isShared_4008_ = v_isSharedCheck_4071_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_4077_ = crate::leanh::lean_ctor_get(v_impl_3990_, 0);
                                crate::leanh::lean_inc(v_size_4077_);
                                v___x_4078_ = lean_nat_add(v___x_3991_, v_size_4077_);
                                crate::leanh::lean_dec(v_size_4077_);
                                if v_isShared_3985_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3984_, 4, v_impl_3990_);
                                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4078_);
                                    v___x_4080_ = v___x_3984_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4081_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4081_,
                                        0,
                                        v___x_4078_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4081_,
                                        1,
                                        v_k_3979_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4081_,
                                        2,
                                        v_v_3980_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4081_,
                                        3,
                                        v_l_3981_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4081_,
                                        4,
                                        v_impl_3990_,
                                    );
                                    v___x_4080_ = v_reuseFailAlloc_4081_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_l_3981_) == 0 {
                                v_l_4082_ = crate::leanh::lean_ctor_get(v_l_3981_, 3);
                                if crate::leanh::lean_obj_tag(v_l_4082_) == 0 {
                                    crate::leanh::lean_inc_ref(v_l_4082_);
                                    v_r_4083_ = crate::leanh::lean_ctor_get(v_l_3981_, 4);
                                    crate::leanh::lean_inc(v_r_4083_);
                                    if crate::leanh::lean_obj_tag(v_r_4083_) == 0 {
                                        v_size_4084_ = crate::leanh::lean_ctor_get(v_l_3981_, 0);
                                        v_k_4085_ = crate::leanh::lean_ctor_get(v_l_3981_, 1);
                                        v_v_4086_ = crate::leanh::lean_ctor_get(v_l_3981_, 2);
                                        v_isSharedCheck_4099_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_3981_)) as u8;
                                        if v_isSharedCheck_4099_ == 0 {
                                            v_unused_4100_ =
                                                crate::leanh::lean_ctor_get(v_l_3981_, 4);
                                            crate::leanh::lean_dec(v_unused_4100_);
                                            v_unused_4101_ =
                                                crate::leanh::lean_ctor_get(v_l_3981_, 3);
                                            crate::leanh::lean_dec(v_unused_4101_);
                                            v___x_4088_ = v_l_3981_;
                                            v_isShared_4089_ = v_isSharedCheck_4099_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_4086_);
                                            crate::leanh::lean_inc(v_k_4085_);
                                            crate::leanh::lean_inc(v_size_4084_);
                                            crate::leanh::lean_dec(v_l_3981_);
                                            v___x_4088_ = crate::leanh::lean_box(0);
                                            v_isShared_4089_ = v_isSharedCheck_4099_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_4102_ = crate::leanh::lean_ctor_get(v_l_3981_, 1);
                                        v_v_4103_ = crate::leanh::lean_ctor_get(v_l_3981_, 2);
                                        v_isSharedCheck_4114_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_3981_)) as u8;
                                        if v_isSharedCheck_4114_ == 0 {
                                            v_unused_4115_ =
                                                crate::leanh::lean_ctor_get(v_l_3981_, 4);
                                            crate::leanh::lean_dec(v_unused_4115_);
                                            v_unused_4116_ =
                                                crate::leanh::lean_ctor_get(v_l_3981_, 3);
                                            crate::leanh::lean_dec(v_unused_4116_);
                                            v_unused_4117_ =
                                                crate::leanh::lean_ctor_get(v_l_3981_, 0);
                                            crate::leanh::lean_dec(v_unused_4117_);
                                            v___x_4105_ = v_l_3981_;
                                            v_isShared_4106_ = v_isSharedCheck_4114_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_4103_);
                                            crate::leanh::lean_inc(v_k_4102_);
                                            crate::leanh::lean_dec(v_l_3981_);
                                            v___x_4105_ = crate::leanh::lean_box(0);
                                            v_isShared_4106_ = v_isSharedCheck_4114_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_4118_ = crate::leanh::lean_ctor_get(v_l_3981_, 4);
                                    crate::leanh::lean_inc(v_r_4118_);
                                    if crate::leanh::lean_obj_tag(v_r_4118_) == 0 {
                                        crate::leanh::lean_inc(v_l_4082_);
                                        v_k_4119_ = crate::leanh::lean_ctor_get(v_l_3981_, 1);
                                        v_v_4120_ = crate::leanh::lean_ctor_get(v_l_3981_, 2);
                                        v_isSharedCheck_4143_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_3981_)) as u8;
                                        if v_isSharedCheck_4143_ == 0 {
                                            v_unused_4144_ =
                                                crate::leanh::lean_ctor_get(v_l_3981_, 4);
                                            crate::leanh::lean_dec(v_unused_4144_);
                                            v_unused_4145_ =
                                                crate::leanh::lean_ctor_get(v_l_3981_, 3);
                                            crate::leanh::lean_dec(v_unused_4145_);
                                            v_unused_4146_ =
                                                crate::leanh::lean_ctor_get(v_l_3981_, 0);
                                            crate::leanh::lean_dec(v_unused_4146_);
                                            v___x_4122_ = v_l_3981_;
                                            v_isShared_4123_ = v_isSharedCheck_4143_;
                                            state = 20;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_4120_);
                                            crate::leanh::lean_inc(v_k_4119_);
                                            crate::leanh::lean_dec(v_l_3981_);
                                            v___x_4122_ = crate::leanh::lean_box(0);
                                            v_isShared_4123_ = v_isSharedCheck_4143_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_4147_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_3985_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_3984_, 4, v_r_4118_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3984_,
                                                0,
                                                v___x_4147_,
                                            );
                                            v___x_4149_ = v___x_3984_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_4150_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4150_,
                                                0,
                                                v___x_4147_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4150_,
                                                1,
                                                v_k_3979_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4150_,
                                                2,
                                                v_v_3980_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4150_,
                                                3,
                                                v_l_3981_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4150_,
                                                4,
                                                v_r_4118_,
                                            );
                                            v___x_4149_ = v_reuseFailAlloc_4150_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_3985_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3984_, 4, v_l_3981_);
                                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_3991_);
                                    v___x_4152_ = v___x_3984_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4153_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4153_,
                                        0,
                                        v___x_3991_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4153_,
                                        1,
                                        v_k_3979_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4153_,
                                        2,
                                        v_v_3980_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4153_,
                                        3,
                                        v_l_3981_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4153_,
                                        4,
                                        v_l_3981_,
                                    );
                                    v___x_4152_ = v_reuseFailAlloc_4153_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3984_);
                        crate::leanh::lean_dec(v_v_3980_);
                        crate::leanh::lean_dec(v_k_3979_);
                        if crate::leanh::lean_obj_tag(v_l_3981_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_3982_) == 0 {
                                v_size_4154_ = crate::leanh::lean_ctor_get(v_l_3981_, 0);
                                v_k_4155_ = crate::leanh::lean_ctor_get(v_l_3981_, 1);
                                v_v_4156_ = crate::leanh::lean_ctor_get(v_l_3981_, 2);
                                v_l_4157_ = crate::leanh::lean_ctor_get(v_l_3981_, 3);
                                v_r_4158_ = crate::leanh::lean_ctor_get(v_l_3981_, 4);
                                crate::leanh::lean_inc(v_r_4158_);
                                v_size_4159_ = crate::leanh::lean_ctor_get(v_r_3982_, 0);
                                v_k_4160_ = crate::leanh::lean_ctor_get(v_r_3982_, 1);
                                v_v_4161_ = crate::leanh::lean_ctor_get(v_r_3982_, 2);
                                v_l_4162_ = crate::leanh::lean_ctor_get(v_r_3982_, 3);
                                crate::leanh::lean_inc(v_l_4162_);
                                v_r_4163_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                                v___x_4164_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_4165_ = lean_nat_dec_lt(v_size_4154_, v_size_4159_);
                                if v___x_4165_ == 0 {
                                    crate::leanh::lean_inc(v_l_4157_);
                                    crate::leanh::lean_inc(v_v_4156_);
                                    crate::leanh::lean_inc(v_k_4155_);
                                    v_isSharedCheck_4301_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_3981_)) as u8;
                                    if v_isSharedCheck_4301_ == 0 {
                                        v_unused_4302_ = crate::leanh::lean_ctor_get(v_l_3981_, 4);
                                        crate::leanh::lean_dec(v_unused_4302_);
                                        v_unused_4303_ = crate::leanh::lean_ctor_get(v_l_3981_, 3);
                                        crate::leanh::lean_dec(v_unused_4303_);
                                        v_unused_4304_ = crate::leanh::lean_ctor_get(v_l_3981_, 2);
                                        crate::leanh::lean_dec(v_unused_4304_);
                                        v_unused_4305_ = crate::leanh::lean_ctor_get(v_l_3981_, 1);
                                        crate::leanh::lean_dec(v_unused_4305_);
                                        v_unused_4306_ = crate::leanh::lean_ctor_get(v_l_3981_, 0);
                                        crate::leanh::lean_dec(v_unused_4306_);
                                        v___x_4167_ = v_l_3981_;
                                        v_isShared_4168_ = v_isSharedCheck_4301_;
                                        state = 27;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_3981_);
                                        v___x_4167_ = crate::leanh::lean_box(0);
                                        v_isShared_4168_ = v_isSharedCheck_4301_;
                                        state = 27;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_4163_);
                                    crate::leanh::lean_inc(v_v_4161_);
                                    crate::leanh::lean_inc(v_k_4160_);
                                    v_isSharedCheck_4459_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_3982_)) as u8;
                                    if v_isSharedCheck_4459_ == 0 {
                                        v_unused_4460_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                                        crate::leanh::lean_dec(v_unused_4460_);
                                        v_unused_4461_ = crate::leanh::lean_ctor_get(v_r_3982_, 3);
                                        crate::leanh::lean_dec(v_unused_4461_);
                                        v_unused_4462_ = crate::leanh::lean_ctor_get(v_r_3982_, 2);
                                        crate::leanh::lean_dec(v_unused_4462_);
                                        v_unused_4463_ = crate::leanh::lean_ctor_get(v_r_3982_, 1);
                                        crate::leanh::lean_dec(v_unused_4463_);
                                        v_unused_4464_ = crate::leanh::lean_ctor_get(v_r_3982_, 0);
                                        crate::leanh::lean_dec(v_unused_4464_);
                                        v___x_4308_ = v_r_3982_;
                                        v_isShared_4309_ = v_isSharedCheck_4459_;
                                        state = 49;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_3982_);
                                        v___x_4308_ = crate::leanh::lean_box(0);
                                        v_isShared_4309_ = v_isSharedCheck_4459_;
                                        state = 49;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_3981_;
                            }
                        } else {
                            return v_r_3982_;
                        }
                    }
                } else {
                    v_impl_4465_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_3977_, v_l_3981_);
                    v___x_4466_ = crate::leanh::lean_unsigned_to_nat(1);
                    if crate::leanh::lean_obj_tag(v_impl_4465_) == 0 {
                        if crate::leanh::lean_obj_tag(v_r_3982_) == 0 {
                            v_size_4467_ = crate::leanh::lean_ctor_get(v_impl_4465_, 0);
                            crate::leanh::lean_inc(v_size_4467_);
                            v_size_4468_ = crate::leanh::lean_ctor_get(v_r_3982_, 0);
                            v_k_4469_ = crate::leanh::lean_ctor_get(v_r_3982_, 1);
                            v_v_4470_ = crate::leanh::lean_ctor_get(v_r_3982_, 2);
                            v_l_4471_ = crate::leanh::lean_ctor_get(v_r_3982_, 3);
                            crate::leanh::lean_inc(v_l_4471_);
                            v_r_4472_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                            v___x_4473_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_4474_ = lean_nat_mul(v___x_4473_, v_size_4467_);
                            v___x_4475_ = lean_nat_dec_lt(v___x_4474_, v_size_4468_);
                            crate::leanh::lean_dec(v___x_4474_);
                            if v___x_4475_ == 0 {
                                crate::leanh::lean_dec(v_l_4471_);
                                v___x_4476_ = lean_nat_add(v___x_4466_, v_size_4467_);
                                crate::leanh::lean_dec(v_size_4467_);
                                v___x_4477_ = lean_nat_add(v___x_4476_, v_size_4468_);
                                crate::leanh::lean_dec(v___x_4476_);
                                if v_isShared_3985_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3984_, 3, v_impl_4465_);
                                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4477_);
                                    v___x_4479_ = v___x_3984_;
                                    state = 72;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4480_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4480_,
                                        0,
                                        v___x_4477_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4480_,
                                        1,
                                        v_k_3979_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4480_,
                                        2,
                                        v_v_3980_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4480_,
                                        3,
                                        v_impl_4465_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4480_,
                                        4,
                                        v_r_3982_,
                                    );
                                    v___x_4479_ = v_reuseFailAlloc_4480_;
                                    state = 72;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_inc(v_r_4472_);
                                crate::leanh::lean_inc(v_v_4470_);
                                crate::leanh::lean_inc(v_k_4469_);
                                crate::leanh::lean_inc(v_size_4468_);
                                v_isSharedCheck_4544_ =
                                    (!crate::leanh::lean_is_exclusive(v_r_3982_)) as u8;
                                if v_isSharedCheck_4544_ == 0 {
                                    v_unused_4545_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                                    crate::leanh::lean_dec(v_unused_4545_);
                                    v_unused_4546_ = crate::leanh::lean_ctor_get(v_r_3982_, 3);
                                    crate::leanh::lean_dec(v_unused_4546_);
                                    v_unused_4547_ = crate::leanh::lean_ctor_get(v_r_3982_, 2);
                                    crate::leanh::lean_dec(v_unused_4547_);
                                    v_unused_4548_ = crate::leanh::lean_ctor_get(v_r_3982_, 1);
                                    crate::leanh::lean_dec(v_unused_4548_);
                                    v_unused_4549_ = crate::leanh::lean_ctor_get(v_r_3982_, 0);
                                    crate::leanh::lean_dec(v_unused_4549_);
                                    v___x_4482_ = v_r_3982_;
                                    v_isShared_4483_ = v_isSharedCheck_4544_;
                                    state = 73;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_r_3982_);
                                    v___x_4482_ = crate::leanh::lean_box(0);
                                    v_isShared_4483_ = v_isSharedCheck_4544_;
                                    state = 73;
                                    continue;
                                }
                            }
                        } else {
                            v_size_4550_ = crate::leanh::lean_ctor_get(v_impl_4465_, 0);
                            crate::leanh::lean_inc(v_size_4550_);
                            v___x_4551_ = lean_nat_add(v___x_4466_, v_size_4550_);
                            crate::leanh::lean_dec(v_size_4550_);
                            if v_isShared_3985_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3984_, 3, v_impl_4465_);
                                crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4551_);
                                v___x_4553_ = v___x_3984_;
                                state = 83;
                                continue;
                            } else {
                                v_reuseFailAlloc_4554_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4551_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4554_, 1, v_k_3979_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4554_, 2, v_v_3980_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4554_,
                                    3,
                                    v_impl_4465_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4554_, 4, v_r_3982_);
                                v___x_4553_ = v_reuseFailAlloc_4554_;
                                state = 83;
                                continue;
                            }
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_3982_) == 0 {
                            v_l_4555_ = crate::leanh::lean_ctor_get(v_r_3982_, 3);
                            crate::leanh::lean_inc(v_l_4555_);
                            if crate::leanh::lean_obj_tag(v_l_4555_) == 0 {
                                v_r_4556_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                                crate::leanh::lean_inc(v_r_4556_);
                                if crate::leanh::lean_obj_tag(v_r_4556_) == 0 {
                                    v_size_4557_ = crate::leanh::lean_ctor_get(v_r_3982_, 0);
                                    v_k_4558_ = crate::leanh::lean_ctor_get(v_r_3982_, 1);
                                    v_v_4559_ = crate::leanh::lean_ctor_get(v_r_3982_, 2);
                                    v_isSharedCheck_4572_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_3982_)) as u8;
                                    if v_isSharedCheck_4572_ == 0 {
                                        v_unused_4573_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                                        crate::leanh::lean_dec(v_unused_4573_);
                                        v_unused_4574_ = crate::leanh::lean_ctor_get(v_r_3982_, 3);
                                        crate::leanh::lean_dec(v_unused_4574_);
                                        v___x_4561_ = v_r_3982_;
                                        v_isShared_4562_ = v_isSharedCheck_4572_;
                                        state = 84;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_4559_);
                                        crate::leanh::lean_inc(v_k_4558_);
                                        crate::leanh::lean_inc(v_size_4557_);
                                        crate::leanh::lean_dec(v_r_3982_);
                                        v___x_4561_ = crate::leanh::lean_box(0);
                                        v_isShared_4562_ = v_isSharedCheck_4572_;
                                        state = 84;
                                        continue;
                                    }
                                } else {
                                    v_k_4575_ = crate::leanh::lean_ctor_get(v_r_3982_, 1);
                                    v_v_4576_ = crate::leanh::lean_ctor_get(v_r_3982_, 2);
                                    v_isSharedCheck_4599_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_3982_)) as u8;
                                    if v_isSharedCheck_4599_ == 0 {
                                        v_unused_4600_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                                        crate::leanh::lean_dec(v_unused_4600_);
                                        v_unused_4601_ = crate::leanh::lean_ctor_get(v_r_3982_, 3);
                                        crate::leanh::lean_dec(v_unused_4601_);
                                        v_unused_4602_ = crate::leanh::lean_ctor_get(v_r_3982_, 0);
                                        crate::leanh::lean_dec(v_unused_4602_);
                                        v___x_4578_ = v_r_3982_;
                                        v_isShared_4579_ = v_isSharedCheck_4599_;
                                        state = 87;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_4576_);
                                        crate::leanh::lean_inc(v_k_4575_);
                                        crate::leanh::lean_dec(v_r_3982_);
                                        v___x_4578_ = crate::leanh::lean_box(0);
                                        v_isShared_4579_ = v_isSharedCheck_4599_;
                                        state = 87;
                                        continue;
                                    }
                                }
                            } else {
                                v_r_4603_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                                crate::leanh::lean_inc(v_r_4603_);
                                if crate::leanh::lean_obj_tag(v_r_4603_) == 0 {
                                    v_k_4604_ = crate::leanh::lean_ctor_get(v_r_3982_, 1);
                                    v_v_4605_ = crate::leanh::lean_ctor_get(v_r_3982_, 2);
                                    v_isSharedCheck_4616_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_3982_)) as u8;
                                    if v_isSharedCheck_4616_ == 0 {
                                        v_unused_4617_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                                        crate::leanh::lean_dec(v_unused_4617_);
                                        v_unused_4618_ = crate::leanh::lean_ctor_get(v_r_3982_, 3);
                                        crate::leanh::lean_dec(v_unused_4618_);
                                        v_unused_4619_ = crate::leanh::lean_ctor_get(v_r_3982_, 0);
                                        crate::leanh::lean_dec(v_unused_4619_);
                                        v___x_4607_ = v_r_3982_;
                                        v_isShared_4608_ = v_isSharedCheck_4616_;
                                        state = 92;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_4605_);
                                        crate::leanh::lean_inc(v_k_4604_);
                                        crate::leanh::lean_dec(v_r_3982_);
                                        v___x_4607_ = crate::leanh::lean_box(0);
                                        v_isShared_4608_ = v_isSharedCheck_4616_;
                                        state = 92;
                                        continue;
                                    }
                                } else {
                                    v_size_4620_ = crate::leanh::lean_ctor_get(v_r_3982_, 0);
                                    v_k_4621_ = crate::leanh::lean_ctor_get(v_r_3982_, 1);
                                    v_v_4622_ = crate::leanh::lean_ctor_get(v_r_3982_, 2);
                                    v_isSharedCheck_4633_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_3982_)) as u8;
                                    if v_isSharedCheck_4633_ == 0 {
                                        v_unused_4634_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                                        crate::leanh::lean_dec(v_unused_4634_);
                                        v_unused_4635_ = crate::leanh::lean_ctor_get(v_r_3982_, 3);
                                        crate::leanh::lean_dec(v_unused_4635_);
                                        v___x_4624_ = v_r_3982_;
                                        v_isShared_4625_ = v_isSharedCheck_4633_;
                                        state = 95;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_4622_);
                                        crate::leanh::lean_inc(v_k_4621_);
                                        crate::leanh::lean_inc(v_size_4620_);
                                        crate::leanh::lean_dec(v_r_3982_);
                                        v___x_4624_ = crate::leanh::lean_box(0);
                                        v_isShared_4625_ = v_isSharedCheck_4633_;
                                        state = 95;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            if v_isShared_3985_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3984_, 3, v_r_3982_);
                                crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4466_);
                                v___x_4637_ = v___x_3984_;
                                state = 98;
                                continue;
                            } else {
                                v_reuseFailAlloc_4638_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4466_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4638_, 1, v_k_3979_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4638_, 2, v_v_3980_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4638_, 3, v_r_3982_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4638_, 4, v_r_3982_);
                                v___x_4637_ = v_reuseFailAlloc_4638_;
                                state = 98;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_4004_;
            }
            3 => {
                v_size_4009_ = crate::leanh::lean_ctor_get(v_l_3996_, 0);
                v_size_4010_ = crate::leanh::lean_ctor_get(v_r_3997_, 0);
                v_k_4011_ = crate::leanh::lean_ctor_get(v_r_3997_, 1);
                v_v_4012_ = crate::leanh::lean_ctor_get(v_r_3997_, 2);
                v_l_4013_ = crate::leanh::lean_ctor_get(v_r_3997_, 3);
                v_r_4014_ = crate::leanh::lean_ctor_get(v_r_3997_, 4);
                v___x_4015_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4016_ = lean_nat_mul(v___x_4015_, v_size_4009_);
                v___x_4017_ = lean_nat_dec_lt(v_size_4010_, v___x_4016_);
                crate::leanh::lean_dec(v___x_4016_);
                if v___x_4017_ == 0 {
                    crate::leanh::lean_inc(v_r_4014_);
                    crate::leanh::lean_inc(v_l_4013_);
                    crate::leanh::lean_inc(v_v_4012_);
                    crate::leanh::lean_inc(v_k_4011_);
                    v_isSharedCheck_4046_ = (!crate::leanh::lean_is_exclusive(v_r_3997_)) as u8;
                    if v_isSharedCheck_4046_ == 0 {
                        v_unused_4047_ = crate::leanh::lean_ctor_get(v_r_3997_, 4);
                        crate::leanh::lean_dec(v_unused_4047_);
                        v_unused_4048_ = crate::leanh::lean_ctor_get(v_r_3997_, 3);
                        crate::leanh::lean_dec(v_unused_4048_);
                        v_unused_4049_ = crate::leanh::lean_ctor_get(v_r_3997_, 2);
                        crate::leanh::lean_dec(v_unused_4049_);
                        v_unused_4050_ = crate::leanh::lean_ctor_get(v_r_3997_, 1);
                        crate::leanh::lean_dec(v_unused_4050_);
                        v_unused_4051_ = crate::leanh::lean_ctor_get(v_r_3997_, 0);
                        crate::leanh::lean_dec(v_unused_4051_);
                        v___x_4019_ = v_r_3997_;
                        v_isShared_4020_ = v_isSharedCheck_4046_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_3997_);
                        v___x_4019_ = crate::leanh::lean_box(0);
                        v_isShared_4020_ = v_isSharedCheck_4046_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3984_);
                    v___x_4052_ = lean_nat_add(v___x_3991_, v_size_3993_);
                    crate::leanh::lean_dec(v_size_3993_);
                    v___x_4053_ = lean_nat_add(v___x_4052_, v_size_3992_);
                    crate::leanh::lean_dec(v___x_4052_);
                    v___x_4054_ = lean_nat_add(v___x_3991_, v_size_3992_);
                    crate::leanh::lean_dec(v_size_3992_);
                    v___x_4055_ = lean_nat_add(v___x_4054_, v_size_4010_);
                    crate::leanh::lean_dec(v___x_4054_);
                    crate::leanh::lean_inc_ref(v_impl_3990_);
                    if v_isShared_4008_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4007_, 4, v_impl_3990_);
                        crate::leanh::lean_ctor_set(v___x_4007_, 3, v_r_3997_);
                        crate::leanh::lean_ctor_set(v___x_4007_, 2, v_v_3980_);
                        crate::leanh::lean_ctor_set(v___x_4007_, 1, v_k_3979_);
                        crate::leanh::lean_ctor_set(v___x_4007_, 0, v___x_4055_);
                        v___x_4057_ = v___x_4007_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4070_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4055_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_k_3979_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 2, v_v_3980_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 3, v_r_3997_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 4, v_impl_3990_);
                        v___x_4057_ = v_reuseFailAlloc_4070_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4021_ = lean_nat_add(v___x_3991_, v_size_3993_);
                crate::leanh::lean_dec(v_size_3993_);
                v___x_4022_ = lean_nat_add(v___x_4021_, v_size_3992_);
                crate::leanh::lean_dec(v___x_4021_);
                v___x_4034_ = lean_nat_add(v___x_3991_, v_size_4009_);
                if crate::leanh::lean_obj_tag(v_l_4013_) == 0 {
                    v_size_4044_ = crate::leanh::lean_ctor_get(v_l_4013_, 0);
                    crate::leanh::lean_inc(v_size_4044_);
                    v___y_4036_ = v_size_4044_;
                    state = 8;
                    continue;
                } else {
                    v___x_4045_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4036_ = v___x_4045_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_4027_ = lean_nat_add(v___y_4024_, v___y_4026_);
                crate::leanh::lean_dec(v___y_4026_);
                crate::leanh::lean_dec(v___y_4024_);
                if v_isShared_4020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4019_, 4, v_impl_3990_);
                    crate::leanh::lean_ctor_set(v___x_4019_, 3, v_r_4014_);
                    crate::leanh::lean_ctor_set(v___x_4019_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v___x_4019_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v___x_4019_, 0, v___x_4027_);
                    v___x_4029_ = v___x_4019_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4033_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4033_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4033_, 3, v_r_4014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4033_, 4, v_impl_3990_);
                    v___x_4029_ = v_reuseFailAlloc_4033_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4008_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4007_, 4, v___x_4029_);
                    crate::leanh::lean_ctor_set(v___x_4007_, 3, v___y_4025_);
                    crate::leanh::lean_ctor_set(v___x_4007_, 2, v_v_4012_);
                    crate::leanh::lean_ctor_set(v___x_4007_, 1, v_k_4011_);
                    crate::leanh::lean_ctor_set(v___x_4007_, 0, v___x_4022_);
                    v___x_4031_ = v___x_4007_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4032_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 1, v_k_4011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 2, v_v_4012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 3, v___y_4025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 4, v___x_4029_);
                    v___x_4031_ = v_reuseFailAlloc_4032_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4031_;
            }
            8 => {
                v___x_4037_ = lean_nat_add(v___x_4034_, v___y_4036_);
                crate::leanh::lean_dec(v___y_4036_);
                crate::leanh::lean_dec(v___x_4034_);
                if v_isShared_3985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3984_, 4, v_l_4013_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 3, v_l_3996_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 2, v_v_3995_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 1, v_k_3994_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4037_);
                    v___x_4039_ = v___x_3984_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4043_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_k_3994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 2, v_v_3995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 3, v_l_3996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 4, v_l_4013_);
                    v___x_4039_ = v_reuseFailAlloc_4043_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4040_ = lean_nat_add(v___x_3991_, v_size_3992_);
                crate::leanh::lean_dec(v_size_3992_);
                if crate::leanh::lean_obj_tag(v_r_4014_) == 0 {
                    v_size_4041_ = crate::leanh::lean_ctor_get(v_r_4014_, 0);
                    crate::leanh::lean_inc(v_size_4041_);
                    v___y_4024_ = v___x_4040_;
                    v___y_4025_ = v___x_4039_;
                    v___y_4026_ = v_size_4041_;
                    state = 5;
                    continue;
                } else {
                    v___x_4042_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4024_ = v___x_4040_;
                    v___y_4025_ = v___x_4039_;
                    v___y_4026_ = v___x_4042_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_4064_ = (!crate::leanh::lean_is_exclusive(v_impl_3990_)) as u8;
                if v_isSharedCheck_4064_ == 0 {
                    v_unused_4065_ = crate::leanh::lean_ctor_get(v_impl_3990_, 4);
                    crate::leanh::lean_dec(v_unused_4065_);
                    v_unused_4066_ = crate::leanh::lean_ctor_get(v_impl_3990_, 3);
                    crate::leanh::lean_dec(v_unused_4066_);
                    v_unused_4067_ = crate::leanh::lean_ctor_get(v_impl_3990_, 2);
                    crate::leanh::lean_dec(v_unused_4067_);
                    v_unused_4068_ = crate::leanh::lean_ctor_get(v_impl_3990_, 1);
                    crate::leanh::lean_dec(v_unused_4068_);
                    v_unused_4069_ = crate::leanh::lean_ctor_get(v_impl_3990_, 0);
                    crate::leanh::lean_dec(v_unused_4069_);
                    v___x_4059_ = v_impl_3990_;
                    v_isShared_4060_ = v_isSharedCheck_4064_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_3990_);
                    v___x_4059_ = crate::leanh::lean_box(0);
                    v_isShared_4060_ = v_isSharedCheck_4064_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4059_, 4, v___x_4057_);
                    crate::leanh::lean_ctor_set(v___x_4059_, 3, v_l_3996_);
                    crate::leanh::lean_ctor_set(v___x_4059_, 2, v_v_3995_);
                    crate::leanh::lean_ctor_set(v___x_4059_, 1, v_k_3994_);
                    crate::leanh::lean_ctor_set(v___x_4059_, 0, v___x_4053_);
                    v___x_4062_ = v___x_4059_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_k_3994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 2, v_v_3995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 3, v_l_3996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 4, v___x_4057_);
                    v___x_4062_ = v_reuseFailAlloc_4063_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4062_;
            }
            13 => {
                return v___x_4080_;
            }
            14 => {
                v_size_4090_ = crate::leanh::lean_ctor_get(v_r_4083_, 0);
                v___x_4091_ = lean_nat_add(v___x_3991_, v_size_4084_);
                crate::leanh::lean_dec(v_size_4084_);
                v___x_4092_ = lean_nat_add(v___x_3991_, v_size_4090_);
                if v_isShared_4089_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4088_, 4, v_impl_3990_);
                    crate::leanh::lean_ctor_set(v___x_4088_, 3, v_r_4083_);
                    crate::leanh::lean_ctor_set(v___x_4088_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v___x_4088_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v___x_4088_, 0, v___x_4092_);
                    v___x_4094_ = v___x_4088_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4098_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_4092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 3, v_r_4083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 4, v_impl_3990_);
                    v___x_4094_ = v_reuseFailAlloc_4098_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3984_, 4, v___x_4094_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 3, v_l_4082_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 2, v_v_4086_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 1, v_k_4085_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4091_);
                    v___x_4096_ = v___x_3984_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4097_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 1, v_k_4085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 2, v_v_4086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 3, v_l_4082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 4, v___x_4094_);
                    v___x_4096_ = v_reuseFailAlloc_4097_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4096_;
            }
            17 => {
                v___x_4107_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4106_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4105_, 3, v_r_4083_);
                    crate::leanh::lean_ctor_set(v___x_4105_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v___x_4105_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v___x_4105_, 0, v___x_3991_);
                    v___x_4109_ = v___x_4105_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_3991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 3, v_r_4083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 4, v_r_4083_);
                    v___x_4109_ = v_reuseFailAlloc_4113_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3984_, 4, v___x_4109_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 3, v_l_4082_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 2, v_v_4103_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 1, v_k_4102_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4107_);
                    v___x_4111_ = v___x_3984_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4112_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 1, v_k_4102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 2, v_v_4103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 3, v_l_4082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 4, v___x_4109_);
                    v___x_4111_ = v_reuseFailAlloc_4112_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4111_;
            }
            20 => {
                v_k_4124_ = crate::leanh::lean_ctor_get(v_r_4118_, 1);
                v_v_4125_ = crate::leanh::lean_ctor_get(v_r_4118_, 2);
                v_isSharedCheck_4139_ = (!crate::leanh::lean_is_exclusive(v_r_4118_)) as u8;
                if v_isSharedCheck_4139_ == 0 {
                    v_unused_4140_ = crate::leanh::lean_ctor_get(v_r_4118_, 4);
                    crate::leanh::lean_dec(v_unused_4140_);
                    v_unused_4141_ = crate::leanh::lean_ctor_get(v_r_4118_, 3);
                    crate::leanh::lean_dec(v_unused_4141_);
                    v_unused_4142_ = crate::leanh::lean_ctor_get(v_r_4118_, 0);
                    crate::leanh::lean_dec(v_unused_4142_);
                    v___x_4127_ = v_r_4118_;
                    v_isShared_4128_ = v_isSharedCheck_4139_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_4125_);
                    crate::leanh::lean_inc(v_k_4124_);
                    crate::leanh::lean_dec(v_r_4118_);
                    v___x_4127_ = crate::leanh::lean_box(0);
                    v_isShared_4128_ = v_isSharedCheck_4139_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_4129_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4128_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4127_, 4, v_l_4082_);
                    crate::leanh::lean_ctor_set(v___x_4127_, 3, v_l_4082_);
                    crate::leanh::lean_ctor_set(v___x_4127_, 2, v_v_4120_);
                    crate::leanh::lean_ctor_set(v___x_4127_, 1, v_k_4119_);
                    crate::leanh::lean_ctor_set(v___x_4127_, 0, v___x_3991_);
                    v___x_4131_ = v___x_4127_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4138_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_3991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 1, v_k_4119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 2, v_v_4120_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 3, v_l_4082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 4, v_l_4082_);
                    v___x_4131_ = v_reuseFailAlloc_4138_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_4123_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4122_, 4, v_l_4082_);
                    crate::leanh::lean_ctor_set(v___x_4122_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v___x_4122_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v___x_4122_, 0, v___x_3991_);
                    v___x_4133_ = v___x_4122_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4137_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_3991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4137_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4137_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4137_, 3, v_l_4082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4137_, 4, v_l_4082_);
                    v___x_4133_ = v_reuseFailAlloc_4137_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3984_, 4, v___x_4133_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 3, v___x_4131_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 2, v_v_4125_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 1, v_k_4124_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4129_);
                    v___x_4135_ = v___x_3984_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_k_4124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 2, v_v_4125_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 3, v___x_4131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 4, v___x_4133_);
                    v___x_4135_ = v_reuseFailAlloc_4136_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4135_;
            }
            25 => {
                return v___x_4149_;
            }
            26 => {
                return v___x_4152_;
            }
            27 => {
                v___x_4169_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_4155_, v_v_4156_, v_l_4157_, v_r_4158_,
                );
                v_tree_4170_ = crate::leanh::lean_ctor_get(v___x_4169_, 2);
                crate::leanh::lean_inc(v_tree_4170_);
                if crate::leanh::lean_obj_tag(v_tree_4170_) == 0 {
                    v_k_4171_ = crate::leanh::lean_ctor_get(v___x_4169_, 0);
                    crate::leanh::lean_inc(v_k_4171_);
                    v_v_4172_ = crate::leanh::lean_ctor_get(v___x_4169_, 1);
                    crate::leanh::lean_inc(v_v_4172_);
                    crate::leanh::lean_dec_ref(v___x_4169_);
                    v_size_4173_ = crate::leanh::lean_ctor_get(v_tree_4170_, 0);
                    v___x_4174_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4175_ = lean_nat_mul(v___x_4174_, v_size_4173_);
                    v___x_4176_ = lean_nat_dec_lt(v___x_4175_, v_size_4159_);
                    crate::leanh::lean_dec(v___x_4175_);
                    if v___x_4176_ == 0 {
                        crate::leanh::lean_dec(v_l_4162_);
                        v___x_4177_ = lean_nat_add(v___x_4164_, v_size_4173_);
                        v___x_4178_ = lean_nat_add(v___x_4177_, v_size_4159_);
                        crate::leanh::lean_dec(v___x_4177_);
                        if v_isShared_4168_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4167_, 4, v_r_3982_);
                            crate::leanh::lean_ctor_set(v___x_4167_, 3, v_tree_4170_);
                            crate::leanh::lean_ctor_set(v___x_4167_, 2, v_v_4172_);
                            crate::leanh::lean_ctor_set(v___x_4167_, 1, v_k_4171_);
                            crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4178_);
                            v___x_4180_ = v___x_4167_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_4181_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4178_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 1, v_k_4171_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 2, v_v_4172_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 3, v_tree_4170_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 4, v_r_3982_);
                            v___x_4180_ = v_reuseFailAlloc_4181_;
                            state = 28;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_r_4163_);
                        crate::leanh::lean_inc(v_v_4161_);
                        crate::leanh::lean_inc(v_k_4160_);
                        crate::leanh::lean_inc(v_size_4159_);
                        v_isSharedCheck_4236_ = (!crate::leanh::lean_is_exclusive(v_r_3982_)) as u8;
                        if v_isSharedCheck_4236_ == 0 {
                            v_unused_4237_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                            crate::leanh::lean_dec(v_unused_4237_);
                            v_unused_4238_ = crate::leanh::lean_ctor_get(v_r_3982_, 3);
                            crate::leanh::lean_dec(v_unused_4238_);
                            v_unused_4239_ = crate::leanh::lean_ctor_get(v_r_3982_, 2);
                            crate::leanh::lean_dec(v_unused_4239_);
                            v_unused_4240_ = crate::leanh::lean_ctor_get(v_r_3982_, 1);
                            crate::leanh::lean_dec(v_unused_4240_);
                            v_unused_4241_ = crate::leanh::lean_ctor_get(v_r_3982_, 0);
                            crate::leanh::lean_dec(v_unused_4241_);
                            v___x_4183_ = v_r_3982_;
                            v_isShared_4184_ = v_isSharedCheck_4236_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_r_3982_);
                            v___x_4183_ = crate::leanh::lean_box(0);
                            v_isShared_4184_ = v_isSharedCheck_4236_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_r_4163_);
                    crate::leanh::lean_inc(v_v_4161_);
                    crate::leanh::lean_inc(v_k_4160_);
                    crate::leanh::lean_inc(v_size_4159_);
                    v_isSharedCheck_4295_ = (!crate::leanh::lean_is_exclusive(v_r_3982_)) as u8;
                    if v_isSharedCheck_4295_ == 0 {
                        v_unused_4296_ = crate::leanh::lean_ctor_get(v_r_3982_, 4);
                        crate::leanh::lean_dec(v_unused_4296_);
                        v_unused_4297_ = crate::leanh::lean_ctor_get(v_r_3982_, 3);
                        crate::leanh::lean_dec(v_unused_4297_);
                        v_unused_4298_ = crate::leanh::lean_ctor_get(v_r_3982_, 2);
                        crate::leanh::lean_dec(v_unused_4298_);
                        v_unused_4299_ = crate::leanh::lean_ctor_get(v_r_3982_, 1);
                        crate::leanh::lean_dec(v_unused_4299_);
                        v_unused_4300_ = crate::leanh::lean_ctor_get(v_r_3982_, 0);
                        crate::leanh::lean_dec(v_unused_4300_);
                        v___x_4243_ = v_r_3982_;
                        v_isShared_4244_ = v_isSharedCheck_4295_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_3982_);
                        v___x_4243_ = crate::leanh::lean_box(0);
                        v_isShared_4244_ = v_isSharedCheck_4295_;
                        state = 38;
                        continue;
                    }
                }
            }
            28 => {
                return v___x_4180_;
            }
            29 => {
                v_size_4185_ = crate::leanh::lean_ctor_get(v_l_4162_, 0);
                v_k_4186_ = crate::leanh::lean_ctor_get(v_l_4162_, 1);
                v_v_4187_ = crate::leanh::lean_ctor_get(v_l_4162_, 2);
                v_l_4188_ = crate::leanh::lean_ctor_get(v_l_4162_, 3);
                v_r_4189_ = crate::leanh::lean_ctor_get(v_l_4162_, 4);
                v_size_4190_ = crate::leanh::lean_ctor_get(v_r_4163_, 0);
                v___x_4191_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4192_ = lean_nat_mul(v___x_4191_, v_size_4190_);
                v___x_4193_ = lean_nat_dec_lt(v_size_4185_, v___x_4192_);
                crate::leanh::lean_dec(v___x_4192_);
                if v___x_4193_ == 0 {
                    crate::leanh::lean_inc(v_r_4189_);
                    crate::leanh::lean_inc(v_l_4188_);
                    crate::leanh::lean_inc(v_v_4187_);
                    crate::leanh::lean_inc(v_k_4186_);
                    v_isSharedCheck_4221_ = (!crate::leanh::lean_is_exclusive(v_l_4162_)) as u8;
                    if v_isSharedCheck_4221_ == 0 {
                        v_unused_4222_ = crate::leanh::lean_ctor_get(v_l_4162_, 4);
                        crate::leanh::lean_dec(v_unused_4222_);
                        v_unused_4223_ = crate::leanh::lean_ctor_get(v_l_4162_, 3);
                        crate::leanh::lean_dec(v_unused_4223_);
                        v_unused_4224_ = crate::leanh::lean_ctor_get(v_l_4162_, 2);
                        crate::leanh::lean_dec(v_unused_4224_);
                        v_unused_4225_ = crate::leanh::lean_ctor_get(v_l_4162_, 1);
                        crate::leanh::lean_dec(v_unused_4225_);
                        v_unused_4226_ = crate::leanh::lean_ctor_get(v_l_4162_, 0);
                        crate::leanh::lean_dec(v_unused_4226_);
                        v___x_4195_ = v_l_4162_;
                        v_isShared_4196_ = v_isSharedCheck_4221_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_4162_);
                        v___x_4195_ = crate::leanh::lean_box(0);
                        v_isShared_4196_ = v_isSharedCheck_4221_;
                        state = 30;
                        continue;
                    }
                } else {
                    v___x_4227_ = lean_nat_add(v___x_4164_, v_size_4173_);
                    v___x_4228_ = lean_nat_add(v___x_4227_, v_size_4159_);
                    crate::leanh::lean_dec(v_size_4159_);
                    v___x_4229_ = lean_nat_add(v___x_4227_, v_size_4185_);
                    crate::leanh::lean_dec(v___x_4227_);
                    if v_isShared_4184_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4183_, 4, v_l_4162_);
                        crate::leanh::lean_ctor_set(v___x_4183_, 3, v_tree_4170_);
                        crate::leanh::lean_ctor_set(v___x_4183_, 2, v_v_4172_);
                        crate::leanh::lean_ctor_set(v___x_4183_, 1, v_k_4171_);
                        crate::leanh::lean_ctor_set(v___x_4183_, 0, v___x_4229_);
                        v___x_4231_ = v___x_4183_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_4235_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4229_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4235_, 1, v_k_4171_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4235_, 2, v_v_4172_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4235_, 3, v_tree_4170_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4235_, 4, v_l_4162_);
                        v___x_4231_ = v_reuseFailAlloc_4235_;
                        state = 36;
                        continue;
                    }
                }
            }
            30 => {
                v___x_4197_ = lean_nat_add(v___x_4164_, v_size_4173_);
                v___x_4198_ = lean_nat_add(v___x_4197_, v_size_4159_);
                crate::leanh::lean_dec(v_size_4159_);
                if crate::leanh::lean_obj_tag(v_l_4188_) == 0 {
                    v_size_4219_ = crate::leanh::lean_ctor_get(v_l_4188_, 0);
                    crate::leanh::lean_inc(v_size_4219_);
                    v___y_4211_ = v_size_4219_;
                    state = 34;
                    continue;
                } else {
                    v___x_4220_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4211_ = v___x_4220_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_4203_ = lean_nat_add(v___y_4201_, v___y_4202_);
                crate::leanh::lean_dec(v___y_4202_);
                crate::leanh::lean_dec(v___y_4201_);
                if v_isShared_4196_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4195_, 4, v_r_4163_);
                    crate::leanh::lean_ctor_set(v___x_4195_, 3, v_r_4189_);
                    crate::leanh::lean_ctor_set(v___x_4195_, 2, v_v_4161_);
                    crate::leanh::lean_ctor_set(v___x_4195_, 1, v_k_4160_);
                    crate::leanh::lean_ctor_set(v___x_4195_, 0, v___x_4203_);
                    v___x_4205_ = v___x_4195_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4209_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 1, v_k_4160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 2, v_v_4161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 3, v_r_4189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 4, v_r_4163_);
                    v___x_4205_ = v_reuseFailAlloc_4209_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_4184_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4183_, 4, v___x_4205_);
                    crate::leanh::lean_ctor_set(v___x_4183_, 3, v___y_4200_);
                    crate::leanh::lean_ctor_set(v___x_4183_, 2, v_v_4187_);
                    crate::leanh::lean_ctor_set(v___x_4183_, 1, v_k_4186_);
                    crate::leanh::lean_ctor_set(v___x_4183_, 0, v___x_4198_);
                    v___x_4207_ = v___x_4183_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4208_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 1, v_k_4186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 2, v_v_4187_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 3, v___y_4200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 4, v___x_4205_);
                    v___x_4207_ = v_reuseFailAlloc_4208_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4207_;
            }
            34 => {
                v___x_4212_ = lean_nat_add(v___x_4197_, v___y_4211_);
                crate::leanh::lean_dec(v___y_4211_);
                crate::leanh::lean_dec(v___x_4197_);
                if v_isShared_4168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4167_, 4, v_l_4188_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 3, v_tree_4170_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 2, v_v_4172_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 1, v_k_4171_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4212_);
                    v___x_4214_ = v___x_4167_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_k_4171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 2, v_v_4172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 3, v_tree_4170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 4, v_l_4188_);
                    v___x_4214_ = v_reuseFailAlloc_4218_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_4215_ = lean_nat_add(v___x_4164_, v_size_4190_);
                if crate::leanh::lean_obj_tag(v_r_4189_) == 0 {
                    v_size_4216_ = crate::leanh::lean_ctor_get(v_r_4189_, 0);
                    crate::leanh::lean_inc(v_size_4216_);
                    v___y_4200_ = v___x_4214_;
                    v___y_4201_ = v___x_4215_;
                    v___y_4202_ = v_size_4216_;
                    state = 31;
                    continue;
                } else {
                    v___x_4217_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4200_ = v___x_4214_;
                    v___y_4201_ = v___x_4215_;
                    v___y_4202_ = v___x_4217_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                if v_isShared_4168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4167_, 4, v_r_4163_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 3, v___x_4231_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 2, v_v_4161_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 1, v_k_4160_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4228_);
                    v___x_4233_ = v___x_4167_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4234_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4234_, 1, v_k_4160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4234_, 2, v_v_4161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4234_, 3, v___x_4231_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4234_, 4, v_r_4163_);
                    v___x_4233_ = v_reuseFailAlloc_4234_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4233_;
            }
            38 => {
                if crate::leanh::lean_obj_tag(v_l_4162_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_4163_) == 0 {
                        v_k_4245_ = crate::leanh::lean_ctor_get(v___x_4169_, 0);
                        crate::leanh::lean_inc(v_k_4245_);
                        v_v_4246_ = crate::leanh::lean_ctor_get(v___x_4169_, 1);
                        crate::leanh::lean_inc(v_v_4246_);
                        crate::leanh::lean_dec_ref(v___x_4169_);
                        v_size_4247_ = crate::leanh::lean_ctor_get(v_l_4162_, 0);
                        v___x_4248_ = lean_nat_add(v___x_4164_, v_size_4159_);
                        crate::leanh::lean_dec(v_size_4159_);
                        v___x_4249_ = lean_nat_add(v___x_4164_, v_size_4247_);
                        if v_isShared_4244_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4243_, 4, v_l_4162_);
                            crate::leanh::lean_ctor_set(v___x_4243_, 3, v_tree_4170_);
                            crate::leanh::lean_ctor_set(v___x_4243_, 2, v_v_4246_);
                            crate::leanh::lean_ctor_set(v___x_4243_, 1, v_k_4245_);
                            crate::leanh::lean_ctor_set(v___x_4243_, 0, v___x_4249_);
                            v___x_4251_ = v___x_4243_;
                            state = 39;
                            continue;
                        } else {
                            v_reuseFailAlloc_4255_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4249_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 1, v_k_4245_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 2, v_v_4246_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 3, v_tree_4170_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 4, v_l_4162_);
                            v___x_4251_ = v_reuseFailAlloc_4255_;
                            state = 39;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_size_4159_);
                        v_k_4256_ = crate::leanh::lean_ctor_get(v___x_4169_, 0);
                        crate::leanh::lean_inc(v_k_4256_);
                        v_v_4257_ = crate::leanh::lean_ctor_get(v___x_4169_, 1);
                        crate::leanh::lean_inc(v_v_4257_);
                        crate::leanh::lean_dec_ref(v___x_4169_);
                        v_k_4258_ = crate::leanh::lean_ctor_get(v_l_4162_, 1);
                        v_v_4259_ = crate::leanh::lean_ctor_get(v_l_4162_, 2);
                        v_isSharedCheck_4273_ = (!crate::leanh::lean_is_exclusive(v_l_4162_)) as u8;
                        if v_isSharedCheck_4273_ == 0 {
                            v_unused_4274_ = crate::leanh::lean_ctor_get(v_l_4162_, 4);
                            crate::leanh::lean_dec(v_unused_4274_);
                            v_unused_4275_ = crate::leanh::lean_ctor_get(v_l_4162_, 3);
                            crate::leanh::lean_dec(v_unused_4275_);
                            v_unused_4276_ = crate::leanh::lean_ctor_get(v_l_4162_, 0);
                            crate::leanh::lean_dec(v_unused_4276_);
                            v___x_4261_ = v_l_4162_;
                            v_isShared_4262_ = v_isSharedCheck_4273_;
                            state = 41;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_4259_);
                            crate::leanh::lean_inc(v_k_4258_);
                            crate::leanh::lean_dec(v_l_4162_);
                            v___x_4261_ = crate::leanh::lean_box(0);
                            v_isShared_4262_ = v_isSharedCheck_4273_;
                            state = 41;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_r_4163_) == 0 {
                        crate::leanh::lean_dec(v_size_4159_);
                        v_k_4277_ = crate::leanh::lean_ctor_get(v___x_4169_, 0);
                        crate::leanh::lean_inc(v_k_4277_);
                        v_v_4278_ = crate::leanh::lean_ctor_get(v___x_4169_, 1);
                        crate::leanh::lean_inc(v_v_4278_);
                        crate::leanh::lean_dec_ref(v___x_4169_);
                        v___x_4279_ = crate::leanh::lean_unsigned_to_nat(3);
                        if v_isShared_4244_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4243_, 4, v_l_4162_);
                            crate::leanh::lean_ctor_set(v___x_4243_, 2, v_v_4278_);
                            crate::leanh::lean_ctor_set(v___x_4243_, 1, v_k_4277_);
                            crate::leanh::lean_ctor_set(v___x_4243_, 0, v___x_4164_);
                            v___x_4281_ = v___x_4243_;
                            state = 45;
                            continue;
                        } else {
                            v_reuseFailAlloc_4285_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 0, v___x_4164_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_k_4277_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 2, v_v_4278_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 3, v_l_4162_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 4, v_l_4162_);
                            v___x_4281_ = v_reuseFailAlloc_4285_;
                            state = 45;
                            continue;
                        }
                    } else {
                        v_k_4286_ = crate::leanh::lean_ctor_get(v___x_4169_, 0);
                        crate::leanh::lean_inc(v_k_4286_);
                        v_v_4287_ = crate::leanh::lean_ctor_get(v___x_4169_, 1);
                        crate::leanh::lean_inc(v_v_4287_);
                        crate::leanh::lean_dec_ref(v___x_4169_);
                        if v_isShared_4244_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4243_, 3, v_r_4163_);
                            v___x_4289_ = v___x_4243_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_4294_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_size_4159_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 1, v_k_4160_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 2, v_v_4161_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 3, v_r_4163_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 4, v_r_4163_);
                            v___x_4289_ = v_reuseFailAlloc_4294_;
                            state = 47;
                            continue;
                        }
                    }
                }
            }
            39 => {
                if v_isShared_4168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4167_, 4, v_r_4163_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 3, v___x_4251_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 2, v_v_4161_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 1, v_k_4160_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4248_);
                    v___x_4253_ = v___x_4167_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4254_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 1, v_k_4160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 2, v_v_4161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 3, v___x_4251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 4, v_r_4163_);
                    v___x_4253_ = v_reuseFailAlloc_4254_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4253_;
            }
            41 => {
                v___x_4263_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4261_, 4, v_r_4163_);
                    crate::leanh::lean_ctor_set(v___x_4261_, 3, v_r_4163_);
                    crate::leanh::lean_ctor_set(v___x_4261_, 2, v_v_4257_);
                    crate::leanh::lean_ctor_set(v___x_4261_, 1, v_k_4256_);
                    crate::leanh::lean_ctor_set(v___x_4261_, 0, v___x_4164_);
                    v___x_4265_ = v___x_4261_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4272_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4272_, 1, v_k_4256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4272_, 2, v_v_4257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4272_, 3, v_r_4163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4272_, 4, v_r_4163_);
                    v___x_4265_ = v_reuseFailAlloc_4272_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                if v_isShared_4244_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4243_, 3, v_r_4163_);
                    crate::leanh::lean_ctor_set(v___x_4243_, 0, v___x_4164_);
                    v___x_4267_ = v___x_4243_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_k_4160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 2, v_v_4161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 3, v_r_4163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 4, v_r_4163_);
                    v___x_4267_ = v_reuseFailAlloc_4271_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_4168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4167_, 4, v___x_4267_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 3, v___x_4265_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 2, v_v_4259_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 1, v_k_4258_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4263_);
                    v___x_4269_ = v___x_4167_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4270_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4270_, 0, v___x_4263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4270_, 1, v_k_4258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4270_, 2, v_v_4259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4270_, 3, v___x_4265_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4270_, 4, v___x_4267_);
                    v___x_4269_ = v_reuseFailAlloc_4270_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_4269_;
            }
            45 => {
                if v_isShared_4168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4167_, 4, v_r_4163_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 3, v___x_4281_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 2, v_v_4161_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 1, v_k_4160_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4279_);
                    v___x_4283_ = v___x_4167_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4284_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_k_4160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4284_, 2, v_v_4161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4284_, 3, v___x_4281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4284_, 4, v_r_4163_);
                    v___x_4283_ = v_reuseFailAlloc_4284_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_4283_;
            }
            47 => {
                v___x_4290_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_4168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4167_, 4, v___x_4289_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 3, v_r_4163_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 2, v_v_4287_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 1, v_k_4286_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4290_);
                    v___x_4292_ = v___x_4167_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_4293_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4290_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4293_, 1, v_k_4286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4293_, 2, v_v_4287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4293_, 3, v_r_4163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4293_, 4, v___x_4289_);
                    v___x_4292_ = v_reuseFailAlloc_4293_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_4292_;
            }
            49 => {
                v___x_4310_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_4160_, v_v_4161_, v_l_4162_, v_r_4163_,
                );
                v_tree_4311_ = crate::leanh::lean_ctor_get(v___x_4310_, 2);
                crate::leanh::lean_inc(v_tree_4311_);
                if crate::leanh::lean_obj_tag(v_tree_4311_) == 0 {
                    v_k_4312_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
                    crate::leanh::lean_inc(v_k_4312_);
                    v_v_4313_ = crate::leanh::lean_ctor_get(v___x_4310_, 1);
                    crate::leanh::lean_inc(v_v_4313_);
                    crate::leanh::lean_dec_ref(v___x_4310_);
                    v_size_4314_ = crate::leanh::lean_ctor_get(v_tree_4311_, 0);
                    v___x_4315_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4316_ = lean_nat_mul(v___x_4315_, v_size_4314_);
                    v___x_4317_ = lean_nat_dec_lt(v___x_4316_, v_size_4154_);
                    crate::leanh::lean_dec(v___x_4316_);
                    if v___x_4317_ == 0 {
                        crate::leanh::lean_dec(v_r_4158_);
                        v___x_4318_ = lean_nat_add(v___x_4164_, v_size_4154_);
                        v___x_4319_ = lean_nat_add(v___x_4318_, v_size_4314_);
                        crate::leanh::lean_dec(v___x_4318_);
                        if v_isShared_4309_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4308_, 4, v_tree_4311_);
                            crate::leanh::lean_ctor_set(v___x_4308_, 3, v_l_3981_);
                            crate::leanh::lean_ctor_set(v___x_4308_, 2, v_v_4313_);
                            crate::leanh::lean_ctor_set(v___x_4308_, 1, v_k_4312_);
                            crate::leanh::lean_ctor_set(v___x_4308_, 0, v___x_4319_);
                            v___x_4321_ = v___x_4308_;
                            state = 50;
                            continue;
                        } else {
                            v_reuseFailAlloc_4322_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4319_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 1, v_k_4312_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 2, v_v_4313_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 3, v_l_3981_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 4, v_tree_4311_);
                            v___x_4321_ = v_reuseFailAlloc_4322_;
                            state = 50;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_l_4157_);
                        crate::leanh::lean_inc(v_v_4156_);
                        crate::leanh::lean_inc(v_k_4155_);
                        crate::leanh::lean_inc(v_size_4154_);
                        v_isSharedCheck_4388_ = (!crate::leanh::lean_is_exclusive(v_l_3981_)) as u8;
                        if v_isSharedCheck_4388_ == 0 {
                            v_unused_4389_ = crate::leanh::lean_ctor_get(v_l_3981_, 4);
                            crate::leanh::lean_dec(v_unused_4389_);
                            v_unused_4390_ = crate::leanh::lean_ctor_get(v_l_3981_, 3);
                            crate::leanh::lean_dec(v_unused_4390_);
                            v_unused_4391_ = crate::leanh::lean_ctor_get(v_l_3981_, 2);
                            crate::leanh::lean_dec(v_unused_4391_);
                            v_unused_4392_ = crate::leanh::lean_ctor_get(v_l_3981_, 1);
                            crate::leanh::lean_dec(v_unused_4392_);
                            v_unused_4393_ = crate::leanh::lean_ctor_get(v_l_3981_, 0);
                            crate::leanh::lean_dec(v_unused_4393_);
                            v___x_4324_ = v_l_3981_;
                            v_isShared_4325_ = v_isSharedCheck_4388_;
                            state = 51;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_3981_);
                            v___x_4324_ = crate::leanh::lean_box(0);
                            v_isShared_4325_ = v_isSharedCheck_4388_;
                            state = 51;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_l_4157_) == 0 {
                        crate::leanh::lean_inc_ref(v_l_4157_);
                        crate::leanh::lean_inc(v_v_4156_);
                        crate::leanh::lean_inc(v_k_4155_);
                        crate::leanh::lean_inc(v_size_4154_);
                        v_isSharedCheck_4417_ = (!crate::leanh::lean_is_exclusive(v_l_3981_)) as u8;
                        if v_isSharedCheck_4417_ == 0 {
                            v_unused_4418_ = crate::leanh::lean_ctor_get(v_l_3981_, 4);
                            crate::leanh::lean_dec(v_unused_4418_);
                            v_unused_4419_ = crate::leanh::lean_ctor_get(v_l_3981_, 3);
                            crate::leanh::lean_dec(v_unused_4419_);
                            v_unused_4420_ = crate::leanh::lean_ctor_get(v_l_3981_, 2);
                            crate::leanh::lean_dec(v_unused_4420_);
                            v_unused_4421_ = crate::leanh::lean_ctor_get(v_l_3981_, 1);
                            crate::leanh::lean_dec(v_unused_4421_);
                            v_unused_4422_ = crate::leanh::lean_ctor_get(v_l_3981_, 0);
                            crate::leanh::lean_dec(v_unused_4422_);
                            v___x_4395_ = v_l_3981_;
                            v_isShared_4396_ = v_isSharedCheck_4417_;
                            state = 61;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_3981_);
                            v___x_4395_ = crate::leanh::lean_box(0);
                            v_isShared_4396_ = v_isSharedCheck_4417_;
                            state = 61;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_4158_) == 0 {
                            crate::leanh::lean_inc(v_l_4157_);
                            crate::leanh::lean_inc(v_v_4156_);
                            crate::leanh::lean_inc(v_k_4155_);
                            v_isSharedCheck_4447_ =
                                (!crate::leanh::lean_is_exclusive(v_l_3981_)) as u8;
                            if v_isSharedCheck_4447_ == 0 {
                                v_unused_4448_ = crate::leanh::lean_ctor_get(v_l_3981_, 4);
                                crate::leanh::lean_dec(v_unused_4448_);
                                v_unused_4449_ = crate::leanh::lean_ctor_get(v_l_3981_, 3);
                                crate::leanh::lean_dec(v_unused_4449_);
                                v_unused_4450_ = crate::leanh::lean_ctor_get(v_l_3981_, 2);
                                crate::leanh::lean_dec(v_unused_4450_);
                                v_unused_4451_ = crate::leanh::lean_ctor_get(v_l_3981_, 1);
                                crate::leanh::lean_dec(v_unused_4451_);
                                v_unused_4452_ = crate::leanh::lean_ctor_get(v_l_3981_, 0);
                                crate::leanh::lean_dec(v_unused_4452_);
                                v___x_4424_ = v_l_3981_;
                                v_isShared_4425_ = v_isSharedCheck_4447_;
                                state = 66;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_3981_);
                                v___x_4424_ = crate::leanh::lean_box(0);
                                v_isShared_4425_ = v_isSharedCheck_4447_;
                                state = 66;
                                continue;
                            }
                        } else {
                            v_k_4453_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
                            crate::leanh::lean_inc(v_k_4453_);
                            v_v_4454_ = crate::leanh::lean_ctor_get(v___x_4310_, 1);
                            crate::leanh::lean_inc(v_v_4454_);
                            crate::leanh::lean_dec_ref(v___x_4310_);
                            v___x_4455_ = crate::leanh::lean_unsigned_to_nat(2);
                            if v_isShared_4309_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4308_, 4, v_r_4158_);
                                crate::leanh::lean_ctor_set(v___x_4308_, 3, v_l_3981_);
                                crate::leanh::lean_ctor_set(v___x_4308_, 2, v_v_4454_);
                                crate::leanh::lean_ctor_set(v___x_4308_, 1, v_k_4453_);
                                crate::leanh::lean_ctor_set(v___x_4308_, 0, v___x_4455_);
                                v___x_4457_ = v___x_4308_;
                                state = 71;
                                continue;
                            } else {
                                v_reuseFailAlloc_4458_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4455_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4458_, 1, v_k_4453_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4458_, 2, v_v_4454_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4458_, 3, v_l_3981_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4458_, 4, v_r_4158_);
                                v___x_4457_ = v_reuseFailAlloc_4458_;
                                state = 71;
                                continue;
                            }
                        }
                    }
                }
            }
            50 => {
                return v___x_4321_;
            }
            51 => {
                v_size_4326_ = crate::leanh::lean_ctor_get(v_l_4157_, 0);
                v_size_4327_ = crate::leanh::lean_ctor_get(v_r_4158_, 0);
                v_k_4328_ = crate::leanh::lean_ctor_get(v_r_4158_, 1);
                v_v_4329_ = crate::leanh::lean_ctor_get(v_r_4158_, 2);
                v_l_4330_ = crate::leanh::lean_ctor_get(v_r_4158_, 3);
                v_r_4331_ = crate::leanh::lean_ctor_get(v_r_4158_, 4);
                v___x_4332_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4333_ = lean_nat_mul(v___x_4332_, v_size_4326_);
                v___x_4334_ = lean_nat_dec_lt(v_size_4327_, v___x_4333_);
                crate::leanh::lean_dec(v___x_4333_);
                if v___x_4334_ == 0 {
                    crate::leanh::lean_inc(v_r_4331_);
                    crate::leanh::lean_inc(v_l_4330_);
                    crate::leanh::lean_inc(v_v_4329_);
                    crate::leanh::lean_inc(v_k_4328_);
                    crate::leanh::lean_del_object(v___x_4324_);
                    v_isSharedCheck_4372_ = (!crate::leanh::lean_is_exclusive(v_r_4158_)) as u8;
                    if v_isSharedCheck_4372_ == 0 {
                        v_unused_4373_ = crate::leanh::lean_ctor_get(v_r_4158_, 4);
                        crate::leanh::lean_dec(v_unused_4373_);
                        v_unused_4374_ = crate::leanh::lean_ctor_get(v_r_4158_, 3);
                        crate::leanh::lean_dec(v_unused_4374_);
                        v_unused_4375_ = crate::leanh::lean_ctor_get(v_r_4158_, 2);
                        crate::leanh::lean_dec(v_unused_4375_);
                        v_unused_4376_ = crate::leanh::lean_ctor_get(v_r_4158_, 1);
                        crate::leanh::lean_dec(v_unused_4376_);
                        v_unused_4377_ = crate::leanh::lean_ctor_get(v_r_4158_, 0);
                        crate::leanh::lean_dec(v_unused_4377_);
                        v___x_4336_ = v_r_4158_;
                        v_isShared_4337_ = v_isSharedCheck_4372_;
                        state = 52;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_4158_);
                        v___x_4336_ = crate::leanh::lean_box(0);
                        v_isShared_4337_ = v_isSharedCheck_4372_;
                        state = 52;
                        continue;
                    }
                } else {
                    v___x_4378_ = lean_nat_add(v___x_4164_, v_size_4154_);
                    crate::leanh::lean_dec(v_size_4154_);
                    v___x_4379_ = lean_nat_add(v___x_4378_, v_size_4314_);
                    crate::leanh::lean_dec(v___x_4378_);
                    v___x_4380_ = lean_nat_add(v___x_4164_, v_size_4314_);
                    v___x_4381_ = lean_nat_add(v___x_4380_, v_size_4327_);
                    crate::leanh::lean_dec(v___x_4380_);
                    if v_isShared_4309_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4308_, 4, v_tree_4311_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 3, v_r_4158_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 2, v_v_4313_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 1, v_k_4312_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 0, v___x_4381_);
                        v___x_4383_ = v___x_4308_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_4387_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4381_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_k_4312_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 2, v_v_4313_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 3, v_r_4158_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 4, v_tree_4311_);
                        v___x_4383_ = v_reuseFailAlloc_4387_;
                        state = 59;
                        continue;
                    }
                }
            }
            52 => {
                v___x_4338_ = lean_nat_add(v___x_4164_, v_size_4154_);
                crate::leanh::lean_dec(v_size_4154_);
                v___x_4339_ = lean_nat_add(v___x_4338_, v_size_4314_);
                crate::leanh::lean_dec(v___x_4338_);
                v___x_4360_ = lean_nat_add(v___x_4164_, v_size_4326_);
                if crate::leanh::lean_obj_tag(v_l_4330_) == 0 {
                    v_size_4370_ = crate::leanh::lean_ctor_get(v_l_4330_, 0);
                    crate::leanh::lean_inc(v_size_4370_);
                    v___y_4362_ = v_size_4370_;
                    state = 57;
                    continue;
                } else {
                    v___x_4371_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4362_ = v___x_4371_;
                    state = 57;
                    continue;
                }
            }
            53 => {
                v___x_4344_ = lean_nat_add(v___y_4342_, v___y_4343_);
                crate::leanh::lean_dec(v___y_4343_);
                crate::leanh::lean_dec(v___y_4342_);
                crate::leanh::lean_inc_ref(v_tree_4311_);
                if v_isShared_4337_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4336_, 4, v_tree_4311_);
                    crate::leanh::lean_ctor_set(v___x_4336_, 3, v_r_4331_);
                    crate::leanh::lean_ctor_set(v___x_4336_, 2, v_v_4313_);
                    crate::leanh::lean_ctor_set(v___x_4336_, 1, v_k_4312_);
                    crate::leanh::lean_ctor_set(v___x_4336_, 0, v___x_4344_);
                    v___x_4346_ = v___x_4336_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_4359_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___x_4344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4359_, 1, v_k_4312_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4359_, 2, v_v_4313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4359_, 3, v_r_4331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4359_, 4, v_tree_4311_);
                    v___x_4346_ = v_reuseFailAlloc_4359_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v_isSharedCheck_4353_ = (!crate::leanh::lean_is_exclusive(v_tree_4311_)) as u8;
                if v_isSharedCheck_4353_ == 0 {
                    v_unused_4354_ = crate::leanh::lean_ctor_get(v_tree_4311_, 4);
                    crate::leanh::lean_dec(v_unused_4354_);
                    v_unused_4355_ = crate::leanh::lean_ctor_get(v_tree_4311_, 3);
                    crate::leanh::lean_dec(v_unused_4355_);
                    v_unused_4356_ = crate::leanh::lean_ctor_get(v_tree_4311_, 2);
                    crate::leanh::lean_dec(v_unused_4356_);
                    v_unused_4357_ = crate::leanh::lean_ctor_get(v_tree_4311_, 1);
                    crate::leanh::lean_dec(v_unused_4357_);
                    v_unused_4358_ = crate::leanh::lean_ctor_get(v_tree_4311_, 0);
                    crate::leanh::lean_dec(v_unused_4358_);
                    v___x_4348_ = v_tree_4311_;
                    v_isShared_4349_ = v_isSharedCheck_4353_;
                    state = 55;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tree_4311_);
                    v___x_4348_ = crate::leanh::lean_box(0);
                    v_isShared_4349_ = v_isSharedCheck_4353_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                if v_isShared_4349_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4348_, 4, v___x_4346_);
                    crate::leanh::lean_ctor_set(v___x_4348_, 3, v___y_4341_);
                    crate::leanh::lean_ctor_set(v___x_4348_, 2, v_v_4329_);
                    crate::leanh::lean_ctor_set(v___x_4348_, 1, v_k_4328_);
                    crate::leanh::lean_ctor_set(v___x_4348_, 0, v___x_4339_);
                    v___x_4351_ = v___x_4348_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_4352_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4339_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4352_, 1, v_k_4328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4352_, 2, v_v_4329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4352_, 3, v___y_4341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4352_, 4, v___x_4346_);
                    v___x_4351_ = v_reuseFailAlloc_4352_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_4351_;
            }
            57 => {
                v___x_4363_ = lean_nat_add(v___x_4360_, v___y_4362_);
                crate::leanh::lean_dec(v___y_4362_);
                crate::leanh::lean_dec(v___x_4360_);
                if v_isShared_4309_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4308_, 4, v_l_4330_);
                    crate::leanh::lean_ctor_set(v___x_4308_, 3, v_l_4157_);
                    crate::leanh::lean_ctor_set(v___x_4308_, 2, v_v_4156_);
                    crate::leanh::lean_ctor_set(v___x_4308_, 1, v_k_4155_);
                    crate::leanh::lean_ctor_set(v___x_4308_, 0, v___x_4363_);
                    v___x_4365_ = v___x_4308_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_4369_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4363_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4369_, 1, v_k_4155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4369_, 2, v_v_4156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4369_, 3, v_l_4157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4369_, 4, v_l_4330_);
                    v___x_4365_ = v_reuseFailAlloc_4369_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___x_4366_ = lean_nat_add(v___x_4164_, v_size_4314_);
                if crate::leanh::lean_obj_tag(v_r_4331_) == 0 {
                    v_size_4367_ = crate::leanh::lean_ctor_get(v_r_4331_, 0);
                    crate::leanh::lean_inc(v_size_4367_);
                    v___y_4341_ = v___x_4365_;
                    v___y_4342_ = v___x_4366_;
                    v___y_4343_ = v_size_4367_;
                    state = 53;
                    continue;
                } else {
                    v___x_4368_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4341_ = v___x_4365_;
                    v___y_4342_ = v___x_4366_;
                    v___y_4343_ = v___x_4368_;
                    state = 53;
                    continue;
                }
            }
            59 => {
                if v_isShared_4325_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4324_, 4, v___x_4383_);
                    crate::leanh::lean_ctor_set(v___x_4324_, 0, v___x_4379_);
                    v___x_4385_ = v___x_4324_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_4386_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4386_, 1, v_k_4155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4386_, 2, v_v_4156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4386_, 3, v_l_4157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4386_, 4, v___x_4383_);
                    v___x_4385_ = v_reuseFailAlloc_4386_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_4385_;
            }
            61 => {
                if crate::leanh::lean_obj_tag(v_r_4158_) == 0 {
                    v_k_4397_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
                    crate::leanh::lean_inc(v_k_4397_);
                    v_v_4398_ = crate::leanh::lean_ctor_get(v___x_4310_, 1);
                    crate::leanh::lean_inc(v_v_4398_);
                    crate::leanh::lean_dec_ref(v___x_4310_);
                    v_size_4399_ = crate::leanh::lean_ctor_get(v_r_4158_, 0);
                    v___x_4400_ = lean_nat_add(v___x_4164_, v_size_4154_);
                    crate::leanh::lean_dec(v_size_4154_);
                    v___x_4401_ = lean_nat_add(v___x_4164_, v_size_4399_);
                    if v_isShared_4309_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4308_, 4, v_tree_4311_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 3, v_r_4158_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 2, v_v_4398_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 1, v_k_4397_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 0, v___x_4401_);
                        v___x_4403_ = v___x_4308_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_4407_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4401_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_k_4397_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4407_, 2, v_v_4398_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4407_, 3, v_r_4158_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4407_, 4, v_tree_4311_);
                        v___x_4403_ = v_reuseFailAlloc_4407_;
                        state = 62;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_size_4154_);
                    v_k_4408_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
                    crate::leanh::lean_inc(v_k_4408_);
                    v_v_4409_ = crate::leanh::lean_ctor_get(v___x_4310_, 1);
                    crate::leanh::lean_inc(v_v_4409_);
                    crate::leanh::lean_dec_ref(v___x_4310_);
                    v___x_4410_ = crate::leanh::lean_unsigned_to_nat(3);
                    if v_isShared_4309_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4308_, 4, v_r_4158_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 3, v_r_4158_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 2, v_v_4409_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 1, v_k_4408_);
                        crate::leanh::lean_ctor_set(v___x_4308_, 0, v___x_4164_);
                        v___x_4412_ = v___x_4308_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_4416_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4164_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 1, v_k_4408_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 2, v_v_4409_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 3, v_r_4158_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 4, v_r_4158_);
                        v___x_4412_ = v_reuseFailAlloc_4416_;
                        state = 64;
                        continue;
                    }
                }
            }
            62 => {
                if v_isShared_4396_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4395_, 4, v___x_4403_);
                    crate::leanh::lean_ctor_set(v___x_4395_, 0, v___x_4400_);
                    v___x_4405_ = v___x_4395_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_4406_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4400_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_k_4155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4406_, 2, v_v_4156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4406_, 3, v_l_4157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4406_, 4, v___x_4403_);
                    v___x_4405_ = v_reuseFailAlloc_4406_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_4405_;
            }
            64 => {
                if v_isShared_4396_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4395_, 4, v___x_4412_);
                    crate::leanh::lean_ctor_set(v___x_4395_, 0, v___x_4410_);
                    v___x_4414_ = v___x_4395_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_4415_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_k_4155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 2, v_v_4156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 3, v_l_4157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 4, v___x_4412_);
                    v___x_4414_ = v_reuseFailAlloc_4415_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_4414_;
            }
            66 => {
                v_k_4426_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
                crate::leanh::lean_inc(v_k_4426_);
                v_v_4427_ = crate::leanh::lean_ctor_get(v___x_4310_, 1);
                crate::leanh::lean_inc(v_v_4427_);
                crate::leanh::lean_dec_ref(v___x_4310_);
                v_k_4428_ = crate::leanh::lean_ctor_get(v_r_4158_, 1);
                v_v_4429_ = crate::leanh::lean_ctor_get(v_r_4158_, 2);
                v_isSharedCheck_4443_ = (!crate::leanh::lean_is_exclusive(v_r_4158_)) as u8;
                if v_isSharedCheck_4443_ == 0 {
                    v_unused_4444_ = crate::leanh::lean_ctor_get(v_r_4158_, 4);
                    crate::leanh::lean_dec(v_unused_4444_);
                    v_unused_4445_ = crate::leanh::lean_ctor_get(v_r_4158_, 3);
                    crate::leanh::lean_dec(v_unused_4445_);
                    v_unused_4446_ = crate::leanh::lean_ctor_get(v_r_4158_, 0);
                    crate::leanh::lean_dec(v_unused_4446_);
                    v___x_4431_ = v_r_4158_;
                    v_isShared_4432_ = v_isSharedCheck_4443_;
                    state = 67;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_4429_);
                    crate::leanh::lean_inc(v_k_4428_);
                    crate::leanh::lean_dec(v_r_4158_);
                    v___x_4431_ = crate::leanh::lean_box(0);
                    v_isShared_4432_ = v_isSharedCheck_4443_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                v___x_4433_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4432_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4431_, 4, v_l_4157_);
                    crate::leanh::lean_ctor_set(v___x_4431_, 3, v_l_4157_);
                    crate::leanh::lean_ctor_set(v___x_4431_, 2, v_v_4156_);
                    crate::leanh::lean_ctor_set(v___x_4431_, 1, v_k_4155_);
                    crate::leanh::lean_ctor_set(v___x_4431_, 0, v___x_4164_);
                    v___x_4435_ = v___x_4431_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_4442_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_k_4155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 2, v_v_4156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 3, v_l_4157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 4, v_l_4157_);
                    v___x_4435_ = v_reuseFailAlloc_4442_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_4309_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4308_, 4, v_l_4157_);
                    crate::leanh::lean_ctor_set(v___x_4308_, 3, v_l_4157_);
                    crate::leanh::lean_ctor_set(v___x_4308_, 2, v_v_4427_);
                    crate::leanh::lean_ctor_set(v___x_4308_, 1, v_k_4426_);
                    crate::leanh::lean_ctor_set(v___x_4308_, 0, v___x_4164_);
                    v___x_4437_ = v___x_4308_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_4441_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 1, v_k_4426_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 2, v_v_4427_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 3, v_l_4157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 4, v_l_4157_);
                    v___x_4437_ = v_reuseFailAlloc_4441_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                if v_isShared_4425_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4424_, 4, v___x_4437_);
                    crate::leanh::lean_ctor_set(v___x_4424_, 3, v___x_4435_);
                    crate::leanh::lean_ctor_set(v___x_4424_, 2, v_v_4429_);
                    crate::leanh::lean_ctor_set(v___x_4424_, 1, v_k_4428_);
                    crate::leanh::lean_ctor_set(v___x_4424_, 0, v___x_4433_);
                    v___x_4439_ = v___x_4424_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_4440_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 1, v_k_4428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 2, v_v_4429_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 3, v___x_4435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 4, v___x_4437_);
                    v___x_4439_ = v_reuseFailAlloc_4440_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_4439_;
            }
            71 => {
                return v___x_4457_;
            }
            72 => {
                return v___x_4479_;
            }
            73 => {
                v_size_4484_ = crate::leanh::lean_ctor_get(v_l_4471_, 0);
                v_k_4485_ = crate::leanh::lean_ctor_get(v_l_4471_, 1);
                v_v_4486_ = crate::leanh::lean_ctor_get(v_l_4471_, 2);
                v_l_4487_ = crate::leanh::lean_ctor_get(v_l_4471_, 3);
                v_r_4488_ = crate::leanh::lean_ctor_get(v_l_4471_, 4);
                v_size_4489_ = crate::leanh::lean_ctor_get(v_r_4472_, 0);
                v___x_4490_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4491_ = lean_nat_mul(v___x_4490_, v_size_4489_);
                v___x_4492_ = lean_nat_dec_lt(v_size_4484_, v___x_4491_);
                crate::leanh::lean_dec(v___x_4491_);
                if v___x_4492_ == 0 {
                    crate::leanh::lean_inc(v_r_4488_);
                    crate::leanh::lean_inc(v_l_4487_);
                    crate::leanh::lean_inc(v_v_4486_);
                    crate::leanh::lean_inc(v_k_4485_);
                    v_isSharedCheck_4520_ = (!crate::leanh::lean_is_exclusive(v_l_4471_)) as u8;
                    if v_isSharedCheck_4520_ == 0 {
                        v_unused_4521_ = crate::leanh::lean_ctor_get(v_l_4471_, 4);
                        crate::leanh::lean_dec(v_unused_4521_);
                        v_unused_4522_ = crate::leanh::lean_ctor_get(v_l_4471_, 3);
                        crate::leanh::lean_dec(v_unused_4522_);
                        v_unused_4523_ = crate::leanh::lean_ctor_get(v_l_4471_, 2);
                        crate::leanh::lean_dec(v_unused_4523_);
                        v_unused_4524_ = crate::leanh::lean_ctor_get(v_l_4471_, 1);
                        crate::leanh::lean_dec(v_unused_4524_);
                        v_unused_4525_ = crate::leanh::lean_ctor_get(v_l_4471_, 0);
                        crate::leanh::lean_dec(v_unused_4525_);
                        v___x_4494_ = v_l_4471_;
                        v_isShared_4495_ = v_isSharedCheck_4520_;
                        state = 74;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_4471_);
                        v___x_4494_ = crate::leanh::lean_box(0);
                        v_isShared_4495_ = v_isSharedCheck_4520_;
                        state = 74;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3984_);
                    v___x_4526_ = lean_nat_add(v___x_4466_, v_size_4467_);
                    crate::leanh::lean_dec(v_size_4467_);
                    v___x_4527_ = lean_nat_add(v___x_4526_, v_size_4468_);
                    crate::leanh::lean_dec(v_size_4468_);
                    v___x_4528_ = lean_nat_add(v___x_4526_, v_size_4484_);
                    crate::leanh::lean_dec(v___x_4526_);
                    crate::leanh::lean_inc_ref(v_impl_4465_);
                    if v_isShared_4483_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4482_, 4, v_l_4471_);
                        crate::leanh::lean_ctor_set(v___x_4482_, 3, v_impl_4465_);
                        crate::leanh::lean_ctor_set(v___x_4482_, 2, v_v_3980_);
                        crate::leanh::lean_ctor_set(v___x_4482_, 1, v_k_3979_);
                        crate::leanh::lean_ctor_set(v___x_4482_, 0, v___x_4528_);
                        v___x_4530_ = v___x_4482_;
                        state = 80;
                        continue;
                    } else {
                        v_reuseFailAlloc_4543_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4528_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4543_, 1, v_k_3979_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4543_, 2, v_v_3980_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4543_, 3, v_impl_4465_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4543_, 4, v_l_4471_);
                        v___x_4530_ = v_reuseFailAlloc_4543_;
                        state = 80;
                        continue;
                    }
                }
            }
            74 => {
                v___x_4496_ = lean_nat_add(v___x_4466_, v_size_4467_);
                crate::leanh::lean_dec(v_size_4467_);
                v___x_4497_ = lean_nat_add(v___x_4496_, v_size_4468_);
                crate::leanh::lean_dec(v_size_4468_);
                if crate::leanh::lean_obj_tag(v_l_4487_) == 0 {
                    v_size_4518_ = crate::leanh::lean_ctor_get(v_l_4487_, 0);
                    crate::leanh::lean_inc(v_size_4518_);
                    v___y_4510_ = v_size_4518_;
                    state = 78;
                    continue;
                } else {
                    v___x_4519_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4510_ = v___x_4519_;
                    state = 78;
                    continue;
                }
            }
            75 => {
                v___x_4502_ = lean_nat_add(v___y_4499_, v___y_4501_);
                crate::leanh::lean_dec(v___y_4501_);
                crate::leanh::lean_dec(v___y_4499_);
                if v_isShared_4495_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4494_, 4, v_r_4472_);
                    crate::leanh::lean_ctor_set(v___x_4494_, 3, v_r_4488_);
                    crate::leanh::lean_ctor_set(v___x_4494_, 2, v_v_4470_);
                    crate::leanh::lean_ctor_set(v___x_4494_, 1, v_k_4469_);
                    crate::leanh::lean_ctor_set(v___x_4494_, 0, v___x_4502_);
                    v___x_4504_ = v___x_4494_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_4508_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 1, v_k_4469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 2, v_v_4470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 3, v_r_4488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 4, v_r_4472_);
                    v___x_4504_ = v_reuseFailAlloc_4508_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                if v_isShared_4483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4482_, 4, v___x_4504_);
                    crate::leanh::lean_ctor_set(v___x_4482_, 3, v___y_4500_);
                    crate::leanh::lean_ctor_set(v___x_4482_, 2, v_v_4486_);
                    crate::leanh::lean_ctor_set(v___x_4482_, 1, v_k_4485_);
                    crate::leanh::lean_ctor_set(v___x_4482_, 0, v___x_4497_);
                    v___x_4506_ = v___x_4482_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_4507_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4507_, 1, v_k_4485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4507_, 2, v_v_4486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4507_, 3, v___y_4500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4507_, 4, v___x_4504_);
                    v___x_4506_ = v_reuseFailAlloc_4507_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_4506_;
            }
            78 => {
                v___x_4511_ = lean_nat_add(v___x_4496_, v___y_4510_);
                crate::leanh::lean_dec(v___y_4510_);
                crate::leanh::lean_dec(v___x_4496_);
                if v_isShared_3985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3984_, 4, v_l_4487_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 3, v_impl_4465_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4511_);
                    v___x_4513_ = v___x_3984_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_4517_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4517_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4517_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4517_, 3, v_impl_4465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4517_, 4, v_l_4487_);
                    v___x_4513_ = v_reuseFailAlloc_4517_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                v___x_4514_ = lean_nat_add(v___x_4466_, v_size_4489_);
                if crate::leanh::lean_obj_tag(v_r_4488_) == 0 {
                    v_size_4515_ = crate::leanh::lean_ctor_get(v_r_4488_, 0);
                    crate::leanh::lean_inc(v_size_4515_);
                    v___y_4499_ = v___x_4514_;
                    v___y_4500_ = v___x_4513_;
                    v___y_4501_ = v_size_4515_;
                    state = 75;
                    continue;
                } else {
                    v___x_4516_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4499_ = v___x_4514_;
                    v___y_4500_ = v___x_4513_;
                    v___y_4501_ = v___x_4516_;
                    state = 75;
                    continue;
                }
            }
            80 => {
                v_isSharedCheck_4537_ = (!crate::leanh::lean_is_exclusive(v_impl_4465_)) as u8;
                if v_isSharedCheck_4537_ == 0 {
                    v_unused_4538_ = crate::leanh::lean_ctor_get(v_impl_4465_, 4);
                    crate::leanh::lean_dec(v_unused_4538_);
                    v_unused_4539_ = crate::leanh::lean_ctor_get(v_impl_4465_, 3);
                    crate::leanh::lean_dec(v_unused_4539_);
                    v_unused_4540_ = crate::leanh::lean_ctor_get(v_impl_4465_, 2);
                    crate::leanh::lean_dec(v_unused_4540_);
                    v_unused_4541_ = crate::leanh::lean_ctor_get(v_impl_4465_, 1);
                    crate::leanh::lean_dec(v_unused_4541_);
                    v_unused_4542_ = crate::leanh::lean_ctor_get(v_impl_4465_, 0);
                    crate::leanh::lean_dec(v_unused_4542_);
                    v___x_4532_ = v_impl_4465_;
                    v_isShared_4533_ = v_isSharedCheck_4537_;
                    state = 81;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_4465_);
                    v___x_4532_ = crate::leanh::lean_box(0);
                    v_isShared_4533_ = v_isSharedCheck_4537_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                if v_isShared_4533_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4532_, 4, v_r_4472_);
                    crate::leanh::lean_ctor_set(v___x_4532_, 3, v___x_4530_);
                    crate::leanh::lean_ctor_set(v___x_4532_, 2, v_v_4470_);
                    crate::leanh::lean_ctor_set(v___x_4532_, 1, v_k_4469_);
                    crate::leanh::lean_ctor_set(v___x_4532_, 0, v___x_4527_);
                    v___x_4535_ = v___x_4532_;
                    state = 82;
                    continue;
                } else {
                    v_reuseFailAlloc_4536_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 1, v_k_4469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 2, v_v_4470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 3, v___x_4530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 4, v_r_4472_);
                    v___x_4535_ = v_reuseFailAlloc_4536_;
                    state = 82;
                    continue;
                }
            }
            82 => {
                return v___x_4535_;
            }
            83 => {
                return v___x_4553_;
            }
            84 => {
                v_size_4563_ = crate::leanh::lean_ctor_get(v_l_4555_, 0);
                v___x_4564_ = lean_nat_add(v___x_4466_, v_size_4557_);
                crate::leanh::lean_dec(v_size_4557_);
                v___x_4565_ = lean_nat_add(v___x_4466_, v_size_4563_);
                if v_isShared_4562_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4561_, 4, v_l_4555_);
                    crate::leanh::lean_ctor_set(v___x_4561_, 3, v_impl_4465_);
                    crate::leanh::lean_ctor_set(v___x_4561_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v___x_4561_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v___x_4561_, 0, v___x_4565_);
                    v___x_4567_ = v___x_4561_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_4571_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4565_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 3, v_impl_4465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 4, v_l_4555_);
                    v___x_4567_ = v_reuseFailAlloc_4571_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                if v_isShared_3985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3984_, 4, v_r_4556_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 3, v___x_4567_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 2, v_v_4559_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 1, v_k_4558_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4564_);
                    v___x_4569_ = v___x_3984_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 1, v_k_4558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 2, v_v_4559_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 3, v___x_4567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 4, v_r_4556_);
                    v___x_4569_ = v_reuseFailAlloc_4570_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                return v___x_4569_;
            }
            87 => {
                v_k_4580_ = crate::leanh::lean_ctor_get(v_l_4555_, 1);
                v_v_4581_ = crate::leanh::lean_ctor_get(v_l_4555_, 2);
                v_isSharedCheck_4595_ = (!crate::leanh::lean_is_exclusive(v_l_4555_)) as u8;
                if v_isSharedCheck_4595_ == 0 {
                    v_unused_4596_ = crate::leanh::lean_ctor_get(v_l_4555_, 4);
                    crate::leanh::lean_dec(v_unused_4596_);
                    v_unused_4597_ = crate::leanh::lean_ctor_get(v_l_4555_, 3);
                    crate::leanh::lean_dec(v_unused_4597_);
                    v_unused_4598_ = crate::leanh::lean_ctor_get(v_l_4555_, 0);
                    crate::leanh::lean_dec(v_unused_4598_);
                    v___x_4583_ = v_l_4555_;
                    v_isShared_4584_ = v_isSharedCheck_4595_;
                    state = 88;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_4581_);
                    crate::leanh::lean_inc(v_k_4580_);
                    crate::leanh::lean_dec(v_l_4555_);
                    v___x_4583_ = crate::leanh::lean_box(0);
                    v_isShared_4584_ = v_isSharedCheck_4595_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                v___x_4585_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4584_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4583_, 4, v_r_4556_);
                    crate::leanh::lean_ctor_set(v___x_4583_, 3, v_r_4556_);
                    crate::leanh::lean_ctor_set(v___x_4583_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v___x_4583_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v___x_4583_, 0, v___x_4466_);
                    v___x_4587_ = v___x_4583_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_4594_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4594_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4594_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4594_, 3, v_r_4556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4594_, 4, v_r_4556_);
                    v___x_4587_ = v_reuseFailAlloc_4594_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                if v_isShared_4579_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4578_, 3, v_r_4556_);
                    crate::leanh::lean_ctor_set(v___x_4578_, 0, v___x_4466_);
                    v___x_4589_ = v___x_4578_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_4593_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4593_, 1, v_k_4575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4593_, 2, v_v_4576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4593_, 3, v_r_4556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4593_, 4, v_r_4556_);
                    v___x_4589_ = v_reuseFailAlloc_4593_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_3985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3984_, 4, v___x_4589_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 3, v___x_4587_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 2, v_v_4581_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 1, v_k_4580_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4585_);
                    v___x_4591_ = v___x_3984_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_4592_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4585_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4592_, 1, v_k_4580_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4592_, 2, v_v_4581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4592_, 3, v___x_4587_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4592_, 4, v___x_4589_);
                    v___x_4591_ = v_reuseFailAlloc_4592_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_4591_;
            }
            92 => {
                v___x_4609_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4608_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4607_, 4, v_l_4555_);
                    crate::leanh::lean_ctor_set(v___x_4607_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v___x_4607_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v___x_4607_, 0, v___x_4466_);
                    v___x_4611_ = v___x_4607_;
                    state = 93;
                    continue;
                } else {
                    v_reuseFailAlloc_4615_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 3, v_l_4555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 4, v_l_4555_);
                    v___x_4611_ = v_reuseFailAlloc_4615_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                if v_isShared_3985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3984_, 4, v_r_4603_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 3, v___x_4611_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 2, v_v_4605_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 1, v_k_4604_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4609_);
                    v___x_4613_ = v___x_3984_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_4614_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4614_, 0, v___x_4609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4614_, 1, v_k_4604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4614_, 2, v_v_4605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4614_, 3, v___x_4611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4614_, 4, v_r_4603_);
                    v___x_4613_ = v_reuseFailAlloc_4614_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                return v___x_4613_;
            }
            95 => {
                if v_isShared_4625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4624_, 3, v_r_4603_);
                    v___x_4627_ = v___x_4624_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_4632_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_size_4620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4632_, 1, v_k_4621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4632_, 2, v_v_4622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4632_, 3, v_r_4603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4632_, 4, v_r_4603_);
                    v___x_4627_ = v_reuseFailAlloc_4632_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                v___x_4628_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_3985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3984_, 4, v___x_4627_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 3, v_r_4603_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_4628_);
                    v___x_4630_ = v___x_3984_;
                    state = 97;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 1, v_k_3979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 2, v_v_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 3, v_r_4603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 4, v___x_4627_);
                    v___x_4630_ = v_reuseFailAlloc_4631_;
                    state = 97;
                    continue;
                }
            }
            97 => {
                return v___x_4630_;
            }
            98 => {
                return v___x_4637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg___boxed(
    mut v_k_4641_: *mut crate::leanh::LeanObject,
    mut v_t_4642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_4643_: u64 = 0;
    let mut v_res_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_4643_ = crate::leanh::lean_unbox_uint64(v_k_4641_);
    crate::leanh::lean_dec_ref(v_k_4641_);
    v_res_4644_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_boxed_4643_, v_t_4642_);
    return v_res_4644_;
}
pub unsafe fn l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(
    mut v_h_4645_: u64,
    mut v_st_4646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4647_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_h_4645_, v_st_4646_);
    return v___x_4647_;
}
pub unsafe fn l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed(
    mut v_h_4648_: *mut crate::leanh::LeanObject,
    mut v_st_4649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_h_boxed_4650_: u64 = 0;
    let mut v_res_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_h_boxed_4650_ = crate::leanh::lean_unbox_uint64(v_h_4648_);
    crate::leanh::lean_dec_ref(v_h_4648_);
    v_res_4651_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0(v_h_boxed_4650_, v_st_4649_);
    return v_res_4651_;
}
pub unsafe fn _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4652_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4652_;
}
pub unsafe fn _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4653_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0_once), _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__0);
    v___x_4654_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4654_, 0, v___x_4653_);
    return v___x_4654_;
}
pub unsafe fn _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4655_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once), _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
    v___x_4656_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4656_, 0, v___x_4655_);
    crate::leanh::lean_ctor_set(v___x_4656_, 1, v___x_4655_);
    return v___x_4656_;
}
pub unsafe fn _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4657_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1_once), _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__1);
    v___x_4658_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4658_, 0, v___x_4657_);
    crate::leanh::lean_ctor_set(v___x_4658_, 1, v___x_4657_);
    crate::leanh::lean_ctor_set(v___x_4658_, 2, v___x_4657_);
    crate::leanh::lean_ctor_set(v___x_4658_, 3, v___x_4657_);
    crate::leanh::lean_ctor_set(v___x_4658_, 4, v___x_4657_);
    crate::leanh::lean_ctor_set(v___x_4658_, 5, v___x_4657_);
    return v___x_4658_;
}
pub unsafe fn l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(
    mut v_h_4659_: u64,
    mut v___y_4660_: *mut crate::leanh::LeanObject,
    mut v___y_4661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4674_: u8 = 0;
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4690_: u8 = 0;
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4698_: u8 = 0;
    let mut v_unused_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4701_: u8 = 0;
    let mut v_unused_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4663_ = lean_st_ref_take(v___y_4661_);
                v_env_4664_ = crate::leanh::lean_ctor_get(v___x_4663_, 0);
                v_nextMacroScope_4665_ = crate::leanh::lean_ctor_get(v___x_4663_, 1);
                v_ngen_4666_ = crate::leanh::lean_ctor_get(v___x_4663_, 2);
                v_auxDeclNGen_4667_ = crate::leanh::lean_ctor_get(v___x_4663_, 3);
                v_traceState_4668_ = crate::leanh::lean_ctor_get(v___x_4663_, 4);
                v_messages_4669_ = crate::leanh::lean_ctor_get(v___x_4663_, 6);
                v_infoState_4670_ = crate::leanh::lean_ctor_get(v___x_4663_, 7);
                v_snapshotTasks_4671_ = crate::leanh::lean_ctor_get(v___x_4663_, 8);
                v_isSharedCheck_4701_ = (!crate::leanh::lean_is_exclusive(v___x_4663_)) as u8;
                if v_isSharedCheck_4701_ == 0 {
                    v_unused_4702_ = crate::leanh::lean_ctor_get(v___x_4663_, 5);
                    crate::leanh::lean_dec(v_unused_4702_);
                    v___x_4673_ = v___x_4663_;
                    v_isShared_4674_ = v_isSharedCheck_4701_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4671_);
                    crate::leanh::lean_inc(v_infoState_4670_);
                    crate::leanh::lean_inc(v_messages_4669_);
                    crate::leanh::lean_inc(v_traceState_4668_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4667_);
                    crate::leanh::lean_inc(v_ngen_4666_);
                    crate::leanh::lean_inc(v_nextMacroScope_4665_);
                    crate::leanh::lean_inc(v_env_4664_);
                    crate::leanh::lean_dec(v___x_4663_);
                    v___x_4673_ = crate::leanh::lean_box(0);
                    v_isShared_4674_ = v_isSharedCheck_4701_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4675_ = crate::leanh::lean_box_uint64(v_h_4659_);
                v___f_4676_ = crate::leanh::lean_alloc_closure(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_4676_, 0, v___x_4675_);
                v___x_4677_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
                v___x_4678_ = l_Lean_ScopedEnvExtension_modifyState___redArg(
                    v___x_4677_,
                    v_env_4664_,
                    v___f_4676_,
                );
                v___x_4679_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once), _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
                if v_isShared_4674_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4673_, 5, v___x_4679_);
                    crate::leanh::lean_ctor_set(v___x_4673_, 0, v___x_4678_);
                    v___x_4681_ = v___x_4673_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4700_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 0, v___x_4678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 1, v_nextMacroScope_4665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 2, v_ngen_4666_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 3, v_auxDeclNGen_4667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 4, v_traceState_4668_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 5, v___x_4679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 6, v_messages_4669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 7, v_infoState_4670_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 8, v_snapshotTasks_4671_);
                    v___x_4681_ = v_reuseFailAlloc_4700_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4682_ = lean_st_ref_set(v___y_4661_, v___x_4681_);
                v___x_4683_ = lean_st_ref_take(v___y_4660_);
                v_mctx_4684_ = crate::leanh::lean_ctor_get(v___x_4683_, 0);
                v_zetaDeltaFVarIds_4685_ = crate::leanh::lean_ctor_get(v___x_4683_, 2);
                v_postponed_4686_ = crate::leanh::lean_ctor_get(v___x_4683_, 3);
                v_diag_4687_ = crate::leanh::lean_ctor_get(v___x_4683_, 4);
                v_isSharedCheck_4698_ = (!crate::leanh::lean_is_exclusive(v___x_4683_)) as u8;
                if v_isSharedCheck_4698_ == 0 {
                    v_unused_4699_ = crate::leanh::lean_ctor_get(v___x_4683_, 1);
                    crate::leanh::lean_dec(v_unused_4699_);
                    v___x_4689_ = v___x_4683_;
                    v_isShared_4690_ = v_isSharedCheck_4698_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4687_);
                    crate::leanh::lean_inc(v_postponed_4686_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4685_);
                    crate::leanh::lean_inc(v_mctx_4684_);
                    crate::leanh::lean_dec(v___x_4683_);
                    v___x_4689_ = crate::leanh::lean_box(0);
                    v_isShared_4690_ = v_isSharedCheck_4698_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4691_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once), _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
                if v_isShared_4690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4689_, 1, v___x_4691_);
                    v___x_4693_ = v___x_4689_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4697_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_mctx_4684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 1, v___x_4691_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4697_,
                        2,
                        v_zetaDeltaFVarIds_4685_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 3, v_postponed_4686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 4, v_diag_4687_);
                    v___x_4693_ = v_reuseFailAlloc_4697_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4694_ = lean_st_ref_set(v___y_4660_, v___x_4693_);
                v___x_4695_ = crate::leanh::lean_box(0);
                v___x_4696_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4696_, 0, v___x_4695_);
                return v___x_4696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___boxed(
    mut v_h_4703_: *mut crate::leanh::LeanObject,
    mut v___y_4704_: *mut crate::leanh::LeanObject,
    mut v___y_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_h_boxed_4707_: u64 = 0;
    let mut v_res_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_h_boxed_4707_ = crate::leanh::lean_unbox_uint64(v_h_4703_);
    crate::leanh::lean_dec_ref(v_h_4703_);
    v_res_4708_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_boxed_4707_, v___y_4704_, v___y_4705_);
    crate::leanh::lean_dec(v___y_4705_);
    crate::leanh::lean_dec(v___y_4704_);
    return v_res_4708_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(
    mut v_t_4709_: *mut crate::leanh::LeanObject,
    mut v_k_4710_: u64,
    mut v_fallback_4711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: u64 = 0;
    let mut v___x_4717_: u8 = 0;
    let mut v___x_4718_: u64 = 0;
    let mut v___x_4719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4709_) == 0 {
                    v_k_4712_ = crate::leanh::lean_ctor_get(v_t_4709_, 1);
                    v_v_4713_ = crate::leanh::lean_ctor_get(v_t_4709_, 2);
                    v_l_4714_ = crate::leanh::lean_ctor_get(v_t_4709_, 3);
                    v_r_4715_ = crate::leanh::lean_ctor_get(v_t_4709_, 4);
                    v___x_4716_ = crate::leanh::lean_unbox_uint64(v_k_4712_);
                    v___x_4717_ = lean_uint64_dec_lt(v_k_4710_, v___x_4716_);
                    if v___x_4717_ == 0 {
                        v___x_4718_ = crate::leanh::lean_unbox_uint64(v_k_4712_);
                        v___x_4719_ = lean_uint64_dec_eq(v_k_4710_, v___x_4718_);
                        if v___x_4719_ == 0 {
                            v_t_4709_ = v_r_4715_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_4713_);
                            return v_v_4713_;
                        }
                    } else {
                        v_t_4709_ = v_l_4714_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_fallback_4711_);
                    return v_fallback_4711_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg___boxed(
    mut v_t_4722_: *mut crate::leanh::LeanObject,
    mut v_k_4723_: *mut crate::leanh::LeanObject,
    mut v_fallback_4724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_4725_: u64 = 0;
    let mut v_res_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_4725_ = crate::leanh::lean_unbox_uint64(v_k_4723_);
    crate::leanh::lean_dec_ref(v_k_4723_);
    v_res_4726_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_4722_, v_k_boxed_4725_, v_fallback_4724_);
    crate::leanh::lean_dec(v_fallback_4724_);
    crate::leanh::lean_dec(v_t_4722_);
    return v_res_4726_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(
    mut v_k_4727_: u64,
    mut v_v_4728_: *mut crate::leanh::LeanObject,
    mut v_t_4729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4737_: u8 = 0;
    let mut v___x_4738_: u64 = 0;
    let mut v___x_4739_: u8 = 0;
    let mut v___x_4740_: u64 = 0;
    let mut v___x_4741_: u8 = 0;
    let mut v_impl_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: u8 = 0;
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4760_: u8 = 0;
    let mut v_size_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: u8 = 0;
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4772_: u8 = 0;
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4797_: u8 = 0;
    let mut v_unused_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4810_: u8 = 0;
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4814_: u8 = 0;
    let mut v_unused_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4821_: u8 = 0;
    let mut v_unused_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4833_: u8 = 0;
    let mut v_k_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4838_: u8 = 0;
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut v_unused_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4853_: u8 = 0;
    let mut v_unused_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4861_: u8 = 0;
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4869_: u8 = 0;
    let mut v_unused_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: u8 = 0;
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4899_: u8 = 0;
    let mut v_size_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: u8 = 0;
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4911_: u8 = 0;
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4937_: u8 = 0;
    let mut v_unused_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4951_: u8 = 0;
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4955_: u8 = 0;
    let mut v_unused_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4962_: u8 = 0;
    let mut v_unused_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4974_: u8 = 0;
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4982_: u8 = 0;
    let mut v_unused_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4990_: u8 = 0;
    let mut v_k_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4995_: u8 = 0;
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5006_: u8 = 0;
    let mut v_unused_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut v_unused_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5018_: u8 = 0;
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4729_) == 0 {
                    v_size_4730_ = crate::leanh::lean_ctor_get(v_t_4729_, 0);
                    v_k_4731_ = crate::leanh::lean_ctor_get(v_t_4729_, 1);
                    v_v_4732_ = crate::leanh::lean_ctor_get(v_t_4729_, 2);
                    v_l_4733_ = crate::leanh::lean_ctor_get(v_t_4729_, 3);
                    v_r_4734_ = crate::leanh::lean_ctor_get(v_t_4729_, 4);
                    v_isSharedCheck_5018_ = (!crate::leanh::lean_is_exclusive(v_t_4729_)) as u8;
                    if v_isSharedCheck_5018_ == 0 {
                        v___x_4736_ = v_t_4729_;
                        v_isShared_4737_ = v_isSharedCheck_5018_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_4734_);
                        crate::leanh::lean_inc(v_l_4733_);
                        crate::leanh::lean_inc(v_v_4732_);
                        crate::leanh::lean_inc(v_k_4731_);
                        crate::leanh::lean_inc(v_size_4730_);
                        crate::leanh::lean_dec(v_t_4729_);
                        v___x_4736_ = crate::leanh::lean_box(0);
                        v_isShared_4737_ = v_isSharedCheck_5018_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_5019_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5020_ = crate::leanh::lean_box_uint64(v_k_4727_);
                    v___x_5021_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5021_, 0, v___x_5019_);
                    crate::leanh::lean_ctor_set(v___x_5021_, 1, v___x_5020_);
                    crate::leanh::lean_ctor_set(v___x_5021_, 2, v_v_4728_);
                    crate::leanh::lean_ctor_set(v___x_5021_, 3, v_t_4729_);
                    crate::leanh::lean_ctor_set(v___x_5021_, 4, v_t_4729_);
                    return v___x_5021_;
                }
            }
            1 => {
                v___x_4738_ = crate::leanh::lean_unbox_uint64(v_k_4731_);
                v___x_4739_ = lean_uint64_dec_lt(v_k_4727_, v___x_4738_);
                if v___x_4739_ == 0 {
                    v___x_4740_ = crate::leanh::lean_unbox_uint64(v_k_4731_);
                    v___x_4741_ = lean_uint64_dec_eq(v_k_4727_, v___x_4740_);
                    if v___x_4741_ == 0 {
                        crate::leanh::lean_dec(v_size_4730_);
                        v_impl_4742_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_4727_, v_v_4728_, v_r_4734_);
                        v___x_4743_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_4733_) == 0 {
                            v_size_4744_ = crate::leanh::lean_ctor_get(v_l_4733_, 0);
                            v_size_4745_ = crate::leanh::lean_ctor_get(v_impl_4742_, 0);
                            crate::leanh::lean_inc(v_size_4745_);
                            v_k_4746_ = crate::leanh::lean_ctor_get(v_impl_4742_, 1);
                            crate::leanh::lean_inc(v_k_4746_);
                            v_v_4747_ = crate::leanh::lean_ctor_get(v_impl_4742_, 2);
                            crate::leanh::lean_inc(v_v_4747_);
                            v_l_4748_ = crate::leanh::lean_ctor_get(v_impl_4742_, 3);
                            crate::leanh::lean_inc(v_l_4748_);
                            v_r_4749_ = crate::leanh::lean_ctor_get(v_impl_4742_, 4);
                            crate::leanh::lean_inc(v_r_4749_);
                            v___x_4750_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_4751_ = lean_nat_mul(v___x_4750_, v_size_4744_);
                            v___x_4752_ = lean_nat_dec_lt(v___x_4751_, v_size_4745_);
                            crate::leanh::lean_dec(v___x_4751_);
                            if v___x_4752_ == 0 {
                                crate::leanh::lean_dec(v_r_4749_);
                                crate::leanh::lean_dec(v_l_4748_);
                                crate::leanh::lean_dec(v_v_4747_);
                                crate::leanh::lean_dec(v_k_4746_);
                                v___x_4753_ = lean_nat_add(v___x_4743_, v_size_4744_);
                                v___x_4754_ = lean_nat_add(v___x_4753_, v_size_4745_);
                                crate::leanh::lean_dec(v_size_4745_);
                                crate::leanh::lean_dec(v___x_4753_);
                                if v_isShared_4737_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_4736_, 4, v_impl_4742_);
                                    crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4754_);
                                    v___x_4756_ = v___x_4736_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4757_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4757_,
                                        0,
                                        v___x_4754_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4757_,
                                        1,
                                        v_k_4731_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4757_,
                                        2,
                                        v_v_4732_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4757_,
                                        3,
                                        v_l_4733_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4757_,
                                        4,
                                        v_impl_4742_,
                                    );
                                    v___x_4756_ = v_reuseFailAlloc_4757_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_4821_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_4742_)) as u8;
                                if v_isSharedCheck_4821_ == 0 {
                                    v_unused_4822_ = crate::leanh::lean_ctor_get(v_impl_4742_, 4);
                                    crate::leanh::lean_dec(v_unused_4822_);
                                    v_unused_4823_ = crate::leanh::lean_ctor_get(v_impl_4742_, 3);
                                    crate::leanh::lean_dec(v_unused_4823_);
                                    v_unused_4824_ = crate::leanh::lean_ctor_get(v_impl_4742_, 2);
                                    crate::leanh::lean_dec(v_unused_4824_);
                                    v_unused_4825_ = crate::leanh::lean_ctor_get(v_impl_4742_, 1);
                                    crate::leanh::lean_dec(v_unused_4825_);
                                    v_unused_4826_ = crate::leanh::lean_ctor_get(v_impl_4742_, 0);
                                    crate::leanh::lean_dec(v_unused_4826_);
                                    v___x_4759_ = v_impl_4742_;
                                    v_isShared_4760_ = v_isSharedCheck_4821_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_4742_);
                                    v___x_4759_ = crate::leanh::lean_box(0);
                                    v_isShared_4760_ = v_isSharedCheck_4821_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_4827_ = crate::leanh::lean_ctor_get(v_impl_4742_, 3);
                            crate::leanh::lean_inc(v_l_4827_);
                            if crate::leanh::lean_obj_tag(v_l_4827_) == 0 {
                                v_r_4828_ = crate::leanh::lean_ctor_get(v_impl_4742_, 4);
                                v_k_4829_ = crate::leanh::lean_ctor_get(v_impl_4742_, 1);
                                v_v_4830_ = crate::leanh::lean_ctor_get(v_impl_4742_, 2);
                                v_isSharedCheck_4853_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_4742_)) as u8;
                                if v_isSharedCheck_4853_ == 0 {
                                    v_unused_4854_ = crate::leanh::lean_ctor_get(v_impl_4742_, 3);
                                    crate::leanh::lean_dec(v_unused_4854_);
                                    v_unused_4855_ = crate::leanh::lean_ctor_get(v_impl_4742_, 0);
                                    crate::leanh::lean_dec(v_unused_4855_);
                                    v___x_4832_ = v_impl_4742_;
                                    v_isShared_4833_ = v_isSharedCheck_4853_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_4828_);
                                    crate::leanh::lean_inc(v_v_4830_);
                                    crate::leanh::lean_inc(v_k_4829_);
                                    crate::leanh::lean_dec(v_impl_4742_);
                                    v___x_4832_ = crate::leanh::lean_box(0);
                                    v_isShared_4833_ = v_isSharedCheck_4853_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_4856_ = crate::leanh::lean_ctor_get(v_impl_4742_, 4);
                                crate::leanh::lean_inc(v_r_4856_);
                                if crate::leanh::lean_obj_tag(v_r_4856_) == 0 {
                                    v_k_4857_ = crate::leanh::lean_ctor_get(v_impl_4742_, 1);
                                    v_v_4858_ = crate::leanh::lean_ctor_get(v_impl_4742_, 2);
                                    v_isSharedCheck_4869_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_4742_)) as u8;
                                    if v_isSharedCheck_4869_ == 0 {
                                        v_unused_4870_ =
                                            crate::leanh::lean_ctor_get(v_impl_4742_, 4);
                                        crate::leanh::lean_dec(v_unused_4870_);
                                        v_unused_4871_ =
                                            crate::leanh::lean_ctor_get(v_impl_4742_, 3);
                                        crate::leanh::lean_dec(v_unused_4871_);
                                        v_unused_4872_ =
                                            crate::leanh::lean_ctor_get(v_impl_4742_, 0);
                                        crate::leanh::lean_dec(v_unused_4872_);
                                        v___x_4860_ = v_impl_4742_;
                                        v_isShared_4861_ = v_isSharedCheck_4869_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_4858_);
                                        crate::leanh::lean_inc(v_k_4857_);
                                        crate::leanh::lean_dec(v_impl_4742_);
                                        v___x_4860_ = crate::leanh::lean_box(0);
                                        v_isShared_4861_ = v_isSharedCheck_4869_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_4873_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_4737_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_4736_, 4, v_impl_4742_);
                                        crate::leanh::lean_ctor_set(v___x_4736_, 3, v_r_4856_);
                                        crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4873_);
                                        v___x_4875_ = v___x_4736_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4876_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4876_,
                                            0,
                                            v___x_4873_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4876_,
                                            1,
                                            v_k_4731_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4876_,
                                            2,
                                            v_v_4732_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4876_,
                                            3,
                                            v_r_4856_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4876_,
                                            4,
                                            v_impl_4742_,
                                        );
                                        v___x_4875_ = v_reuseFailAlloc_4876_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_v_4732_);
                        crate::leanh::lean_dec(v_k_4731_);
                        v___x_4877_ = crate::leanh::lean_box_uint64(v_k_4727_);
                        if v_isShared_4737_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4736_, 2, v_v_4728_);
                            crate::leanh::lean_ctor_set(v___x_4736_, 1, v___x_4877_);
                            v___x_4879_ = v___x_4736_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_4880_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_size_4730_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4880_, 1, v___x_4877_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4880_, 2, v_v_4728_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4880_, 3, v_l_4733_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4880_, 4, v_r_4734_);
                            v___x_4879_ = v_reuseFailAlloc_4880_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_size_4730_);
                    v_impl_4881_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_4727_, v_v_4728_, v_l_4733_);
                    v___x_4882_ = crate::leanh::lean_unsigned_to_nat(1);
                    if crate::leanh::lean_obj_tag(v_r_4734_) == 0 {
                        v_size_4883_ = crate::leanh::lean_ctor_get(v_r_4734_, 0);
                        v_size_4884_ = crate::leanh::lean_ctor_get(v_impl_4881_, 0);
                        crate::leanh::lean_inc(v_size_4884_);
                        v_k_4885_ = crate::leanh::lean_ctor_get(v_impl_4881_, 1);
                        crate::leanh::lean_inc(v_k_4885_);
                        v_v_4886_ = crate::leanh::lean_ctor_get(v_impl_4881_, 2);
                        crate::leanh::lean_inc(v_v_4886_);
                        v_l_4887_ = crate::leanh::lean_ctor_get(v_impl_4881_, 3);
                        crate::leanh::lean_inc(v_l_4887_);
                        v_r_4888_ = crate::leanh::lean_ctor_get(v_impl_4881_, 4);
                        crate::leanh::lean_inc(v_r_4888_);
                        v___x_4889_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_4890_ = lean_nat_mul(v___x_4889_, v_size_4883_);
                        v___x_4891_ = lean_nat_dec_lt(v___x_4890_, v_size_4884_);
                        crate::leanh::lean_dec(v___x_4890_);
                        if v___x_4891_ == 0 {
                            crate::leanh::lean_dec(v_r_4888_);
                            crate::leanh::lean_dec(v_l_4887_);
                            crate::leanh::lean_dec(v_v_4886_);
                            crate::leanh::lean_dec(v_k_4885_);
                            v___x_4892_ = lean_nat_add(v___x_4882_, v_size_4884_);
                            crate::leanh::lean_dec(v_size_4884_);
                            v___x_4893_ = lean_nat_add(v___x_4892_, v_size_4883_);
                            crate::leanh::lean_dec(v___x_4892_);
                            if v_isShared_4737_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4736_, 3, v_impl_4881_);
                                crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4893_);
                                v___x_4895_ = v___x_4736_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_4896_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 1, v_k_4731_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 2, v_v_4732_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4896_,
                                    3,
                                    v_impl_4881_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 4, v_r_4734_);
                                v___x_4895_ = v_reuseFailAlloc_4896_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_4962_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_4881_)) as u8;
                            if v_isSharedCheck_4962_ == 0 {
                                v_unused_4963_ = crate::leanh::lean_ctor_get(v_impl_4881_, 4);
                                crate::leanh::lean_dec(v_unused_4963_);
                                v_unused_4964_ = crate::leanh::lean_ctor_get(v_impl_4881_, 3);
                                crate::leanh::lean_dec(v_unused_4964_);
                                v_unused_4965_ = crate::leanh::lean_ctor_get(v_impl_4881_, 2);
                                crate::leanh::lean_dec(v_unused_4965_);
                                v_unused_4966_ = crate::leanh::lean_ctor_get(v_impl_4881_, 1);
                                crate::leanh::lean_dec(v_unused_4966_);
                                v_unused_4967_ = crate::leanh::lean_ctor_get(v_impl_4881_, 0);
                                crate::leanh::lean_dec(v_unused_4967_);
                                v___x_4898_ = v_impl_4881_;
                                v_isShared_4899_ = v_isSharedCheck_4962_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_impl_4881_);
                                v___x_4898_ = crate::leanh::lean_box(0);
                                v_isShared_4899_ = v_isSharedCheck_4962_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_4968_ = crate::leanh::lean_ctor_get(v_impl_4881_, 3);
                        crate::leanh::lean_inc(v_l_4968_);
                        if crate::leanh::lean_obj_tag(v_l_4968_) == 0 {
                            v_r_4969_ = crate::leanh::lean_ctor_get(v_impl_4881_, 4);
                            v_k_4970_ = crate::leanh::lean_ctor_get(v_impl_4881_, 1);
                            v_v_4971_ = crate::leanh::lean_ctor_get(v_impl_4881_, 2);
                            v_isSharedCheck_4982_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_4881_)) as u8;
                            if v_isSharedCheck_4982_ == 0 {
                                v_unused_4983_ = crate::leanh::lean_ctor_get(v_impl_4881_, 3);
                                crate::leanh::lean_dec(v_unused_4983_);
                                v_unused_4984_ = crate::leanh::lean_ctor_get(v_impl_4881_, 0);
                                crate::leanh::lean_dec(v_unused_4984_);
                                v___x_4973_ = v_impl_4881_;
                                v_isShared_4974_ = v_isSharedCheck_4982_;
                                state = 34;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_r_4969_);
                                crate::leanh::lean_inc(v_v_4971_);
                                crate::leanh::lean_inc(v_k_4970_);
                                crate::leanh::lean_dec(v_impl_4881_);
                                v___x_4973_ = crate::leanh::lean_box(0);
                                v_isShared_4974_ = v_isSharedCheck_4982_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_4985_ = crate::leanh::lean_ctor_get(v_impl_4881_, 4);
                            crate::leanh::lean_inc(v_r_4985_);
                            if crate::leanh::lean_obj_tag(v_r_4985_) == 0 {
                                v_k_4986_ = crate::leanh::lean_ctor_get(v_impl_4881_, 1);
                                v_v_4987_ = crate::leanh::lean_ctor_get(v_impl_4881_, 2);
                                v_isSharedCheck_5010_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_4881_)) as u8;
                                if v_isSharedCheck_5010_ == 0 {
                                    v_unused_5011_ = crate::leanh::lean_ctor_get(v_impl_4881_, 4);
                                    crate::leanh::lean_dec(v_unused_5011_);
                                    v_unused_5012_ = crate::leanh::lean_ctor_get(v_impl_4881_, 3);
                                    crate::leanh::lean_dec(v_unused_5012_);
                                    v_unused_5013_ = crate::leanh::lean_ctor_get(v_impl_4881_, 0);
                                    crate::leanh::lean_dec(v_unused_5013_);
                                    v___x_4989_ = v_impl_4881_;
                                    v_isShared_4990_ = v_isSharedCheck_5010_;
                                    state = 37;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_v_4987_);
                                    crate::leanh::lean_inc(v_k_4986_);
                                    crate::leanh::lean_dec(v_impl_4881_);
                                    v___x_4989_ = crate::leanh::lean_box(0);
                                    v_isShared_4990_ = v_isSharedCheck_5010_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_5014_ = crate::leanh::lean_unsigned_to_nat(2);
                                if v_isShared_4737_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_4736_, 4, v_r_4985_);
                                    crate::leanh::lean_ctor_set(v___x_4736_, 3, v_impl_4881_);
                                    crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_5014_);
                                    v___x_5016_ = v___x_4736_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5017_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5017_,
                                        0,
                                        v___x_5014_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5017_,
                                        1,
                                        v_k_4731_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5017_,
                                        2,
                                        v_v_4732_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5017_,
                                        3,
                                        v_impl_4881_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5017_,
                                        4,
                                        v_r_4985_,
                                    );
                                    v___x_5016_ = v_reuseFailAlloc_5017_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_4756_;
            }
            3 => {
                v_size_4761_ = crate::leanh::lean_ctor_get(v_l_4748_, 0);
                v_k_4762_ = crate::leanh::lean_ctor_get(v_l_4748_, 1);
                v_v_4763_ = crate::leanh::lean_ctor_get(v_l_4748_, 2);
                v_l_4764_ = crate::leanh::lean_ctor_get(v_l_4748_, 3);
                v_r_4765_ = crate::leanh::lean_ctor_get(v_l_4748_, 4);
                v_size_4766_ = crate::leanh::lean_ctor_get(v_r_4749_, 0);
                v___x_4767_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4768_ = lean_nat_mul(v___x_4767_, v_size_4766_);
                v___x_4769_ = lean_nat_dec_lt(v_size_4761_, v___x_4768_);
                crate::leanh::lean_dec(v___x_4768_);
                if v___x_4769_ == 0 {
                    crate::leanh::lean_inc(v_r_4765_);
                    crate::leanh::lean_inc(v_l_4764_);
                    crate::leanh::lean_inc(v_v_4763_);
                    crate::leanh::lean_inc(v_k_4762_);
                    v_isSharedCheck_4797_ = (!crate::leanh::lean_is_exclusive(v_l_4748_)) as u8;
                    if v_isSharedCheck_4797_ == 0 {
                        v_unused_4798_ = crate::leanh::lean_ctor_get(v_l_4748_, 4);
                        crate::leanh::lean_dec(v_unused_4798_);
                        v_unused_4799_ = crate::leanh::lean_ctor_get(v_l_4748_, 3);
                        crate::leanh::lean_dec(v_unused_4799_);
                        v_unused_4800_ = crate::leanh::lean_ctor_get(v_l_4748_, 2);
                        crate::leanh::lean_dec(v_unused_4800_);
                        v_unused_4801_ = crate::leanh::lean_ctor_get(v_l_4748_, 1);
                        crate::leanh::lean_dec(v_unused_4801_);
                        v_unused_4802_ = crate::leanh::lean_ctor_get(v_l_4748_, 0);
                        crate::leanh::lean_dec(v_unused_4802_);
                        v___x_4771_ = v_l_4748_;
                        v_isShared_4772_ = v_isSharedCheck_4797_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_4748_);
                        v___x_4771_ = crate::leanh::lean_box(0);
                        v_isShared_4772_ = v_isSharedCheck_4797_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4736_);
                    v___x_4803_ = lean_nat_add(v___x_4743_, v_size_4744_);
                    v___x_4804_ = lean_nat_add(v___x_4803_, v_size_4745_);
                    crate::leanh::lean_dec(v_size_4745_);
                    v___x_4805_ = lean_nat_add(v___x_4803_, v_size_4761_);
                    crate::leanh::lean_dec(v___x_4803_);
                    crate::leanh::lean_inc_ref(v_l_4733_);
                    if v_isShared_4760_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4759_, 4, v_l_4748_);
                        crate::leanh::lean_ctor_set(v___x_4759_, 3, v_l_4733_);
                        crate::leanh::lean_ctor_set(v___x_4759_, 2, v_v_4732_);
                        crate::leanh::lean_ctor_set(v___x_4759_, 1, v_k_4731_);
                        crate::leanh::lean_ctor_set(v___x_4759_, 0, v___x_4805_);
                        v___x_4807_ = v___x_4759_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4820_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4805_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4820_, 1, v_k_4731_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4820_, 2, v_v_4732_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4820_, 3, v_l_4733_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4820_, 4, v_l_4748_);
                        v___x_4807_ = v_reuseFailAlloc_4820_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4773_ = lean_nat_add(v___x_4743_, v_size_4744_);
                v___x_4774_ = lean_nat_add(v___x_4773_, v_size_4745_);
                crate::leanh::lean_dec(v_size_4745_);
                if crate::leanh::lean_obj_tag(v_l_4764_) == 0 {
                    v_size_4795_ = crate::leanh::lean_ctor_get(v_l_4764_, 0);
                    crate::leanh::lean_inc(v_size_4795_);
                    v___y_4787_ = v_size_4795_;
                    state = 8;
                    continue;
                } else {
                    v___x_4796_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4787_ = v___x_4796_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_4779_ = lean_nat_add(v___y_4776_, v___y_4778_);
                crate::leanh::lean_dec(v___y_4778_);
                crate::leanh::lean_dec(v___y_4776_);
                if v_isShared_4772_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4771_, 4, v_r_4749_);
                    crate::leanh::lean_ctor_set(v___x_4771_, 3, v_r_4765_);
                    crate::leanh::lean_ctor_set(v___x_4771_, 2, v_v_4747_);
                    crate::leanh::lean_ctor_set(v___x_4771_, 1, v_k_4746_);
                    crate::leanh::lean_ctor_set(v___x_4771_, 0, v___x_4779_);
                    v___x_4781_ = v___x_4771_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4785_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_k_4746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 2, v_v_4747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 3, v_r_4765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 4, v_r_4749_);
                    v___x_4781_ = v_reuseFailAlloc_4785_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4760_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4759_, 4, v___x_4781_);
                    crate::leanh::lean_ctor_set(v___x_4759_, 3, v___y_4777_);
                    crate::leanh::lean_ctor_set(v___x_4759_, 2, v_v_4763_);
                    crate::leanh::lean_ctor_set(v___x_4759_, 1, v_k_4762_);
                    crate::leanh::lean_ctor_set(v___x_4759_, 0, v___x_4774_);
                    v___x_4783_ = v___x_4759_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4784_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4784_, 1, v_k_4762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4784_, 2, v_v_4763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4784_, 3, v___y_4777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4784_, 4, v___x_4781_);
                    v___x_4783_ = v_reuseFailAlloc_4784_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4783_;
            }
            8 => {
                v___x_4788_ = lean_nat_add(v___x_4773_, v___y_4787_);
                crate::leanh::lean_dec(v___y_4787_);
                crate::leanh::lean_dec(v___x_4773_);
                if v_isShared_4737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4736_, 4, v_l_4764_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4788_);
                    v___x_4790_ = v___x_4736_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4794_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4794_, 1, v_k_4731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4794_, 2, v_v_4732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4794_, 3, v_l_4733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4794_, 4, v_l_4764_);
                    v___x_4790_ = v_reuseFailAlloc_4794_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4791_ = lean_nat_add(v___x_4743_, v_size_4766_);
                if crate::leanh::lean_obj_tag(v_r_4765_) == 0 {
                    v_size_4792_ = crate::leanh::lean_ctor_get(v_r_4765_, 0);
                    crate::leanh::lean_inc(v_size_4792_);
                    v___y_4776_ = v___x_4791_;
                    v___y_4777_ = v___x_4790_;
                    v___y_4778_ = v_size_4792_;
                    state = 5;
                    continue;
                } else {
                    v___x_4793_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4776_ = v___x_4791_;
                    v___y_4777_ = v___x_4790_;
                    v___y_4778_ = v___x_4793_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_4814_ = (!crate::leanh::lean_is_exclusive(v_l_4733_)) as u8;
                if v_isSharedCheck_4814_ == 0 {
                    v_unused_4815_ = crate::leanh::lean_ctor_get(v_l_4733_, 4);
                    crate::leanh::lean_dec(v_unused_4815_);
                    v_unused_4816_ = crate::leanh::lean_ctor_get(v_l_4733_, 3);
                    crate::leanh::lean_dec(v_unused_4816_);
                    v_unused_4817_ = crate::leanh::lean_ctor_get(v_l_4733_, 2);
                    crate::leanh::lean_dec(v_unused_4817_);
                    v_unused_4818_ = crate::leanh::lean_ctor_get(v_l_4733_, 1);
                    crate::leanh::lean_dec(v_unused_4818_);
                    v_unused_4819_ = crate::leanh::lean_ctor_get(v_l_4733_, 0);
                    crate::leanh::lean_dec(v_unused_4819_);
                    v___x_4809_ = v_l_4733_;
                    v_isShared_4810_ = v_isSharedCheck_4814_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_4733_);
                    v___x_4809_ = crate::leanh::lean_box(0);
                    v_isShared_4810_ = v_isSharedCheck_4814_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4810_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4809_, 4, v_r_4749_);
                    crate::leanh::lean_ctor_set(v___x_4809_, 3, v___x_4807_);
                    crate::leanh::lean_ctor_set(v___x_4809_, 2, v_v_4747_);
                    crate::leanh::lean_ctor_set(v___x_4809_, 1, v_k_4746_);
                    crate::leanh::lean_ctor_set(v___x_4809_, 0, v___x_4804_);
                    v___x_4812_ = v___x_4809_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4813_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4813_, 1, v_k_4746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4813_, 2, v_v_4747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4813_, 3, v___x_4807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4813_, 4, v_r_4749_);
                    v___x_4812_ = v_reuseFailAlloc_4813_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4812_;
            }
            13 => {
                v_k_4834_ = crate::leanh::lean_ctor_get(v_l_4827_, 1);
                v_v_4835_ = crate::leanh::lean_ctor_get(v_l_4827_, 2);
                v_isSharedCheck_4849_ = (!crate::leanh::lean_is_exclusive(v_l_4827_)) as u8;
                if v_isSharedCheck_4849_ == 0 {
                    v_unused_4850_ = crate::leanh::lean_ctor_get(v_l_4827_, 4);
                    crate::leanh::lean_dec(v_unused_4850_);
                    v_unused_4851_ = crate::leanh::lean_ctor_get(v_l_4827_, 3);
                    crate::leanh::lean_dec(v_unused_4851_);
                    v_unused_4852_ = crate::leanh::lean_ctor_get(v_l_4827_, 0);
                    crate::leanh::lean_dec(v_unused_4852_);
                    v___x_4837_ = v_l_4827_;
                    v_isShared_4838_ = v_isSharedCheck_4849_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_4835_);
                    crate::leanh::lean_inc(v_k_4834_);
                    crate::leanh::lean_dec(v_l_4827_);
                    v___x_4837_ = crate::leanh::lean_box(0);
                    v_isShared_4838_ = v_isSharedCheck_4849_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4839_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_4828_, 2);
                if v_isShared_4838_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4837_, 4, v_r_4828_);
                    crate::leanh::lean_ctor_set(v___x_4837_, 3, v_r_4828_);
                    crate::leanh::lean_ctor_set(v___x_4837_, 2, v_v_4732_);
                    crate::leanh::lean_ctor_set(v___x_4837_, 1, v_k_4731_);
                    crate::leanh::lean_ctor_set(v___x_4837_, 0, v___x_4743_);
                    v___x_4841_ = v___x_4837_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4848_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 1, v_k_4731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 2, v_v_4732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 3, v_r_4828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 4, v_r_4828_);
                    v___x_4841_ = v_reuseFailAlloc_4848_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_inc(v_r_4828_);
                if v_isShared_4833_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4832_, 3, v_r_4828_);
                    crate::leanh::lean_ctor_set(v___x_4832_, 0, v___x_4743_);
                    v___x_4843_ = v___x_4832_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4847_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 1, v_k_4829_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 2, v_v_4830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 3, v_r_4828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 4, v_r_4828_);
                    v___x_4843_ = v_reuseFailAlloc_4847_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_4737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4736_, 4, v___x_4843_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 3, v___x_4841_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 2, v_v_4835_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 1, v_k_4834_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4839_);
                    v___x_4845_ = v___x_4736_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4846_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4846_, 1, v_k_4834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4846_, 2, v_v_4835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4846_, 3, v___x_4841_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4846_, 4, v___x_4843_);
                    v___x_4845_ = v_reuseFailAlloc_4846_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4845_;
            }
            18 => {
                v___x_4862_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4861_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4860_, 4, v_l_4827_);
                    crate::leanh::lean_ctor_set(v___x_4860_, 2, v_v_4732_);
                    crate::leanh::lean_ctor_set(v___x_4860_, 1, v_k_4731_);
                    crate::leanh::lean_ctor_set(v___x_4860_, 0, v___x_4743_);
                    v___x_4864_ = v___x_4860_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4868_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4868_, 1, v_k_4731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4868_, 2, v_v_4732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4868_, 3, v_l_4827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4868_, 4, v_l_4827_);
                    v___x_4864_ = v_reuseFailAlloc_4868_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4736_, 4, v_r_4856_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 3, v___x_4864_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 2, v_v_4858_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 1, v_k_4857_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4862_);
                    v___x_4866_ = v___x_4736_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4867_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4867_, 1, v_k_4857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4867_, 2, v_v_4858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4867_, 3, v___x_4864_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4867_, 4, v_r_4856_);
                    v___x_4866_ = v_reuseFailAlloc_4867_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4866_;
            }
            21 => {
                return v___x_4875_;
            }
            22 => {
                return v___x_4879_;
            }
            23 => {
                return v___x_4895_;
            }
            24 => {
                v_size_4900_ = crate::leanh::lean_ctor_get(v_l_4887_, 0);
                v_size_4901_ = crate::leanh::lean_ctor_get(v_r_4888_, 0);
                v_k_4902_ = crate::leanh::lean_ctor_get(v_r_4888_, 1);
                v_v_4903_ = crate::leanh::lean_ctor_get(v_r_4888_, 2);
                v_l_4904_ = crate::leanh::lean_ctor_get(v_r_4888_, 3);
                v_r_4905_ = crate::leanh::lean_ctor_get(v_r_4888_, 4);
                v___x_4906_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4907_ = lean_nat_mul(v___x_4906_, v_size_4900_);
                v___x_4908_ = lean_nat_dec_lt(v_size_4901_, v___x_4907_);
                crate::leanh::lean_dec(v___x_4907_);
                if v___x_4908_ == 0 {
                    crate::leanh::lean_inc(v_r_4905_);
                    crate::leanh::lean_inc(v_l_4904_);
                    crate::leanh::lean_inc(v_v_4903_);
                    crate::leanh::lean_inc(v_k_4902_);
                    v_isSharedCheck_4937_ = (!crate::leanh::lean_is_exclusive(v_r_4888_)) as u8;
                    if v_isSharedCheck_4937_ == 0 {
                        v_unused_4938_ = crate::leanh::lean_ctor_get(v_r_4888_, 4);
                        crate::leanh::lean_dec(v_unused_4938_);
                        v_unused_4939_ = crate::leanh::lean_ctor_get(v_r_4888_, 3);
                        crate::leanh::lean_dec(v_unused_4939_);
                        v_unused_4940_ = crate::leanh::lean_ctor_get(v_r_4888_, 2);
                        crate::leanh::lean_dec(v_unused_4940_);
                        v_unused_4941_ = crate::leanh::lean_ctor_get(v_r_4888_, 1);
                        crate::leanh::lean_dec(v_unused_4941_);
                        v_unused_4942_ = crate::leanh::lean_ctor_get(v_r_4888_, 0);
                        crate::leanh::lean_dec(v_unused_4942_);
                        v___x_4910_ = v_r_4888_;
                        v_isShared_4911_ = v_isSharedCheck_4937_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_4888_);
                        v___x_4910_ = crate::leanh::lean_box(0);
                        v_isShared_4911_ = v_isSharedCheck_4937_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4736_);
                    v___x_4943_ = lean_nat_add(v___x_4882_, v_size_4884_);
                    crate::leanh::lean_dec(v_size_4884_);
                    v___x_4944_ = lean_nat_add(v___x_4943_, v_size_4883_);
                    crate::leanh::lean_dec(v___x_4943_);
                    v___x_4945_ = lean_nat_add(v___x_4882_, v_size_4883_);
                    v___x_4946_ = lean_nat_add(v___x_4945_, v_size_4901_);
                    crate::leanh::lean_dec(v___x_4945_);
                    crate::leanh::lean_inc_ref(v_r_4734_);
                    if v_isShared_4899_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4898_, 4, v_r_4734_);
                        crate::leanh::lean_ctor_set(v___x_4898_, 3, v_r_4888_);
                        crate::leanh::lean_ctor_set(v___x_4898_, 2, v_v_4732_);
                        crate::leanh::lean_ctor_set(v___x_4898_, 1, v_k_4731_);
                        crate::leanh::lean_ctor_set(v___x_4898_, 0, v___x_4946_);
                        v___x_4948_ = v___x_4898_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_4961_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4961_, 0, v___x_4946_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4961_, 1, v_k_4731_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4961_, 2, v_v_4732_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4961_, 3, v_r_4888_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4961_, 4, v_r_4734_);
                        v___x_4948_ = v_reuseFailAlloc_4961_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_4912_ = lean_nat_add(v___x_4882_, v_size_4884_);
                crate::leanh::lean_dec(v_size_4884_);
                v___x_4913_ = lean_nat_add(v___x_4912_, v_size_4883_);
                crate::leanh::lean_dec(v___x_4912_);
                v___x_4925_ = lean_nat_add(v___x_4882_, v_size_4900_);
                if crate::leanh::lean_obj_tag(v_l_4904_) == 0 {
                    v_size_4935_ = crate::leanh::lean_ctor_get(v_l_4904_, 0);
                    crate::leanh::lean_inc(v_size_4935_);
                    v___y_4927_ = v_size_4935_;
                    state = 29;
                    continue;
                } else {
                    v___x_4936_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4927_ = v___x_4936_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_4918_ = lean_nat_add(v___y_4916_, v___y_4917_);
                crate::leanh::lean_dec(v___y_4917_);
                crate::leanh::lean_dec(v___y_4916_);
                if v_isShared_4911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4910_, 4, v_r_4734_);
                    crate::leanh::lean_ctor_set(v___x_4910_, 3, v_r_4905_);
                    crate::leanh::lean_ctor_set(v___x_4910_, 2, v_v_4732_);
                    crate::leanh::lean_ctor_set(v___x_4910_, 1, v_k_4731_);
                    crate::leanh::lean_ctor_set(v___x_4910_, 0, v___x_4918_);
                    v___x_4920_ = v___x_4910_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4924_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4924_, 1, v_k_4731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4924_, 2, v_v_4732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4924_, 3, v_r_4905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4924_, 4, v_r_4734_);
                    v___x_4920_ = v_reuseFailAlloc_4924_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_4899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4898_, 4, v___x_4920_);
                    crate::leanh::lean_ctor_set(v___x_4898_, 3, v___y_4915_);
                    crate::leanh::lean_ctor_set(v___x_4898_, 2, v_v_4903_);
                    crate::leanh::lean_ctor_set(v___x_4898_, 1, v_k_4902_);
                    crate::leanh::lean_ctor_set(v___x_4898_, 0, v___x_4913_);
                    v___x_4922_ = v___x_4898_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4923_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 0, v___x_4913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 1, v_k_4902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 2, v_v_4903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 3, v___y_4915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 4, v___x_4920_);
                    v___x_4922_ = v_reuseFailAlloc_4923_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4922_;
            }
            29 => {
                v___x_4928_ = lean_nat_add(v___x_4925_, v___y_4927_);
                crate::leanh::lean_dec(v___y_4927_);
                crate::leanh::lean_dec(v___x_4925_);
                if v_isShared_4737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4736_, 4, v_l_4904_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 3, v_l_4887_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 2, v_v_4886_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 1, v_k_4885_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4928_);
                    v___x_4930_ = v___x_4736_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4934_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 1, v_k_4885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 2, v_v_4886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 3, v_l_4887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 4, v_l_4904_);
                    v___x_4930_ = v_reuseFailAlloc_4934_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_4931_ = lean_nat_add(v___x_4882_, v_size_4883_);
                if crate::leanh::lean_obj_tag(v_r_4905_) == 0 {
                    v_size_4932_ = crate::leanh::lean_ctor_get(v_r_4905_, 0);
                    crate::leanh::lean_inc(v_size_4932_);
                    v___y_4915_ = v___x_4930_;
                    v___y_4916_ = v___x_4931_;
                    v___y_4917_ = v_size_4932_;
                    state = 26;
                    continue;
                } else {
                    v___x_4933_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4915_ = v___x_4930_;
                    v___y_4916_ = v___x_4931_;
                    v___y_4917_ = v___x_4933_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_4955_ = (!crate::leanh::lean_is_exclusive(v_r_4734_)) as u8;
                if v_isSharedCheck_4955_ == 0 {
                    v_unused_4956_ = crate::leanh::lean_ctor_get(v_r_4734_, 4);
                    crate::leanh::lean_dec(v_unused_4956_);
                    v_unused_4957_ = crate::leanh::lean_ctor_get(v_r_4734_, 3);
                    crate::leanh::lean_dec(v_unused_4957_);
                    v_unused_4958_ = crate::leanh::lean_ctor_get(v_r_4734_, 2);
                    crate::leanh::lean_dec(v_unused_4958_);
                    v_unused_4959_ = crate::leanh::lean_ctor_get(v_r_4734_, 1);
                    crate::leanh::lean_dec(v_unused_4959_);
                    v_unused_4960_ = crate::leanh::lean_ctor_get(v_r_4734_, 0);
                    crate::leanh::lean_dec(v_unused_4960_);
                    v___x_4950_ = v_r_4734_;
                    v_isShared_4951_ = v_isSharedCheck_4955_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_4734_);
                    v___x_4950_ = crate::leanh::lean_box(0);
                    v_isShared_4951_ = v_isSharedCheck_4955_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_4951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4950_, 4, v___x_4948_);
                    crate::leanh::lean_ctor_set(v___x_4950_, 3, v_l_4887_);
                    crate::leanh::lean_ctor_set(v___x_4950_, 2, v_v_4886_);
                    crate::leanh::lean_ctor_set(v___x_4950_, 1, v_k_4885_);
                    crate::leanh::lean_ctor_set(v___x_4950_, 0, v___x_4944_);
                    v___x_4953_ = v___x_4950_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4954_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4954_, 0, v___x_4944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4954_, 1, v_k_4885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4954_, 2, v_v_4886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4954_, 3, v_l_4887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4954_, 4, v___x_4948_);
                    v___x_4953_ = v_reuseFailAlloc_4954_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4953_;
            }
            34 => {
                v___x_4975_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_4969_);
                if v_isShared_4974_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4973_, 3, v_r_4969_);
                    crate::leanh::lean_ctor_set(v___x_4973_, 2, v_v_4732_);
                    crate::leanh::lean_ctor_set(v___x_4973_, 1, v_k_4731_);
                    crate::leanh::lean_ctor_set(v___x_4973_, 0, v___x_4882_);
                    v___x_4977_ = v___x_4973_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4981_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 0, v___x_4882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 1, v_k_4731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 2, v_v_4732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 3, v_r_4969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 4, v_r_4969_);
                    v___x_4977_ = v_reuseFailAlloc_4981_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_4737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4736_, 4, v___x_4977_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 3, v_l_4968_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 2, v_v_4971_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 1, v_k_4970_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4975_);
                    v___x_4979_ = v___x_4736_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4980_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 1, v_k_4970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 2, v_v_4971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 3, v_l_4968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 4, v___x_4977_);
                    v___x_4979_ = v_reuseFailAlloc_4980_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_4979_;
            }
            37 => {
                v_k_4991_ = crate::leanh::lean_ctor_get(v_r_4985_, 1);
                v_v_4992_ = crate::leanh::lean_ctor_get(v_r_4985_, 2);
                v_isSharedCheck_5006_ = (!crate::leanh::lean_is_exclusive(v_r_4985_)) as u8;
                if v_isSharedCheck_5006_ == 0 {
                    v_unused_5007_ = crate::leanh::lean_ctor_get(v_r_4985_, 4);
                    crate::leanh::lean_dec(v_unused_5007_);
                    v_unused_5008_ = crate::leanh::lean_ctor_get(v_r_4985_, 3);
                    crate::leanh::lean_dec(v_unused_5008_);
                    v_unused_5009_ = crate::leanh::lean_ctor_get(v_r_4985_, 0);
                    crate::leanh::lean_dec(v_unused_5009_);
                    v___x_4994_ = v_r_4985_;
                    v_isShared_4995_ = v_isSharedCheck_5006_;
                    state = 38;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_4992_);
                    crate::leanh::lean_inc(v_k_4991_);
                    crate::leanh::lean_dec(v_r_4985_);
                    v___x_4994_ = crate::leanh::lean_box(0);
                    v_isShared_4995_ = v_isSharedCheck_5006_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_4996_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4995_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4994_, 4, v_l_4968_);
                    crate::leanh::lean_ctor_set(v___x_4994_, 3, v_l_4968_);
                    crate::leanh::lean_ctor_set(v___x_4994_, 2, v_v_4987_);
                    crate::leanh::lean_ctor_set(v___x_4994_, 1, v_k_4986_);
                    crate::leanh::lean_ctor_set(v___x_4994_, 0, v___x_4882_);
                    v___x_4998_ = v___x_4994_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_5005_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 0, v___x_4882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 1, v_k_4986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 2, v_v_4987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 3, v_l_4968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 4, v_l_4968_);
                    v___x_4998_ = v_reuseFailAlloc_5005_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_4990_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4989_, 4, v_l_4968_);
                    crate::leanh::lean_ctor_set(v___x_4989_, 2, v_v_4732_);
                    crate::leanh::lean_ctor_set(v___x_4989_, 1, v_k_4731_);
                    crate::leanh::lean_ctor_set(v___x_4989_, 0, v___x_4882_);
                    v___x_5000_ = v___x_4989_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5004_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_4882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 1, v_k_4731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 2, v_v_4732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 3, v_l_4968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 4, v_l_4968_);
                    v___x_5000_ = v_reuseFailAlloc_5004_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_4737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4736_, 4, v___x_5000_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 3, v___x_4998_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 2, v_v_4992_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 1, v_k_4991_);
                    crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4996_);
                    v___x_5002_ = v___x_4736_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5003_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5003_, 0, v___x_4996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5003_, 1, v_k_4991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5003_, 2, v_v_4992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5003_, 3, v___x_4998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5003_, 4, v___x_5000_);
                    v___x_5002_ = v_reuseFailAlloc_5003_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_5002_;
            }
            42 => {
                return v___x_5016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg___boxed(
    mut v_k_5022_: *mut crate::leanh::LeanObject,
    mut v_v_5023_: *mut crate::leanh::LeanObject,
    mut v_t_5024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_5025_: u64 = 0;
    let mut v_res_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_5025_ = crate::leanh::lean_unbox_uint64(v_k_5022_);
    crate::leanh::lean_dec_ref(v_k_5022_);
    v_res_5026_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_boxed_5025_, v_v_5023_, v_t_5024_);
    return v_res_5026_;
}
pub unsafe fn l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0(
    mut v_wi_5027_: *mut crate::leanh::LeanObject,
    mut v_s_5028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_javascriptHash_5029_: u64 = 0;
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_javascriptHash_5029_ = crate::leanh::lean_ctor_get_uint64(
        v_wi_5027_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    v___x_5030_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5030_, 0, v_wi_5027_);
    v___x_5031_ = crate::leanh::lean_box(0);
    v___x_5032_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_s_5028_, v_javascriptHash_5029_, v___x_5031_);
    v___x_5033_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5033_, 0, v___x_5030_);
    crate::leanh::lean_ctor_set(v___x_5033_, 1, v___x_5032_);
    v___x_5034_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_javascriptHash_5029_, v___x_5033_, v_s_5028_);
    return v___x_5034_;
}
pub unsafe fn l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(
    mut v_wi_5035_: *mut crate::leanh::LeanObject,
    mut v___y_5036_: *mut crate::leanh::LeanObject,
    mut v___y_5037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5050_: u8 = 0;
    let mut v___f_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5065_: u8 = 0;
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5073_: u8 = 0;
    let mut v_unused_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5076_: u8 = 0;
    let mut v_unused_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5039_ = lean_st_ref_take(v___y_5037_);
                v_env_5040_ = crate::leanh::lean_ctor_get(v___x_5039_, 0);
                v_nextMacroScope_5041_ = crate::leanh::lean_ctor_get(v___x_5039_, 1);
                v_ngen_5042_ = crate::leanh::lean_ctor_get(v___x_5039_, 2);
                v_auxDeclNGen_5043_ = crate::leanh::lean_ctor_get(v___x_5039_, 3);
                v_traceState_5044_ = crate::leanh::lean_ctor_get(v___x_5039_, 4);
                v_messages_5045_ = crate::leanh::lean_ctor_get(v___x_5039_, 6);
                v_infoState_5046_ = crate::leanh::lean_ctor_get(v___x_5039_, 7);
                v_snapshotTasks_5047_ = crate::leanh::lean_ctor_get(v___x_5039_, 8);
                v_isSharedCheck_5076_ = (!crate::leanh::lean_is_exclusive(v___x_5039_)) as u8;
                if v_isSharedCheck_5076_ == 0 {
                    v_unused_5077_ = crate::leanh::lean_ctor_get(v___x_5039_, 5);
                    crate::leanh::lean_dec(v_unused_5077_);
                    v___x_5049_ = v___x_5039_;
                    v_isShared_5050_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5047_);
                    crate::leanh::lean_inc(v_infoState_5046_);
                    crate::leanh::lean_inc(v_messages_5045_);
                    crate::leanh::lean_inc(v_traceState_5044_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5043_);
                    crate::leanh::lean_inc(v_ngen_5042_);
                    crate::leanh::lean_inc(v_nextMacroScope_5041_);
                    crate::leanh::lean_inc(v_env_5040_);
                    crate::leanh::lean_dec(v___x_5039_);
                    v___x_5049_ = crate::leanh::lean_box(0);
                    v_isShared_5050_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_5051_ = crate::leanh::lean_alloc_closure(l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_5051_, 0, v_wi_5035_);
                v___x_5052_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
                v___x_5053_ = l_Lean_ScopedEnvExtension_modifyState___redArg(
                    v___x_5052_,
                    v_env_5040_,
                    v___f_5051_,
                );
                v___x_5054_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once), _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
                if v_isShared_5050_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5049_, 5, v___x_5054_);
                    crate::leanh::lean_ctor_set(v___x_5049_, 0, v___x_5053_);
                    v___x_5056_ = v___x_5049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5075_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 0, v___x_5053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 1, v_nextMacroScope_5041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 2, v_ngen_5042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 3, v_auxDeclNGen_5043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 4, v_traceState_5044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 5, v___x_5054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 6, v_messages_5045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 7, v_infoState_5046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 8, v_snapshotTasks_5047_);
                    v___x_5056_ = v_reuseFailAlloc_5075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5057_ = lean_st_ref_set(v___y_5037_, v___x_5056_);
                v___x_5058_ = lean_st_ref_take(v___y_5036_);
                v_mctx_5059_ = crate::leanh::lean_ctor_get(v___x_5058_, 0);
                v_zetaDeltaFVarIds_5060_ = crate::leanh::lean_ctor_get(v___x_5058_, 2);
                v_postponed_5061_ = crate::leanh::lean_ctor_get(v___x_5058_, 3);
                v_diag_5062_ = crate::leanh::lean_ctor_get(v___x_5058_, 4);
                v_isSharedCheck_5073_ = (!crate::leanh::lean_is_exclusive(v___x_5058_)) as u8;
                if v_isSharedCheck_5073_ == 0 {
                    v_unused_5074_ = crate::leanh::lean_ctor_get(v___x_5058_, 1);
                    crate::leanh::lean_dec(v_unused_5074_);
                    v___x_5064_ = v___x_5058_;
                    v_isShared_5065_ = v_isSharedCheck_5073_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5062_);
                    crate::leanh::lean_inc(v_postponed_5061_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5060_);
                    crate::leanh::lean_inc(v_mctx_5059_);
                    crate::leanh::lean_dec(v___x_5058_);
                    v___x_5064_ = crate::leanh::lean_box(0);
                    v_isShared_5065_ = v_isSharedCheck_5073_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5066_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once), _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
                if v_isShared_5065_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5064_, 1, v___x_5066_);
                    v___x_5068_ = v___x_5064_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5072_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_mctx_5059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5072_, 1, v___x_5066_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5072_,
                        2,
                        v_zetaDeltaFVarIds_5060_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5072_, 3, v_postponed_5061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5072_, 4, v_diag_5062_);
                    v___x_5068_ = v_reuseFailAlloc_5072_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5069_ = lean_st_ref_set(v___y_5036_, v___x_5068_);
                v___x_5070_ = crate::leanh::lean_box(0);
                v___x_5071_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5071_, 0, v___x_5070_);
                return v___x_5071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg___boxed(
    mut v_wi_5078_: *mut crate::leanh::LeanObject,
    mut v___y_5079_: *mut crate::leanh::LeanObject,
    mut v___y_5080_: *mut crate::leanh::LeanObject,
    mut v___y_5081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5082_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_5078_, v___y_5079_, v___y_5080_);
    crate::leanh::lean_dec(v___y_5080_);
    crate::leanh::lean_dec(v___y_5079_);
    return v_res_5082_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(
    mut v_ext_5083_: *mut crate::leanh::LeanObject,
    mut v_b_5084_: *mut crate::leanh::LeanObject,
    mut v_kind_5085_: u8,
    mut v___y_5086_: *mut crate::leanh::LeanObject,
    mut v___y_5087_: *mut crate::leanh::LeanObject,
    mut v___y_5088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_currNamespace_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5102_: u8 = 0;
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5123_: u8 = 0;
    let mut v_unused_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5126_: u8 = 0;
    let mut v_unused_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_5090_ = crate::leanh::lean_ctor_get(v___y_5087_, 6);
                v___x_5091_ = lean_st_ref_take(v___y_5088_);
                v_env_5092_ = crate::leanh::lean_ctor_get(v___x_5091_, 0);
                v_nextMacroScope_5093_ = crate::leanh::lean_ctor_get(v___x_5091_, 1);
                v_ngen_5094_ = crate::leanh::lean_ctor_get(v___x_5091_, 2);
                v_auxDeclNGen_5095_ = crate::leanh::lean_ctor_get(v___x_5091_, 3);
                v_traceState_5096_ = crate::leanh::lean_ctor_get(v___x_5091_, 4);
                v_messages_5097_ = crate::leanh::lean_ctor_get(v___x_5091_, 6);
                v_infoState_5098_ = crate::leanh::lean_ctor_get(v___x_5091_, 7);
                v_snapshotTasks_5099_ = crate::leanh::lean_ctor_get(v___x_5091_, 8);
                v_isSharedCheck_5126_ = (!crate::leanh::lean_is_exclusive(v___x_5091_)) as u8;
                if v_isSharedCheck_5126_ == 0 {
                    v_unused_5127_ = crate::leanh::lean_ctor_get(v___x_5091_, 5);
                    crate::leanh::lean_dec(v_unused_5127_);
                    v___x_5101_ = v___x_5091_;
                    v_isShared_5102_ = v_isSharedCheck_5126_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5099_);
                    crate::leanh::lean_inc(v_infoState_5098_);
                    crate::leanh::lean_inc(v_messages_5097_);
                    crate::leanh::lean_inc(v_traceState_5096_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5095_);
                    crate::leanh::lean_inc(v_ngen_5094_);
                    crate::leanh::lean_inc(v_nextMacroScope_5093_);
                    crate::leanh::lean_inc(v_env_5092_);
                    crate::leanh::lean_dec(v___x_5091_);
                    v___x_5101_ = crate::leanh::lean_box(0);
                    v_isShared_5102_ = v_isSharedCheck_5126_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_currNamespace_5090_);
                v___x_5103_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_5092_,
                    v_ext_5083_,
                    v_b_5084_,
                    v_kind_5085_,
                    v_currNamespace_5090_,
                );
                v___x_5104_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once), _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
                if v_isShared_5102_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5101_, 5, v___x_5104_);
                    crate::leanh::lean_ctor_set(v___x_5101_, 0, v___x_5103_);
                    v___x_5106_ = v___x_5101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5125_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 0, v___x_5103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 1, v_nextMacroScope_5093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 2, v_ngen_5094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 3, v_auxDeclNGen_5095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 4, v_traceState_5096_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 5, v___x_5104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 6, v_messages_5097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 7, v_infoState_5098_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 8, v_snapshotTasks_5099_);
                    v___x_5106_ = v_reuseFailAlloc_5125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5107_ = lean_st_ref_set(v___y_5088_, v___x_5106_);
                v___x_5108_ = lean_st_ref_take(v___y_5086_);
                v_mctx_5109_ = crate::leanh::lean_ctor_get(v___x_5108_, 0);
                v_zetaDeltaFVarIds_5110_ = crate::leanh::lean_ctor_get(v___x_5108_, 2);
                v_postponed_5111_ = crate::leanh::lean_ctor_get(v___x_5108_, 3);
                v_diag_5112_ = crate::leanh::lean_ctor_get(v___x_5108_, 4);
                v_isSharedCheck_5123_ = (!crate::leanh::lean_is_exclusive(v___x_5108_)) as u8;
                if v_isSharedCheck_5123_ == 0 {
                    v_unused_5124_ = crate::leanh::lean_ctor_get(v___x_5108_, 1);
                    crate::leanh::lean_dec(v_unused_5124_);
                    v___x_5114_ = v___x_5108_;
                    v_isShared_5115_ = v_isSharedCheck_5123_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5112_);
                    crate::leanh::lean_inc(v_postponed_5111_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5110_);
                    crate::leanh::lean_inc(v_mctx_5109_);
                    crate::leanh::lean_dec(v___x_5108_);
                    v___x_5114_ = crate::leanh::lean_box(0);
                    v_isShared_5115_ = v_isSharedCheck_5123_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5116_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once), _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
                if v_isShared_5115_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5114_, 1, v___x_5116_);
                    v___x_5118_ = v___x_5114_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5122_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_mctx_5109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 1, v___x_5116_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5122_,
                        2,
                        v_zetaDeltaFVarIds_5110_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 3, v_postponed_5111_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 4, v_diag_5112_);
                    v___x_5118_ = v_reuseFailAlloc_5122_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5119_ = lean_st_ref_set(v___y_5086_, v___x_5118_);
                v___x_5120_ = crate::leanh::lean_box(0);
                v___x_5121_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5121_, 0, v___x_5120_);
                return v___x_5121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg___boxed(
    mut v_ext_5128_: *mut crate::leanh::LeanObject,
    mut v_b_5129_: *mut crate::leanh::LeanObject,
    mut v_kind_5130_: *mut crate::leanh::LeanObject,
    mut v___y_5131_: *mut crate::leanh::LeanObject,
    mut v___y_5132_: *mut crate::leanh::LeanObject,
    mut v___y_5133_: *mut crate::leanh::LeanObject,
    mut v___y_5134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_5135_: u8 = 0;
    let mut v_res_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5135_ = (crate::leanh::lean_unbox(v_kind_5130_) as u8);
    v_res_5136_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_5128_, v_b_5129_, v_kind_boxed_5135_, v___y_5131_, v___y_5132_, v___y_5133_);
    crate::leanh::lean_dec(v___y_5133_);
    crate::leanh::lean_dec_ref(v___y_5132_);
    crate::leanh::lean_dec(v___y_5131_);
    return v_res_5136_;
}
pub unsafe fn l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(
    mut v_h_5137_: u64,
    mut v_n_5138_: *mut crate::leanh::LeanObject,
    mut v___y_5139_: *mut crate::leanh::LeanObject,
    mut v___y_5140_: *mut crate::leanh::LeanObject,
    mut v___y_5141_: *mut crate::leanh::LeanObject,
    mut v___y_5142_: *mut crate::leanh::LeanObject,
    mut v___y_5143_: *mut crate::leanh::LeanObject,
    mut v___y_5144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: u8 = 0;
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5146_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
    v___x_5147_ = crate::leanh::lean_box_uint64(v_h_5137_);
    v___x_5148_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5148_, 0, v___x_5147_);
    crate::leanh::lean_ctor_set(v___x_5148_, 1, v_n_5138_);
    v___x_5149_ = 2;
    v___x_5150_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_5146_, v___x_5148_, v___x_5149_, v___y_5142_, v___y_5143_, v___y_5144_);
    return v___x_5150_;
}
pub unsafe fn l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5___boxed(
    mut v_h_5151_: *mut crate::leanh::LeanObject,
    mut v_n_5152_: *mut crate::leanh::LeanObject,
    mut v___y_5153_: *mut crate::leanh::LeanObject,
    mut v___y_5154_: *mut crate::leanh::LeanObject,
    mut v___y_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
    mut v___y_5158_: *mut crate::leanh::LeanObject,
    mut v___y_5159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_h_boxed_5160_: u64 = 0;
    let mut v_res_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_h_boxed_5160_ = crate::leanh::lean_unbox_uint64(v_h_5151_);
    crate::leanh::lean_dec_ref(v_h_5151_);
    v_res_5161_ =
        l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(
            v_h_boxed_5160_,
            v_n_5152_,
            v___y_5153_,
            v___y_5154_,
            v___y_5155_,
            v___y_5156_,
            v___y_5157_,
            v___y_5158_,
        );
    crate::leanh::lean_dec(v___y_5158_);
    crate::leanh::lean_dec_ref(v___y_5157_);
    crate::leanh::lean_dec(v___y_5156_);
    crate::leanh::lean_dec_ref(v___y_5155_);
    crate::leanh::lean_dec(v___y_5154_);
    crate::leanh::lean_dec_ref(v___y_5153_);
    return v_res_5161_;
}
pub unsafe fn l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(
    mut v_h_5162_: u64,
    mut v_n_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
    mut v___y_5165_: *mut crate::leanh::LeanObject,
    mut v___y_5166_: *mut crate::leanh::LeanObject,
    mut v___y_5167_: *mut crate::leanh::LeanObject,
    mut v___y_5168_: *mut crate::leanh::LeanObject,
    mut v___y_5169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: u8 = 0;
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5171_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_panelWidgetsExt;
    v___x_5172_ = crate::leanh::lean_box_uint64(v_h_5162_);
    v___x_5173_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5173_, 0, v___x_5172_);
    crate::leanh::lean_ctor_set(v___x_5173_, 1, v_n_5163_);
    v___x_5174_ = 0;
    v___x_5175_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v___x_5171_, v___x_5173_, v___x_5174_, v___y_5167_, v___y_5168_, v___y_5169_);
    return v___x_5175_;
}
pub unsafe fn l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4___boxed(
    mut v_h_5176_: *mut crate::leanh::LeanObject,
    mut v_n_5177_: *mut crate::leanh::LeanObject,
    mut v___y_5178_: *mut crate::leanh::LeanObject,
    mut v___y_5179_: *mut crate::leanh::LeanObject,
    mut v___y_5180_: *mut crate::leanh::LeanObject,
    mut v___y_5181_: *mut crate::leanh::LeanObject,
    mut v___y_5182_: *mut crate::leanh::LeanObject,
    mut v___y_5183_: *mut crate::leanh::LeanObject,
    mut v___y_5184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_h_boxed_5185_: u64 = 0;
    let mut v_res_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_h_boxed_5185_ = crate::leanh::lean_unbox_uint64(v_h_5176_);
    crate::leanh::lean_dec_ref(v_h_5176_);
    v_res_5186_ =
        l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(
            v_h_boxed_5185_,
            v_n_5177_,
            v___y_5178_,
            v___y_5179_,
            v___y_5180_,
            v___y_5181_,
            v___y_5182_,
            v___y_5183_,
        );
    crate::leanh::lean_dec(v___y_5183_);
    crate::leanh::lean_dec_ref(v___y_5182_);
    crate::leanh::lean_dec(v___y_5181_);
    crate::leanh::lean_dec_ref(v___y_5180_);
    crate::leanh::lean_dec(v___y_5179_);
    crate::leanh::lean_dec_ref(v___y_5178_);
    return v_res_5186_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(
    mut v_env_5187_: *mut crate::leanh::LeanObject,
    mut v_declName_5188_: *mut crate::leanh::LeanObject,
    mut v___y_5189_: *mut crate::leanh::LeanObject,
    mut v___y_5190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5191_: u8 = 0;
    let mut v_env_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: u8 = 0;
    let mut v___x_5195_: u8 = 0;
    v___x_5191_ = 0;
    v_env_5192_ = l_Lean_Environment_setExporting(v_env_5187_, v___x_5191_);
    crate::leanh::lean_inc(v_declName_5188_);
    v___x_5193_ = l_Lean_mkPrivateName(v_env_5192_, v_declName_5188_);
    v___x_5194_ = 1;
    crate::leanh::lean_inc_ref(v_env_5192_);
    v___x_5195_ = l_Lean_Environment_contains(v_env_5192_, v___x_5193_, v___x_5194_);
    if v___x_5195_ == 0 {
        let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5197_: u8 = 0;
        let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5196_ = l_Lean_privateToUserName(v_declName_5188_);
        v___x_5197_ = l_Lean_Environment_contains(v_env_5192_, v___x_5196_, v___x_5194_);
        v___x_5198_ = crate::leanh::lean_box((v___x_5197_) as usize);
        v___x_5199_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5199_, 0, v___x_5198_);
        crate::leanh::lean_ctor_set(v___x_5199_, 1, v___y_5190_);
        return v___x_5199_;
    } else {
        let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_5192_);
        crate::leanh::lean_dec(v_declName_5188_);
        v___x_5200_ = crate::leanh::lean_box((v___x_5195_) as usize);
        v___x_5201_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5201_, 0, v___x_5200_);
        crate::leanh::lean_ctor_set(v___x_5201_, 1, v___y_5190_);
        return v___x_5201_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed(
    mut v_env_5202_: *mut crate::leanh::LeanObject,
    mut v_declName_5203_: *mut crate::leanh::LeanObject,
    mut v___y_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5206_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1(v_env_5202_, v_declName_5203_, v___y_5204_, v___y_5205_);
    crate::leanh::lean_dec_ref(v___y_5204_);
    return v_res_5206_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(
    mut v_msgData_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
    mut v___y_5209_: *mut crate::leanh::LeanObject,
    mut v___y_5210_: *mut crate::leanh::LeanObject,
    mut v___y_5211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5213_ = lean_st_ref_get(v___y_5211_);
    v_env_5214_ = crate::leanh::lean_ctor_get(v___x_5213_, 0);
    crate::leanh::lean_inc_ref(v_env_5214_);
    crate::leanh::lean_dec(v___x_5213_);
    v___x_5215_ = lean_st_ref_get(v___y_5209_);
    v_mctx_5216_ = crate::leanh::lean_ctor_get(v___x_5215_, 0);
    crate::leanh::lean_inc_ref(v_mctx_5216_);
    crate::leanh::lean_dec(v___x_5215_);
    v_lctx_5217_ = crate::leanh::lean_ctor_get(v___y_5208_, 2);
    v_options_5218_ = crate::leanh::lean_ctor_get(v___y_5210_, 2);
    crate::leanh::lean_inc_ref(v_options_5218_);
    crate::leanh::lean_inc_ref(v_lctx_5217_);
    v___x_5219_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5219_, 0, v_env_5214_);
    crate::leanh::lean_ctor_set(v___x_5219_, 1, v_mctx_5216_);
    crate::leanh::lean_ctor_set(v___x_5219_, 2, v_lctx_5217_);
    crate::leanh::lean_ctor_set(v___x_5219_, 3, v_options_5218_);
    v___x_5220_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5220_, 0, v___x_5219_);
    crate::leanh::lean_ctor_set(v___x_5220_, 1, v_msgData_5207_);
    v___x_5221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5221_, 0, v___x_5220_);
    return v___x_5221_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16___boxed(
    mut v_msgData_5222_: *mut crate::leanh::LeanObject,
    mut v___y_5223_: *mut crate::leanh::LeanObject,
    mut v___y_5224_: *mut crate::leanh::LeanObject,
    mut v___y_5225_: *mut crate::leanh::LeanObject,
    mut v___y_5226_: *mut crate::leanh::LeanObject,
    mut v___y_5227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5228_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msgData_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_);
    crate::leanh::lean_dec(v___y_5226_);
    crate::leanh::lean_dec_ref(v___y_5225_);
    crate::leanh::lean_dec(v___y_5224_);
    crate::leanh::lean_dec_ref(v___y_5223_);
    return v_res_5228_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: f64 = 0.0;
    v___x_5229_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5230_ = lean_float_of_nat(v___x_5229_);
    return v___x_5230_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(
    mut v_cls_5233_: *mut crate::leanh::LeanObject,
    mut v_msg_5234_: *mut crate::leanh::LeanObject,
    mut v___y_5235_: *mut crate::leanh::LeanObject,
    mut v___y_5236_: *mut crate::leanh::LeanObject,
    mut v___y_5237_: *mut crate::leanh::LeanObject,
    mut v___y_5238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5245_: u8 = 0;
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v_tid_5259_: u64 = 0;
    let mut v_traces_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5263_: u8 = 0;
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: f64 = 0.0;
    let mut v___x_5266_: u8 = 0;
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5284_: u8 = 0;
    let mut v_isSharedCheck_5285_: u8 = 0;
    let mut v_isSharedCheck_5286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5240_ = crate::leanh::lean_ctor_get(v___y_5237_, 5);
                v___x_5241_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_);
                v_a_5242_ = crate::leanh::lean_ctor_get(v___x_5241_, 0);
                v_isSharedCheck_5286_ = (!crate::leanh::lean_is_exclusive(v___x_5241_)) as u8;
                if v_isSharedCheck_5286_ == 0 {
                    v___x_5244_ = v___x_5241_;
                    v_isShared_5245_ = v_isSharedCheck_5286_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5242_);
                    crate::leanh::lean_dec(v___x_5241_);
                    v___x_5244_ = crate::leanh::lean_box(0);
                    v_isShared_5245_ = v_isSharedCheck_5286_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5246_ = lean_st_ref_take(v___y_5238_);
                v_traceState_5247_ = crate::leanh::lean_ctor_get(v___x_5246_, 4);
                v_env_5248_ = crate::leanh::lean_ctor_get(v___x_5246_, 0);
                v_nextMacroScope_5249_ = crate::leanh::lean_ctor_get(v___x_5246_, 1);
                v_ngen_5250_ = crate::leanh::lean_ctor_get(v___x_5246_, 2);
                v_auxDeclNGen_5251_ = crate::leanh::lean_ctor_get(v___x_5246_, 3);
                v_cache_5252_ = crate::leanh::lean_ctor_get(v___x_5246_, 5);
                v_messages_5253_ = crate::leanh::lean_ctor_get(v___x_5246_, 6);
                v_infoState_5254_ = crate::leanh::lean_ctor_get(v___x_5246_, 7);
                v_snapshotTasks_5255_ = crate::leanh::lean_ctor_get(v___x_5246_, 8);
                v_isSharedCheck_5285_ = (!crate::leanh::lean_is_exclusive(v___x_5246_)) as u8;
                if v_isSharedCheck_5285_ == 0 {
                    v___x_5257_ = v___x_5246_;
                    v_isShared_5258_ = v_isSharedCheck_5285_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5255_);
                    crate::leanh::lean_inc(v_infoState_5254_);
                    crate::leanh::lean_inc(v_messages_5253_);
                    crate::leanh::lean_inc(v_cache_5252_);
                    crate::leanh::lean_inc(v_traceState_5247_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5251_);
                    crate::leanh::lean_inc(v_ngen_5250_);
                    crate::leanh::lean_inc(v_nextMacroScope_5249_);
                    crate::leanh::lean_inc(v_env_5248_);
                    crate::leanh::lean_dec(v___x_5246_);
                    v___x_5257_ = crate::leanh::lean_box(0);
                    v_isShared_5258_ = v_isSharedCheck_5285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5259_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5247_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5260_ = crate::leanh::lean_ctor_get(v_traceState_5247_, 0);
                v_isSharedCheck_5284_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5247_)) as u8;
                if v_isSharedCheck_5284_ == 0 {
                    v___x_5262_ = v_traceState_5247_;
                    v_isShared_5263_ = v_isSharedCheck_5284_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_5260_);
                    crate::leanh::lean_dec(v_traceState_5247_);
                    v___x_5262_ = crate::leanh::lean_box(0);
                    v_isShared_5263_ = v_isSharedCheck_5284_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5264_ = crate::leanh::lean_box(0);
                v___x_5265_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__0);
                v___x_5266_ = 0;
                v___x_5267_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34;
                v___x_5268_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_5268_, 0, v_cls_5233_);
                crate::leanh::lean_ctor_set(v___x_5268_, 1, v___x_5264_);
                crate::leanh::lean_ctor_set(v___x_5268_, 2, v___x_5267_);
                crate::leanh::lean_ctor_set_float(
                    v___x_5268_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5265_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_5268_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5265_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5268_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_5266_,
                );
                v___x_5269_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___closed__1;
                v___x_5270_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5270_, 0, v___x_5268_);
                crate::leanh::lean_ctor_set(v___x_5270_, 1, v_a_5242_);
                crate::leanh::lean_ctor_set(v___x_5270_, 2, v___x_5269_);
                crate::leanh::lean_inc(v_ref_5240_);
                v___x_5271_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5271_, 0, v_ref_5240_);
                crate::leanh::lean_ctor_set(v___x_5271_, 1, v___x_5270_);
                v___x_5272_ = l_Lean_PersistentArray_push___redArg(v_traces_5260_, v___x_5271_);
                if v_isShared_5263_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5262_, 0, v___x_5272_);
                    v___x_5274_ = v___x_5262_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5283_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5272_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5283_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5259_,
                    );
                    v___x_5274_ = v_reuseFailAlloc_5283_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5258_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5257_, 4, v___x_5274_);
                    v___x_5276_ = v___x_5257_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_env_5248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 1, v_nextMacroScope_5249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 2, v_ngen_5250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 3, v_auxDeclNGen_5251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 4, v___x_5274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 5, v_cache_5252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 6, v_messages_5253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 7, v_infoState_5254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 8, v_snapshotTasks_5255_);
                    v___x_5276_ = v_reuseFailAlloc_5282_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5277_ = lean_st_ref_set(v___y_5238_, v___x_5276_);
                v___x_5278_ = crate::leanh::lean_box(0);
                if v_isShared_5245_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5244_, 0, v___x_5278_);
                    v___x_5280_ = v___x_5244_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5281_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5281_, 0, v___x_5278_);
                    v___x_5280_ = v_reuseFailAlloc_5281_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg___boxed(
    mut v_cls_5287_: *mut crate::leanh::LeanObject,
    mut v_msg_5288_: *mut crate::leanh::LeanObject,
    mut v___y_5289_: *mut crate::leanh::LeanObject,
    mut v___y_5290_: *mut crate::leanh::LeanObject,
    mut v___y_5291_: *mut crate::leanh::LeanObject,
    mut v___y_5292_: *mut crate::leanh::LeanObject,
    mut v___y_5293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5294_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_5287_, v_msg_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_);
    crate::leanh::lean_dec(v___y_5292_);
    crate::leanh::lean_dec_ref(v___y_5291_);
    crate::leanh::lean_dec(v___y_5290_);
    crate::leanh::lean_dec_ref(v___y_5289_);
    return v_res_5294_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(
    mut v_as_5298_: *mut crate::leanh::LeanObject,
    mut v___y_5299_: *mut crate::leanh::LeanObject,
    mut v___y_5300_: *mut crate::leanh::LeanObject,
    mut v___y_5301_: *mut crate::leanh::LeanObject,
    mut v___y_5302_: *mut crate::leanh::LeanObject,
    mut v___y_5303_: *mut crate::leanh::LeanObject,
    mut v___y_5304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5309_: u8 = 0;
    let mut v_tail_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: u8 = 0;
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_5298_) == 0 {
                    v___x_5306_ = crate::leanh::lean_box(0);
                    v___x_5307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5307_, 0, v___x_5306_);
                    return v___x_5307_;
                } else {
                    v_options_5308_ = crate::leanh::lean_ctor_get(v___y_5303_, 2);
                    v_hasTrace_5309_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_5308_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5309_ == 0 {
                        v_tail_5310_ = crate::leanh::lean_ctor_get(v_as_5298_, 1);
                        crate::leanh::lean_inc(v_tail_5310_);
                        crate::leanh::lean_dec_ref_known(v_as_5298_, 2);
                        v_as_5298_ = v_tail_5310_;
                        state = 0;
                        continue;
                    } else {
                        v_head_5312_ = crate::leanh::lean_ctor_get(v_as_5298_, 0);
                        crate::leanh::lean_inc(v_head_5312_);
                        v_tail_5313_ = crate::leanh::lean_ctor_get(v_as_5298_, 1);
                        crate::leanh::lean_inc(v_tail_5313_);
                        crate::leanh::lean_dec_ref_known(v_as_5298_, 2);
                        v_fst_5314_ = crate::leanh::lean_ctor_get(v_head_5312_, 0);
                        crate::leanh::lean_inc_n(v_fst_5314_, 2);
                        v_snd_5315_ = crate::leanh::lean_ctor_get(v_head_5312_, 1);
                        crate::leanh::lean_inc(v_snd_5315_);
                        crate::leanh::lean_dec(v_head_5312_);
                        v_inheritedTraceOptions_5316_ =
                            crate::leanh::lean_ctor_get(v___y_5303_, 13);
                        v___x_5317_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1;
                        v___x_5318_ = l_Lean_Name_append(v___x_5317_, v_fst_5314_);
                        v___x_5319_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5316_,
                            v_options_5308_,
                            v___x_5318_,
                        );
                        crate::leanh::lean_dec(v___x_5318_);
                        if v___x_5319_ == 0 {
                            crate::leanh::lean_dec(v_snd_5315_);
                            crate::leanh::lean_dec(v_fst_5314_);
                            v_as_5298_ = v_tail_5313_;
                            state = 0;
                            continue;
                        } else {
                            v___x_5321_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5321_, 0, v_snd_5315_);
                            v___x_5322_ = l_Lean_MessageData_ofFormat(v___x_5321_);
                            v___x_5323_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_fst_5314_, v___x_5322_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
                            if crate::leanh::lean_obj_tag(v___x_5323_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5323_, 1);
                                v_as_5298_ = v_tail_5313_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_tail_5313_);
                                return v___x_5323_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___boxed(
    mut v_as_5325_: *mut crate::leanh::LeanObject,
    mut v___y_5326_: *mut crate::leanh::LeanObject,
    mut v___y_5327_: *mut crate::leanh::LeanObject,
    mut v___y_5328_: *mut crate::leanh::LeanObject,
    mut v___y_5329_: *mut crate::leanh::LeanObject,
    mut v___y_5330_: *mut crate::leanh::LeanObject,
    mut v___y_5331_: *mut crate::leanh::LeanObject,
    mut v___y_5332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5333_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v_as_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_);
    crate::leanh::lean_dec(v___y_5331_);
    crate::leanh::lean_dec_ref(v___y_5330_);
    crate::leanh::lean_dec(v___y_5329_);
    crate::leanh::lean_dec_ref(v___y_5328_);
    crate::leanh::lean_dec(v___y_5327_);
    crate::leanh::lean_dec_ref(v___y_5326_);
    return v_res_5333_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(
    mut v_env_5334_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5335_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5336_: *mut crate::leanh::LeanObject,
    mut v_n_5337_: *mut crate::leanh::LeanObject,
    mut v___y_5338_: *mut crate::leanh::LeanObject,
    mut v___y_5339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5340_ = l_Lean_ResolveName_resolveNamespace(
        v_env_5334_,
        v_currNamespace_5335_,
        v_openDecls_5336_,
        v_n_5337_,
    );
    v___x_5341_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5341_, 0, v___x_5340_);
    crate::leanh::lean_ctor_set(v___x_5341_, 1, v___y_5339_);
    return v___x_5341_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed(
    mut v_env_5342_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5343_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5344_: *mut crate::leanh::LeanObject,
    mut v_n_5345_: *mut crate::leanh::LeanObject,
    mut v___y_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5348_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2(v_env_5342_, v_currNamespace_5343_, v_openDecls_5344_, v_n_5345_, v___y_5346_, v___y_5347_);
    crate::leanh::lean_dec_ref(v___y_5346_);
    return v_res_5348_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(
    mut v_opts_5349_: *mut crate::leanh::LeanObject,
    mut v_opt_5350_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5351_ = crate::leanh::lean_ctor_get(v_opt_5350_, 0);
    v_defValue_5352_ = crate::leanh::lean_ctor_get(v_opt_5350_, 1);
    v_map_5353_ = crate::leanh::lean_ctor_get(v_opts_5349_, 0);
    v___x_5354_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5353_,
            v_name_5351_,
        );
    if crate::leanh::lean_obj_tag(v___x_5354_) == 0 {
        let mut v___x_5355_: u8 = 0;
        v___x_5355_ = (crate::leanh::lean_unbox(v_defValue_5352_) as u8);
        return v___x_5355_;
    } else {
        let mut v_val_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5356_ = crate::leanh::lean_ctor_get(v___x_5354_, 0);
        crate::leanh::lean_inc(v_val_5356_);
        crate::leanh::lean_dec_ref_known(v___x_5354_, 1);
        if crate::leanh::lean_obj_tag(v_val_5356_) == 1 {
            let mut v_v_5357_: u8 = 0;
            v_v_5357_ = crate::leanh::lean_ctor_get_uint8(v_val_5356_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_5356_, 0);
            return v_v_5357_;
        } else {
            let mut v___x_5358_: u8 = 0;
            crate::leanh::lean_dec(v_val_5356_);
            v___x_5358_ = (crate::leanh::lean_unbox(v_defValue_5352_) as u8);
            return v___x_5358_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21___boxed(
    mut v_opts_5359_: *mut crate::leanh::LeanObject,
    mut v_opt_5360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5361_: u8 = 0;
    let mut v_r_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5361_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_opts_5359_, v_opt_5360_);
    crate::leanh::lean_dec_ref(v_opt_5360_);
    crate::leanh::lean_dec_ref(v_opts_5359_);
    v_r_5362_ = crate::leanh::lean_box((v_res_5361_) as usize);
    return v_r_5362_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5363_ = crate::leanh::lean_box(1);
    v___x_5364_ = l_Lean_MessageData_ofFormat(v___x_5363_);
    return v___x_5364_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5368_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__2;
    v___x_5369_ = l_Lean_MessageData_ofFormat(v___x_5368_);
    return v___x_5369_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(
    mut v_x_5370_: *mut crate::leanh::LeanObject,
    mut v_x_5371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5376_: u8 = 0;
    let mut v_before_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5380_: u8 = 0;
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5393_: u8 = 0;
    let mut v_unused_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5371_) == 0 {
                    return v_x_5370_;
                } else {
                    v_head_5372_ = crate::leanh::lean_ctor_get(v_x_5371_, 0);
                    v_tail_5373_ = crate::leanh::lean_ctor_get(v_x_5371_, 1);
                    v_isSharedCheck_5395_ = (!crate::leanh::lean_is_exclusive(v_x_5371_)) as u8;
                    if v_isSharedCheck_5395_ == 0 {
                        v___x_5375_ = v_x_5371_;
                        v_isShared_5376_ = v_isSharedCheck_5395_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5373_);
                        crate::leanh::lean_inc(v_head_5372_);
                        crate::leanh::lean_dec(v_x_5371_);
                        v___x_5375_ = crate::leanh::lean_box(0);
                        v_isShared_5376_ = v_isSharedCheck_5395_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5377_ = crate::leanh::lean_ctor_get(v_head_5372_, 0);
                v_isSharedCheck_5393_ = (!crate::leanh::lean_is_exclusive(v_head_5372_)) as u8;
                if v_isSharedCheck_5393_ == 0 {
                    v_unused_5394_ = crate::leanh::lean_ctor_get(v_head_5372_, 1);
                    crate::leanh::lean_dec(v_unused_5394_);
                    v___x_5379_ = v_head_5372_;
                    v_isShared_5380_ = v_isSharedCheck_5393_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_5377_);
                    crate::leanh::lean_dec(v_head_5372_);
                    v___x_5379_ = crate::leanh::lean_box(0);
                    v_isShared_5380_ = v_isSharedCheck_5393_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5381_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
                if v_isShared_5380_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5379_, 7);
                    crate::leanh::lean_ctor_set(v___x_5379_, 1, v___x_5381_);
                    crate::leanh::lean_ctor_set(v___x_5379_, 0, v_x_5370_);
                    v___x_5383_ = v___x_5379_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5392_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_x_5370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5392_, 1, v___x_5381_);
                    v___x_5383_ = v_reuseFailAlloc_5392_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5384_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__3);
                if v_isShared_5376_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5375_, 7);
                    crate::leanh::lean_ctor_set(v___x_5375_, 1, v___x_5384_);
                    crate::leanh::lean_ctor_set(v___x_5375_, 0, v___x_5383_);
                    v___x_5386_ = v___x_5375_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5391_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5391_, 0, v___x_5383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5391_, 1, v___x_5384_);
                    v___x_5386_ = v_reuseFailAlloc_5391_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5387_ = l_Lean_MessageData_ofSyntax(v_before_5377_);
                v___x_5388_ = l_Lean_indentD(v___x_5387_);
                v___x_5389_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5389_, 0, v___x_5386_);
                crate::leanh::lean_ctor_set(v___x_5389_, 1, v___x_5388_);
                v_x_5370_ = v___x_5389_;
                v_x_5371_ = v_tail_5373_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5399_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__1;
    v___x_5400_ = l_Lean_MessageData_ofFormat(v___x_5399_);
    return v___x_5400_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(
    mut v_msgData_5401_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5402_: *mut crate::leanh::LeanObject,
    mut v___y_5403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: u8 = 0;
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5414_: u8 = 0;
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5426_: u8 = 0;
    let mut v_unused_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5405_ = crate::leanh::lean_ctor_get(v___y_5403_, 2);
                v___x_5406_ = l_Lean_Elab_pp_macroStack;
                v___x_5407_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__21(v_options_5405_, v___x_5406_);
                if v___x_5407_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_5402_);
                    v___x_5408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5408_, 0, v_msgData_5401_);
                    return v___x_5408_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_5402_) == 0 {
                        v___x_5409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5409_, 0, v_msgData_5401_);
                        return v___x_5409_;
                    } else {
                        v_head_5410_ = crate::leanh::lean_ctor_get(v_macroStack_5402_, 0);
                        crate::leanh::lean_inc(v_head_5410_);
                        v_after_5411_ = crate::leanh::lean_ctor_get(v_head_5410_, 1);
                        v_isSharedCheck_5426_ =
                            (!crate::leanh::lean_is_exclusive(v_head_5410_)) as u8;
                        if v_isSharedCheck_5426_ == 0 {
                            v_unused_5427_ = crate::leanh::lean_ctor_get(v_head_5410_, 0);
                            crate::leanh::lean_dec(v_unused_5427_);
                            v___x_5413_ = v_head_5410_;
                            v_isShared_5414_ = v_isSharedCheck_5426_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_5411_);
                            crate::leanh::lean_dec(v_head_5410_);
                            v___x_5413_ = crate::leanh::lean_box(0);
                            v_isShared_5414_ = v_isSharedCheck_5426_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5415_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22___closed__0);
                if v_isShared_5414_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5413_, 7);
                    crate::leanh::lean_ctor_set(v___x_5413_, 1, v___x_5415_);
                    crate::leanh::lean_ctor_set(v___x_5413_, 0, v_msgData_5401_);
                    v___x_5417_ = v___x_5413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5425_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_msgData_5401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5425_, 1, v___x_5415_);
                    v___x_5417_ = v_reuseFailAlloc_5425_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5418_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___closed__2);
                v___x_5419_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5419_, 0, v___x_5417_);
                crate::leanh::lean_ctor_set(v___x_5419_, 1, v___x_5418_);
                v___x_5420_ = l_Lean_MessageData_ofSyntax(v_after_5411_);
                v___x_5421_ = l_Lean_indentD(v___x_5420_);
                v_msgData_5422_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_5422_, 0, v___x_5419_);
                crate::leanh::lean_ctor_set(v_msgData_5422_, 1, v___x_5421_);
                v___x_5423_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17_spec__22(v_msgData_5422_, v_macroStack_5402_);
                v___x_5424_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5424_, 0, v___x_5423_);
                return v___x_5424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg___boxed(
    mut v_msgData_5428_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5429_: *mut crate::leanh::LeanObject,
    mut v___y_5430_: *mut crate::leanh::LeanObject,
    mut v___y_5431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5432_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_5428_, v_macroStack_5429_, v___y_5430_);
    crate::leanh::lean_dec_ref(v___y_5430_);
    return v_res_5432_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(
    mut v_msg_5433_: *mut crate::leanh::LeanObject,
    mut v___y_5434_: *mut crate::leanh::LeanObject,
    mut v___y_5435_: *mut crate::leanh::LeanObject,
    mut v___y_5436_: *mut crate::leanh::LeanObject,
    mut v___y_5437_: *mut crate::leanh::LeanObject,
    mut v___y_5438_: *mut crate::leanh::LeanObject,
    mut v___y_5439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5450_: u8 = 0;
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5441_ = crate::leanh::lean_ctor_get(v___y_5438_, 5);
                v___x_5442_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__16(v_msg_5433_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_);
                v_a_5443_ = crate::leanh::lean_ctor_get(v___x_5442_, 0);
                crate::leanh::lean_inc(v_a_5443_);
                crate::leanh::lean_dec_ref(v___x_5442_);
                v_macroStack_5444_ = crate::leanh::lean_ctor_get(v___y_5434_, 1);
                v___x_5445_ = l_Lean_Elab_getBetterRef(v_ref_5441_, v_macroStack_5444_);
                crate::leanh::lean_inc(v_macroStack_5444_);
                v___x_5446_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_a_5443_, v_macroStack_5444_, v___y_5438_);
                v_a_5447_ = crate::leanh::lean_ctor_get(v___x_5446_, 0);
                v_isSharedCheck_5455_ = (!crate::leanh::lean_is_exclusive(v___x_5446_)) as u8;
                if v_isSharedCheck_5455_ == 0 {
                    v___x_5449_ = v___x_5446_;
                    v_isShared_5450_ = v_isSharedCheck_5455_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5447_);
                    crate::leanh::lean_dec(v___x_5446_);
                    v___x_5449_ = crate::leanh::lean_box(0);
                    v_isShared_5450_ = v_isSharedCheck_5455_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5451_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5451_, 0, v___x_5445_);
                crate::leanh::lean_ctor_set(v___x_5451_, 1, v_a_5447_);
                if v_isShared_5450_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5449_, 1);
                    crate::leanh::lean_ctor_set(v___x_5449_, 0, v___x_5451_);
                    v___x_5453_ = v___x_5449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5454_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5454_, 0, v___x_5451_);
                    v___x_5453_ = v_reuseFailAlloc_5454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg___boxed(
    mut v_msg_5456_: *mut crate::leanh::LeanObject,
    mut v___y_5457_: *mut crate::leanh::LeanObject,
    mut v___y_5458_: *mut crate::leanh::LeanObject,
    mut v___y_5459_: *mut crate::leanh::LeanObject,
    mut v___y_5460_: *mut crate::leanh::LeanObject,
    mut v___y_5461_: *mut crate::leanh::LeanObject,
    mut v___y_5462_: *mut crate::leanh::LeanObject,
    mut v___y_5463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5464_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(
        v_msg_5456_,
        v___y_5457_,
        v___y_5458_,
        v___y_5459_,
        v___y_5460_,
        v___y_5461_,
        v___y_5462_,
    );
    crate::leanh::lean_dec(v___y_5462_);
    crate::leanh::lean_dec_ref(v___y_5461_);
    crate::leanh::lean_dec(v___y_5460_);
    crate::leanh::lean_dec_ref(v___y_5459_);
    crate::leanh::lean_dec(v___y_5458_);
    crate::leanh::lean_dec_ref(v___y_5457_);
    return v_res_5464_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(
    mut v_ref_5465_: *mut crate::leanh::LeanObject,
    mut v_msg_5466_: *mut crate::leanh::LeanObject,
    mut v___y_5467_: *mut crate::leanh::LeanObject,
    mut v___y_5468_: *mut crate::leanh::LeanObject,
    mut v___y_5469_: *mut crate::leanh::LeanObject,
    mut v___y_5470_: *mut crate::leanh::LeanObject,
    mut v___y_5471_: *mut crate::leanh::LeanObject,
    mut v___y_5472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5486_: u8 = 0;
    let mut v_cancelTk_x3f_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5488_: u8 = 0;
    let mut v_inheritedTraceOptions_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5474_ = crate::leanh::lean_ctor_get(v___y_5471_, 0);
    v_fileMap_5475_ = crate::leanh::lean_ctor_get(v___y_5471_, 1);
    v_options_5476_ = crate::leanh::lean_ctor_get(v___y_5471_, 2);
    v_currRecDepth_5477_ = crate::leanh::lean_ctor_get(v___y_5471_, 3);
    v_maxRecDepth_5478_ = crate::leanh::lean_ctor_get(v___y_5471_, 4);
    v_ref_5479_ = crate::leanh::lean_ctor_get(v___y_5471_, 5);
    v_currNamespace_5480_ = crate::leanh::lean_ctor_get(v___y_5471_, 6);
    v_openDecls_5481_ = crate::leanh::lean_ctor_get(v___y_5471_, 7);
    v_initHeartbeats_5482_ = crate::leanh::lean_ctor_get(v___y_5471_, 8);
    v_maxHeartbeats_5483_ = crate::leanh::lean_ctor_get(v___y_5471_, 9);
    v_quotContext_5484_ = crate::leanh::lean_ctor_get(v___y_5471_, 10);
    v_currMacroScope_5485_ = crate::leanh::lean_ctor_get(v___y_5471_, 11);
    v_diag_5486_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5471_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5487_ = crate::leanh::lean_ctor_get(v___y_5471_, 12);
    v_suppressElabErrors_5488_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5471_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5489_ = crate::leanh::lean_ctor_get(v___y_5471_, 13);
    v_ref_5490_ = l_Lean_replaceRef(v_ref_5465_, v_ref_5479_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5489_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5487_);
    crate::leanh::lean_inc(v_currMacroScope_5485_);
    crate::leanh::lean_inc(v_quotContext_5484_);
    crate::leanh::lean_inc(v_maxHeartbeats_5483_);
    crate::leanh::lean_inc(v_initHeartbeats_5482_);
    crate::leanh::lean_inc(v_openDecls_5481_);
    crate::leanh::lean_inc(v_currNamespace_5480_);
    crate::leanh::lean_inc(v_maxRecDepth_5478_);
    crate::leanh::lean_inc(v_currRecDepth_5477_);
    crate::leanh::lean_inc_ref(v_options_5476_);
    crate::leanh::lean_inc_ref(v_fileMap_5475_);
    crate::leanh::lean_inc_ref(v_fileName_5474_);
    v___x_5491_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5491_, 0, v_fileName_5474_);
    crate::leanh::lean_ctor_set(v___x_5491_, 1, v_fileMap_5475_);
    crate::leanh::lean_ctor_set(v___x_5491_, 2, v_options_5476_);
    crate::leanh::lean_ctor_set(v___x_5491_, 3, v_currRecDepth_5477_);
    crate::leanh::lean_ctor_set(v___x_5491_, 4, v_maxRecDepth_5478_);
    crate::leanh::lean_ctor_set(v___x_5491_, 5, v_ref_5490_);
    crate::leanh::lean_ctor_set(v___x_5491_, 6, v_currNamespace_5480_);
    crate::leanh::lean_ctor_set(v___x_5491_, 7, v_openDecls_5481_);
    crate::leanh::lean_ctor_set(v___x_5491_, 8, v_initHeartbeats_5482_);
    crate::leanh::lean_ctor_set(v___x_5491_, 9, v_maxHeartbeats_5483_);
    crate::leanh::lean_ctor_set(v___x_5491_, 10, v_quotContext_5484_);
    crate::leanh::lean_ctor_set(v___x_5491_, 11, v_currMacroScope_5485_);
    crate::leanh::lean_ctor_set(v___x_5491_, 12, v_cancelTk_x3f_5487_);
    crate::leanh::lean_ctor_set(v___x_5491_, 13, v_inheritedTraceOptions_5489_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5491_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5486_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5491_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5488_,
    );
    v___x_5492_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(
        v_msg_5466_,
        v___y_5467_,
        v___y_5468_,
        v___y_5469_,
        v___y_5470_,
        v___x_5491_,
        v___y_5472_,
    );
    crate::leanh::lean_dec_ref_known(v___x_5491_, 14);
    return v___x_5492_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg___boxed(
    mut v_ref_5493_: *mut crate::leanh::LeanObject,
    mut v_msg_5494_: *mut crate::leanh::LeanObject,
    mut v___y_5495_: *mut crate::leanh::LeanObject,
    mut v___y_5496_: *mut crate::leanh::LeanObject,
    mut v___y_5497_: *mut crate::leanh::LeanObject,
    mut v___y_5498_: *mut crate::leanh::LeanObject,
    mut v___y_5499_: *mut crate::leanh::LeanObject,
    mut v___y_5500_: *mut crate::leanh::LeanObject,
    mut v___y_5501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5502_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_5493_, v_msg_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_);
    crate::leanh::lean_dec(v___y_5500_);
    crate::leanh::lean_dec_ref(v___y_5499_);
    crate::leanh::lean_dec(v___y_5498_);
    crate::leanh::lean_dec_ref(v___y_5497_);
    crate::leanh::lean_dec(v___y_5496_);
    crate::leanh::lean_dec_ref(v___y_5495_);
    crate::leanh::lean_dec(v_ref_5493_);
    return v_res_5502_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(
    mut v_env_5503_: *mut crate::leanh::LeanObject,
    mut v_options_5504_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5505_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5506_: *mut crate::leanh::LeanObject,
    mut v_n_5507_: *mut crate::leanh::LeanObject,
    mut v___y_5508_: *mut crate::leanh::LeanObject,
    mut v___y_5509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5510_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_5503_,
        v_options_5504_,
        v_currNamespace_5505_,
        v_openDecls_5506_,
        v_n_5507_,
    );
    v___x_5511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5511_, 0, v___x_5510_);
    crate::leanh::lean_ctor_set(v___x_5511_, 1, v___y_5509_);
    return v___x_5511_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed(
    mut v_env_5512_: *mut crate::leanh::LeanObject,
    mut v_options_5513_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5514_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5515_: *mut crate::leanh::LeanObject,
    mut v_n_5516_: *mut crate::leanh::LeanObject,
    mut v___y_5517_: *mut crate::leanh::LeanObject,
    mut v___y_5518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5519_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4(v_env_5512_, v_options_5513_, v_currNamespace_5514_, v_openDecls_5515_, v_n_5516_, v___y_5517_, v___y_5518_);
    crate::leanh::lean_dec_ref(v___y_5517_);
    crate::leanh::lean_dec_ref(v_options_5513_);
    return v_res_5519_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(
    mut v_keys_5520_: *mut crate::leanh::LeanObject,
    mut v_i_5521_: *mut crate::leanh::LeanObject,
    mut v_k_5522_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: u8 = 0;
    let mut v_k_x27_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: u8 = 0;
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5523_ = lean_array_get_size(v_keys_5520_);
                v___x_5524_ = lean_nat_dec_lt(v_i_5521_, v___x_5523_);
                if v___x_5524_ == 0 {
                    crate::leanh::lean_dec(v_i_5521_);
                    return v___x_5524_;
                } else {
                    v_k_x27_5525_ = lean_array_fget_borrowed(v_keys_5520_, v_i_5521_);
                    v___x_5526_ = l_Lean_instBEqExtraModUse_beq(v_k_5522_, v_k_x27_5525_);
                    if v___x_5526_ == 0 {
                        v___x_5527_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5528_ = lean_nat_add(v_i_5521_, v___x_5527_);
                        crate::leanh::lean_dec(v_i_5521_);
                        v_i_5521_ = v___x_5528_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_5521_);
                        return v___x_5526_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg___boxed(
    mut v_keys_5530_: *mut crate::leanh::LeanObject,
    mut v_i_5531_: *mut crate::leanh::LeanObject,
    mut v_k_5532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5533_: u8 = 0;
    let mut v_r_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5533_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_5530_, v_i_5531_, v_k_5532_);
    crate::leanh::lean_dec_ref(v_k_5532_);
    crate::leanh::lean_dec_ref(v_keys_5530_);
    v_r_5534_ = crate::leanh::lean_box((v_res_5533_) as usize);
    return v_r_5534_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0()
-> usize {
    let mut v___x_5535_: usize = 0;
    let mut v___x_5536_: usize = 0;
    let mut v___x_5537_: usize = 0;
    v___x_5535_ = 5usize;
    v___x_5536_ = 1usize;
    v___x_5537_ = lean_usize_shift_left(v___x_5536_, v___x_5535_);
    return v___x_5537_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1()
-> usize {
    let mut v___x_5538_: usize = 0;
    let mut v___x_5539_: usize = 0;
    let mut v___x_5540_: usize = 0;
    v___x_5538_ = 1usize;
    v___x_5539_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__0);
    v___x_5540_ = lean_usize_sub(v___x_5539_, v___x_5538_);
    return v___x_5540_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(
    mut v_x_5541_: *mut crate::leanh::LeanObject,
    mut v_x_5542_: usize,
    mut v_x_5543_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: usize = 0;
    let mut v___x_5547_: usize = 0;
    let mut v___x_5548_: usize = 0;
    let mut v_j_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: u8 = 0;
    let mut v_node_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: usize = 0;
    let mut v___x_5556_: u8 = 0;
    let mut v_ks_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5541_) == 0 {
                    v_es_5544_ = crate::leanh::lean_ctor_get(v_x_5541_, 0);
                    v___x_5545_ = crate::leanh::lean_box(2);
                    v___x_5546_ = 5usize;
                    v___x_5547_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___closed__1);
                    v___x_5548_ = lean_usize_land(v_x_5542_, v___x_5547_);
                    v_j_5549_ = lean_usize_to_nat(v___x_5548_);
                    v___x_5550_ = lean_array_get_borrowed(v___x_5545_, v_es_5544_, v_j_5549_);
                    crate::leanh::lean_dec(v_j_5549_);
                    match crate::leanh::lean_obj_tag(v___x_5550_) {
                        0 => {
                            v_key_5551_ = crate::leanh::lean_ctor_get(v___x_5550_, 0);
                            v___x_5552_ = l_Lean_instBEqExtraModUse_beq(v_x_5543_, v_key_5551_);
                            return v___x_5552_;
                        }
                        1 => {
                            v_node_5553_ = crate::leanh::lean_ctor_get(v___x_5550_, 0);
                            v___x_5554_ = lean_usize_shift_right(v_x_5542_, v___x_5546_);
                            v_x_5541_ = v_node_5553_;
                            v_x_5542_ = v___x_5554_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5556_ = 0;
                            return v___x_5556_;
                        }
                    }
                } else {
                    v_ks_5557_ = crate::leanh::lean_ctor_get(v_x_5541_, 0);
                    v___x_5558_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5559_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_ks_5557_, v___x_5558_, v_x_5543_);
                    return v___x_5559_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg___boxed(
    mut v_x_5560_: *mut crate::leanh::LeanObject,
    mut v_x_5561_: *mut crate::leanh::LeanObject,
    mut v_x_5562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33537__boxed_5563_: usize = 0;
    let mut v_res_5564_: u8 = 0;
    let mut v_r_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33537__boxed_5563_ = crate::leanh::lean_unbox_usize(v_x_5561_);
    crate::leanh::lean_dec(v_x_5561_);
    v_res_5564_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_5560_, v_x_33537__boxed_5563_, v_x_5562_);
    crate::leanh::lean_dec_ref(v_x_5562_);
    crate::leanh::lean_dec_ref(v_x_5560_);
    v_r_5565_ = crate::leanh::lean_box((v_res_5564_) as usize);
    return v_r_5565_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(
    mut v_x_5566_: *mut crate::leanh::LeanObject,
    mut v_x_5567_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5568_: u64 = 0;
    let mut v___x_5569_: usize = 0;
    let mut v___x_5570_: u8 = 0;
    v___x_5568_ = l_Lean_instHashableExtraModUse_hash(v_x_5567_);
    v___x_5569_ = lean_uint64_to_usize(v___x_5568_);
    v___x_5570_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_5566_, v___x_5569_, v_x_5567_);
    return v___x_5570_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg___boxed(
    mut v_x_5571_: *mut crate::leanh::LeanObject,
    mut v_x_5572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5573_: u8 = 0;
    let mut v_r_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5573_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_5571_, v_x_5572_);
    crate::leanh::lean_dec_ref(v_x_5572_);
    crate::leanh::lean_dec_ref(v_x_5571_);
    v_r_5574_ = crate::leanh::lean_box((v_res_5573_) as usize);
    return v_r_5574_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5577_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__1;
    v___x_5578_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__0;
    v___x_5579_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5578_,
        v___x_5577_,
    );
    return v___x_5579_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5584_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__5;
    v___x_5585_ = l_Lean_stringToMessageData(v___x_5584_);
    return v___x_5585_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5587_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__7;
    v___x_5588_ = l_Lean_stringToMessageData(v___x_5587_);
    return v___x_5588_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5589_ =
        l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__34;
    v___x_5590_ = l_Lean_stringToMessageData(v___x_5589_);
    return v___x_5590_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_5591_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4;
    v___x_5592_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5___closed__1;
    v___x_5593_ = l_Lean_Name_append(v___x_5592_, v_cls_5591_);
    return v___x_5593_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5595_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__11;
    v___x_5596_ = l_Lean_stringToMessageData(v___x_5595_);
    return v___x_5596_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5598_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__13;
    v___x_5599_ = l_Lean_stringToMessageData(v___x_5598_);
    return v___x_5599_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(
    mut v_mod_5604_: *mut crate::leanh::LeanObject,
    mut v_isMeta_5605_: u8,
    mut v_hint_5606_: *mut crate::leanh::LeanObject,
    mut v___y_5607_: *mut crate::leanh::LeanObject,
    mut v___y_5608_: *mut crate::leanh::LeanObject,
    mut v___y_5609_: *mut crate::leanh::LeanObject,
    mut v___y_5610_: *mut crate::leanh::LeanObject,
    mut v___y_5611_: *mut crate::leanh::LeanObject,
    mut v___y_5612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_5616_: u8 = 0;
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v_asyncMode_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5653_: u8 = 0;
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5661_: u8 = 0;
    let mut v_unused_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5664_: u8 = 0;
    let mut v_unused_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: u8 = 0;
    let mut v_options_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5669_: u8 = 0;
    let mut v_inheritedTraceOptions_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: u8 = 0;
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: u8 = 0;
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5614_ = lean_st_ref_get(v___y_5612_);
                v_env_5615_ = crate::leanh::lean_ctor_get(v___x_5614_, 0);
                crate::leanh::lean_inc_ref(v_env_5615_);
                crate::leanh::lean_dec(v___x_5614_);
                v_isExporting_5616_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_5615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_5615_);
                v___x_5617_ = lean_st_ref_get(v___y_5612_);
                v_env_5618_ = crate::leanh::lean_ctor_get(v___x_5617_, 0);
                crate::leanh::lean_inc_ref(v_env_5618_);
                crate::leanh::lean_dec(v___x_5617_);
                v___x_5619_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__2);
                crate::leanh::lean_inc(v_mod_5604_);
                v_entry_5620_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_5620_, 0, v_mod_5604_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_5620_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_5616_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_5620_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_5605_,
                );
                v___x_5621_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_5622_ = crate::leanh::lean_box(1);
                v___x_5623_ = crate::leanh::lean_box(0);
                v___x_5666_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_5619_,
                    v___x_5621_,
                    v_env_5618_,
                    v___x_5622_,
                    v___x_5623_,
                );
                v___x_5667_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v___x_5666_, v_entry_5620_);
                crate::leanh::lean_dec(v___x_5666_);
                if v___x_5667_ == 0 {
                    v_options_5668_ = crate::leanh::lean_ctor_get(v___y_5611_, 2);
                    v_hasTrace_5669_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_5668_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5669_ == 0 {
                        crate::leanh::lean_dec(v_hint_5606_);
                        crate::leanh::lean_dec(v_mod_5604_);
                        v___y_5625_ = v___y_5610_;
                        v___y_5626_ = v___y_5612_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5670_ =
                            crate::leanh::lean_ctor_get(v___y_5611_, 13);
                        v_cls_5671_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__4;
                        v___x_5691_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__10);
                        v___x_5692_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5670_,
                            v_options_5668_,
                            v___x_5691_,
                        );
                        if v___x_5692_ == 0 {
                            crate::leanh::lean_dec(v_hint_5606_);
                            crate::leanh::lean_dec(v_mod_5604_);
                            v___y_5625_ = v___y_5610_;
                            v___y_5626_ = v___y_5612_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5693_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__12);
                            if v_isExporting_5616_ == 0 {
                                v___x_5702_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__17;
                                v___y_5695_ = v___x_5702_;
                                state = 8;
                                continue;
                            } else {
                                v___x_5703_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__18;
                                v___y_5695_ = v___x_5703_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_5620_, 1);
                    crate::leanh::lean_dec(v_hint_5606_);
                    crate::leanh::lean_dec(v_mod_5604_);
                    v___x_5704_ = crate::leanh::lean_box(0);
                    v___x_5705_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5705_, 0, v___x_5704_);
                    return v___x_5705_;
                }
            }
            1 => {
                v___x_5627_ = lean_st_ref_take(v___y_5626_);
                v_toEnvExtension_5628_ = crate::leanh::lean_ctor_get(v___x_5621_, 0);
                v_env_5629_ = crate::leanh::lean_ctor_get(v___x_5627_, 0);
                v_nextMacroScope_5630_ = crate::leanh::lean_ctor_get(v___x_5627_, 1);
                v_ngen_5631_ = crate::leanh::lean_ctor_get(v___x_5627_, 2);
                v_auxDeclNGen_5632_ = crate::leanh::lean_ctor_get(v___x_5627_, 3);
                v_traceState_5633_ = crate::leanh::lean_ctor_get(v___x_5627_, 4);
                v_messages_5634_ = crate::leanh::lean_ctor_get(v___x_5627_, 6);
                v_infoState_5635_ = crate::leanh::lean_ctor_get(v___x_5627_, 7);
                v_snapshotTasks_5636_ = crate::leanh::lean_ctor_get(v___x_5627_, 8);
                v_isSharedCheck_5664_ = (!crate::leanh::lean_is_exclusive(v___x_5627_)) as u8;
                if v_isSharedCheck_5664_ == 0 {
                    v_unused_5665_ = crate::leanh::lean_ctor_get(v___x_5627_, 5);
                    crate::leanh::lean_dec(v_unused_5665_);
                    v___x_5638_ = v___x_5627_;
                    v_isShared_5639_ = v_isSharedCheck_5664_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5636_);
                    crate::leanh::lean_inc(v_infoState_5635_);
                    crate::leanh::lean_inc(v_messages_5634_);
                    crate::leanh::lean_inc(v_traceState_5633_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5632_);
                    crate::leanh::lean_inc(v_ngen_5631_);
                    crate::leanh::lean_inc(v_nextMacroScope_5630_);
                    crate::leanh::lean_inc(v_env_5629_);
                    crate::leanh::lean_dec(v___x_5627_);
                    v___x_5638_ = crate::leanh::lean_box(0);
                    v_isShared_5639_ = v_isSharedCheck_5664_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_5640_ = crate::leanh::lean_ctor_get(v_toEnvExtension_5628_, 2);
                v___x_5641_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_5621_,
                    v_env_5629_,
                    v_entry_5620_,
                    v_asyncMode_5640_,
                    v___x_5623_,
                );
                v___x_5642_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2_once), _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__2);
                if v_isShared_5639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5638_, 5, v___x_5642_);
                    crate::leanh::lean_ctor_set(v___x_5638_, 0, v___x_5641_);
                    v___x_5644_ = v___x_5638_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5663_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 0, v___x_5641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 1, v_nextMacroScope_5630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 2, v_ngen_5631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 3, v_auxDeclNGen_5632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 4, v_traceState_5633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 5, v___x_5642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 6, v_messages_5634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 7, v_infoState_5635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 8, v_snapshotTasks_5636_);
                    v___x_5644_ = v_reuseFailAlloc_5663_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5645_ = lean_st_ref_set(v___y_5626_, v___x_5644_);
                v___x_5646_ = lean_st_ref_take(v___y_5625_);
                v_mctx_5647_ = crate::leanh::lean_ctor_get(v___x_5646_, 0);
                v_zetaDeltaFVarIds_5648_ = crate::leanh::lean_ctor_get(v___x_5646_, 2);
                v_postponed_5649_ = crate::leanh::lean_ctor_get(v___x_5646_, 3);
                v_diag_5650_ = crate::leanh::lean_ctor_get(v___x_5646_, 4);
                v_isSharedCheck_5661_ = (!crate::leanh::lean_is_exclusive(v___x_5646_)) as u8;
                if v_isSharedCheck_5661_ == 0 {
                    v_unused_5662_ = crate::leanh::lean_ctor_get(v___x_5646_, 1);
                    crate::leanh::lean_dec(v_unused_5662_);
                    v___x_5652_ = v___x_5646_;
                    v_isShared_5653_ = v_isSharedCheck_5661_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5650_);
                    crate::leanh::lean_inc(v_postponed_5649_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5648_);
                    crate::leanh::lean_inc(v_mctx_5647_);
                    crate::leanh::lean_dec(v___x_5646_);
                    v___x_5652_ = crate::leanh::lean_box(0);
                    v_isShared_5653_ = v_isSharedCheck_5661_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5654_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3_once), _init_l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg___closed__3);
                if v_isShared_5653_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5652_, 1, v___x_5654_);
                    v___x_5656_ = v___x_5652_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5660_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_mctx_5647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 1, v___x_5654_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5660_,
                        2,
                        v_zetaDeltaFVarIds_5648_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 3, v_postponed_5649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 4, v_diag_5650_);
                    v___x_5656_ = v_reuseFailAlloc_5660_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5657_ = lean_st_ref_set(v___y_5625_, v___x_5656_);
                v___x_5658_ = crate::leanh::lean_box(0);
                v___x_5659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5659_, 0, v___x_5658_);
                return v___x_5659_;
            }
            6 => {
                v___x_5675_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5675_, 0, v___y_5673_);
                crate::leanh::lean_ctor_set(v___x_5675_, 1, v___y_5674_);
                v___x_5676_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_5671_, v___x_5675_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_);
                if crate::leanh::lean_obj_tag(v___x_5676_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5676_, 1);
                    v___y_5625_ = v___y_5610_;
                    v___y_5626_ = v___y_5612_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_5620_, 1);
                    return v___x_5676_;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v___y_5679_);
                v___x_5680_ = l_Lean_stringToMessageData(v___y_5679_);
                v___x_5681_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5681_, 0, v___y_5678_);
                crate::leanh::lean_ctor_set(v___x_5681_, 1, v___x_5680_);
                v___x_5682_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__6);
                v___x_5683_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5683_, 0, v___x_5681_);
                crate::leanh::lean_ctor_set(v___x_5683_, 1, v___x_5682_);
                v___x_5684_ = l_Lean_MessageData_ofName(v_mod_5604_);
                v___x_5685_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5685_, 0, v___x_5683_);
                crate::leanh::lean_ctor_set(v___x_5685_, 1, v___x_5684_);
                v___x_5686_ = l_Lean_Name_isAnonymous(v_hint_5606_);
                if v___x_5686_ == 0 {
                    v___x_5687_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__8);
                    v___x_5688_ = l_Lean_MessageData_ofName(v_hint_5606_);
                    v___x_5689_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5689_, 0, v___x_5687_);
                    crate::leanh::lean_ctor_set(v___x_5689_, 1, v___x_5688_);
                    v___y_5673_ = v___x_5685_;
                    v___y_5674_ = v___x_5689_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_5606_);
                    v___x_5690_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__9);
                    v___y_5673_ = v___x_5685_;
                    v___y_5674_ = v___x_5690_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v___y_5695_);
                v___x_5696_ = l_Lean_stringToMessageData(v___y_5695_);
                v___x_5697_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5697_, 0, v___x_5693_);
                crate::leanh::lean_ctor_set(v___x_5697_, 1, v___x_5696_);
                v___x_5698_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__14);
                v___x_5699_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5699_, 0, v___x_5697_);
                crate::leanh::lean_ctor_set(v___x_5699_, 1, v___x_5698_);
                if v_isMeta_5605_ == 0 {
                    v___x_5700_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__15;
                    v___y_5678_ = v___x_5699_;
                    v___y_5679_ = v___x_5700_;
                    state = 7;
                    continue;
                } else {
                    v___x_5701_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___closed__16;
                    v___y_5678_ = v___x_5699_;
                    v___y_5679_ = v___x_5701_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5___boxed(
    mut v_mod_5706_: *mut crate::leanh::LeanObject,
    mut v_isMeta_5707_: *mut crate::leanh::LeanObject,
    mut v_hint_5708_: *mut crate::leanh::LeanObject,
    mut v___y_5709_: *mut crate::leanh::LeanObject,
    mut v___y_5710_: *mut crate::leanh::LeanObject,
    mut v___y_5711_: *mut crate::leanh::LeanObject,
    mut v___y_5712_: *mut crate::leanh::LeanObject,
    mut v___y_5713_: *mut crate::leanh::LeanObject,
    mut v___y_5714_: *mut crate::leanh::LeanObject,
    mut v___y_5715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_5716_: u8 = 0;
    let mut v_res_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_5716_ = (crate::leanh::lean_unbox(v_isMeta_5707_) as u8);
    v_res_5717_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_mod_5706_, v_isMeta_boxed_5716_, v_hint_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
    crate::leanh::lean_dec(v___y_5714_);
    crate::leanh::lean_dec_ref(v___y_5713_);
    crate::leanh::lean_dec(v___y_5712_);
    crate::leanh::lean_dec_ref(v___y_5711_);
    crate::leanh::lean_dec(v___y_5710_);
    crate::leanh::lean_dec_ref(v___y_5709_);
    return v_res_5717_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(
    mut v___x_5718_: *mut crate::leanh::LeanObject,
    mut v_declName_5719_: *mut crate::leanh::LeanObject,
    mut v_as_5720_: *mut crate::leanh::LeanObject,
    mut v_sz_5721_: usize,
    mut v_i_5722_: usize,
    mut v_b_5723_: *mut crate::leanh::LeanObject,
    mut v___y_5724_: *mut crate::leanh::LeanObject,
    mut v___y_5725_: *mut crate::leanh::LeanObject,
    mut v___y_5726_: *mut crate::leanh::LeanObject,
    mut v___y_5727_: *mut crate::leanh::LeanObject,
    mut v___y_5728_: *mut crate::leanh::LeanObject,
    mut v___y_5729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5731_: u8 = 0;
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: u8 = 0;
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: usize = 0;
    let mut v___x_5744_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5731_ = lean_usize_dec_lt(v_i_5722_, v_sz_5721_);
                if v___x_5731_ == 0 {
                    crate::leanh::lean_dec(v_declName_5719_);
                    v___x_5732_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5732_, 0, v_b_5723_);
                    return v___x_5732_;
                } else {
                    v___x_5733_ = l_Lean_Environment_header(v___x_5718_);
                    v_modules_5734_ = crate::leanh::lean_ctor_get(v___x_5733_, 3);
                    crate::leanh::lean_inc_ref(v_modules_5734_);
                    crate::leanh::lean_dec_ref(v___x_5733_);
                    v___x_5735_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_5736_ = lean_array_uget_borrowed(v_as_5720_, v_i_5722_);
                    v___x_5737_ = lean_array_get(v___x_5735_, v_modules_5734_, v_a_5736_);
                    crate::leanh::lean_dec_ref(v_modules_5734_);
                    v_toImport_5738_ = crate::leanh::lean_ctor_get(v___x_5737_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_5738_);
                    crate::leanh::lean_dec(v___x_5737_);
                    v_module_5739_ = crate::leanh::lean_ctor_get(v_toImport_5738_, 0);
                    crate::leanh::lean_inc(v_module_5739_);
                    crate::leanh::lean_dec_ref(v_toImport_5738_);
                    v___x_5740_ = 0;
                    crate::leanh::lean_inc(v_declName_5719_);
                    v___x_5741_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_5739_, v___x_5740_, v_declName_5719_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_);
                    if crate::leanh::lean_obj_tag(v___x_5741_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5741_, 1);
                        v___x_5742_ = crate::leanh::lean_box(0);
                        v___x_5743_ = 1usize;
                        v___x_5744_ = lean_usize_add(v_i_5722_, v___x_5743_);
                        v_i_5722_ = v___x_5744_;
                        v_b_5723_ = v___x_5742_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_5719_);
                        return v___x_5741_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6___boxed(
    mut v___x_5746_: *mut crate::leanh::LeanObject,
    mut v_declName_5747_: *mut crate::leanh::LeanObject,
    mut v_as_5748_: *mut crate::leanh::LeanObject,
    mut v_sz_5749_: *mut crate::leanh::LeanObject,
    mut v_i_5750_: *mut crate::leanh::LeanObject,
    mut v_b_5751_: *mut crate::leanh::LeanObject,
    mut v___y_5752_: *mut crate::leanh::LeanObject,
    mut v___y_5753_: *mut crate::leanh::LeanObject,
    mut v___y_5754_: *mut crate::leanh::LeanObject,
    mut v___y_5755_: *mut crate::leanh::LeanObject,
    mut v___y_5756_: *mut crate::leanh::LeanObject,
    mut v___y_5757_: *mut crate::leanh::LeanObject,
    mut v___y_5758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5759_: usize = 0;
    let mut v_i_boxed_5760_: usize = 0;
    let mut v_res_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5759_ = crate::leanh::lean_unbox_usize(v_sz_5749_);
    crate::leanh::lean_dec(v_sz_5749_);
    v_i_boxed_5760_ = crate::leanh::lean_unbox_usize(v_i_5750_);
    crate::leanh::lean_dec(v_i_5750_);
    v_res_5761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v___x_5746_, v_declName_5747_, v_as_5748_, v_sz_boxed_5759_, v_i_boxed_5760_, v_b_5751_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_, v___y_5757_);
    crate::leanh::lean_dec(v___y_5757_);
    crate::leanh::lean_dec_ref(v___y_5756_);
    crate::leanh::lean_dec(v___y_5755_);
    crate::leanh::lean_dec_ref(v___y_5754_);
    crate::leanh::lean_dec(v___y_5753_);
    crate::leanh::lean_dec_ref(v___y_5752_);
    crate::leanh::lean_dec_ref(v_as_5748_);
    crate::leanh::lean_dec_ref(v___x_5746_);
    return v_res_5761_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(
    mut v_a_5762_: *mut crate::leanh::LeanObject,
    mut v_x_5763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: u8 = 0;
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5763_) == 0 {
                    v___x_5764_ = crate::leanh::lean_box(0);
                    return v___x_5764_;
                } else {
                    v_key_5765_ = crate::leanh::lean_ctor_get(v_x_5763_, 0);
                    v_value_5766_ = crate::leanh::lean_ctor_get(v_x_5763_, 1);
                    v_tail_5767_ = crate::leanh::lean_ctor_get(v_x_5763_, 2);
                    v___x_5768_ = lean_name_eq(v_key_5765_, v_a_5762_);
                    if v___x_5768_ == 0 {
                        v_x_5763_ = v_tail_5767_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5766_);
                        v___x_5770_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5770_, 0, v_value_5766_);
                        return v___x_5770_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg___boxed(
    mut v_a_5771_: *mut crate::leanh::LeanObject,
    mut v_x_5772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5773_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_5771_, v_x_5772_);
    crate::leanh::lean_dec(v_x_5772_);
    crate::leanh::lean_dec(v_a_5771_);
    return v_res_5773_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0()
-> u64 {
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: u64 = 0;
    v___x_5774_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_5775_ = lean_uint64_of_nat(v___x_5774_);
    return v___x_5775_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(
    mut v_m_5776_: *mut crate::leanh::LeanObject,
    mut v_a_5777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5781_: u64 = 0;
    let mut v___x_5782_: u64 = 0;
    let mut v___x_5783_: u64 = 0;
    let mut v_fold_5784_: u64 = 0;
    let mut v___x_5785_: u64 = 0;
    let mut v___x_5786_: u64 = 0;
    let mut v___x_5787_: u64 = 0;
    let mut v___x_5788_: usize = 0;
    let mut v___x_5789_: usize = 0;
    let mut v___x_5790_: usize = 0;
    let mut v___x_5791_: usize = 0;
    let mut v___x_5792_: usize = 0;
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: u64 = 0;
    let mut v_hash_5796_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_5778_ = crate::leanh::lean_ctor_get(v_m_5776_, 1);
                v___x_5779_ = lean_array_get_size(v_buckets_5778_);
                if crate::leanh::lean_obj_tag(v_a_5777_) == 0 {
                    v___x_5795_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___closed__0);
                    v___y_5781_ = v___x_5795_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5796_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_5777_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5781_ = v_hash_5796_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5782_ = 32u64;
                v___x_5783_ = lean_uint64_shift_right(v___y_5781_, v___x_5782_);
                v_fold_5784_ = lean_uint64_xor(v___y_5781_, v___x_5783_);
                v___x_5785_ = 16u64;
                v___x_5786_ = lean_uint64_shift_right(v_fold_5784_, v___x_5785_);
                v___x_5787_ = lean_uint64_xor(v_fold_5784_, v___x_5786_);
                v___x_5788_ = lean_uint64_to_usize(v___x_5787_);
                v___x_5789_ = lean_usize_of_nat(v___x_5779_);
                v___x_5790_ = 1usize;
                v___x_5791_ = lean_usize_sub(v___x_5789_, v___x_5790_);
                v___x_5792_ = lean_usize_land(v___x_5788_, v___x_5791_);
                v___x_5793_ = lean_array_uget_borrowed(v_buckets_5778_, v___x_5792_);
                v___x_5794_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_5777_, v___x_5793_);
                return v___x_5794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_m_5797_: *mut crate::leanh::LeanObject,
    mut v_a_5798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5799_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_5797_, v_a_5798_);
    crate::leanh::lean_dec(v_a_5798_);
    crate::leanh::lean_dec_ref(v_m_5797_);
    return v_res_5799_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5802_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__1;
    v___x_5803_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__0;
    v___x_5804_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5803_,
        v___x_5802_,
    );
    return v___x_5804_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(
    mut v_declName_5807_: *mut crate::leanh::LeanObject,
    mut v_isMeta_5808_: u8,
    mut v___y_5809_: *mut crate::leanh::LeanObject,
    mut v___y_5810_: *mut crate::leanh::LeanObject,
    mut v___y_5811_: *mut crate::leanh::LeanObject,
    mut v___y_5812_: *mut crate::leanh::LeanObject,
    mut v___y_5813_: *mut crate::leanh::LeanObject,
    mut v___y_5814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5824_: usize = 0;
    let mut v___x_5825_: usize = 0;
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5829_: u8 = 0;
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5833_: u8 = 0;
    let mut v_unused_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: u8 = 0;
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5846_: u8 = 0;
    let mut v_toImport_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: u8 = 0;
    let mut v___x_5858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5816_ = lean_st_ref_get(v___y_5814_);
                v_env_5820_ = crate::leanh::lean_ctor_get(v___x_5816_, 0);
                crate::leanh::lean_inc_ref(v_env_5820_);
                crate::leanh::lean_dec(v___x_5816_);
                v___x_5835_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5820_, v_declName_5807_);
                if crate::leanh::lean_obj_tag(v___x_5835_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_5820_);
                    crate::leanh::lean_dec(v_declName_5807_);
                    state = 1;
                    continue;
                } else {
                    v_val_5836_ = crate::leanh::lean_ctor_get(v___x_5835_, 0);
                    crate::leanh::lean_inc(v_val_5836_);
                    crate::leanh::lean_dec_ref_known(v___x_5835_, 1);
                    v___x_5837_ = l_Lean_Environment_header(v_env_5820_);
                    v_modules_5838_ = crate::leanh::lean_ctor_get(v___x_5837_, 3);
                    crate::leanh::lean_inc_ref(v_modules_5838_);
                    crate::leanh::lean_dec_ref(v___x_5837_);
                    v___x_5839_ = lean_array_get_size(v_modules_5838_);
                    v___x_5840_ = lean_nat_dec_lt(v_val_5836_, v___x_5839_);
                    if v___x_5840_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_5838_);
                        crate::leanh::lean_dec(v_val_5836_);
                        crate::leanh::lean_dec_ref(v_env_5820_);
                        crate::leanh::lean_dec(v_declName_5807_);
                        state = 1;
                        continue;
                    } else {
                        v___x_5841_ = lean_st_ref_get(v___y_5814_);
                        v_env_5842_ = crate::leanh::lean_ctor_get(v___x_5841_, 0);
                        crate::leanh::lean_inc_ref(v_env_5842_);
                        crate::leanh::lean_dec(v___x_5841_);
                        v___x_5843_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__2);
                        v___x_5844_ = lean_array_fget(v_modules_5838_, v_val_5836_);
                        crate::leanh::lean_dec(v_val_5836_);
                        crate::leanh::lean_dec_ref(v_modules_5838_);
                        if v_isMeta_5808_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_5842_);
                            v___y_5846_ = v_isMeta_5808_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_5807_);
                            v___x_5857_ = l_Lean_isMarkedMeta(v_env_5842_, v_declName_5807_);
                            if v___x_5857_ == 0 {
                                v___y_5846_ = v_isMeta_5808_;
                                state = 5;
                                continue;
                            } else {
                                v___x_5858_ = 0;
                                v___y_5846_ = v___x_5858_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5818_ = crate::leanh::lean_box(0);
                v___x_5819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5819_, 0, v___x_5818_);
                return v___x_5819_;
            }
            2 => {
                v___x_5823_ = crate::leanh::lean_box(0);
                v_sz_5824_ = lean_array_size(v___y_5822_);
                v___x_5825_ = 0usize;
                v___x_5826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__6(v_env_5820_, v_declName_5807_, v___y_5822_, v_sz_5824_, v___x_5825_, v___x_5823_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_);
                crate::leanh::lean_dec_ref(v___y_5822_);
                crate::leanh::lean_dec_ref(v_env_5820_);
                if crate::leanh::lean_obj_tag(v___x_5826_) == 0 {
                    v_isSharedCheck_5833_ = (!crate::leanh::lean_is_exclusive(v___x_5826_)) as u8;
                    if v_isSharedCheck_5833_ == 0 {
                        v_unused_5834_ = crate::leanh::lean_ctor_get(v___x_5826_, 0);
                        crate::leanh::lean_dec(v_unused_5834_);
                        v___x_5828_ = v___x_5826_;
                        v_isShared_5829_ = v_isSharedCheck_5833_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5826_);
                        v___x_5828_ = crate::leanh::lean_box(0);
                        v_isShared_5829_ = v_isSharedCheck_5833_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_5826_;
                }
            }
            3 => {
                if v_isShared_5829_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5828_, 0, v___x_5823_);
                    v___x_5831_ = v___x_5828_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5832_, 0, v___x_5823_);
                    v___x_5831_ = v_reuseFailAlloc_5832_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5831_;
            }
            5 => {
                v_toImport_5847_ = crate::leanh::lean_ctor_get(v___x_5844_, 0);
                crate::leanh::lean_inc_ref(v_toImport_5847_);
                crate::leanh::lean_dec(v___x_5844_);
                v_module_5848_ = crate::leanh::lean_ctor_get(v_toImport_5847_, 0);
                crate::leanh::lean_inc(v_module_5848_);
                crate::leanh::lean_dec_ref(v_toImport_5847_);
                crate::leanh::lean_inc(v_declName_5807_);
                v___x_5849_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5(v_module_5848_, v___y_5846_, v_declName_5807_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_);
                if crate::leanh::lean_obj_tag(v___x_5849_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5849_, 1);
                    v___x_5850_ = l_Lean_indirectModUseExt;
                    v___x_5851_ = crate::leanh::lean_box(1);
                    v___x_5852_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_5820_);
                    v___x_5853_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_5843_,
                        v___x_5850_,
                        v_env_5820_,
                        v___x_5851_,
                        v___x_5852_,
                    );
                    v___x_5854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v___x_5853_, v_declName_5807_);
                    crate::leanh::lean_dec(v___x_5853_);
                    if crate::leanh::lean_obj_tag(v___x_5854_) == 0 {
                        v___x_5855_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___closed__3;
                        v___y_5822_ = v___x_5855_;
                        state = 2;
                        continue;
                    } else {
                        v_val_5856_ = crate::leanh::lean_ctor_get(v___x_5854_, 0);
                        crate::leanh::lean_inc(v_val_5856_);
                        crate::leanh::lean_dec_ref_known(v___x_5854_, 1);
                        v___y_5822_ = v_val_5856_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_5820_);
                    crate::leanh::lean_dec(v_declName_5807_);
                    return v___x_5849_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3___boxed(
    mut v_declName_5859_: *mut crate::leanh::LeanObject,
    mut v_isMeta_5860_: *mut crate::leanh::LeanObject,
    mut v___y_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
    mut v___y_5864_: *mut crate::leanh::LeanObject,
    mut v___y_5865_: *mut crate::leanh::LeanObject,
    mut v___y_5866_: *mut crate::leanh::LeanObject,
    mut v___y_5867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_5868_: u8 = 0;
    let mut v_res_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_5868_ = (crate::leanh::lean_unbox(v_isMeta_5860_) as u8);
    v_res_5869_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_declName_5859_, v_isMeta_boxed_5868_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_);
    crate::leanh::lean_dec(v___y_5866_);
    crate::leanh::lean_dec_ref(v___y_5865_);
    crate::leanh::lean_dec(v___y_5864_);
    crate::leanh::lean_dec_ref(v___y_5863_);
    crate::leanh::lean_dec(v___y_5862_);
    crate::leanh::lean_dec_ref(v___y_5861_);
    return v_res_5869_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(
    mut v_as_x27_5870_: *mut crate::leanh::LeanObject,
    mut v_b_5871_: *mut crate::leanh::LeanObject,
    mut v___y_5872_: *mut crate::leanh::LeanObject,
    mut v___y_5873_: *mut crate::leanh::LeanObject,
    mut v___y_5874_: *mut crate::leanh::LeanObject,
    mut v___y_5875_: *mut crate::leanh::LeanObject,
    mut v___y_5876_: *mut crate::leanh::LeanObject,
    mut v___y_5877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: u8 = 0;
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5870_) == 0 {
                    v___x_5879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5879_, 0, v_b_5871_);
                    return v___x_5879_;
                } else {
                    v_head_5880_ = crate::leanh::lean_ctor_get(v_as_x27_5870_, 0);
                    v_tail_5881_ = crate::leanh::lean_ctor_get(v_as_x27_5870_, 1);
                    v___x_5882_ = 1;
                    crate::leanh::lean_inc(v_head_5880_);
                    v___x_5883_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3(v_head_5880_, v___x_5882_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_);
                    if crate::leanh::lean_obj_tag(v___x_5883_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5883_, 1);
                        v___x_5884_ = crate::leanh::lean_box(0);
                        v_as_x27_5870_ = v_tail_5881_;
                        v_b_5871_ = v___x_5884_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5883_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg___boxed(
    mut v_as_x27_5886_: *mut crate::leanh::LeanObject,
    mut v_b_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
    mut v___y_5889_: *mut crate::leanh::LeanObject,
    mut v___y_5890_: *mut crate::leanh::LeanObject,
    mut v___y_5891_: *mut crate::leanh::LeanObject,
    mut v___y_5892_: *mut crate::leanh::LeanObject,
    mut v___y_5893_: *mut crate::leanh::LeanObject,
    mut v___y_5894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5895_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_5886_, v_b_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_);
    crate::leanh::lean_dec(v___y_5893_);
    crate::leanh::lean_dec_ref(v___y_5892_);
    crate::leanh::lean_dec(v___y_5891_);
    crate::leanh::lean_dec_ref(v___y_5890_);
    crate::leanh::lean_dec(v___y_5889_);
    crate::leanh::lean_dec_ref(v___y_5888_);
    crate::leanh::lean_dec(v_as_x27_5886_);
    return v_res_5895_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(
    mut v_currNamespace_5896_: *mut crate::leanh::LeanObject,
    mut v___y_5897_: *mut crate::leanh::LeanObject,
    mut v___y_5898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5899_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5899_, 0, v_currNamespace_5896_);
    crate::leanh::lean_ctor_set(v___x_5899_, 1, v___y_5898_);
    return v___x_5899_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed(
    mut v_currNamespace_5900_: *mut crate::leanh::LeanObject,
    mut v___y_5901_: *mut crate::leanh::LeanObject,
    mut v___y_5902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5903_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3(v_currNamespace_5900_, v___y_5901_, v___y_5902_);
    crate::leanh::lean_dec_ref(v___y_5901_);
    return v_res_5903_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(
    mut v_x_5904_: *mut crate::leanh::LeanObject,
    mut v___y_5905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5904_) == 0 {
        let mut v_a_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5906_ = crate::leanh::lean_ctor_get(v_x_5904_, 0);
        crate::leanh::lean_inc(v_a_5906_);
        v___x_5907_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5907_, 0, v_a_5906_);
        crate::leanh::lean_ctor_set(v___x_5907_, 1, v___y_5905_);
        return v___x_5907_;
    } else {
        let mut v_a_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5908_ = crate::leanh::lean_ctor_get(v_x_5904_, 0);
        crate::leanh::lean_inc(v_a_5908_);
        v___x_5909_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5909_, 0, v_a_5908_);
        crate::leanh::lean_ctor_set(v___x_5909_, 1, v___y_5905_);
        return v___x_5909_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg___boxed(
    mut v_x_5910_: *mut crate::leanh::LeanObject,
    mut v___y_5911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5912_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_5910_, v___y_5911_);
    crate::leanh::lean_dec_ref(v_x_5910_);
    return v_res_5912_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(
    mut v_env_5913_: *mut crate::leanh::LeanObject,
    mut v_stx_5914_: *mut crate::leanh::LeanObject,
    mut v___y_5915_: *mut crate::leanh::LeanObject,
    mut v___y_5916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5922_: u8 = 0;
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5927_: u8 = 0;
    let mut v_unused_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5932_: u8 = 0;
    let mut v_snd_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5938_: u8 = 0;
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5943_: u8 = 0;
    let mut v_a_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5948_: u8 = 0;
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5956_: u8 = 0;
    let mut v_isSharedCheck_5957_: u8 = 0;
    let mut v_a_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5962_: u8 = 0;
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5966_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5917_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_5913_,
                    v_stx_5914_,
                    v___y_5915_,
                    v___y_5916_,
                );
                if crate::leanh::lean_obj_tag(v___x_5917_) == 0 {
                    v_a_5918_ = crate::leanh::lean_ctor_get(v___x_5917_, 0);
                    crate::leanh::lean_inc(v_a_5918_);
                    if crate::leanh::lean_obj_tag(v_a_5918_) == 0 {
                        v_a_5919_ = crate::leanh::lean_ctor_get(v___x_5917_, 1);
                        v_isSharedCheck_5927_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5917_)) as u8;
                        if v_isSharedCheck_5927_ == 0 {
                            v_unused_5928_ = crate::leanh::lean_ctor_get(v___x_5917_, 0);
                            crate::leanh::lean_dec(v_unused_5928_);
                            v___x_5921_ = v___x_5917_;
                            v_isShared_5922_ = v_isSharedCheck_5927_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5919_);
                            crate::leanh::lean_dec(v___x_5917_);
                            v___x_5921_ = crate::leanh::lean_box(0);
                            v_isShared_5922_ = v_isSharedCheck_5927_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_5929_ = crate::leanh::lean_ctor_get(v_a_5918_, 0);
                        v_isSharedCheck_5957_ = (!crate::leanh::lean_is_exclusive(v_a_5918_)) as u8;
                        if v_isSharedCheck_5957_ == 0 {
                            v___x_5931_ = v_a_5918_;
                            v_isShared_5932_ = v_isSharedCheck_5957_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5929_);
                            crate::leanh::lean_dec(v_a_5918_);
                            v___x_5931_ = crate::leanh::lean_box(0);
                            v_isShared_5932_ = v_isSharedCheck_5957_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_5958_ = crate::leanh::lean_ctor_get(v___x_5917_, 0);
                    v_a_5959_ = crate::leanh::lean_ctor_get(v___x_5917_, 1);
                    v_isSharedCheck_5966_ = (!crate::leanh::lean_is_exclusive(v___x_5917_)) as u8;
                    if v_isSharedCheck_5966_ == 0 {
                        v___x_5961_ = v___x_5917_;
                        v_isShared_5962_ = v_isSharedCheck_5966_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5959_);
                        crate::leanh::lean_inc(v_a_5958_);
                        crate::leanh::lean_dec(v___x_5917_);
                        v___x_5961_ = crate::leanh::lean_box(0);
                        v_isShared_5962_ = v_isSharedCheck_5966_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5923_ = crate::leanh::lean_box(0);
                if v_isShared_5922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_5923_);
                    v___x_5925_ = v___x_5921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5926_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 0, v___x_5923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 1, v_a_5919_);
                    v___x_5925_ = v_reuseFailAlloc_5926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5925_;
            }
            3 => {
                v_snd_5933_ = crate::leanh::lean_ctor_get(v_val_5929_, 1);
                crate::leanh::lean_inc(v_snd_5933_);
                crate::leanh::lean_dec(v_val_5929_);
                if crate::leanh::lean_obj_tag(v_snd_5933_) == 0 {
                    crate::leanh::lean_del_object(v___x_5931_);
                    v_a_5934_ = crate::leanh::lean_ctor_get(v___x_5917_, 1);
                    crate::leanh::lean_inc(v_a_5934_);
                    crate::leanh::lean_dec_ref_known(v___x_5917_, 2);
                    v_a_5935_ = crate::leanh::lean_ctor_get(v_snd_5933_, 0);
                    v_isSharedCheck_5943_ = (!crate::leanh::lean_is_exclusive(v_snd_5933_)) as u8;
                    if v_isSharedCheck_5943_ == 0 {
                        v___x_5937_ = v_snd_5933_;
                        v_isShared_5938_ = v_isSharedCheck_5943_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5935_);
                        crate::leanh::lean_dec(v_snd_5933_);
                        v___x_5937_ = crate::leanh::lean_box(0);
                        v_isShared_5938_ = v_isSharedCheck_5943_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_5944_ = crate::leanh::lean_ctor_get(v___x_5917_, 1);
                    crate::leanh::lean_inc(v_a_5944_);
                    crate::leanh::lean_dec_ref_known(v___x_5917_, 2);
                    v_a_5945_ = crate::leanh::lean_ctor_get(v_snd_5933_, 0);
                    v_isSharedCheck_5956_ = (!crate::leanh::lean_is_exclusive(v_snd_5933_)) as u8;
                    if v_isSharedCheck_5956_ == 0 {
                        v___x_5947_ = v_snd_5933_;
                        v_isShared_5948_ = v_isSharedCheck_5956_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5945_);
                        crate::leanh::lean_dec(v_snd_5933_);
                        v___x_5947_ = crate::leanh::lean_box(0);
                        v_isShared_5948_ = v_isSharedCheck_5956_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5938_ == 0 {
                    v___x_5940_ = v___x_5937_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5942_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5942_, 0, v_a_5935_);
                    v___x_5940_ = v_reuseFailAlloc_5942_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5941_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_5940_, v_a_5934_);
                crate::leanh::lean_dec_ref(v___x_5940_);
                return v___x_5941_;
            }
            6 => {
                if v_isShared_5932_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5931_, 0, v_a_5945_);
                    v___x_5950_ = v___x_5931_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5955_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5955_, 0, v_a_5945_);
                    v___x_5950_ = v_reuseFailAlloc_5955_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5948_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5947_, 0, v___x_5950_);
                    v___x_5952_ = v___x_5947_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5954_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5954_, 0, v___x_5950_);
                    v___x_5952_ = v_reuseFailAlloc_5954_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5953_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v___x_5952_, v_a_5944_);
                crate::leanh::lean_dec_ref(v___x_5952_);
                return v___x_5953_;
            }
            9 => {
                if v_isShared_5962_ == 0 {
                    v___x_5964_ = v___x_5961_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5965_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5965_, 0, v_a_5958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5965_, 1, v_a_5959_);
                    v___x_5964_ = v_reuseFailAlloc_5965_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5964_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed(
    mut v_env_5967_: *mut crate::leanh::LeanObject,
    mut v_stx_5968_: *mut crate::leanh::LeanObject,
    mut v___y_5969_: *mut crate::leanh::LeanObject,
    mut v___y_5970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5971_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0(v_env_5967_, v_stx_5968_, v___y_5969_, v___y_5970_);
    crate::leanh::lean_dec_ref(v___y_5969_);
    return v_res_5971_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5977_ = l_Lean_maxRecDepthErrorMessage;
    v___x_5978_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5978_, 0, v___x_5977_);
    return v___x_5978_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5979_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__3);
    v___x_5980_ = l_Lean_MessageData_ofFormat(v___x_5979_);
    return v___x_5980_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5981_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__4);
    v___x_5982_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__2;
    v___x_5983_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5983_, 0, v___x_5982_);
    crate::leanh::lean_ctor_set(v___x_5983_, 1, v___x_5981_);
    return v___x_5983_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(
    mut v_ref_5984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5986_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___closed__5);
    v___x_5987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5987_, 0, v_ref_5984_);
    crate::leanh::lean_ctor_set(v___x_5987_, 1, v___x_5986_);
    v___x_5988_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5988_, 0, v___x_5987_);
    return v___x_5988_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg___boxed(
    mut v_ref_5989_: *mut crate::leanh::LeanObject,
    mut v___y_5990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5991_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_5989_);
    return v_res_5991_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(
    mut v_x_5993_: *mut crate::leanh::LeanObject,
    mut v___y_5994_: *mut crate::leanh::LeanObject,
    mut v___y_5995_: *mut crate::leanh::LeanObject,
    mut v___y_5996_: *mut crate::leanh::LeanObject,
    mut v___y_5997_: *mut crate::leanh::LeanObject,
    mut v___y_5998_: *mut crate::leanh::LeanObject,
    mut v___y_5999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6041_: u8 = 0;
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6049_: u8 = 0;
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6053_: u8 = 0;
    let mut v_unused_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6058_: u8 = 0;
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6062_: u8 = 0;
    let mut v_reuseFailAlloc_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6064_: u8 = 0;
    let mut v_unused_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_a_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: u8 = 0;
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6001_ = lean_st_ref_get(v___y_5999_);
                v_env_6002_ = crate::leanh::lean_ctor_get(v___x_6001_, 0);
                crate::leanh::lean_inc_ref_n(v_env_6002_, 4);
                crate::leanh::lean_dec(v___x_6001_);
                v_options_6003_ = crate::leanh::lean_ctor_get(v___y_5998_, 2);
                v_currRecDepth_6004_ = crate::leanh::lean_ctor_get(v___y_5998_, 3);
                v_maxRecDepth_6005_ = crate::leanh::lean_ctor_get(v___y_5998_, 4);
                v_ref_6006_ = crate::leanh::lean_ctor_get(v___y_5998_, 5);
                v_currNamespace_6007_ = crate::leanh::lean_ctor_get(v___y_5998_, 6);
                v_openDecls_6008_ = crate::leanh::lean_ctor_get(v___y_5998_, 7);
                v_quotContext_6009_ = crate::leanh::lean_ctor_get(v___y_5998_, 10);
                v_currMacroScope_6010_ = crate::leanh::lean_ctor_get(v___y_5998_, 11);
                v___x_6011_ = lean_st_ref_get(v___y_5999_);
                v_nextMacroScope_6012_ = crate::leanh::lean_ctor_get(v___x_6011_, 1);
                crate::leanh::lean_inc(v_nextMacroScope_6012_);
                crate::leanh::lean_dec(v___x_6011_);
                v___f_6013_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_6013_, 0, v_env_6002_);
                v___f_6014_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_6014_, 0, v_env_6002_);
                crate::leanh::lean_inc_n(v_openDecls_6008_, 2);
                crate::leanh::lean_inc_n(v_currNamespace_6007_, 3);
                v___f_6015_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 3);
                crate::leanh::lean_closure_set(v___f_6015_, 0, v_env_6002_);
                crate::leanh::lean_closure_set(v___f_6015_, 1, v_currNamespace_6007_);
                crate::leanh::lean_closure_set(v___f_6015_, 2, v_openDecls_6008_);
                v___f_6016_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 1);
                crate::leanh::lean_closure_set(v___f_6016_, 0, v_currNamespace_6007_);
                crate::leanh::lean_inc_ref(v_options_6003_);
                v___f_6017_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                crate::leanh::lean_closure_set(v___f_6017_, 0, v_env_6002_);
                crate::leanh::lean_closure_set(v___f_6017_, 1, v_options_6003_);
                crate::leanh::lean_closure_set(v___f_6017_, 2, v_currNamespace_6007_);
                crate::leanh::lean_closure_set(v___f_6017_, 3, v_openDecls_6008_);
                v_methods_6018_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v_methods_6018_, 0, v___f_6013_);
                crate::leanh::lean_ctor_set(v_methods_6018_, 1, v___f_6016_);
                crate::leanh::lean_ctor_set(v_methods_6018_, 2, v___f_6014_);
                crate::leanh::lean_ctor_set(v_methods_6018_, 3, v___f_6015_);
                crate::leanh::lean_ctor_set(v_methods_6018_, 4, v___f_6017_);
                crate::leanh::lean_inc(v_ref_6006_);
                crate::leanh::lean_inc(v_maxRecDepth_6005_);
                crate::leanh::lean_inc(v_currRecDepth_6004_);
                crate::leanh::lean_inc(v_currMacroScope_6010_);
                crate::leanh::lean_inc(v_quotContext_6009_);
                v___x_6019_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6019_, 0, v_methods_6018_);
                crate::leanh::lean_ctor_set(v___x_6019_, 1, v_quotContext_6009_);
                crate::leanh::lean_ctor_set(v___x_6019_, 2, v_currMacroScope_6010_);
                crate::leanh::lean_ctor_set(v___x_6019_, 3, v_currRecDepth_6004_);
                crate::leanh::lean_ctor_set(v___x_6019_, 4, v_maxRecDepth_6005_);
                crate::leanh::lean_ctor_set(v___x_6019_, 5, v_ref_6006_);
                v___x_6020_ = crate::leanh::lean_box(0);
                v___x_6021_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6021_, 0, v_nextMacroScope_6012_);
                crate::leanh::lean_ctor_set(v___x_6021_, 1, v___x_6020_);
                crate::leanh::lean_ctor_set(v___x_6021_, 2, v___x_6020_);
                v___x_6022_ = crate::leanh::lean_apply_2(v_x_5993_, v___x_6019_, v___x_6021_);
                if crate::leanh::lean_obj_tag(v___x_6022_) == 0 {
                    v_a_6023_ = crate::leanh::lean_ctor_get(v___x_6022_, 1);
                    crate::leanh::lean_inc(v_a_6023_);
                    v_a_6024_ = crate::leanh::lean_ctor_get(v___x_6022_, 0);
                    crate::leanh::lean_inc(v_a_6024_);
                    crate::leanh::lean_dec_ref_known(v___x_6022_, 2);
                    v_macroScope_6025_ = crate::leanh::lean_ctor_get(v_a_6023_, 0);
                    crate::leanh::lean_inc(v_macroScope_6025_);
                    v_traceMsgs_6026_ = crate::leanh::lean_ctor_get(v_a_6023_, 1);
                    crate::leanh::lean_inc(v_traceMsgs_6026_);
                    v_expandedMacroDecls_6027_ = crate::leanh::lean_ctor_get(v_a_6023_, 2);
                    crate::leanh::lean_inc(v_expandedMacroDecls_6027_);
                    crate::leanh::lean_dec(v_a_6023_);
                    v___x_6028_ = crate::leanh::lean_box(0);
                    v___x_6029_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_expandedMacroDecls_6027_, v___x_6028_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_);
                    crate::leanh::lean_dec(v_expandedMacroDecls_6027_);
                    if crate::leanh::lean_obj_tag(v___x_6029_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6029_, 1);
                        v___x_6030_ = lean_st_ref_take(v___y_5999_);
                        v_env_6031_ = crate::leanh::lean_ctor_get(v___x_6030_, 0);
                        v_ngen_6032_ = crate::leanh::lean_ctor_get(v___x_6030_, 2);
                        v_auxDeclNGen_6033_ = crate::leanh::lean_ctor_get(v___x_6030_, 3);
                        v_traceState_6034_ = crate::leanh::lean_ctor_get(v___x_6030_, 4);
                        v_cache_6035_ = crate::leanh::lean_ctor_get(v___x_6030_, 5);
                        v_messages_6036_ = crate::leanh::lean_ctor_get(v___x_6030_, 6);
                        v_infoState_6037_ = crate::leanh::lean_ctor_get(v___x_6030_, 7);
                        v_snapshotTasks_6038_ = crate::leanh::lean_ctor_get(v___x_6030_, 8);
                        v_isSharedCheck_6064_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6030_)) as u8;
                        if v_isSharedCheck_6064_ == 0 {
                            v_unused_6065_ = crate::leanh::lean_ctor_get(v___x_6030_, 1);
                            crate::leanh::lean_dec(v_unused_6065_);
                            v___x_6040_ = v___x_6030_;
                            v_isShared_6041_ = v_isSharedCheck_6064_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_6038_);
                            crate::leanh::lean_inc(v_infoState_6037_);
                            crate::leanh::lean_inc(v_messages_6036_);
                            crate::leanh::lean_inc(v_cache_6035_);
                            crate::leanh::lean_inc(v_traceState_6034_);
                            crate::leanh::lean_inc(v_auxDeclNGen_6033_);
                            crate::leanh::lean_inc(v_ngen_6032_);
                            crate::leanh::lean_inc(v_env_6031_);
                            crate::leanh::lean_dec(v___x_6030_);
                            v___x_6040_ = crate::leanh::lean_box(0);
                            v_isShared_6041_ = v_isSharedCheck_6064_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_traceMsgs_6026_);
                        crate::leanh::lean_dec(v_macroScope_6025_);
                        crate::leanh::lean_dec(v_a_6024_);
                        v_a_6066_ = crate::leanh::lean_ctor_get(v___x_6029_, 0);
                        v_isSharedCheck_6073_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6029_)) as u8;
                        if v_isSharedCheck_6073_ == 0 {
                            v___x_6068_ = v___x_6029_;
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6066_);
                            crate::leanh::lean_dec(v___x_6029_);
                            v___x_6068_ = crate::leanh::lean_box(0);
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_6074_ = crate::leanh::lean_ctor_get(v___x_6022_, 0);
                    crate::leanh::lean_inc(v_a_6074_);
                    crate::leanh::lean_dec_ref_known(v___x_6022_, 2);
                    if crate::leanh::lean_obj_tag(v_a_6074_) == 0 {
                        v_a_6075_ = crate::leanh::lean_ctor_get(v_a_6074_, 0);
                        crate::leanh::lean_inc(v_a_6075_);
                        v_a_6076_ = crate::leanh::lean_ctor_get(v_a_6074_, 1);
                        crate::leanh::lean_inc_ref(v_a_6076_);
                        crate::leanh::lean_dec_ref_known(v_a_6074_, 2);
                        v___x_6077_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___closed__0;
                        v___x_6078_ = lean_string_dec_eq(v_a_6076_, v___x_6077_);
                        if v___x_6078_ == 0 {
                            v___x_6079_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6079_, 0, v_a_6076_);
                            v___x_6080_ = l_Lean_MessageData_ofFormat(v___x_6079_);
                            v___x_6081_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_a_6075_, v___x_6080_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_);
                            crate::leanh::lean_dec(v_a_6075_);
                            return v___x_6081_;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_6076_);
                            v___x_6082_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_a_6075_);
                            return v___x_6082_;
                        }
                    } else {
                        v___x_6083_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
                        return v___x_6083_;
                    }
                }
            }
            1 => {
                if v_isShared_6041_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6040_, 1, v_macroScope_6025_);
                    v___x_6043_ = v___x_6040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6063_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6063_, 0, v_env_6031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6063_, 1, v_macroScope_6025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6063_, 2, v_ngen_6032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6063_, 3, v_auxDeclNGen_6033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6063_, 4, v_traceState_6034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6063_, 5, v_cache_6035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6063_, 6, v_messages_6036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6063_, 7, v_infoState_6037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6063_, 8, v_snapshotTasks_6038_);
                    v___x_6043_ = v_reuseFailAlloc_6063_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6044_ = lean_st_ref_set(v___y_5999_, v___x_6043_);
                v___x_6045_ = l_List_reverse___redArg(v_traceMsgs_6026_);
                v___x_6046_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__5(v___x_6045_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_);
                if crate::leanh::lean_obj_tag(v___x_6046_) == 0 {
                    v_isSharedCheck_6053_ = (!crate::leanh::lean_is_exclusive(v___x_6046_)) as u8;
                    if v_isSharedCheck_6053_ == 0 {
                        v_unused_6054_ = crate::leanh::lean_ctor_get(v___x_6046_, 0);
                        crate::leanh::lean_dec(v_unused_6054_);
                        v___x_6048_ = v___x_6046_;
                        v_isShared_6049_ = v_isSharedCheck_6053_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6046_);
                        v___x_6048_ = crate::leanh::lean_box(0);
                        v_isShared_6049_ = v_isSharedCheck_6053_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6024_);
                    v_a_6055_ = crate::leanh::lean_ctor_get(v___x_6046_, 0);
                    v_isSharedCheck_6062_ = (!crate::leanh::lean_is_exclusive(v___x_6046_)) as u8;
                    if v_isSharedCheck_6062_ == 0 {
                        v___x_6057_ = v___x_6046_;
                        v_isShared_6058_ = v_isSharedCheck_6062_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6055_);
                        crate::leanh::lean_dec(v___x_6046_);
                        v___x_6057_ = crate::leanh::lean_box(0);
                        v_isShared_6058_ = v_isSharedCheck_6062_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6048_, 0, v_a_6024_);
                    v___x_6051_ = v___x_6048_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6052_, 0, v_a_6024_);
                    v___x_6051_ = v_reuseFailAlloc_6052_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6051_;
            }
            5 => {
                if v_isShared_6058_ == 0 {
                    v___x_6060_ = v___x_6057_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6061_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6061_, 0, v_a_6055_);
                    v___x_6060_ = v_reuseFailAlloc_6061_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6060_;
            }
            7 => {
                if v_isShared_6069_ == 0 {
                    v___x_6071_ = v___x_6068_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
                    v___x_6071_ = v_reuseFailAlloc_6072_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg___boxed(
    mut v_x_6084_: *mut crate::leanh::LeanObject,
    mut v___y_6085_: *mut crate::leanh::LeanObject,
    mut v___y_6086_: *mut crate::leanh::LeanObject,
    mut v___y_6087_: *mut crate::leanh::LeanObject,
    mut v___y_6088_: *mut crate::leanh::LeanObject,
    mut v___y_6089_: *mut crate::leanh::LeanObject,
    mut v___y_6090_: *mut crate::leanh::LeanObject,
    mut v___y_6091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6092_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(
            v_x_6084_,
            v___y_6085_,
            v___y_6086_,
            v___y_6087_,
            v___y_6088_,
            v___y_6089_,
            v___y_6090_,
        );
    crate::leanh::lean_dec(v___y_6090_);
    crate::leanh::lean_dec_ref(v___y_6089_);
    crate::leanh::lean_dec(v___y_6088_);
    crate::leanh::lean_dec_ref(v___y_6087_);
    crate::leanh::lean_dec(v___y_6086_);
    crate::leanh::lean_dec_ref(v___y_6085_);
    return v_res_6092_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6096_ = crate::leanh::lean_box(0);
    v___x_6097_ =
        l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__75;
    v___x_6098_ = l_Lean_mkConst(v___x_6097_, v___x_6096_);
    return v___x_6098_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__3;
    v___x_6101_ = l_Lean_stringToMessageData(v___x_6100_);
    return v___x_6101_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6107_ = crate::leanh::lean_box(0);
    v___x_6108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__6;
    v___x_6109_ = l_Lean_mkConst(v___x_6108_, v___x_6107_);
    return v___x_6109_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6110_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__7);
    v___x_6111_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6111_, 0, v___x_6110_);
    return v___x_6111_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(
    mut v___x_6112_: u8,
    mut v_as_6113_: *mut crate::leanh::LeanObject,
    mut v_sz_6114_: usize,
    mut v_i_6115_: usize,
    mut v_b_6116_: *mut crate::leanh::LeanObject,
    mut v___y_6117_: *mut crate::leanh::LeanObject,
    mut v___y_6118_: *mut crate::leanh::LeanObject,
    mut v___y_6119_: *mut crate::leanh::LeanObject,
    mut v___y_6120_: *mut crate::leanh::LeanObject,
    mut v___y_6121_: *mut crate::leanh::LeanObject,
    mut v___y_6122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: usize = 0;
    let mut v___x_6127_: usize = 0;
    let mut v___x_6129_: u8 = 0;
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: u8 = 0;
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: u8 = 0;
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: u8 = 0;
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: u8 = 0;
    let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: u8 = 0;
    let mut v___x_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: u8 = 0;
    let mut v_a_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_javascriptHash_6163_: u64 = 0;
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: u8 = 0;
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: u8 = 0;
    let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: u8 = 0;
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6197_: u8 = 0;
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6201_: u8 = 0;
    let mut v_a_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6205_: u8 = 0;
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6209_: u8 = 0;
    let mut v_a_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6213_: u8 = 0;
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6217_: u8 = 0;
    let mut v_a_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6221_: u8 = 0;
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6225_: u8 = 0;
    let mut v_a_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6229_: u8 = 0;
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6233_: u8 = 0;
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: u8 = 0;
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: u8 = 0;
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_javascriptHash_6257_: u64 = 0;
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6262_: u8 = 0;
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6266_: u8 = 0;
    let mut v_a_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6270_: u8 = 0;
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6274_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6129_ = lean_usize_dec_lt(v_i_6115_, v_sz_6114_);
                if v___x_6129_ == 0 {
                    v___x_6130_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6130_, 0, v_b_6116_);
                    return v___x_6130_;
                } else {
                    v___x_6131_ = l_Lean_Widget_showWidgetSpec___closed__1;
                    v___x_6132_ = crate::leanh::lean_box(0);
                    v_a_6133_ = lean_array_uget_borrowed(v_as_6113_, v_i_6115_);
                    crate::leanh::lean_inc(v_a_6133_);
                    v___x_6134_ = l_Lean_Syntax_isOfKind(v_a_6133_, v___x_6131_);
                    if v___x_6134_ == 0 {
                        v___x_6135_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
                        if crate::leanh::lean_obj_tag(v___x_6135_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6135_, 1);
                            v_a_6125_ = v___x_6132_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_6135_;
                        }
                    } else {
                        v___x_6136_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6137_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6138_ = l_Lean_Syntax_getArg(v_a_6133_, v___x_6136_);
                        v___x_6139_ = l_Lean_Widget_eraseWidgetSpec___closed__1;
                        crate::leanh::lean_inc(v___x_6138_);
                        v___x_6140_ = l_Lean_Syntax_isOfKind(v___x_6138_, v___x_6139_);
                        if v___x_6140_ == 0 {
                            v___x_6141_ = l_Lean_Widget_addWidgetSpec___closed__1;
                            crate::leanh::lean_inc(v___x_6138_);
                            v___x_6142_ = l_Lean_Syntax_isOfKind(v___x_6138_, v___x_6141_);
                            if v___x_6142_ == 0 {
                                crate::leanh::lean_dec(v___x_6138_);
                                v___x_6143_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
                                if crate::leanh::lean_obj_tag(v___x_6143_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6143_, 1);
                                    v_a_6125_ = v___x_6132_;
                                    state = 1;
                                    continue;
                                } else {
                                    return v___x_6143_;
                                }
                            } else {
                                v___x_6144_ = l_Lean_Syntax_getArg(v___x_6138_, v___x_6136_);
                                v___x_6145_ = l_Lean_Widget_addWidgetSpec___closed__3;
                                crate::leanh::lean_inc(v___x_6144_);
                                v___x_6146_ = l_Lean_Syntax_isOfKind(v___x_6144_, v___x_6145_);
                                if v___x_6146_ == 0 {
                                    crate::leanh::lean_dec(v___x_6144_);
                                    crate::leanh::lean_dec(v___x_6138_);
                                    v___x_6147_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
                                    if crate::leanh::lean_obj_tag(v___x_6147_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_6147_, 1);
                                        v_a_6125_ = v___x_6132_;
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_6147_;
                                    }
                                } else {
                                    v___x_6148_ = l_Lean_Syntax_getArg(v___x_6138_, v___x_6137_);
                                    crate::leanh::lean_dec(v___x_6138_);
                                    v___x_6149_ = l_Lean_Widget_widgetInstanceSpec___closed__3;
                                    crate::leanh::lean_inc(v___x_6148_);
                                    v___x_6150_ = l_Lean_Syntax_isOfKind(v___x_6148_, v___x_6149_);
                                    if v___x_6150_ == 0 {
                                        crate::leanh::lean_dec(v___x_6148_);
                                        crate::leanh::lean_dec(v___x_6144_);
                                        v___x_6151_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
                                        if crate::leanh::lean_obj_tag(v___x_6151_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_6151_, 1);
                                            v_a_6125_ = v___x_6132_;
                                            state = 1;
                                            continue;
                                        } else {
                                            return v___x_6151_;
                                        }
                                    } else {
                                        v___x_6152_ = crate::leanh::lean_alloc_closure(
                                            l_Lean_Elab_toAttributeKind___boxed
                                                as *mut core::ffi::c_void,
                                            3,
                                            1,
                                        );
                                        crate::leanh::lean_closure_set(v___x_6152_, 0, v___x_6144_);
                                        v___x_6153_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(v___x_6152_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
                                        if crate::leanh::lean_obj_tag(v___x_6153_) == 0 {
                                            v_a_6154_ = crate::leanh::lean_ctor_get(v___x_6153_, 0);
                                            crate::leanh::lean_inc(v_a_6154_);
                                            crate::leanh::lean_dec_ref_known(v___x_6153_, 1);
                                            v___x_6155_ = l_Lean_Widget_elabWidgetInstanceSpec(
                                                v___x_6148_,
                                                v___y_6117_,
                                                v___y_6118_,
                                                v___y_6119_,
                                                v___y_6120_,
                                                v___y_6121_,
                                                v___y_6122_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_6155_) == 0 {
                                                v_a_6156_ =
                                                    crate::leanh::lean_ctor_get(v___x_6155_, 0);
                                                crate::leanh::lean_inc_n(v_a_6156_, 2);
                                                crate::leanh::lean_dec_ref_known(v___x_6155_, 1);
                                                v___x_6157_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(v_a_6156_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
                                                if crate::leanh::lean_obj_tag(v___x_6157_) == 0 {
                                                    v___x_6158_ =
                                                        (crate::leanh::lean_unbox(v_a_6154_) as u8);
                                                    if v___x_6158_ == 1 {
                                                        crate::leanh::lean_dec(v_a_6156_);
                                                        crate::leanh::lean_dec(v_a_6154_);
                                                        v_a_6159_ = crate::leanh::lean_ctor_get(
                                                            v___x_6157_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_6159_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_6157_,
                                                            1,
                                                        );
                                                        v___x_6160_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_a_6159_, v___y_6120_, v___y_6122_);
                                                        if crate::leanh::lean_obj_tag(v___x_6160_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_6160_,
                                                                1,
                                                            );
                                                            v_a_6125_ = v___x_6132_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            return v___x_6160_;
                                                        }
                                                    } else {
                                                        v_a_6161_ = crate::leanh::lean_ctor_get(
                                                            v___x_6157_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_6161_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_6157_,
                                                            1,
                                                        );
                                                        v_id_6162_ = crate::leanh::lean_ctor_get(
                                                            v_a_6161_, 0,
                                                        );
                                                        crate::leanh::lean_inc(v_id_6162_);
                                                        v_javascriptHash_6163_ =
                                                            crate::leanh::lean_ctor_get_uint64(
                                                                v_a_6161_,
                                                                (core::mem::size_of::<
                                                                    *mut crate::leanh::LeanObject,
                                                                >(
                                                                ) * 2)
                                                                    as u32,
                                                            );
                                                        crate::leanh::lean_dec(v_a_6161_);
                                                        v___x_6164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__1;
                                                        v___x_6165_ = l_Lean_Name_append(
                                                            v_id_6162_,
                                                            v___x_6164_,
                                                        );
                                                        v___x_6166_ = l_Lean_Core_mkFreshUserName(
                                                            v___x_6165_,
                                                            v___y_6121_,
                                                            v___y_6122_,
                                                        );
                                                        if crate::leanh::lean_obj_tag(v___x_6166_)
                                                            == 0
                                                        {
                                                            v_a_6167_ = crate::leanh::lean_ctor_get(
                                                                v___x_6166_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_6167_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_6166_,
                                                                1,
                                                            );
                                                            v___x_6168_ = l_Lean_instantiateMVars___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__3___redArg(v_a_6156_, v___y_6120_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_6168_,
                                                            ) == 0
                                                            {
                                                                v_a_6169_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_6168_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_6169_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_6168_,
                                                                    1,
                                                                );
                                                                v___x_6170_ =
                                                                    crate::leanh::lean_box(0);
                                                                v___x_6189_ =
                                                                    l_Lean_Expr_hasMVar(v_a_6169_);
                                                                if v___x_6189_ == 0 {
                                                                    v___y_6172_ = v___y_6117_;
                                                                    v___y_6173_ = v___y_6118_;
                                                                    v___y_6174_ = v___y_6119_;
                                                                    v___y_6175_ = v___y_6120_;
                                                                    v___y_6176_ = v___y_6121_;
                                                                    v___y_6177_ = v___y_6122_;
                                                                    state = 2;
                                                                    continue;
                                                                } else {
                                                                    v___x_6190_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__4);
                                                                    crate::leanh::lean_inc(
                                                                        v_a_6169_,
                                                                    );
                                                                    v___x_6191_ = l_Lean_indentExpr(
                                                                        v_a_6169_,
                                                                    );
                                                                    v___x_6192_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                                                    crate::leanh::lean_ctor_set(
                                                                        v___x_6192_,
                                                                        0,
                                                                        v___x_6190_,
                                                                    );
                                                                    crate::leanh::lean_ctor_set(
                                                                        v___x_6192_,
                                                                        1,
                                                                        v___x_6191_,
                                                                    );
                                                                    v___x_6193_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(v___x_6192_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_6193_,
                                                                    ) == 0
                                                                    {
                                                                        crate::leanh::lean_dec_ref_known(v___x_6193_, 1);
                                                                        v___y_6172_ = v___y_6117_;
                                                                        v___y_6173_ = v___y_6118_;
                                                                        v___y_6174_ = v___y_6119_;
                                                                        v___y_6175_ = v___y_6120_;
                                                                        v___y_6176_ = v___y_6121_;
                                                                        v___y_6177_ = v___y_6122_;
                                                                        state = 2;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_dec(
                                                                            v_a_6169_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_6167_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_6154_,
                                                                        );
                                                                        return v___x_6193_;
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec(v_a_6167_);
                                                                crate::leanh::lean_dec(v_a_6154_);
                                                                v_a_6194_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_6168_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_6201_ = (!crate::leanh::lean_is_exclusive(v___x_6168_)) as u8;
                                                                if v_isSharedCheck_6201_ == 0 {
                                                                    v___x_6196_ = v___x_6168_;
                                                                    v_isShared_6197_ =
                                                                        v_isSharedCheck_6201_;
                                                                    state = 3;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_6194_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_6168_,
                                                                    );
                                                                    v___x_6196_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_6197_ =
                                                                        v_isSharedCheck_6201_;
                                                                    state = 3;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_a_6156_);
                                                            crate::leanh::lean_dec(v_a_6154_);
                                                            v_a_6202_ = crate::leanh::lean_ctor_get(
                                                                v___x_6166_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_6209_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_6166_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_6209_ == 0 {
                                                                v___x_6204_ = v___x_6166_;
                                                                v_isShared_6205_ =
                                                                    v_isSharedCheck_6209_;
                                                                state = 5;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_6202_);
                                                                crate::leanh::lean_dec(v___x_6166_);
                                                                v___x_6204_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_6205_ =
                                                                    v_isSharedCheck_6209_;
                                                                state = 5;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_6156_);
                                                    crate::leanh::lean_dec(v_a_6154_);
                                                    v_a_6210_ =
                                                        crate::leanh::lean_ctor_get(v___x_6157_, 0);
                                                    v_isSharedCheck_6217_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_6157_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_6217_ == 0 {
                                                        v___x_6212_ = v___x_6157_;
                                                        v_isShared_6213_ = v_isSharedCheck_6217_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_6210_);
                                                        crate::leanh::lean_dec(v___x_6157_);
                                                        v___x_6212_ = crate::leanh::lean_box(0);
                                                        v_isShared_6213_ = v_isSharedCheck_6217_;
                                                        state = 7;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_6154_);
                                                v_a_6218_ =
                                                    crate::leanh::lean_ctor_get(v___x_6155_, 0);
                                                v_isSharedCheck_6225_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_6155_))
                                                        as u8;
                                                if v_isSharedCheck_6225_ == 0 {
                                                    v___x_6220_ = v___x_6155_;
                                                    v_isShared_6221_ = v_isSharedCheck_6225_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_6218_);
                                                    crate::leanh::lean_dec(v___x_6155_);
                                                    v___x_6220_ = crate::leanh::lean_box(0);
                                                    v_isShared_6221_ = v_isSharedCheck_6225_;
                                                    state = 9;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v___x_6148_);
                                            v_a_6226_ = crate::leanh::lean_ctor_get(v___x_6153_, 0);
                                            v_isSharedCheck_6233_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_6153_))
                                                    as u8;
                                            if v_isSharedCheck_6233_ == 0 {
                                                v___x_6228_ = v___x_6153_;
                                                v_isShared_6229_ = v_isSharedCheck_6233_;
                                                state = 11;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_6226_);
                                                crate::leanh::lean_dec(v___x_6153_);
                                                v___x_6228_ = crate::leanh::lean_box(0);
                                                v_isShared_6229_ = v_isSharedCheck_6233_;
                                                state = 11;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_6234_ = l_Lean_Syntax_getArg(v___x_6138_, v___x_6137_);
                            crate::leanh::lean_dec(v___x_6138_);
                            v___x_6235_ = l_Lean_Widget_widgetInstanceSpec___closed__7;
                            crate::leanh::lean_inc(v___x_6234_);
                            v___x_6236_ = l_Lean_Syntax_isOfKind(v___x_6234_, v___x_6235_);
                            if v___x_6236_ == 0 {
                                crate::leanh::lean_dec(v___x_6234_);
                                v___x_6237_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabWidgetInstanceSpec_spec__0___redArg();
                                if crate::leanh::lean_obj_tag(v___x_6237_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6237_, 1);
                                    v_a_6125_ = v___x_6132_;
                                    state = 1;
                                    continue;
                                } else {
                                    return v___x_6237_;
                                }
                            } else {
                                v_ref_6238_ = crate::leanh::lean_ctor_get(v___y_6121_, 5);
                                v_quotContext_6239_ = crate::leanh::lean_ctor_get(v___y_6121_, 10);
                                v_currMacroScope_6240_ =
                                    crate::leanh::lean_ctor_get(v___y_6121_, 11);
                                v___x_6241_ = 0;
                                v___x_6242_ = l_Lean_SourceInfo_fromRef(v_ref_6238_, v___x_6241_);
                                v___x_6243_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__48;
                                v___x_6244_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50), core::ptr::addr_of_mut!(l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50_once), _init_l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__50);
                                v___x_6245_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__53;
                                crate::leanh::lean_inc(v_currMacroScope_6240_);
                                crate::leanh::lean_inc(v_quotContext_6239_);
                                v___x_6246_ = l_Lean_addMacroScope(
                                    v_quotContext_6239_,
                                    v___x_6245_,
                                    v_currMacroScope_6240_,
                                );
                                v___x_6247_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__56;
                                crate::leanh::lean_inc_n(v___x_6242_, 2);
                                v___x_6248_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6248_, 0, v___x_6242_);
                                crate::leanh::lean_ctor_set(v___x_6248_, 1, v___x_6244_);
                                crate::leanh::lean_ctor_set(v___x_6248_, 2, v___x_6246_);
                                crate::leanh::lean_ctor_set(v___x_6248_, 3, v___x_6247_);
                                v___x_6249_ = l___private_Lean_Widget_Commands_0__Lean_Widget_elabWidgetInstanceSpecAux___closed__6;
                                v___x_6250_ =
                                    l_Lean_Syntax_node1(v___x_6242_, v___x_6249_, v___x_6234_);
                                v___x_6251_ = l_Lean_Syntax_node2(
                                    v___x_6242_,
                                    v___x_6243_,
                                    v___x_6248_,
                                    v___x_6250_,
                                );
                                v___x_6252_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__8);
                                v___x_6253_ = l_Lean_Elab_Term_elabTerm(
                                    v___x_6251_,
                                    v___x_6252_,
                                    v___x_6112_,
                                    v___x_6112_,
                                    v___y_6117_,
                                    v___y_6118_,
                                    v___y_6119_,
                                    v___y_6120_,
                                    v___y_6121_,
                                    v___y_6122_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_6253_) == 0 {
                                    v_a_6254_ = crate::leanh::lean_ctor_get(v___x_6253_, 0);
                                    crate::leanh::lean_inc(v_a_6254_);
                                    crate::leanh::lean_dec_ref_known(v___x_6253_, 1);
                                    v___x_6255_ = l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalModuleUnsafe(v_a_6254_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
                                    if crate::leanh::lean_obj_tag(v___x_6255_) == 0 {
                                        v_a_6256_ = crate::leanh::lean_ctor_get(v___x_6255_, 0);
                                        crate::leanh::lean_inc(v_a_6256_);
                                        crate::leanh::lean_dec_ref_known(v___x_6255_, 1);
                                        v_javascriptHash_6257_ = crate::leanh::lean_ctor_get_uint64(
                                            v_a_6256_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 1)
                                                as u32,
                                        );
                                        crate::leanh::lean_dec(v_a_6256_);
                                        v___x_6258_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_javascriptHash_6257_, v___y_6120_, v___y_6122_);
                                        if crate::leanh::lean_obj_tag(v___x_6258_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_6258_, 1);
                                            v_a_6125_ = v___x_6132_;
                                            state = 1;
                                            continue;
                                        } else {
                                            return v___x_6258_;
                                        }
                                    } else {
                                        v_a_6259_ = crate::leanh::lean_ctor_get(v___x_6255_, 0);
                                        v_isSharedCheck_6266_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6255_)) as u8;
                                        if v_isSharedCheck_6266_ == 0 {
                                            v___x_6261_ = v___x_6255_;
                                            v_isShared_6262_ = v_isSharedCheck_6266_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6259_);
                                            crate::leanh::lean_dec(v___x_6255_);
                                            v___x_6261_ = crate::leanh::lean_box(0);
                                            v_isShared_6262_ = v_isSharedCheck_6266_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_a_6267_ = crate::leanh::lean_ctor_get(v___x_6253_, 0);
                                    v_isSharedCheck_6274_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6253_)) as u8;
                                    if v_isSharedCheck_6274_ == 0 {
                                        v___x_6269_ = v___x_6253_;
                                        v_isShared_6270_ = v_isSharedCheck_6274_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6267_);
                                        crate::leanh::lean_dec(v___x_6253_);
                                        v___x_6269_ = crate::leanh::lean_box(0);
                                        v_isShared_6270_ = v_isSharedCheck_6274_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6126_ = 1usize;
                v___x_6127_ = lean_usize_add(v_i_6115_, v___x_6126_);
                v_i_6115_ = v___x_6127_;
                v_b_6116_ = v_a_6125_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6178_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___closed__2);
                crate::leanh::lean_inc_n(v_a_6167_, 2);
                v___x_6179_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6179_, 0, v_a_6167_);
                crate::leanh::lean_ctor_set(v___x_6179_, 1, v___x_6170_);
                crate::leanh::lean_ctor_set(v___x_6179_, 2, v___x_6178_);
                v___x_6180_ = crate::leanh::lean_box(0);
                v___x_6181_ = 1;
                v___x_6182_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6182_, 0, v_a_6167_);
                crate::leanh::lean_ctor_set(v___x_6182_, 1, v___x_6170_);
                v___x_6183_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_6183_, 0, v___x_6179_);
                crate::leanh::lean_ctor_set(v___x_6183_, 1, v_a_6169_);
                crate::leanh::lean_ctor_set(v___x_6183_, 2, v___x_6180_);
                crate::leanh::lean_ctor_set(v___x_6183_, 3, v___x_6182_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6183_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_6181_,
                );
                v___x_6184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6184_, 0, v___x_6183_);
                v___x_6185_ = l_Lean_addAndCompile(
                    v___x_6184_,
                    v___x_6112_,
                    v___x_6140_,
                    v___y_6176_,
                    v___y_6177_,
                );
                if crate::leanh::lean_obj_tag(v___x_6185_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6185_, 1);
                    v___x_6186_ = (crate::leanh::lean_unbox(v_a_6154_) as u8);
                    crate::leanh::lean_dec(v_a_6154_);
                    if v___x_6186_ == 0 {
                        v___x_6187_ = l_Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4(v_javascriptHash_6163_, v_a_6167_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
                        if crate::leanh::lean_obj_tag(v___x_6187_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6187_, 1);
                            v_a_6125_ = v___x_6132_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_6187_;
                        }
                    } else {
                        v___x_6188_ = l_Lean_Widget_addPanelWidgetScoped___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__5(v_javascriptHash_6163_, v_a_6167_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
                        if crate::leanh::lean_obj_tag(v___x_6188_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6188_, 1);
                            v_a_6125_ = v___x_6132_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_6188_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6167_);
                    crate::leanh::lean_dec(v_a_6154_);
                    return v___x_6185_;
                }
            }
            3 => {
                if v_isShared_6197_ == 0 {
                    v___x_6199_ = v___x_6196_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6200_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6200_, 0, v_a_6194_);
                    v___x_6199_ = v_reuseFailAlloc_6200_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6199_;
            }
            5 => {
                if v_isShared_6205_ == 0 {
                    v___x_6207_ = v___x_6204_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6208_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6208_, 0, v_a_6202_);
                    v___x_6207_ = v_reuseFailAlloc_6208_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6207_;
            }
            7 => {
                if v_isShared_6213_ == 0 {
                    v___x_6215_ = v___x_6212_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6216_, 0, v_a_6210_);
                    v___x_6215_ = v_reuseFailAlloc_6216_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6215_;
            }
            9 => {
                if v_isShared_6221_ == 0 {
                    v___x_6223_ = v___x_6220_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6224_, 0, v_a_6218_);
                    v___x_6223_ = v_reuseFailAlloc_6224_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6223_;
            }
            11 => {
                if v_isShared_6229_ == 0 {
                    v___x_6231_ = v___x_6228_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6232_, 0, v_a_6226_);
                    v___x_6231_ = v_reuseFailAlloc_6232_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6231_;
            }
            13 => {
                if v_isShared_6262_ == 0 {
                    v___x_6264_ = v___x_6261_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6265_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6265_, 0, v_a_6259_);
                    v___x_6264_ = v_reuseFailAlloc_6265_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6264_;
            }
            15 => {
                if v_isShared_6270_ == 0 {
                    v___x_6272_ = v___x_6269_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6273_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6273_, 0, v_a_6267_);
                    v___x_6272_ = v_reuseFailAlloc_6273_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6272_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8___boxed(
    mut v___x_6275_: *mut crate::leanh::LeanObject,
    mut v_as_6276_: *mut crate::leanh::LeanObject,
    mut v_sz_6277_: *mut crate::leanh::LeanObject,
    mut v_i_6278_: *mut crate::leanh::LeanObject,
    mut v_b_6279_: *mut crate::leanh::LeanObject,
    mut v___y_6280_: *mut crate::leanh::LeanObject,
    mut v___y_6281_: *mut crate::leanh::LeanObject,
    mut v___y_6282_: *mut crate::leanh::LeanObject,
    mut v___y_6283_: *mut crate::leanh::LeanObject,
    mut v___y_6284_: *mut crate::leanh::LeanObject,
    mut v___y_6285_: *mut crate::leanh::LeanObject,
    mut v___y_6286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_34554__boxed_6287_: u8 = 0;
    let mut v_sz_boxed_6288_: usize = 0;
    let mut v_i_boxed_6289_: usize = 0;
    let mut v_res_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_34554__boxed_6287_ = (crate::leanh::lean_unbox(v___x_6275_) as u8);
    v_sz_boxed_6288_ = crate::leanh::lean_unbox_usize(v_sz_6277_);
    crate::leanh::lean_dec(v_sz_6277_);
    v_i_boxed_6289_ = crate::leanh::lean_unbox_usize(v_i_6278_);
    crate::leanh::lean_dec(v_i_6278_);
    v_res_6290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_34554__boxed_6287_, v_as_6276_, v_sz_boxed_6288_, v_i_boxed_6289_, v_b_6279_, v___y_6280_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_, v___y_6285_);
    crate::leanh::lean_dec(v___y_6285_);
    crate::leanh::lean_dec_ref(v___y_6284_);
    crate::leanh::lean_dec(v___y_6283_);
    crate::leanh::lean_dec_ref(v___y_6282_);
    crate::leanh::lean_dec(v___y_6281_);
    crate::leanh::lean_dec_ref(v___y_6280_);
    crate::leanh::lean_dec_ref(v_as_6276_);
    return v_res_6290_;
}
pub unsafe fn l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(
    mut v___x_6291_: u8,
    mut v___x_6292_: *mut crate::leanh::LeanObject,
    mut v_sz_6293_: usize,
    mut v___x_6294_: usize,
    mut v___x_6295_: *mut crate::leanh::LeanObject,
    mut v___y_6296_: *mut crate::leanh::LeanObject,
    mut v___y_6297_: *mut crate::leanh::LeanObject,
    mut v___y_6298_: *mut crate::leanh::LeanObject,
    mut v___y_6299_: *mut crate::leanh::LeanObject,
    mut v___y_6300_: *mut crate::leanh::LeanObject,
    mut v___y_6301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6306_: u8 = 0;
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6310_: u8 = 0;
    let mut v_unused_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__8(v___x_6291_, v___x_6292_, v_sz_6293_, v___x_6294_, v___x_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_);
                if crate::leanh::lean_obj_tag(v___x_6303_) == 0 {
                    v_isSharedCheck_6310_ = (!crate::leanh::lean_is_exclusive(v___x_6303_)) as u8;
                    if v_isSharedCheck_6310_ == 0 {
                        v_unused_6311_ = crate::leanh::lean_ctor_get(v___x_6303_, 0);
                        crate::leanh::lean_dec(v_unused_6311_);
                        v___x_6305_ = v___x_6303_;
                        v_isShared_6306_ = v_isSharedCheck_6310_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6303_);
                        v___x_6305_ = crate::leanh::lean_box(0);
                        v_isShared_6306_ = v_isSharedCheck_6310_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_6303_;
                }
            }
            1 => {
                if v_isShared_6306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6305_, 0, v___x_6295_);
                    v___x_6308_ = v___x_6305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6309_, 0, v___x_6295_);
                    v___x_6308_ = v_reuseFailAlloc_6309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed(
    mut v___x_6312_: *mut crate::leanh::LeanObject,
    mut v___x_6313_: *mut crate::leanh::LeanObject,
    mut v_sz_6314_: *mut crate::leanh::LeanObject,
    mut v___x_6315_: *mut crate::leanh::LeanObject,
    mut v___x_6316_: *mut crate::leanh::LeanObject,
    mut v___y_6317_: *mut crate::leanh::LeanObject,
    mut v___y_6318_: *mut crate::leanh::LeanObject,
    mut v___y_6319_: *mut crate::leanh::LeanObject,
    mut v___y_6320_: *mut crate::leanh::LeanObject,
    mut v___y_6321_: *mut crate::leanh::LeanObject,
    mut v___y_6322_: *mut crate::leanh::LeanObject,
    mut v___y_6323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_34906__boxed_6324_: u8 = 0;
    let mut v_sz_boxed_6325_: usize = 0;
    let mut v___x_34908__boxed_6326_: usize = 0;
    let mut v_res_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_34906__boxed_6324_ = (crate::leanh::lean_unbox(v___x_6312_) as u8);
    v_sz_boxed_6325_ = crate::leanh::lean_unbox_usize(v_sz_6314_);
    crate::leanh::lean_dec(v_sz_6314_);
    v___x_34908__boxed_6326_ = crate::leanh::lean_unbox_usize(v___x_6315_);
    crate::leanh::lean_dec(v___x_6315_);
    v_res_6327_ = l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0(
        v___x_34906__boxed_6324_,
        v___x_6313_,
        v_sz_boxed_6325_,
        v___x_34908__boxed_6326_,
        v___x_6316_,
        v___y_6317_,
        v___y_6318_,
        v___y_6319_,
        v___y_6320_,
        v___y_6321_,
        v___y_6322_,
    );
    crate::leanh::lean_dec(v___y_6322_);
    crate::leanh::lean_dec_ref(v___y_6321_);
    crate::leanh::lean_dec(v___y_6320_);
    crate::leanh::lean_dec_ref(v___y_6319_);
    crate::leanh::lean_dec(v___y_6318_);
    crate::leanh::lean_dec_ref(v___y_6317_);
    crate::leanh::lean_dec_ref(v___x_6313_);
    return v_res_6327_;
}
pub unsafe fn l_Lean_Widget_elabShowPanelWidgetsCmd(
    mut v_x_6330_: *mut crate::leanh::LeanObject,
    mut v_a_6331_: *mut crate::leanh::LeanObject,
    mut v_a_6332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: u8 = 0;
    v___x_6334_ = l_Lean_Widget_showPanelWidgetsCmd___closed__1;
    crate::leanh::lean_inc(v_x_6330_);
    v___x_6335_ = l_Lean_Syntax_isOfKind(v_x_6330_, v___x_6334_);
    if v___x_6335_ == 0 {
        let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_6330_);
        v___x_6336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
        return v___x_6336_;
    } else {
        let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ws_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_6342_: usize = 0;
        let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6337_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_6338_ = l_Lean_Syntax_getArg(v_x_6330_, v___x_6337_);
        crate::leanh::lean_dec(v_x_6330_);
        v_ws_6339_ = l_Lean_Syntax_getArgs(v___x_6338_);
        crate::leanh::lean_dec(v___x_6338_);
        v___x_6340_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ws_6339_);
        crate::leanh::lean_dec_ref(v_ws_6339_);
        v___x_6341_ = crate::leanh::lean_box(0);
        v_sz_6342_ = lean_array_size(v___x_6340_);
        v___x_6343_ = crate::leanh::lean_box((v___x_6335_) as usize);
        v___x_6344_ = crate::leanh::lean_box_usize(v_sz_6342_);
        v___x_6345_ = l_Lean_Widget_elabShowPanelWidgetsCmd___boxed__const__1;
        v___f_6346_ = crate::leanh::lean_alloc_closure(
            l_Lean_Widget_elabShowPanelWidgetsCmd___lam__0___boxed as *mut core::ffi::c_void,
            12,
            5,
        );
        crate::leanh::lean_closure_set(v___f_6346_, 0, v___x_6343_);
        crate::leanh::lean_closure_set(v___f_6346_, 1, v___x_6340_);
        crate::leanh::lean_closure_set(v___f_6346_, 2, v___x_6344_);
        crate::leanh::lean_closure_set(v___f_6346_, 3, v___x_6345_);
        crate::leanh::lean_closure_set(v___f_6346_, 4, v___x_6341_);
        v___x_6347_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_6346_, v_a_6331_, v_a_6332_);
        return v___x_6347_;
    }
}
pub unsafe fn l_Lean_Widget_elabShowPanelWidgetsCmd___boxed(
    mut v_x_6348_: *mut crate::leanh::LeanObject,
    mut v_a_6349_: *mut crate::leanh::LeanObject,
    mut v_a_6350_: *mut crate::leanh::LeanObject,
    mut v_a_6351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6352_ = l_Lean_Widget_elabShowPanelWidgetsCmd(v_x_6348_, v_a_6349_, v_a_6350_);
    crate::leanh::lean_dec(v_a_6350_);
    crate::leanh::lean_dec_ref(v_a_6349_);
    return v_res_6352_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(
    mut v_00_u03b1_6353_: *mut crate::leanh::LeanObject,
    mut v_x_6354_: *mut crate::leanh::LeanObject,
    mut v___y_6355_: *mut crate::leanh::LeanObject,
    mut v___y_6356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6357_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___redArg(v_x_6354_, v___y_6356_);
    return v___x_6357_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2___boxed(
    mut v_00_u03b1_6358_: *mut crate::leanh::LeanObject,
    mut v_x_6359_: *mut crate::leanh::LeanObject,
    mut v___y_6360_: *mut crate::leanh::LeanObject,
    mut v___y_6361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6362_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__2(v_00_u03b1_6358_, v_x_6359_, v___y_6360_, v___y_6361_);
    crate::leanh::lean_dec_ref(v___y_6360_);
    crate::leanh::lean_dec_ref(v_x_6359_);
    return v_res_6362_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(
    mut v_00_u03b1_6363_: *mut crate::leanh::LeanObject,
    mut v_ref_6364_: *mut crate::leanh::LeanObject,
    mut v___y_6365_: *mut crate::leanh::LeanObject,
    mut v___y_6366_: *mut crate::leanh::LeanObject,
    mut v___y_6367_: *mut crate::leanh::LeanObject,
    mut v___y_6368_: *mut crate::leanh::LeanObject,
    mut v___y_6369_: *mut crate::leanh::LeanObject,
    mut v___y_6370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6372_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___redArg(v_ref_6364_);
    return v___x_6372_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7___boxed(
    mut v_00_u03b1_6373_: *mut crate::leanh::LeanObject,
    mut v_ref_6374_: *mut crate::leanh::LeanObject,
    mut v___y_6375_: *mut crate::leanh::LeanObject,
    mut v___y_6376_: *mut crate::leanh::LeanObject,
    mut v___y_6377_: *mut crate::leanh::LeanObject,
    mut v___y_6378_: *mut crate::leanh::LeanObject,
    mut v___y_6379_: *mut crate::leanh::LeanObject,
    mut v___y_6380_: *mut crate::leanh::LeanObject,
    mut v___y_6381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6382_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__7(v_00_u03b1_6373_, v_ref_6374_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_, v___y_6379_, v___y_6380_);
    crate::leanh::lean_dec(v___y_6380_);
    crate::leanh::lean_dec_ref(v___y_6379_);
    crate::leanh::lean_dec(v___y_6378_);
    crate::leanh::lean_dec_ref(v___y_6377_);
    crate::leanh::lean_dec(v___y_6376_);
    crate::leanh::lean_dec_ref(v___y_6375_);
    return v_res_6382_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(
    mut v_00_u03b1_6383_: *mut crate::leanh::LeanObject,
    mut v_x_6384_: *mut crate::leanh::LeanObject,
    mut v___y_6385_: *mut crate::leanh::LeanObject,
    mut v___y_6386_: *mut crate::leanh::LeanObject,
    mut v___y_6387_: *mut crate::leanh::LeanObject,
    mut v___y_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
    mut v___y_6390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6392_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___redArg(
            v_x_6384_,
            v___y_6385_,
            v___y_6386_,
            v___y_6387_,
            v___y_6388_,
            v___y_6389_,
            v___y_6390_,
        );
    return v___x_6392_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1___boxed(
    mut v_00_u03b1_6393_: *mut crate::leanh::LeanObject,
    mut v_x_6394_: *mut crate::leanh::LeanObject,
    mut v___y_6395_: *mut crate::leanh::LeanObject,
    mut v___y_6396_: *mut crate::leanh::LeanObject,
    mut v___y_6397_: *mut crate::leanh::LeanObject,
    mut v___y_6398_: *mut crate::leanh::LeanObject,
    mut v___y_6399_: *mut crate::leanh::LeanObject,
    mut v___y_6400_: *mut crate::leanh::LeanObject,
    mut v___y_6401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6402_ = l_Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1(
        v_00_u03b1_6393_,
        v_x_6394_,
        v___y_6395_,
        v___y_6396_,
        v___y_6397_,
        v___y_6398_,
        v___y_6399_,
        v___y_6400_,
    );
    crate::leanh::lean_dec(v___y_6400_);
    crate::leanh::lean_dec_ref(v___y_6399_);
    crate::leanh::lean_dec(v___y_6398_);
    crate::leanh::lean_dec_ref(v___y_6397_);
    crate::leanh::lean_dec(v___y_6396_);
    crate::leanh::lean_dec_ref(v___y_6395_);
    return v_res_6402_;
}
pub unsafe fn l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(
    mut v_wi_6403_: *mut crate::leanh::LeanObject,
    mut v___y_6404_: *mut crate::leanh::LeanObject,
    mut v___y_6405_: *mut crate::leanh::LeanObject,
    mut v___y_6406_: *mut crate::leanh::LeanObject,
    mut v___y_6407_: *mut crate::leanh::LeanObject,
    mut v___y_6408_: *mut crate::leanh::LeanObject,
    mut v___y_6409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6411_ = l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___redArg(v_wi_6403_, v___y_6407_, v___y_6409_);
    return v___x_6411_;
}
pub unsafe fn l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2___boxed(
    mut v_wi_6412_: *mut crate::leanh::LeanObject,
    mut v___y_6413_: *mut crate::leanh::LeanObject,
    mut v___y_6414_: *mut crate::leanh::LeanObject,
    mut v___y_6415_: *mut crate::leanh::LeanObject,
    mut v___y_6416_: *mut crate::leanh::LeanObject,
    mut v___y_6417_: *mut crate::leanh::LeanObject,
    mut v___y_6418_: *mut crate::leanh::LeanObject,
    mut v___y_6419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6420_ =
        l_Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2(
            v_wi_6412_,
            v___y_6413_,
            v___y_6414_,
            v___y_6415_,
            v___y_6416_,
            v___y_6417_,
            v___y_6418_,
        );
    crate::leanh::lean_dec(v___y_6418_);
    crate::leanh::lean_dec_ref(v___y_6417_);
    crate::leanh::lean_dec(v___y_6416_);
    crate::leanh::lean_dec_ref(v___y_6415_);
    crate::leanh::lean_dec(v___y_6414_);
    crate::leanh::lean_dec_ref(v___y_6413_);
    return v_res_6420_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(
    mut v_00_u03b1_6421_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6422_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6423_: *mut crate::leanh::LeanObject,
    mut v_ext_6424_: *mut crate::leanh::LeanObject,
    mut v_b_6425_: *mut crate::leanh::LeanObject,
    mut v_kind_6426_: u8,
    mut v___y_6427_: *mut crate::leanh::LeanObject,
    mut v___y_6428_: *mut crate::leanh::LeanObject,
    mut v___y_6429_: *mut crate::leanh::LeanObject,
    mut v___y_6430_: *mut crate::leanh::LeanObject,
    mut v___y_6431_: *mut crate::leanh::LeanObject,
    mut v___y_6432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6434_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___redArg(v_ext_6424_, v_b_6425_, v_kind_6426_, v___y_6430_, v___y_6431_, v___y_6432_);
    return v___x_6434_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13___boxed(
    mut v_00_u03b1_6435_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6436_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6437_: *mut crate::leanh::LeanObject,
    mut v_ext_6438_: *mut crate::leanh::LeanObject,
    mut v_b_6439_: *mut crate::leanh::LeanObject,
    mut v_kind_6440_: *mut crate::leanh::LeanObject,
    mut v___y_6441_: *mut crate::leanh::LeanObject,
    mut v___y_6442_: *mut crate::leanh::LeanObject,
    mut v___y_6443_: *mut crate::leanh::LeanObject,
    mut v___y_6444_: *mut crate::leanh::LeanObject,
    mut v___y_6445_: *mut crate::leanh::LeanObject,
    mut v___y_6446_: *mut crate::leanh::LeanObject,
    mut v___y_6447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_6448_: u8 = 0;
    let mut v_res_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6448_ = (crate::leanh::lean_unbox(v_kind_6440_) as u8);
    v_res_6449_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Widget_addPanelWidgetGlobal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__4_spec__13(v_00_u03b1_6435_, v_00_u03b2_6436_, v_00_u03c3_6437_, v_ext_6438_, v_b_6439_, v_kind_boxed_6448_, v___y_6441_, v___y_6442_, v___y_6443_, v___y_6444_, v___y_6445_, v___y_6446_);
    crate::leanh::lean_dec(v___y_6446_);
    crate::leanh::lean_dec_ref(v___y_6445_);
    crate::leanh::lean_dec(v___y_6444_);
    crate::leanh::lean_dec_ref(v___y_6443_);
    crate::leanh::lean_dec(v___y_6442_);
    crate::leanh::lean_dec_ref(v___y_6441_);
    return v_res_6449_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(
    mut v_00_u03b1_6450_: *mut crate::leanh::LeanObject,
    mut v_msg_6451_: *mut crate::leanh::LeanObject,
    mut v___y_6452_: *mut crate::leanh::LeanObject,
    mut v___y_6453_: *mut crate::leanh::LeanObject,
    mut v___y_6454_: *mut crate::leanh::LeanObject,
    mut v___y_6455_: *mut crate::leanh::LeanObject,
    mut v___y_6456_: *mut crate::leanh::LeanObject,
    mut v___y_6457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6459_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___redArg(
        v_msg_6451_,
        v___y_6452_,
        v___y_6453_,
        v___y_6454_,
        v___y_6455_,
        v___y_6456_,
        v___y_6457_,
    );
    return v___x_6459_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6___boxed(
    mut v_00_u03b1_6460_: *mut crate::leanh::LeanObject,
    mut v_msg_6461_: *mut crate::leanh::LeanObject,
    mut v___y_6462_: *mut crate::leanh::LeanObject,
    mut v___y_6463_: *mut crate::leanh::LeanObject,
    mut v___y_6464_: *mut crate::leanh::LeanObject,
    mut v___y_6465_: *mut crate::leanh::LeanObject,
    mut v___y_6466_: *mut crate::leanh::LeanObject,
    mut v___y_6467_: *mut crate::leanh::LeanObject,
    mut v___y_6468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6469_ = l_Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6(
        v_00_u03b1_6460_,
        v_msg_6461_,
        v___y_6462_,
        v___y_6463_,
        v___y_6464_,
        v___y_6465_,
        v___y_6466_,
        v___y_6467_,
    );
    crate::leanh::lean_dec(v___y_6467_);
    crate::leanh::lean_dec_ref(v___y_6466_);
    crate::leanh::lean_dec(v___y_6465_);
    crate::leanh::lean_dec_ref(v___y_6464_);
    crate::leanh::lean_dec(v___y_6463_);
    crate::leanh::lean_dec_ref(v___y_6462_);
    return v_res_6469_;
}
pub unsafe fn l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(
    mut v_h_6470_: u64,
    mut v___y_6471_: *mut crate::leanh::LeanObject,
    mut v___y_6472_: *mut crate::leanh::LeanObject,
    mut v___y_6473_: *mut crate::leanh::LeanObject,
    mut v___y_6474_: *mut crate::leanh::LeanObject,
    mut v___y_6475_: *mut crate::leanh::LeanObject,
    mut v___y_6476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6478_ = l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___redArg(v_h_6470_, v___y_6474_, v___y_6476_);
    return v___x_6478_;
}
pub unsafe fn l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7___boxed(
    mut v_h_6479_: *mut crate::leanh::LeanObject,
    mut v___y_6480_: *mut crate::leanh::LeanObject,
    mut v___y_6481_: *mut crate::leanh::LeanObject,
    mut v___y_6482_: *mut crate::leanh::LeanObject,
    mut v___y_6483_: *mut crate::leanh::LeanObject,
    mut v___y_6484_: *mut crate::leanh::LeanObject,
    mut v___y_6485_: *mut crate::leanh::LeanObject,
    mut v___y_6486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_h_boxed_6487_: u64 = 0;
    let mut v_res_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_h_boxed_6487_ = crate::leanh::lean_unbox_uint64(v_h_6479_);
    crate::leanh::lean_dec_ref(v_h_6479_);
    v_res_6488_ =
        l_Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7(
            v_h_boxed_6487_,
            v___y_6480_,
            v___y_6481_,
            v___y_6482_,
            v___y_6483_,
            v___y_6484_,
            v___y_6485_,
        );
    crate::leanh::lean_dec(v___y_6485_);
    crate::leanh::lean_dec_ref(v___y_6484_);
    crate::leanh::lean_dec(v___y_6483_);
    crate::leanh::lean_dec_ref(v___y_6482_);
    crate::leanh::lean_dec(v___y_6481_);
    crate::leanh::lean_dec_ref(v___y_6480_);
    return v_res_6488_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(
    mut v_cls_6489_: *mut crate::leanh::LeanObject,
    mut v_msg_6490_: *mut crate::leanh::LeanObject,
    mut v___y_6491_: *mut crate::leanh::LeanObject,
    mut v___y_6492_: *mut crate::leanh::LeanObject,
    mut v___y_6493_: *mut crate::leanh::LeanObject,
    mut v___y_6494_: *mut crate::leanh::LeanObject,
    mut v___y_6495_: *mut crate::leanh::LeanObject,
    mut v___y_6496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6498_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___redArg(v_cls_6489_, v_msg_6490_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_);
    return v___x_6498_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1___boxed(
    mut v_cls_6499_: *mut crate::leanh::LeanObject,
    mut v_msg_6500_: *mut crate::leanh::LeanObject,
    mut v___y_6501_: *mut crate::leanh::LeanObject,
    mut v___y_6502_: *mut crate::leanh::LeanObject,
    mut v___y_6503_: *mut crate::leanh::LeanObject,
    mut v___y_6504_: *mut crate::leanh::LeanObject,
    mut v___y_6505_: *mut crate::leanh::LeanObject,
    mut v___y_6506_: *mut crate::leanh::LeanObject,
    mut v___y_6507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6508_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__1(v_cls_6499_, v_msg_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_, v___y_6506_);
    crate::leanh::lean_dec(v___y_6506_);
    crate::leanh::lean_dec_ref(v___y_6505_);
    crate::leanh::lean_dec(v___y_6504_);
    crate::leanh::lean_dec_ref(v___y_6503_);
    crate::leanh::lean_dec(v___y_6502_);
    crate::leanh::lean_dec_ref(v___y_6501_);
    return v_res_6508_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(
    mut v_as_6509_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6510_: *mut crate::leanh::LeanObject,
    mut v_b_6511_: *mut crate::leanh::LeanObject,
    mut v_a_6512_: *mut crate::leanh::LeanObject,
    mut v___y_6513_: *mut crate::leanh::LeanObject,
    mut v___y_6514_: *mut crate::leanh::LeanObject,
    mut v___y_6515_: *mut crate::leanh::LeanObject,
    mut v___y_6516_: *mut crate::leanh::LeanObject,
    mut v___y_6517_: *mut crate::leanh::LeanObject,
    mut v___y_6518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6520_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___redArg(v_as_x27_6510_, v_b_6511_, v___y_6513_, v___y_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_);
    return v___x_6520_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4___boxed(
    mut v_as_6521_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6522_: *mut crate::leanh::LeanObject,
    mut v_b_6523_: *mut crate::leanh::LeanObject,
    mut v_a_6524_: *mut crate::leanh::LeanObject,
    mut v___y_6525_: *mut crate::leanh::LeanObject,
    mut v___y_6526_: *mut crate::leanh::LeanObject,
    mut v___y_6527_: *mut crate::leanh::LeanObject,
    mut v___y_6528_: *mut crate::leanh::LeanObject,
    mut v___y_6529_: *mut crate::leanh::LeanObject,
    mut v___y_6530_: *mut crate::leanh::LeanObject,
    mut v___y_6531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6532_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__4(v_as_6521_, v_as_x27_6522_, v_b_6523_, v_a_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_, v___y_6529_, v___y_6530_);
    crate::leanh::lean_dec(v___y_6530_);
    crate::leanh::lean_dec_ref(v___y_6529_);
    crate::leanh::lean_dec(v___y_6528_);
    crate::leanh::lean_dec_ref(v___y_6527_);
    crate::leanh::lean_dec(v___y_6526_);
    crate::leanh::lean_dec_ref(v___y_6525_);
    crate::leanh::lean_dec(v_as_x27_6522_);
    crate::leanh::lean_dec(v_as_6521_);
    return v_res_6532_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(
    mut v_00_u03b1_6533_: *mut crate::leanh::LeanObject,
    mut v_ref_6534_: *mut crate::leanh::LeanObject,
    mut v_msg_6535_: *mut crate::leanh::LeanObject,
    mut v___y_6536_: *mut crate::leanh::LeanObject,
    mut v___y_6537_: *mut crate::leanh::LeanObject,
    mut v___y_6538_: *mut crate::leanh::LeanObject,
    mut v___y_6539_: *mut crate::leanh::LeanObject,
    mut v___y_6540_: *mut crate::leanh::LeanObject,
    mut v___y_6541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6543_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___redArg(v_ref_6534_, v_msg_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_, v___y_6540_, v___y_6541_);
    return v___x_6543_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6___boxed(
    mut v_00_u03b1_6544_: *mut crate::leanh::LeanObject,
    mut v_ref_6545_: *mut crate::leanh::LeanObject,
    mut v_msg_6546_: *mut crate::leanh::LeanObject,
    mut v___y_6547_: *mut crate::leanh::LeanObject,
    mut v___y_6548_: *mut crate::leanh::LeanObject,
    mut v___y_6549_: *mut crate::leanh::LeanObject,
    mut v___y_6550_: *mut crate::leanh::LeanObject,
    mut v___y_6551_: *mut crate::leanh::LeanObject,
    mut v___y_6552_: *mut crate::leanh::LeanObject,
    mut v___y_6553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6554_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__6(v_00_u03b1_6544_, v_ref_6545_, v_msg_6546_, v___y_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_, v___y_6552_);
    crate::leanh::lean_dec(v___y_6552_);
    crate::leanh::lean_dec_ref(v___y_6551_);
    crate::leanh::lean_dec(v___y_6550_);
    crate::leanh::lean_dec_ref(v___y_6549_);
    crate::leanh::lean_dec(v___y_6548_);
    crate::leanh::lean_dec_ref(v___y_6547_);
    crate::leanh::lean_dec(v_ref_6545_);
    return v_res_6554_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(
    mut v_00_u03b4_6555_: *mut crate::leanh::LeanObject,
    mut v_t_6556_: *mut crate::leanh::LeanObject,
    mut v_k_6557_: u64,
    mut v_fallback_6558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6559_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___redArg(v_t_6556_, v_k_6557_, v_fallback_6558_);
    return v___x_6559_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9___boxed(
    mut v_00_u03b4_6560_: *mut crate::leanh::LeanObject,
    mut v_t_6561_: *mut crate::leanh::LeanObject,
    mut v_k_6562_: *mut crate::leanh::LeanObject,
    mut v_fallback_6563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_6564_: u64 = 0;
    let mut v_res_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_6564_ = crate::leanh::lean_unbox_uint64(v_k_6562_);
    crate::leanh::lean_dec_ref(v_k_6562_);
    v_res_6565_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__9(v_00_u03b4_6560_, v_t_6561_, v_k_boxed_6564_, v_fallback_6563_);
    crate::leanh::lean_dec(v_fallback_6563_);
    crate::leanh::lean_dec(v_t_6561_);
    return v_res_6565_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(
    mut v_00_u03b2_6566_: *mut crate::leanh::LeanObject,
    mut v_k_6567_: u64,
    mut v_v_6568_: *mut crate::leanh::LeanObject,
    mut v_t_6569_: *mut crate::leanh::LeanObject,
    mut v_hl_6570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6571_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___redArg(v_k_6567_, v_v_6568_, v_t_6569_);
    return v___x_6571_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10___boxed(
    mut v_00_u03b2_6572_: *mut crate::leanh::LeanObject,
    mut v_k_6573_: *mut crate::leanh::LeanObject,
    mut v_v_6574_: *mut crate::leanh::LeanObject,
    mut v_t_6575_: *mut crate::leanh::LeanObject,
    mut v_hl_6576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_6577_: u64 = 0;
    let mut v_res_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_6577_ = crate::leanh::lean_unbox_uint64(v_k_6573_);
    crate::leanh::lean_dec_ref(v_k_6573_);
    v_res_6578_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Widget_addPanelWidgetLocal___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__2_spec__10(v_00_u03b2_6572_, v_k_boxed_6577_, v_v_6574_, v_t_6575_, v_hl_6576_);
    return v_res_6578_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(
    mut v_msgData_6579_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6580_: *mut crate::leanh::LeanObject,
    mut v___y_6581_: *mut crate::leanh::LeanObject,
    mut v___y_6582_: *mut crate::leanh::LeanObject,
    mut v___y_6583_: *mut crate::leanh::LeanObject,
    mut v___y_6584_: *mut crate::leanh::LeanObject,
    mut v___y_6585_: *mut crate::leanh::LeanObject,
    mut v___y_6586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6588_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___redArg(v_msgData_6579_, v_macroStack_6580_, v___y_6585_);
    return v___x_6588_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17___boxed(
    mut v_msgData_6589_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6590_: *mut crate::leanh::LeanObject,
    mut v___y_6591_: *mut crate::leanh::LeanObject,
    mut v___y_6592_: *mut crate::leanh::LeanObject,
    mut v___y_6593_: *mut crate::leanh::LeanObject,
    mut v___y_6594_: *mut crate::leanh::LeanObject,
    mut v___y_6595_: *mut crate::leanh::LeanObject,
    mut v___y_6596_: *mut crate::leanh::LeanObject,
    mut v___y_6597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6598_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__6_spec__17(v_msgData_6589_, v_macroStack_6590_, v___y_6591_, v___y_6592_, v___y_6593_, v___y_6594_, v___y_6595_, v___y_6596_);
    crate::leanh::lean_dec(v___y_6596_);
    crate::leanh::lean_dec_ref(v___y_6595_);
    crate::leanh::lean_dec(v___y_6594_);
    crate::leanh::lean_dec_ref(v___y_6593_);
    crate::leanh::lean_dec(v___y_6592_);
    crate::leanh::lean_dec_ref(v___y_6591_);
    return v_res_6598_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(
    mut v_00_u03b2_6599_: *mut crate::leanh::LeanObject,
    mut v_k_6600_: u64,
    mut v_t_6601_: *mut crate::leanh::LeanObject,
    mut v_h_6602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6603_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___redArg(v_k_6600_, v_t_6601_);
    return v___x_6603_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19___boxed(
    mut v_00_u03b2_6604_: *mut crate::leanh::LeanObject,
    mut v_k_6605_: *mut crate::leanh::LeanObject,
    mut v_t_6606_: *mut crate::leanh::LeanObject,
    mut v_h_6607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_6608_: u64 = 0;
    let mut v_res_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_6608_ = crate::leanh::lean_unbox_uint64(v_k_6605_);
    crate::leanh::lean_dec_ref(v_k_6605_);
    v_res_6609_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Widget_erasePanelWidget___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__7_spec__19(v_00_u03b2_6604_, v_k_boxed_6608_, v_t_6606_, v_h_6607_);
    return v_res_6609_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(
    mut v_00_u03b2_6610_: *mut crate::leanh::LeanObject,
    mut v_m_6611_: *mut crate::leanh::LeanObject,
    mut v_a_6612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___redArg(v_m_6611_, v_a_6612_);
    return v___x_6613_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_6614_: *mut crate::leanh::LeanObject,
    mut v_m_6615_: *mut crate::leanh::LeanObject,
    mut v_a_6616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7(v_00_u03b2_6614_, v_m_6615_, v_a_6616_);
    crate::leanh::lean_dec(v_a_6616_);
    crate::leanh::lean_dec_ref(v_m_6615_);
    return v_res_6617_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(
    mut v_00_u03b2_6618_: *mut crate::leanh::LeanObject,
    mut v_x_6619_: *mut crate::leanh::LeanObject,
    mut v_x_6620_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6621_: u8 = 0;
    v___x_6621_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___redArg(v_x_6619_, v_x_6620_);
    return v___x_6621_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15___boxed(
    mut v_00_u03b2_6622_: *mut crate::leanh::LeanObject,
    mut v_x_6623_: *mut crate::leanh::LeanObject,
    mut v_x_6624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6625_: u8 = 0;
    let mut v_r_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6625_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15(v_00_u03b2_6622_, v_x_6623_, v_x_6624_);
    crate::leanh::lean_dec_ref(v_x_6624_);
    crate::leanh::lean_dec_ref(v_x_6623_);
    v_r_6626_ = crate::leanh::lean_box((v_res_6625_) as usize);
    return v_r_6626_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(
    mut v_00_u03b2_6627_: *mut crate::leanh::LeanObject,
    mut v_a_6628_: *mut crate::leanh::LeanObject,
    mut v_x_6629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6630_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___redArg(v_a_6628_, v_x_6629_);
    return v___x_6630_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18___boxed(
    mut v_00_u03b2_6631_: *mut crate::leanh::LeanObject,
    mut v_a_6632_: *mut crate::leanh::LeanObject,
    mut v_x_6633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6634_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__7_spec__18(v_00_u03b2_6631_, v_a_6632_, v_x_6633_);
    crate::leanh::lean_dec(v_x_6633_);
    crate::leanh::lean_dec(v_a_6632_);
    return v_res_6634_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(
    mut v_00_u03b2_6635_: *mut crate::leanh::LeanObject,
    mut v_x_6636_: *mut crate::leanh::LeanObject,
    mut v_x_6637_: usize,
    mut v_x_6638_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6639_: u8 = 0;
    v___x_6639_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___redArg(v_x_6636_, v_x_6637_, v_x_6638_);
    return v___x_6639_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24___boxed(
    mut v_00_u03b2_6640_: *mut crate::leanh::LeanObject,
    mut v_x_6641_: *mut crate::leanh::LeanObject,
    mut v_x_6642_: *mut crate::leanh::LeanObject,
    mut v_x_6643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_35270__boxed_6644_: usize = 0;
    let mut v_res_6645_: u8 = 0;
    let mut v_r_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_35270__boxed_6644_ = crate::leanh::lean_unbox_usize(v_x_6642_);
    crate::leanh::lean_dec(v_x_6642_);
    v_res_6645_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24(v_00_u03b2_6640_, v_x_6641_, v_x_35270__boxed_6644_, v_x_6643_);
    crate::leanh::lean_dec_ref(v_x_6643_);
    crate::leanh::lean_dec_ref(v_x_6641_);
    v_r_6646_ = crate::leanh::lean_box((v_res_6645_) as usize);
    return v_r_6646_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(
    mut v_00_u03b2_6647_: *mut crate::leanh::LeanObject,
    mut v_keys_6648_: *mut crate::leanh::LeanObject,
    mut v_vals_6649_: *mut crate::leanh::LeanObject,
    mut v_heq_6650_: *mut crate::leanh::LeanObject,
    mut v_i_6651_: *mut crate::leanh::LeanObject,
    mut v_k_6652_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6653_: u8 = 0;
    v___x_6653_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___redArg(v_keys_6648_, v_i_6651_, v_k_6652_);
    return v___x_6653_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28___boxed(
    mut v_00_u03b2_6654_: *mut crate::leanh::LeanObject,
    mut v_keys_6655_: *mut crate::leanh::LeanObject,
    mut v_vals_6656_: *mut crate::leanh::LeanObject,
    mut v_heq_6657_: *mut crate::leanh::LeanObject,
    mut v_i_6658_: *mut crate::leanh::LeanObject,
    mut v_k_6659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6660_: u8 = 0;
    let mut v_r_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6660_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__1_spec__3_spec__5_spec__15_spec__24_spec__28(v_00_u03b2_6654_, v_keys_6655_, v_vals_6656_, v_heq_6657_, v_i_6658_, v_k_6659_);
    crate::leanh::lean_dec_ref(v_k_6659_);
    crate::leanh::lean_dec_ref(v_vals_6656_);
    crate::leanh::lean_dec_ref(v_keys_6655_);
    v_r_6661_ = crate::leanh::lean_box((v_res_6660_) as usize);
    return v_r_6661_;
}
pub unsafe fn l_Lean_Widget_elabWidgetCmd___lam__0(
    mut v_s_6679_: *mut crate::leanh::LeanObject,
    mut v_x_6680_: *mut crate::leanh::LeanObject,
    mut v___y_6681_: *mut crate::leanh::LeanObject,
    mut v___y_6682_: *mut crate::leanh::LeanObject,
    mut v___y_6683_: *mut crate::leanh::LeanObject,
    mut v___y_6684_: *mut crate::leanh::LeanObject,
    mut v___y_6685_: *mut crate::leanh::LeanObject,
    mut v___y_6686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_javascriptHash_6692_: u64 = 0;
    let mut v_props_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6698_: u8 = 0;
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6702_: u8 = 0;
    let mut v_a_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6706_: u8 = 0;
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6688_ = l_Lean_Widget_elabWidgetInstanceSpec(
                    v_s_6679_,
                    v___y_6681_,
                    v___y_6682_,
                    v___y_6683_,
                    v___y_6684_,
                    v___y_6685_,
                    v___y_6686_,
                );
                if crate::leanh::lean_obj_tag(v___x_6688_) == 0 {
                    v_a_6689_ = crate::leanh::lean_ctor_get(v___x_6688_, 0);
                    crate::leanh::lean_inc(v_a_6689_);
                    crate::leanh::lean_dec_ref_known(v___x_6688_, 1);
                    v___x_6690_ =
                        l___private_Lean_Widget_UserWidget_0__Lean_Widget_evalWidgetInstanceUnsafe(
                            v_a_6689_,
                            v___y_6683_,
                            v___y_6684_,
                            v___y_6685_,
                            v___y_6686_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_6690_) == 0 {
                        v_a_6691_ = crate::leanh::lean_ctor_get(v___x_6690_, 0);
                        crate::leanh::lean_inc(v_a_6691_);
                        crate::leanh::lean_dec_ref_known(v___x_6690_, 1);
                        v_javascriptHash_6692_ = crate::leanh::lean_ctor_get_uint64(
                            v_a_6691_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v_props_6693_ = crate::leanh::lean_ctor_get(v_a_6691_, 1);
                        crate::leanh::lean_inc_ref(v_props_6693_);
                        crate::leanh::lean_dec(v_a_6691_);
                        v___x_6694_ = l_Lean_Widget_savePanelWidgetInfo(
                            v_javascriptHash_6692_,
                            v_props_6693_,
                            v_x_6680_,
                            v___y_6685_,
                            v___y_6686_,
                        );
                        return v___x_6694_;
                    } else {
                        crate::leanh::lean_dec(v_x_6680_);
                        v_a_6695_ = crate::leanh::lean_ctor_get(v___x_6690_, 0);
                        v_isSharedCheck_6702_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6690_)) as u8;
                        if v_isSharedCheck_6702_ == 0 {
                            v___x_6697_ = v___x_6690_;
                            v_isShared_6698_ = v_isSharedCheck_6702_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6695_);
                            crate::leanh::lean_dec(v___x_6690_);
                            v___x_6697_ = crate::leanh::lean_box(0);
                            v_isShared_6698_ = v_isSharedCheck_6702_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_6680_);
                    v_a_6703_ = crate::leanh::lean_ctor_get(v___x_6688_, 0);
                    v_isSharedCheck_6710_ = (!crate::leanh::lean_is_exclusive(v___x_6688_)) as u8;
                    if v_isSharedCheck_6710_ == 0 {
                        v___x_6705_ = v___x_6688_;
                        v_isShared_6706_ = v_isSharedCheck_6710_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6703_);
                        crate::leanh::lean_dec(v___x_6688_);
                        v___x_6705_ = crate::leanh::lean_box(0);
                        v_isShared_6706_ = v_isSharedCheck_6710_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6698_ == 0 {
                    v___x_6700_ = v___x_6697_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6701_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6701_, 0, v_a_6695_);
                    v___x_6700_ = v_reuseFailAlloc_6701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6700_;
            }
            3 => {
                if v_isShared_6706_ == 0 {
                    v___x_6708_ = v___x_6705_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6709_, 0, v_a_6703_);
                    v___x_6708_ = v_reuseFailAlloc_6709_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_elabWidgetCmd___lam__0___boxed(
    mut v_s_6711_: *mut crate::leanh::LeanObject,
    mut v_x_6712_: *mut crate::leanh::LeanObject,
    mut v___y_6713_: *mut crate::leanh::LeanObject,
    mut v___y_6714_: *mut crate::leanh::LeanObject,
    mut v___y_6715_: *mut crate::leanh::LeanObject,
    mut v___y_6716_: *mut crate::leanh::LeanObject,
    mut v___y_6717_: *mut crate::leanh::LeanObject,
    mut v___y_6718_: *mut crate::leanh::LeanObject,
    mut v___y_6719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6720_ = l_Lean_Widget_elabWidgetCmd___lam__0(
        v_s_6711_,
        v_x_6712_,
        v___y_6713_,
        v___y_6714_,
        v___y_6715_,
        v___y_6716_,
        v___y_6717_,
        v___y_6718_,
    );
    crate::leanh::lean_dec(v___y_6718_);
    crate::leanh::lean_dec_ref(v___y_6717_);
    crate::leanh::lean_dec(v___y_6716_);
    crate::leanh::lean_dec_ref(v___y_6715_);
    crate::leanh::lean_dec(v___y_6714_);
    crate::leanh::lean_dec_ref(v___y_6713_);
    return v_res_6720_;
}
pub unsafe fn l_Lean_Widget_elabWidgetCmd(
    mut v_x_6721_: *mut crate::leanh::LeanObject,
    mut v_a_6722_: *mut crate::leanh::LeanObject,
    mut v_a_6723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: u8 = 0;
    v___x_6725_ = l_Lean_Widget_widgetCmd___closed__1;
    crate::leanh::lean_inc(v_x_6721_);
    v___x_6726_ = l_Lean_Syntax_isOfKind(v_x_6721_, v___x_6725_);
    if v___x_6726_ == 0 {
        let mut v___x_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_6721_);
        v___x_6727_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Widget_elabShowPanelWidgetsCmd_spec__0___redArg();
        return v___x_6727_;
    } else {
        let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6728_ = crate::leanh::lean_unsigned_to_nat(1);
        v_s_6729_ = l_Lean_Syntax_getArg(v_x_6721_, v___x_6728_);
        v___f_6730_ = crate::leanh::lean_alloc_closure(
            l_Lean_Widget_elabWidgetCmd___lam__0___boxed as *mut core::ffi::c_void,
            9,
            2,
        );
        crate::leanh::lean_closure_set(v___f_6730_, 0, v_s_6729_);
        crate::leanh::lean_closure_set(v___f_6730_, 1, v_x_6721_);
        v___x_6731_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_6730_, v_a_6722_, v_a_6723_);
        return v___x_6731_;
    }
}
pub unsafe fn l_Lean_Widget_elabWidgetCmd___boxed(
    mut v_x_6732_: *mut crate::leanh::LeanObject,
    mut v_a_6733_: *mut crate::leanh::LeanObject,
    mut v_a_6734_: *mut crate::leanh::LeanObject,
    mut v_a_6735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6736_ = l_Lean_Widget_elabWidgetCmd(v_x_6732_, v_a_6733_, v_a_6734_);
    crate::leanh::lean_dec(v_a_6734_);
    crate::leanh::lean_dec_ref(v_a_6733_);
    return v_res_6736_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget_Commands(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget_Commands(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Widget_UserWidget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Widget_Commands(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Widget_UserWidget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_Commands(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Widget_Commands(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Widget_Commands(builtin);
}
