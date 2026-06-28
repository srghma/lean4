// Lean compiler output
// Module: Lean.Parser.Extra
// Imports: Lean.PrettyPrinter.Formatter Lean.PrettyPrinter.Parenthesizer Lean.Parser.Types Lean.Parser.Basic Lean.Parser.Extension Lean.Hygiene
use crate::r#gen::Init::Data::List::Basic::{l_List_range, l_List_reverse___redArg};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_trimAscii;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_isNone,
    l_Lean_Syntax_mkNameLit, l_Lean_TSyntax_getId, l_Lean_TSyntax_getString, l_Lean_mkIdentFrom,
    l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Macro_resolveGlobalName, l_Lean_Macro_throwError___redArg,
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_addMacroScope,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Format::l_Std_Format_getIndent;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Hygiene::{initialize_Lean_Hygiene, meta_initialize_Lean_Hygiene};
use crate::r#gen::Lean::InternalExceptionId::l_Lean_instBEqInternalExceptionId_beq;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Parser::Basic::{
    initialize_Lean_Parser_Basic, l_Lean_Parser_andthen, l_Lean_Parser_charLitNoAntiquot,
    l_Lean_Parser_checkColEq, l_Lean_Parser_checkColGe, l_Lean_Parser_checkLinebreakBefore,
    l_Lean_Parser_checkNoWsBefore, l_Lean_Parser_hexnumNoAntiquot,
    l_Lean_Parser_hygieneInfoNoAntiquot, l_Lean_Parser_identNoAntiquot,
    l_Lean_Parser_many1NoAntiquot, l_Lean_Parser_manyNoAntiquot, l_Lean_Parser_mkAntiquot,
    l_Lean_Parser_nameLitNoAntiquot, l_Lean_Parser_node, l_Lean_Parser_notFollowedBy,
    l_Lean_Parser_numLitNoAntiquot, l_Lean_Parser_optionalNoAntiquot, l_Lean_Parser_orelse,
    l_Lean_Parser_pushNone, l_Lean_Parser_rawIdentNoAntiquot,
    l_Lean_Parser_scientificLitNoAntiquot, l_Lean_Parser_sepBy, l_Lean_Parser_sepBy1,
    l_Lean_Parser_skip, l_Lean_Parser_strLitNoAntiquot, l_Lean_Parser_symbol,
    l_Lean_Parser_withAntiquot, l_Lean_Parser_withAntiquotSpliceAndSuffix,
    l_Lean_Parser_withPosition, runtime_initialize_Lean_Parser_Basic,
};
use crate::r#gen::Lean::Parser::Extension::{
    initialize_Lean_Parser_Extension, l_Lean_Parser_registerAlias,
    runtime_initialize_Lean_Parser_Extension,
};
use crate::r#gen::Lean::Parser::Types::{
    initialize_Lean_Parser_Types, runtime_initialize_Lean_Parser_Types,
};
use crate::r#gen::Lean::PrettyPrinter::Basic::l_Lean_PrettyPrinter_backtrackExceptionId;
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    initialize_Lean_PrettyPrinter_Formatter, l_Lean_PrettyPrinter_Formatter_andthen_formatter,
    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_categoryParser_formatter,
    l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_concat, l_Lean_PrettyPrinter_Formatter_fill,
    l_Lean_PrettyPrinter_Formatter_fill___boxed, l_Lean_PrettyPrinter_Formatter_group,
    l_Lean_PrettyPrinter_Formatter_group___boxed,
    l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_indent, l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter,
    l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_node_formatter,
    l_Lean_PrettyPrinter_Formatter_node_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg,
    l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_pushAlign___redArg,
    l_Lean_PrettyPrinter_Formatter_pushLine___redArg,
    l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg,
    l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_registerAlias,
    l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg,
    l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter,
    l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter,
    l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter,
    l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_visitArgs,
    l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed,
    l_Lean_PrettyPrinter_formatterAttribute,
    l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed,
    runtime_initialize_Lean_PrettyPrinter_Formatter,
};
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::{
    initialize_Lean_PrettyPrinter_Parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg,
    l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_registerAlias,
    l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg,
    l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg,
    l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_visitArgs,
    l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg,
    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer,
    l_Lean_PrettyPrinter_parenthesizerAttribute,
    l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed,
    runtime_initialize_Lean_PrettyPrinter_Parenthesizer,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_Traverser_left;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::{lean_int_sub, lean_nat_to_int};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_mod, lean_nat_sub, lean_string_utf8_byte_size, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Lean_Parser_termParser_formatter___redArg___closed__0_value: LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lean_Parser_termParser_formatter___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_termParser_formatter___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_termParser_formatter___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_termParser_formatter___redArg___closed__0_value)
                as *mut LeanObject,
            8609355255726335675 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_termParser_formatter___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_termParser_formatter___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_commandParser_formatter___redArg___closed__0_value: LeanStringObject<8> =
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
        m_data: [99, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Parser_commandParser_formatter___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_commandParser_formatter___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_commandParser_formatter___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_commandParser_formatter___redArg___closed__0_value)
                as *mut LeanObject,
            5063646790596052253 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_commandParser_formatter___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_commandParser_formatter___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_formatter___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_termParser_formatter___redArg___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_antiquotNestedExpr_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value: LeanStringObject<19> =
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
            97, 110, 116, 105, 113, 117, 111, 116, 78, 101, 115, 116, 101, 100, 69, 120, 112, 114,
            0,
        ],
    };
static mut l_Lean_Parser_antiquotNestedExpr_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_formatter___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value)
                as *mut LeanObject,
            9054665995413608708 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_antiquotNestedExpr_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value: LeanStringObject<2> =
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
static mut l_Lean_Parser_antiquotNestedExpr_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_formatter___closed__4_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_antiquotNestedExpr_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value: LeanStringObject<2> =
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
static mut l_Lean_Parser_antiquotNestedExpr_formatter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_formatter___closed__6_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_antiquotNestedExpr_formatter___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_formatter___closed__7_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_antiquotNestedExpr_formatter___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_formatter___closed__8_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_antiquotNestedExpr_formatter___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__8_value)
        as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value) as *mut LeanObject,11058019052651198536 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value) as *mut LeanObject,5082666044522342297 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_antiquotExpr_formatter___closed__0_value: LeanStringObject<2> =
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
static mut l_Lean_Parser_antiquotExpr_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotExpr_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_antiquotExpr_formatter___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_antiquotExpr_formatter___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_antiquotExpr_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotExpr_formatter___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_antiquotExpr_formatter___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_antiquotExpr_formatter___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0_value: LeanStringObject<13> =
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
        m_data: [97, 110, 116, 105, 113, 117, 111, 116, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0_value)
                as *mut LeanObject,
            5763156871072657475 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value: LeanStringObject<2> =
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
        m_data: [58, 0],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_formatter___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Parser_mkAntiquot_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___closed__2_value: LeanStringObject<9> =
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
        m_data: [97, 110, 116, 105, 113, 117, 111, 116, 0],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__2_value)
                as *mut LeanObject,
            7653097574325063121 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___closed__4_value: LeanStringObject<2> =
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
        m_data: [36, 0],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___closed__5_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_formatter___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___closed__6_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___closed__7_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___closed__8_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___closed__9_value: LeanStringObject<7> =
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
        m_data: [112, 115, 101, 117, 100, 111, 0],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_formatter___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__9_value)
                as *mut LeanObject,
            17091268464027434998 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquot_formatter___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value) as *mut LeanObject,11058019052651198536 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value) as *mut LeanObject,12028802102950516365 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_antiquotExpr_parenthesizer___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_antiquotExpr_formatter___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_antiquotExpr_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_antiquotExpr_parenthesizer___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Parser_antiquotExpr_parenthesizer___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_antiquotExpr_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_parenthesizer___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Parser_mkAntiquot_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_parenthesizer___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquot_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquot_parenthesizer___closed__2_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_formatter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquot_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquot_parenthesizer___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Parser_mkAntiquot_parenthesizer___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_mkAntiquot_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_mkAntiquot_parenthesizer___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_mkAntiquot_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_mkAntiquotSplice_formatter___closed__0_value: LeanStringObject<15> =
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
            97, 110, 116, 105, 113, 117, 111, 116, 95, 115, 99, 111, 112, 101, 0,
        ],
    };
static mut l_Lean_Parser_mkAntiquotSplice_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquotSplice_formatter___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__0_value)
                as *mut LeanObject,
            7788232707699198947 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquotSplice_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value: LeanStringObject<2> =
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
        m_data: [91, 0],
    };
static mut l_Lean_Parser_mkAntiquotSplice_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquotSplice_formatter___closed__3_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquotSplice_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquotSplice_formatter___closed__4_value: LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Parser_mkAntiquotSplice_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquotSplice_formatter___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__4_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquotSplice_formatter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value: LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lean_Parser_mkAntiquotSplice_formatter___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquotSplice_formatter___closed__7_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquotSplice_formatter___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_sepByElemParser_formatter___closed__0_value: LeanStringObject<6> =
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
        m_data: [115, 101, 112, 66, 121, 0],
    };
static mut l_Lean_Parser_sepByElemParser_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_sepByElemParser_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_sepByElemParser_formatter___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_sepByElemParser_formatter___closed__0_value)
                as *mut LeanObject,
            10608024464111057092 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_sepByElemParser_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_sepByElemParser_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_sepByElemParser_formatter___closed__2_value: LeanStringObject<2> =
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
        m_data: [42, 0],
    };
static mut l_Lean_Parser_sepByElemParser_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_sepByElemParser_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_optional_formatter___closed__0_value: LeanStringObject<9> =
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
        m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
    };
static mut l_Lean_Parser_optional_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_optional_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_optional_formatter___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_optional_formatter___closed__0_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_optional_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_optional_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_optional_formatter___closed__2_value: LeanStringObject<2> =
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
static mut l_Lean_Parser_optional_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_optional_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_optional_formatter___closed__3_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_optional_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_optional_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_optional_formatter___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_optional_parenthesizer___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_optional_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_optional_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_optional_parenthesizer___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_optional___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_optional___closed__0: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_optional_formatter___closed__0_value) as *mut LeanObject,2933775029743101773 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1_value: LeanStringObject<507> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 507, m_capacity: 507, m_length: 506, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 111, 112, 116, 105, 111, 110, 97, 108, 40, 112, 41, 96, 44, 32, 111, 114, 32, 96, 40, 112, 41, 63, 96, 44, 32, 112, 97, 114, 115, 101, 115, 32, 96, 112, 96, 32, 105, 102, 32, 105, 116, 32, 115, 117, 99, 99, 101, 101, 100, 115, 44, 10, 111, 116, 104, 101, 114, 119, 105, 115, 101, 32, 105, 116, 32, 115, 117, 99, 99, 101, 101, 100, 115, 32, 119, 105, 116, 104, 32, 110, 111, 32, 118, 97, 108, 117, 101, 46, 10, 10, 78, 111, 116, 101, 32, 116, 104, 97, 116, 32, 98, 101, 99, 97, 117, 115, 101, 32, 96, 63, 96, 32, 105, 115, 32, 97, 32, 108, 101, 103, 97, 108, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 44, 32, 111, 110, 101, 32, 109, 117, 115, 116, 32, 119, 114, 105, 116, 101, 32, 96, 40, 112, 41, 63, 96, 32, 111, 114, 32, 96, 112, 32, 63, 96, 32, 102, 111, 114, 10, 105, 116, 32, 116, 111, 32, 112, 97, 114, 115, 101, 32, 99, 111, 114, 114, 101, 99, 116, 108, 121, 46, 32, 96, 105, 100, 101, 110, 116, 63, 96, 32, 119, 105, 108, 108, 32, 110, 111, 116, 32, 119, 111, 114, 107, 59, 32, 111, 110, 101, 32, 109, 117, 115, 116, 32, 119, 114, 105, 116, 101, 32, 96, 40, 105, 100, 101, 110, 116, 41, 63, 96, 32, 105, 110, 115, 116, 101, 97, 100, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 58, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 96, 110, 117, 108, 108, 75, 105, 110, 100, 96, 32, 110, 111, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 101, 105, 116, 104, 101, 114, 32, 122, 101, 114, 111, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 10, 40, 102, 111, 114, 32, 116, 104, 101, 32, 96, 110, 111, 110, 101, 96, 32, 99, 97, 115, 101, 41, 32, 111, 114, 32, 116, 104, 101, 32, 108, 105, 115, 116, 32, 111, 102, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 112, 114, 111, 100, 117, 99, 101, 100, 32, 98, 121, 32, 96, 112, 96, 46, 10, 40, 73, 110, 32, 112, 97, 114, 116, 105, 99, 117, 108, 97, 114, 44, 32, 105, 102, 32, 96, 112, 96, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 48, 32, 116, 104, 101, 110, 32, 116, 104, 101, 32, 116, 119, 111, 32, 99, 97, 115, 101, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 105, 97, 116, 101, 100, 33, 41, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_many_formatter___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [109, 97, 110, 121, 0],
};
static mut l_Lean_Parser_many_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_many_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_many_formatter___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_many_formatter___closed__0_value) as *mut LeanObject,
        2302572775315350313 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_many_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_many_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_many_formatter___closed__2_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_sepByElemParser_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_many_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_many_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_many_parenthesizer___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_sepByElemParser_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_many_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_many_parenthesizer___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_many___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_many___closed__0: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_many_formatter___closed__0_value) as *mut LeanObject,11576560798023578125 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1_value: LeanStringObject<390> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 390, m_capacity: 390, m_length: 389, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 109, 97, 110, 121, 40, 112, 41, 96, 44, 32, 111, 114, 32, 96, 112, 42, 96, 44, 32, 114, 101, 112, 101, 97, 116, 115, 32, 96, 112, 96, 32, 117, 110, 116, 105, 108, 32, 105, 116, 32, 102, 97, 105, 108, 115, 44, 32, 97, 110, 100, 32, 114, 101, 116, 117, 114, 110, 115, 32, 116, 104, 101, 32, 108, 105, 115, 116, 32, 111, 102, 32, 114, 101, 115, 117, 108, 116, 115, 46, 10, 10, 84, 104, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 96, 112, 96, 32, 105, 115, 32, 34, 97, 117, 116, 111, 45, 103, 114, 111, 117, 112, 101, 100, 34, 44, 32, 109, 101, 97, 110, 105, 110, 103, 32, 116, 104, 97, 116, 32, 105, 102, 32, 116, 104, 101, 32, 97, 114, 105, 116, 121, 32, 105, 115, 32, 103, 114, 101, 97, 116, 101, 114, 32, 116, 104, 97, 110, 32, 49, 32, 105, 116, 32, 119, 105, 108, 108, 32, 98, 101, 10, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 98, 121, 32, 96, 103, 114, 111, 117, 112, 40, 112, 41, 96, 32, 116, 111, 32, 101, 110, 115, 117, 114, 101, 32, 116, 104, 97, 116, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 101, 120, 97, 99, 116, 108, 121, 32, 49, 32, 118, 97, 108, 117, 101, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 58, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 96, 110, 117, 108, 108, 75, 105, 110, 100, 96, 32, 110, 111, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 111, 110, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 102, 111, 114, 32, 101, 97, 99, 104, 10, 105, 110, 118, 111, 99, 97, 116, 105, 111, 110, 32, 111, 102, 32, 96, 112, 96, 32, 40, 111, 114, 32, 96, 103, 114, 111, 117, 112, 40, 112, 41, 96, 41, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 97, 110, 121, 49, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0_value) as *mut LeanObject,13889654070509321555 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2_value: LeanStringObject<648> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 648, m_capacity: 648, m_length: 647, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 109, 97, 110, 121, 49, 40, 112, 41, 96, 44, 32, 111, 114, 32, 96, 112, 43, 96, 44, 32, 114, 101, 112, 101, 97, 116, 115, 32, 96, 112, 96, 32, 117, 110, 116, 105, 108, 32, 105, 116, 32, 102, 97, 105, 108, 115, 44, 32, 97, 110, 100, 32, 114, 101, 116, 117, 114, 110, 115, 32, 116, 104, 101, 32, 108, 105, 115, 116, 32, 111, 102, 32, 114, 101, 115, 117, 108, 116, 115, 46, 10, 96, 112, 96, 32, 109, 117, 115, 116, 32, 115, 117, 99, 99, 101, 101, 100, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 111, 110, 99, 101, 44, 32, 111, 114, 32, 116, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 119, 105, 108, 108, 32, 102, 97, 105, 108, 46, 10, 10, 78, 111, 116, 101, 32, 116, 104, 97, 116, 32, 116, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 112, 97, 114, 115, 101, 32, 116, 114, 101, 101, 32, 97, 115, 32, 116, 104, 101, 32, 96, 109, 97, 110, 121, 40, 112, 41, 96, 32, 47, 32, 96, 112, 42, 96, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 44, 10, 97, 110, 100, 32, 111, 110, 101, 32, 109, 97, 116, 99, 104, 101, 115, 32, 98, 111, 116, 104, 32, 96, 112, 42, 96, 32, 97, 110, 100, 32, 96, 112, 43, 96, 32, 117, 115, 105, 110, 103, 32, 96, 36, 91, 32, 46, 46, 32, 93, 42, 96, 32, 115, 121, 110, 116, 97, 120, 32, 105, 110, 32, 97, 32, 115, 121, 110, 116, 97, 120, 32, 109, 97, 116, 99, 104, 46, 10, 40, 84, 104, 101, 114, 101, 32, 105, 115, 32, 110, 111, 32, 96, 36, 91, 32, 46, 46, 32, 93, 43, 96, 32, 115, 121, 110, 116, 97, 120, 46, 41, 10, 10, 84, 104, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 96, 112, 96, 32, 105, 115, 32, 34, 97, 117, 116, 111, 45, 103, 114, 111, 117, 112, 101, 100, 34, 44, 32, 109, 101, 97, 110, 105, 110, 103, 32, 116, 104, 97, 116, 32, 105, 102, 32, 116, 104, 101, 32, 97, 114, 105, 116, 121, 32, 105, 115, 32, 103, 114, 101, 97, 116, 101, 114, 32, 116, 104, 97, 110, 32, 49, 32, 105, 116, 32, 119, 105, 108, 108, 32, 98, 101, 10, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 98, 121, 32, 96, 103, 114, 111, 117, 112, 40, 112, 41, 96, 32, 116, 111, 32, 101, 110, 115, 117, 114, 101, 32, 116, 104, 97, 116, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 101, 120, 97, 99, 116, 108, 121, 32, 49, 32, 118, 97, 108, 117, 101, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 58, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 96, 110, 117, 108, 108, 75, 105, 110, 100, 96, 32, 110, 111, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 111, 110, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 102, 111, 114, 32, 101, 97, 99, 104, 10, 105, 110, 118, 111, 99, 97, 116, 105, 111, 110, 32, 111, 102, 32, 96, 112, 96, 32, 40, 111, 114, 32, 96, 103, 114, 111, 117, 112, 40, 112, 41, 96, 41, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_ident_formatter___closed__0_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_ident_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ident_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_ident_formatter___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_ident_formatter___closed__0_value) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_ident_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ident_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_ident_formatter___closed__2_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_ident_formatter___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_ident_formatter___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_ident_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ident_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_ident_parenthesizer___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_ident_formatter___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_ident_formatter___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_ident_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ident_parenthesizer___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_ident___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_ident___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_ident___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_ident___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_ident: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_ident_formatter___closed__0_value) as *mut LeanObject,12357768255797326360 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1_value: LeanStringObject<856> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 856, m_capacity: 856, m_length: 845, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 105, 100, 101, 110, 116, 96, 32, 112, 97, 114, 115, 101, 115, 32, 97, 32, 115, 105, 110, 103, 108, 101, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 44, 32, 112, 111, 115, 115, 105, 98, 108, 121, 32, 119, 105, 116, 104, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101, 115, 44, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 102, 111, 111, 96, 32, 111, 114, 10, 96, 98, 97, 114, 46, 98, 97, 122, 96, 46, 32, 84, 104, 101, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 109, 117, 115, 116, 32, 110, 111, 116, 32, 98, 101, 32, 97, 32, 100, 101, 99, 108, 97, 114, 101, 100, 32, 116, 111, 107, 101, 110, 44, 32, 115, 111, 32, 102, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 32, 105, 116, 32, 119, 105, 108, 108, 32, 110, 111, 116, 32, 109, 97, 116, 99, 104, 32, 96, 34, 100, 101, 102, 34, 96, 10, 98, 101, 99, 97, 117, 115, 101, 32, 96, 100, 101, 102, 96, 32, 105, 115, 32, 97, 32, 107, 101, 121, 119, 111, 114, 100, 32, 116, 111, 107, 101, 110, 46, 32, 84, 111, 107, 101, 110, 115, 32, 97, 114, 101, 32, 105, 109, 112, 108, 105, 99, 105, 116, 108, 121, 32, 100, 101, 99, 108, 97, 114, 101, 100, 32, 98, 121, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 109, 32, 105, 110, 32, 115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 115, 10, 105, 110, 32, 112, 97, 114, 115, 101, 114, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 44, 32, 115, 111, 32, 96, 115, 121, 110, 116, 97, 120, 32, 102, 111, 111, 32, 58, 61, 32, 34, 98, 108, 97, 34, 96, 32, 119, 105, 108, 108, 32, 109, 97, 107, 101, 32, 96, 98, 108, 97, 96, 32, 110, 111, 32, 108, 111, 110, 103, 101, 114, 32, 108, 101, 103, 97, 108, 32, 97, 115, 32, 97, 110, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 46, 10, 10, 73, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 32, 99, 97, 110, 32, 99, 111, 110, 116, 97, 105, 110, 32, 115, 112, 101, 99, 105, 97, 108, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 115, 32, 111, 114, 32, 107, 101, 121, 119, 111, 114, 100, 115, 32, 105, 102, 32, 116, 104, 101, 121, 32, 97, 114, 101, 32, 101, 115, 99, 97, 112, 101, 100, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 96, 194, 171, 194, 187, 96, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 115, 58, 10, 96, 194, 171, 100, 101, 102, 194, 187, 96, 32, 105, 115, 32, 97, 110, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 110, 97, 109, 101, 100, 32, 96, 100, 101, 102, 96, 44, 32, 97, 110, 100, 32, 96, 194, 171, 120, 194, 187, 96, 32, 105, 115, 32, 116, 114, 101, 97, 116, 101, 100, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 97, 115, 32, 96, 120, 96, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 10, 117, 115, 105, 110, 103, 32, 100, 105, 115, 97, 108, 108, 111, 119, 101, 100, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 115, 32, 105, 110, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 194, 171, 102, 111, 111, 46, 98, 97, 114, 194, 187, 46, 98, 97, 122, 96, 32, 111, 114, 32, 96, 194, 171, 104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 194, 187, 96, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 58, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 96, 83, 121, 110, 116, 97, 120, 46, 105, 100, 101, 110, 116, 96, 32, 110, 111, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 116, 104, 101, 32, 112, 97, 114, 115, 101, 100, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 46, 10, 89, 111, 117, 32, 99, 97, 110, 32, 117, 115, 101, 32, 96, 84, 83, 121, 110, 116, 97, 120, 46, 103, 101, 116, 73, 100, 96, 32, 116, 111, 32, 101, 120, 116, 114, 97, 99, 116, 32, 116, 104, 101, 32, 110, 97, 109, 101, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 32, 111, 98, 106, 101, 99, 116, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_identWithPartialTrailingDot___closed__0_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            110, 111, 32, 115, 112, 97, 99, 101, 32, 98, 101, 102, 111, 114, 101, 0,
        ],
    };
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_identWithPartialTrailingDot___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_identWithPartialTrailingDot___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_identWithPartialTrailingDot: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_rawIdent_parenthesizer___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_rawIdent_parenthesizer___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_rawIdent_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_rawIdent_parenthesizer___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_rawIdent___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_rawIdent___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_rawIdent: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_hygieneInfo_formatter___closed__0_value: LeanStringObject<12> =
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
        m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
    };
static mut l_Lean_Parser_hygieneInfo_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_hygieneInfo_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_hygieneInfo_formatter___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_hygieneInfo_formatter___closed__0_value)
                as *mut LeanObject,
            9871775667037945883 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_hygieneInfo_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_hygieneInfo_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_hygieneInfo_formatter___closed__2_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_hygieneInfo_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_hygieneInfo_formatter___closed__1_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_hygieneInfo_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_hygieneInfo_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_hygieneInfo_parenthesizer___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_hygieneInfo_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_hygieneInfo_formatter___closed__1_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_hygieneInfo_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_hygieneInfo_parenthesizer___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Parser_hygieneInfo___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_hygieneInfo___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_hygieneInfo___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_hygieneInfo___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_hygieneInfo: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_hygieneInfo_formatter___closed__0_value) as *mut LeanObject,3737801725909557423 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1_value: LeanStringObject<1028> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1028, m_capacity: 1028, m_length: 1026, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 96, 32, 112, 97, 114, 115, 101, 115, 32, 110, 111, 32, 116, 101, 120, 116, 44, 32, 98, 117, 116, 32, 99, 114, 101, 97, 116, 101, 115, 32, 97, 32, 96, 104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 75, 105, 110, 100, 96, 32, 110, 111, 100, 101, 10, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 97, 110, 32, 97, 110, 111, 110, 121, 109, 111, 117, 115, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 97, 115, 32, 105, 102, 32, 105, 116, 32, 119, 101, 114, 101, 32, 112, 97, 114, 115, 101, 100, 32, 97, 116, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 112, 111, 115, 105, 116, 105, 111, 110, 46, 10, 84, 104, 105, 115, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 105, 115, 32, 109, 111, 100, 105, 102, 105, 101, 100, 32, 98, 121, 32, 115, 121, 110, 116, 97, 120, 32, 113, 117, 111, 116, 97, 116, 105, 111, 110, 115, 32, 116, 111, 32, 97, 100, 100, 32, 109, 97, 99, 114, 111, 32, 115, 99, 111, 112, 101, 115, 32, 108, 105, 107, 101, 32, 97, 32, 114, 101, 103, 117, 108, 97, 114, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 46, 10, 10, 84, 104, 105, 115, 32, 105, 115, 32, 117, 115, 101, 100, 32, 116, 111, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 32, 96, 104, 97, 118, 101, 32, 58, 61, 32, 46, 46, 46, 96, 32, 115, 121, 110, 116, 97, 120, 58, 32, 116, 104, 101, 32, 96, 104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 96, 32, 98, 101, 116, 119, 101, 101, 110, 32, 116, 104, 101, 32, 96, 104, 97, 118, 101, 96, 32, 97, 110, 100, 32, 96, 58, 61, 96, 10, 99, 111, 108, 108, 101, 99, 116, 115, 32, 109, 97, 99, 114, 111, 32, 115, 99, 111, 112, 101, 115, 44, 32, 119, 104, 105, 99, 104, 32, 119, 101, 32, 99, 97, 110, 32, 97, 112, 112, 108, 121, 32, 116, 111, 32, 96, 116, 104, 105, 115, 96, 32, 119, 104, 101, 110, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 32, 116, 111, 32, 96, 104, 97, 118, 101, 32, 116, 104, 105, 115, 32, 58, 61, 32, 46, 46, 46, 96, 46, 10, 83, 101, 101, 32, 91, 116, 104, 101, 32, 108, 97, 110, 103, 117, 97, 103, 101, 32, 114, 101, 102, 101, 114, 101, 110, 99, 101, 93, 40, 108, 101, 97, 110, 45, 109, 97, 110, 117, 97, 108, 58, 47, 47, 115, 101, 99, 116, 105, 111, 110, 47, 109, 97, 99, 114, 111, 45, 104, 121, 103, 105, 101, 110, 101, 41, 32, 102, 111, 114, 32, 109, 111, 114, 101, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 32, 97, 98, 111, 117, 116, 10, 109, 97, 99, 114, 111, 32, 104, 121, 103, 105, 101, 110, 101, 46, 10, 10, 84, 104, 105, 115, 32, 105, 115, 32, 97, 108, 115, 111, 32, 117, 115, 101, 100, 32, 116, 111, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 32, 99, 100, 111, 116, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 40, 49, 32, 43, 32, 194, 183, 41, 96, 46, 32, 84, 104, 101, 32, 111, 112, 101, 110, 105, 110, 103, 32, 112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 115, 32, 99, 111, 110, 116, 97, 105, 110, 115, 10, 97, 32, 96, 104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 96, 32, 110, 111, 100, 101, 32, 97, 115, 32, 100, 111, 101, 115, 32, 116, 104, 101, 32, 99, 100, 111, 116, 44, 32, 119, 104, 105, 99, 104, 32, 108, 101, 116, 115, 32, 99, 100, 111, 116, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 32, 104, 121, 103, 105, 101, 110, 105, 99, 97, 108, 108, 121, 32, 97, 115, 115, 111, 99, 105, 97, 116, 101, 32, 112, 97, 114, 101, 110, 116, 104, 101, 115, 101, 115, 32, 116, 111, 32, 99, 100, 111, 116, 115, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 58, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 96, 104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 75, 105, 110, 100, 96, 32, 110, 111, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 97, 110, 32, 97, 110, 111, 110, 121, 109, 111, 117, 115, 32, 96, 83, 121, 110, 116, 97, 120, 46, 105, 100, 101, 110, 116, 96, 46, 10, 89, 111, 117, 32, 99, 97, 110, 32, 117, 115, 101, 32, 96, 72, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 46, 109, 107, 73, 100, 101, 110, 116, 96, 32, 116, 111, 32, 99, 114, 101, 97, 116, 101, 32, 97, 110, 32, 96, 73, 100, 101, 110, 116, 96, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 115, 121, 110, 116, 97, 120, 32, 111, 98, 106, 101, 99, 116, 44, 10, 98, 117, 116, 32, 121, 111, 117, 32, 99, 97, 110, 32, 97, 108, 115, 111, 32, 117, 115, 101, 32, 96, 84, 83, 121, 110, 116, 97, 120, 46, 103, 101, 116, 72, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 96, 32, 116, 111, 32, 103, 101, 116, 32, 116, 104, 101, 32, 114, 97, 119, 32, 110, 97, 109, 101, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_numLit_formatter___closed__0_value: LeanStringObject<4> =
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
        m_data: [110, 117, 109, 0],
    };
static mut l_Lean_Parser_numLit_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_numLit_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_numLit_formatter___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_numLit_formatter___closed__0_value) as *mut LeanObject,
        6110315075117401315 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_numLit_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_numLit_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_numLit_formatter___closed__2_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_numLit_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_numLit_formatter___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_numLit_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_numLit_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_numLit_parenthesizer___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_numLit_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_numLit_formatter___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_numLit_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_numLit_parenthesizer___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_numLit___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_numLit___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_numLit___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_numLit___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_numLit: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 117, 109, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0_value) as *mut LeanObject,15973081547164711991 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2_value: LeanStringObject<335> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 335, m_capacity: 335, m_length: 334, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 110, 117, 109, 96, 32, 112, 97, 114, 115, 101, 115, 32, 97, 32, 110, 117, 109, 101, 114, 105, 99, 32, 108, 105, 116, 101, 114, 97, 108, 32, 105, 110, 32, 115, 101, 118, 101, 114, 97, 108, 32, 98, 97, 115, 101, 115, 58, 10, 10, 42, 32, 68, 101, 99, 105, 109, 97, 108, 58, 32, 96, 49, 50, 57, 96, 10, 42, 32, 72, 101, 120, 97, 100, 101, 99, 105, 109, 97, 108, 58, 32, 96, 48, 120, 100, 101, 97, 100, 98, 101, 101, 102, 96, 10, 42, 32, 79, 99, 116, 97, 108, 58, 32, 96, 48, 111, 55, 53, 53, 96, 10, 42, 32, 66, 105, 110, 97, 114, 121, 58, 32, 96, 48, 98, 49, 49, 48, 49, 96, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 58, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 96, 110, 117, 109, 76, 105, 116, 75, 105, 110, 100, 96, 32, 110, 111, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 97, 110, 32, 97, 116, 111, 109, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 116, 101, 120, 116, 32, 111, 102, 32, 116, 104, 101, 10, 108, 105, 116, 101, 114, 97, 108, 46, 10, 89, 111, 117, 32, 99, 97, 110, 32, 117, 115, 101, 32, 96, 84, 83, 121, 110, 116, 97, 120, 46, 103, 101, 116, 78, 97, 116, 96, 32, 116, 111, 32, 101, 120, 116, 114, 97, 99, 116, 32, 116, 104, 101, 32, 110, 117, 109, 98, 101, 114, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 32, 111, 98, 106, 101, 99, 116, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_hexnum___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [104, 101, 120, 110, 117, 109, 0],
};
static mut l_Lean_Parser_hexnum___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_hexnum___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_hexnum___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_hexnum___closed__0_value) as *mut LeanObject,
        11510626477845773464 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_hexnum___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_hexnum___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_hexnum___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_hexnum___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_hexnum___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_hexnum___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_hexnum: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_hexnum___closed__0_value) as *mut LeanObject,11982095303264823988 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1_value: LeanStringObject<385> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 385, m_capacity: 385, m_length: 384, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 104, 101, 120, 110, 117, 109, 96, 32, 112, 97, 114, 115, 101, 115, 32, 97, 32, 104, 101, 120, 97, 100, 101, 99, 105, 109, 97, 108, 32, 110, 117, 109, 101, 114, 105, 99, 32, 108, 105, 116, 101, 114, 97, 108, 32, 110, 111, 116, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 116, 104, 101, 32, 96, 48, 120, 96, 32, 112, 114, 101, 102, 105, 120, 46, 10, 10, 73, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 96, 104, 101, 120, 110, 117, 109, 75, 105, 110, 100, 96, 32, 110, 111, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 97, 110, 32, 97, 116, 111, 109, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 116, 101, 120, 116, 32, 111, 102, 32, 116, 104, 101, 10, 108, 105, 116, 101, 114, 97, 108, 46, 32, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 105, 115, 32, 109, 97, 105, 110, 108, 121, 32, 117, 115, 101, 100, 32, 102, 111, 114, 32, 99, 114, 101, 97, 116, 105, 110, 103, 32, 97, 116, 111, 109, 115, 32, 115, 117, 99, 104, 32, 96, 35, 60, 104, 101, 120, 110, 117, 109, 62, 96, 46, 32, 82, 101, 99, 97, 108, 108, 32, 116, 104, 97, 116, 32, 96, 104, 101, 120, 110, 117, 109, 96, 10, 105, 115, 32, 110, 111, 116, 32, 97, 32, 116, 111, 107, 101, 110, 32, 97, 110, 100, 32, 116, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 109, 117, 115, 116, 32, 98, 101, 32, 112, 114, 101, 102, 105, 120, 101, 100, 32, 98, 121, 32, 97, 110, 111, 116, 104, 101, 114, 32, 112, 97, 114, 115, 101, 114, 46, 10, 10, 70, 111, 114, 32, 110, 117, 109, 101, 114, 97, 108, 115, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 48, 120, 97, 100, 101, 102, 49, 48, 48, 97, 96, 44, 32, 121, 111, 117, 32, 115, 104, 111, 117, 108, 100, 32, 117, 115, 101, 32, 96, 110, 117, 109, 76, 105, 116, 96, 46, 10, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_scientificLit_formatter___closed__0_value: LeanStringObject<11> =
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
        m_data: [115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 0],
    };
static mut l_Lean_Parser_scientificLit_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_scientificLit_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_scientificLit_formatter___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_scientificLit_formatter___closed__0_value)
                as *mut LeanObject,
            12926801259741997275 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_scientificLit_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_scientificLit_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_scientificLit_formatter___closed__2_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_scientificLit_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_scientificLit_formatter___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_scientificLit_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_scientificLit_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_scientificLit_parenthesizer___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_scientificLit_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_scientificLit_formatter___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_scientificLit_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_scientificLit_parenthesizer___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Parser_scientificLit___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_scientificLit___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_scientificLit___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_scientificLit___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_scientificLit: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0_value) as *mut LeanObject,11460878236439353836 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2_value: LeanStringObject<287> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 287, m_capacity: 287, m_length: 286, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 96, 32, 112, 97, 114, 115, 101, 115, 32, 97, 32, 115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 45, 110, 111, 116, 97, 116, 105, 111, 110, 32, 108, 105, 116, 101, 114, 97, 108, 44, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 49, 46, 51, 101, 45, 50, 52, 96, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 58, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 96, 115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 76, 105, 116, 75, 105, 110, 100, 96, 32, 110, 111, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 97, 110, 32, 97, 116, 111, 109, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 116, 101, 120, 116, 10, 111, 102, 32, 116, 104, 101, 32, 108, 105, 116, 101, 114, 97, 108, 46, 10, 89, 111, 117, 32, 99, 97, 110, 32, 117, 115, 101, 32, 96, 84, 83, 121, 110, 116, 97, 120, 46, 103, 101, 116, 83, 99, 105, 101, 110, 116, 105, 102, 105, 99, 96, 32, 116, 111, 32, 101, 120, 116, 114, 97, 99, 116, 32, 116, 104, 101, 32, 112, 97, 114, 116, 115, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 32, 111, 98, 106, 101, 99, 116, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_strLit_formatter___closed__0_value: LeanStringObject<4> =
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
        m_data: [115, 116, 114, 0],
    };
static mut l_Lean_Parser_strLit_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_strLit_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_strLit_formatter___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_strLit_formatter___closed__0_value) as *mut LeanObject,
        9232979286016572671 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_strLit_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_strLit_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_strLit_formatter___closed__2_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_strLit_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_strLit_formatter___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_strLit_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_strLit_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_strLit_parenthesizer___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_strLit_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_strLit_formatter___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_strLit_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_strLit_parenthesizer___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_strLit___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_strLit___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_strLit___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_strLit___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_strLit: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 116, 114, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0_value) as *mut LeanObject,3202936226761841983 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2_value: LeanStringObject<494> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 494, m_capacity: 494, m_length: 491, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 115, 116, 114, 96, 32, 112, 97, 114, 115, 101, 115, 32, 97, 32, 115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 44, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 34, 102, 111, 111, 34, 96, 32, 111, 114, 32, 96, 34, 92, 114, 92, 110, 34, 96, 46, 32, 83, 116, 114, 105, 110, 103, 115, 32, 99, 97, 110, 32, 99, 111, 110, 116, 97, 105, 110, 10, 67, 45, 115, 116, 121, 108, 101, 32, 101, 115, 99, 97, 112, 101, 115, 32, 108, 105, 107, 101, 32, 96, 92, 110, 96, 44, 32, 96, 92, 34, 96, 44, 32, 96, 92, 120, 48, 48, 96, 32, 111, 114, 32, 96, 92, 117, 50, 54, 54, 53, 96, 44, 32, 97, 115, 32, 119, 101, 108, 108, 32, 97, 115, 32, 108, 105, 116, 101, 114, 97, 108, 32, 117, 110, 105, 99, 111, 100, 101, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 115, 32, 108, 105, 107, 101, 32, 96, 226, 136, 136, 96, 46, 10, 78, 101, 119, 108, 105, 110, 101, 115, 32, 105, 110, 32, 97, 32, 115, 116, 114, 105, 110, 103, 32, 97, 114, 101, 32, 105, 110, 116, 101, 114, 112, 114, 101, 116, 101, 100, 32, 108, 105, 116, 101, 114, 97, 108, 108, 121, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 58, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 96, 115, 116, 114, 76, 105, 116, 75, 105, 110, 100, 96, 32, 110, 111, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 97, 110, 32, 97, 116, 111, 109, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 114, 97, 119, 10, 108, 105, 116, 101, 114, 97, 108, 32, 40, 105, 110, 99, 108, 117, 100, 105, 110, 103, 32, 116, 104, 101, 32, 113, 117, 111, 116, 101, 32, 109, 97, 114, 107, 115, 32, 97, 110, 100, 32, 119, 105, 116, 104, 111, 117, 116, 32, 105, 110, 116, 101, 114, 112, 114, 101, 116, 105, 110, 103, 32, 116, 104, 101, 32, 101, 115, 99, 97, 112, 101, 115, 41, 46, 10, 89, 111, 117, 32, 99, 97, 110, 32, 117, 115, 101, 32, 96, 84, 83, 121, 110, 116, 97, 120, 46, 103, 101, 116, 83, 116, 114, 105, 110, 103, 96, 32, 116, 111, 32, 100, 101, 99, 111, 100, 101, 32, 116, 104, 101, 32, 115, 116, 114, 105, 110, 103, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 32, 111, 98, 106, 101, 99, 116, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_charLit_formatter___closed__0_value: LeanStringObject<5> =
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
        m_data: [99, 104, 97, 114, 0],
    };
static mut l_Lean_Parser_charLit_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_charLit_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_charLit_formatter___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_charLit_formatter___closed__0_value) as *mut LeanObject,
        16760301032635233067 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_charLit_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_charLit_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_charLit_formatter___closed__2_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_charLit_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_charLit_formatter___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_charLit_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_charLit_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_charLit_parenthesizer___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_charLit_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_charLit_formatter___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_charLit_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_charLit_parenthesizer___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_charLit___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_charLit___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_charLit___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_charLit___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_charLit: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 104, 97, 114, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0_value) as *mut LeanObject,11096140698252235337 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2_value: LeanStringObject<604> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 604, m_capacity: 604, m_length: 595, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 99, 104, 97, 114, 96, 32, 112, 97, 114, 115, 101, 115, 32, 97, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 32, 108, 105, 116, 101, 114, 97, 108, 44, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 39, 97, 39, 96, 32, 111, 114, 32, 96, 39, 92, 110, 39, 96, 46, 32, 67, 104, 97, 114, 97, 99, 116, 101, 114, 32, 108, 105, 116, 101, 114, 97, 108, 115, 32, 99, 97, 110, 10, 99, 111, 110, 116, 97, 105, 110, 32, 67, 45, 115, 116, 121, 108, 101, 32, 101, 115, 99, 97, 112, 101, 115, 32, 108, 105, 107, 101, 32, 96, 92, 110, 96, 44, 32, 96, 92, 34, 96, 44, 32, 96, 92, 120, 48, 48, 96, 32, 111, 114, 32, 96, 92, 117, 50, 54, 54, 53, 96, 44, 32, 97, 115, 32, 119, 101, 108, 108, 32, 97, 115, 32, 108, 105, 116, 101, 114, 97, 108, 32, 117, 110, 105, 99, 111, 100, 101, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 115, 10, 108, 105, 107, 101, 32, 96, 226, 136, 136, 96, 44, 32, 98, 117, 116, 32, 109, 117, 115, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 116, 111, 32, 97, 32, 115, 105, 110, 103, 108, 101, 32, 117, 110, 105, 99, 111, 100, 101, 32, 99, 111, 100, 101, 112, 111, 105, 110, 116, 44, 32, 115, 111, 32, 96, 39, 226, 153, 165, 39, 96, 32, 105, 115, 32, 97, 108, 108, 111, 119, 101, 100, 32, 98, 117, 116, 32, 96, 39, 226, 157, 164, 239, 184, 143, 39, 96, 32, 105, 115, 32, 110, 111, 116, 10, 40, 115, 105, 110, 99, 101, 32, 105, 116, 32, 105, 115, 32, 116, 119, 111, 32, 99, 111, 100, 101, 112, 111, 105, 110, 116, 115, 32, 98, 117, 116, 32, 111, 110, 101, 32, 103, 114, 97, 112, 104, 101, 109, 101, 32, 99, 108, 117, 115, 116, 101, 114, 41, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 58, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 96, 99, 104, 97, 114, 76, 105, 116, 75, 105, 110, 100, 96, 32, 110, 111, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 97, 110, 32, 97, 116, 111, 109, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 114, 97, 119, 10, 108, 105, 116, 101, 114, 97, 108, 32, 40, 105, 110, 99, 108, 117, 100, 105, 110, 103, 32, 116, 104, 101, 32, 113, 117, 111, 116, 101, 32, 109, 97, 114, 107, 115, 32, 97, 110, 100, 32, 119, 105, 116, 104, 111, 117, 116, 32, 105, 110, 116, 101, 114, 112, 114, 101, 116, 105, 110, 103, 32, 116, 104, 101, 32, 101, 115, 99, 97, 112, 101, 115, 41, 46, 10, 89, 111, 117, 32, 99, 97, 110, 32, 117, 115, 101, 32, 96, 84, 83, 121, 110, 116, 97, 120, 46, 103, 101, 116, 67, 104, 97, 114, 96, 32, 116, 111, 32, 100, 101, 99, 111, 100, 101, 32, 116, 104, 101, 32, 115, 116, 114, 105, 110, 103, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 32, 111, 98, 106, 101, 99, 116, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_nameLit_formatter___closed__0_value: LeanStringObject<5> =
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
        m_data: [110, 97, 109, 101, 0],
    };
static mut l_Lean_Parser_nameLit_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_nameLit_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_nameLit_formatter___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_nameLit_formatter___closed__0_value) as *mut LeanObject,
        5949480926448383572 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_nameLit_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_nameLit_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_nameLit_formatter___closed__2_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_nameLit_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_nameLit_formatter___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_nameLit_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_nameLit_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_nameLit_parenthesizer___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_nameLit_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_nameLit_formatter___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_nameLit_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_nameLit_parenthesizer___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_nameLit___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_nameLit___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_nameLit___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_nameLit___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_nameLit: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 109, 101, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0_value) as *mut LeanObject,8815315524667565364 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2_value: LeanStringObject<340> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 340, m_capacity: 340, m_length: 339, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 110, 97, 109, 101, 96, 32, 112, 97, 114, 115, 101, 115, 32, 97, 32, 110, 97, 109, 101, 32, 108, 105, 116, 101, 114, 97, 108, 32, 108, 105, 107, 101, 32, 96, 96, 32, 96, 102, 111, 111, 96, 96, 46, 32, 84, 104, 101, 32, 115, 121, 110, 116, 97, 120, 32, 105, 115, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 97, 115, 32, 102, 111, 114, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 10, 40, 115, 101, 101, 32, 96, 105, 100, 101, 110, 116, 96, 41, 32, 98, 117, 116, 32, 119, 105, 116, 104, 32, 97, 32, 108, 101, 97, 100, 105, 110, 103, 32, 98, 97, 99, 107, 113, 117, 111, 116, 101, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 58, 32, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 96, 110, 97, 109, 101, 76, 105, 116, 75, 105, 110, 100, 96, 32, 110, 111, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 105, 110, 103, 32, 116, 104, 101, 32, 114, 97, 119, 32, 108, 105, 116, 101, 114, 97, 108, 10, 40, 105, 110, 99, 108, 117, 100, 105, 110, 103, 32, 116, 104, 101, 32, 98, 97, 99, 107, 113, 117, 111, 116, 101, 41, 46, 10, 89, 111, 117, 32, 99, 97, 110, 32, 117, 115, 101, 32, 96, 84, 83, 121, 110, 116, 97, 120, 46, 103, 101, 116, 78, 97, 109, 101, 96, 32, 116, 111, 32, 101, 120, 116, 114, 97, 99, 116, 32, 116, 104, 101, 32, 110, 97, 109, 101, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 32, 111, 98, 106, 101, 99, 116, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_group_formatter___closed__0_value: LeanStringObject<6> =
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
        m_data: [103, 114, 111, 117, 112, 0],
    };
static mut l_Lean_Parser_group_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_group_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_group_formatter___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_group_formatter___closed__0_value) as *mut LeanObject,
        2214559063752339918 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_group_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_group_formatter___closed__1_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_group_formatter___closed__0_value) as *mut LeanObject,5383646628424319122 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1_value: LeanStringObject<323> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 323, m_capacity: 323, m_length: 322, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 103, 114, 111, 117, 112, 40, 112, 41, 96, 32, 112, 97, 114, 115, 101, 115, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 116, 104, 105, 110, 103, 32, 97, 115, 32, 96, 112, 96, 44, 32, 98, 117, 116, 32, 105, 116, 32, 119, 114, 97, 112, 115, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 115, 32, 105, 110, 32, 97, 32, 96, 103, 114, 111, 117, 112, 75, 105, 110, 100, 96, 10, 110, 111, 100, 101, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 97, 108, 119, 97, 121, 115, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 44, 32, 101, 118, 101, 110, 32, 105, 102, 32, 96, 112, 96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 46, 32, 80, 97, 114, 115, 101, 114, 115, 32, 108, 105, 107, 101, 32, 96, 112, 42, 96, 32, 97, 114, 101, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 10, 114, 101, 119, 114, 105, 116, 116, 101, 110, 32, 116, 111, 32, 96, 103, 114, 111, 117, 112, 40, 112, 41, 42, 96, 32, 105, 102, 32, 96, 112, 96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 114, 105, 116, 121, 32, 49, 44, 32, 115, 111, 32, 116, 104, 97, 116, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 115, 32, 102, 114, 111, 109, 32, 115, 101, 112, 97, 114, 97, 116, 101, 32, 105, 110, 118, 111, 99, 97, 116, 105, 111, 110, 115, 10, 111, 102, 32, 96, 112, 96, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 105, 97, 116, 101, 100, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_many1Indent___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 114, 114, 101, 108, 101, 118, 97, 110, 116, 0],
};
static mut l_Lean_Parser_many1Indent___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_many1Indent___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_many1Indent___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_many1Indent___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 110, 121, 49, 73, 110, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0_value) as *mut LeanObject,12455907124956747413 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2_value: LeanStringObject<343> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 343, m_capacity: 343, m_length: 342, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 109, 97, 110, 121, 49, 73, 110, 100, 101, 110, 116, 40, 112, 41, 96, 32, 105, 115, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 32, 116, 111, 32, 96, 119, 105, 116, 104, 80, 111, 115, 105, 116, 105, 111, 110, 40, 40, 99, 111, 108, 71, 101, 32, 112, 41, 43, 41, 96, 46, 32, 84, 104, 105, 115, 32, 104, 97, 115, 32, 116, 104, 101, 32, 101, 102, 102, 101, 99, 116, 32, 111, 102, 10, 112, 97, 114, 115, 105, 110, 103, 32, 111, 110, 101, 32, 111, 114, 32, 109, 111, 114, 101, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 115, 32, 111, 102, 32, 96, 112, 96, 44, 32, 119, 104, 101, 114, 101, 32, 101, 97, 99, 104, 32, 115, 117, 98, 115, 101, 113, 117, 101, 110, 116, 32, 96, 112, 96, 32, 112, 97, 114, 115, 101, 32, 110, 101, 101, 100, 115, 32, 116, 111, 32, 98, 101, 32, 105, 110, 100, 101, 110, 116, 101, 100, 10, 116, 104, 101, 32, 115, 97, 109, 101, 32, 111, 114, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 32, 112, 97, 114, 115, 101, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 44, 32, 97, 110, 100, 32, 114, 101, 116, 117, 114, 110, 115, 32, 97, 32, 108, 105, 115, 116, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 115, 32, 102, 114, 111, 109, 32, 96, 112, 96, 46, 10, 96, 112, 96, 32, 105, 115, 32, 34, 97, 117, 116, 111, 45, 103, 114, 111, 117, 112, 101, 100, 34, 32, 105, 102, 32, 105, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 114, 105, 116, 121, 32, 49, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 110, 121, 73, 110, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0_value) as *mut LeanObject,1556038599081871155 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2_value: LeanStringObject<343> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 343, m_capacity: 343, m_length: 342, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 109, 97, 110, 121, 73, 110, 100, 101, 110, 116, 40, 112, 41, 96, 32, 105, 115, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 32, 116, 111, 32, 96, 119, 105, 116, 104, 80, 111, 115, 105, 116, 105, 111, 110, 40, 40, 99, 111, 108, 71, 101, 32, 112, 41, 42, 41, 96, 46, 32, 84, 104, 105, 115, 32, 104, 97, 115, 32, 116, 104, 101, 32, 101, 102, 102, 101, 99, 116, 32, 111, 102, 10, 112, 97, 114, 115, 105, 110, 103, 32, 122, 101, 114, 111, 32, 111, 114, 32, 109, 111, 114, 101, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 115, 32, 111, 102, 32, 96, 112, 96, 44, 32, 119, 104, 101, 114, 101, 32, 101, 97, 99, 104, 32, 115, 117, 98, 115, 101, 113, 117, 101, 110, 116, 32, 96, 112, 96, 32, 112, 97, 114, 115, 101, 32, 110, 101, 101, 100, 115, 32, 116, 111, 32, 98, 101, 32, 105, 110, 100, 101, 110, 116, 101, 100, 10, 116, 104, 101, 32, 115, 97, 109, 101, 32, 111, 114, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 32, 112, 97, 114, 115, 101, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 44, 32, 97, 110, 100, 32, 114, 101, 116, 117, 114, 110, 115, 32, 97, 32, 108, 105, 115, 116, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 115, 32, 102, 114, 111, 109, 32, 96, 112, 96, 46, 10, 96, 112, 96, 32, 105, 115, 32, 34, 97, 117, 116, 111, 45, 103, 114, 111, 117, 112, 101, 100, 34, 32, 105, 102, 32, 105, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 114, 105, 116, 121, 32, 49, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_sepByIndent___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_sepByIndent___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_sepByIndent___closed__1_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [108, 105, 110, 101, 32, 98, 114, 101, 97, 107, 0],
};
static mut l_Lean_Parser_sepByIndent___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_sepByIndent___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_sepByIndent___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_sepByIndent___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_sepByIndent___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_sepByIndent___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_sepByIndent___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_sepByIndent___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_sepByIndent_parenthesizer___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_sepByIndent_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_sepByIndent_parenthesizer___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_sepByIndent_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_patternIgnore_formatter___closed__0_value: LeanStringObject<14> =
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
            112, 97, 116, 116, 101, 114, 110, 73, 103, 110, 111, 114, 101, 0,
        ],
    };
static mut l_Lean_Parser_patternIgnore_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_patternIgnore_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_patternIgnore_formatter___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_patternIgnore_formatter___closed__0_value)
                as *mut LeanObject,
            17328449285856252867 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_patternIgnore_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_patternIgnore_formatter___closed__1_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_patternIgnore_formatter___closed__0_value) as *mut LeanObject,13758920526339364615 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1_value: LeanStringObject<83> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 83, m_capacity: 83, m_length: 82, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 32, 116, 104, 97, 116, 32, 97, 110, 110, 111, 116, 97, 116, 101, 115, 32, 115, 117, 98, 116, 114, 101, 101, 115, 32, 116, 111, 32, 98, 101, 32, 105, 103, 110, 111, 114, 101, 100, 32, 105, 110, 32, 115, 121, 110, 116, 97, 120, 32, 112, 97, 116, 116, 101, 114, 110, 115, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_Parser_ppHardSpace: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 112, 72, 97, 114, 100, 83, 112, 97, 99, 101, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value) as *mut LeanObject,10681202847716441275 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2_value: LeanStringObject<76> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 76, m_capacity: 76, m_length: 75, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 116, 104, 97, 116, 32, 97, 100, 118, 105, 115, 101, 115, 32, 116, 104, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 32, 116, 111, 32, 101, 109, 105, 116, 32, 97, 32, 110, 111, 110, 45, 98, 114, 101, 97, 107, 105, 110, 103, 32, 115, 112, 97, 99, 101, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Parser_ppSpace: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 112, 83, 112, 97, 99, 101, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value) as *mut LeanObject,8702527878508030907 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 116, 104, 97, 116, 32, 97, 100, 118, 105, 115, 101, 115, 32, 116, 104, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 32, 116, 111, 32, 101, 109, 105, 116, 32, 97, 32, 115, 112, 97, 99, 101, 47, 115, 111, 102, 116, 32, 108, 105, 110, 101, 32, 98, 114, 101, 97, 107, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Parser_ppLine: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 112, 76, 105, 110, 101, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value) as *mut LeanObject,11952458875687197953 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2_value: LeanStringObject<73> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 73, m_capacity: 73, m_length: 72, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 116, 104, 97, 116, 32, 97, 100, 118, 105, 115, 101, 115, 32, 116, 104, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 32, 116, 111, 32, 101, 109, 105, 116, 32, 97, 32, 104, 97, 114, 100, 32, 108, 105, 110, 101, 32, 98, 114, 101, 97, 107, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [112, 112, 82, 101, 97, 108, 70, 105, 108, 108, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value) as *mut LeanObject,11116100332334613537 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2_value: LeanStringObject<87> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 87, m_capacity: 87, m_length: 86, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 32, 116, 104, 97, 116, 32, 97, 100, 118, 105, 115, 101, 115, 32, 116, 104, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 32, 116, 111, 32, 101, 109, 105, 116, 32, 97, 32, 96, 70, 111, 114, 109, 97, 116, 46, 102, 105, 108, 108, 96, 32, 110, 111, 100, 101, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 112, 82, 101, 97, 108, 71, 114, 111, 117, 112, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value) as *mut LeanObject,14365465373773348682 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2_value: LeanStringObject<88> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 88, m_capacity: 88, m_length: 87, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 32, 116, 104, 97, 116, 32, 97, 100, 118, 105, 115, 101, 115, 32, 116, 104, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 32, 116, 111, 32, 101, 109, 105, 116, 32, 97, 32, 96, 70, 111, 114, 109, 97, 116, 46, 103, 114, 111, 117, 112, 96, 32, 110, 111, 100, 101, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 112, 73, 110, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value) as *mut LeanObject,11261044947187515996 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2_value: LeanStringObject<105> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 105, m_capacity: 105, m_length: 104, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 32, 116, 104, 97, 116, 32, 97, 100, 118, 105, 115, 101, 115, 32, 116, 104, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 32, 116, 111, 32, 105, 110, 100, 101, 110, 116, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 115, 121, 110, 116, 97, 120, 32, 119, 105, 116, 104, 111, 117, 116, 32, 103, 114, 111, 117, 112, 105, 110, 103, 32, 105, 116, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 112, 71, 114, 111, 117, 112, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value) as *mut LeanObject,5596117090558593697 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2_value: LeanStringObject<143> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 143, m_capacity: 143, m_length: 142, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 32, 116, 104, 97, 116, 32, 97, 100, 118, 105, 115, 101, 115, 32, 116, 104, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 32, 116, 111, 32, 103, 114, 111, 117, 112, 32, 97, 110, 100, 32, 105, 110, 100, 101, 110, 116, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 115, 121, 110, 116, 97, 120, 46, 10, 66, 121, 32, 100, 101, 102, 97, 117, 108, 116, 44, 32, 111, 110, 108, 121, 32, 115, 121, 110, 116, 97, 120, 32, 99, 97, 116, 101, 103, 111, 114, 105, 101, 115, 32, 97, 114, 101, 32, 103, 114, 111, 117, 112, 101, 100, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 112, 68, 101, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value) as *mut LeanObject,14444481492728590766 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2_value: LeanStringObject<158> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 32, 116, 104, 97, 116, 32, 97, 100, 118, 105, 115, 101, 115, 32, 116, 104, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 32, 116, 111, 32, 100, 101, 100, 101, 110, 116, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 115, 121, 110, 116, 97, 120, 46, 10, 68, 101, 100, 101, 110, 116, 105, 110, 103, 32, 99, 97, 110, 32, 105, 110, 32, 112, 97, 114, 116, 105, 99, 117, 108, 97, 114, 32, 98, 101, 32, 117, 115, 101, 100, 32, 116, 111, 32, 99, 111, 117, 110, 116, 101, 114, 97, 99, 116, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 32, 105, 110, 100, 101, 110, 116, 97, 116, 105, 111, 110, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Parser_ppAllowUngrouped: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [112, 112, 65, 108, 108, 111, 119, 85, 110, 103, 114, 111, 117, 112, 101, 100, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value) as *mut LeanObject,9574488591815391586 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2_value: LeanStringObject<277> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 277, m_capacity: 277, m_length: 276, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 32, 116, 104, 97, 116, 32, 97, 108, 108, 111, 119, 115, 32, 116, 104, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 32, 116, 111, 32, 111, 109, 105, 116, 32, 116, 104, 101, 32, 103, 114, 111, 117, 112, 32, 97, 110, 100, 10, 105, 110, 100, 101, 110, 116, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 32, 105, 110, 32, 116, 104, 101, 32, 101, 110, 99, 108, 111, 115, 105, 110, 103, 32, 99, 97, 116, 101, 103, 111, 114, 121, 32, 112, 97, 114, 115, 101, 114, 46, 10, 96, 96, 96, 10, 115, 121, 110, 116, 97, 120, 32, 112, 112, 65, 108, 108, 111, 119, 85, 110, 103, 114, 111, 117, 112, 101, 100, 32, 34, 98, 121, 32, 34, 32, 116, 97, 99, 116, 105, 99, 83, 101, 113, 32, 58, 32, 116, 101, 114, 109, 10, 45, 45, 32, 97, 108, 108, 111, 119, 115, 32, 97, 32, 96, 98, 121, 96, 32, 97, 102, 116, 101, 114, 32, 96, 58, 61, 96, 32, 119, 105, 116, 104, 111, 117, 116, 32, 108, 105, 110, 101, 98, 114, 101, 97, 107, 32, 105, 110, 32, 98, 101, 116, 119, 101, 101, 110, 58, 10, 116, 104, 101, 111, 114, 101, 109, 32, 102, 111, 111, 32, 58, 32, 84, 114, 117, 101, 32, 58, 61, 32, 98, 121, 10, 32, 32, 116, 114, 105, 118, 105, 97, 108, 10, 96, 96, 96, 10, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [112, 112, 68, 101, 100, 101, 110, 116, 73, 102, 71, 114, 111, 117, 112, 101, 100, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value) as *mut LeanObject,15454112464827046919 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2_value: LeanStringObject<200> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 200, m_capacity: 200, m_length: 199, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 32, 116, 104, 97, 116, 32, 97, 100, 118, 105, 115, 101, 115, 32, 116, 104, 101, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 32, 116, 111, 32, 100, 101, 100, 101, 110, 116, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 115, 121, 110, 116, 97, 120, 44, 10, 105, 102, 32, 105, 116, 32, 119, 97, 115, 32, 103, 114, 111, 117, 112, 101, 100, 32, 98, 121, 32, 116, 104, 101, 32, 99, 97, 116, 101, 103, 111, 114, 121, 32, 112, 97, 114, 115, 101, 114, 46, 10, 68, 101, 100, 101, 110, 116, 105, 110, 103, 32, 99, 97, 110, 32, 105, 110, 32, 112, 97, 114, 116, 105, 99, 117, 108, 97, 114, 32, 98, 101, 32, 117, 115, 101, 100, 32, 116, 111, 32, 99, 111, 117, 110, 116, 101, 114, 97, 99, 116, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 32, 105, 110, 100, 101, 110, 116, 97, 116, 105, 111, 110, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Parser_ppHardLineUnlessUngrouped: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [112, 112, 72, 97, 114, 100, 76, 105, 110, 101, 85, 110, 108, 101, 115, 115, 85, 110, 103, 114, 111, 117, 112, 101, 100, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value) as *mut LeanObject,492679553298697224 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2_value: LeanStringObject<167> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 167, m_capacity: 167, m_length: 166, m_data: [78, 111, 45, 111, 112, 32, 112, 97, 114, 115, 101, 114, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 32, 116, 104, 97, 116, 32, 112, 114, 105, 110, 116, 115, 32, 97, 32, 108, 105, 110, 101, 32, 98, 114, 101, 97, 107, 46, 10, 84, 104, 101, 32, 108, 105, 110, 101, 32, 98, 114, 101, 97, 107, 32, 105, 115, 32, 115, 111, 102, 116, 32, 105, 102, 32, 116, 104, 101, 32, 99, 111, 109, 98, 105, 110, 97, 116, 111, 114, 32, 105, 115, 32, 102, 111, 108, 108, 111, 119, 101, 100, 10, 98, 121, 32, 97, 110, 32, 117, 110, 103, 114, 111, 117, 112, 101, 100, 32, 112, 97, 114, 115, 101, 114, 32, 40, 115, 101, 101, 32, 112, 112, 65, 108, 108, 111, 119, 85, 110, 103, 114, 111, 117, 112, 101, 100, 41, 44, 32, 111, 116, 104, 101, 114, 119, 105, 115, 101, 32, 104, 97, 114, 100, 46, 32, 0]};
static mut l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_ppHardSpace_formatter___redArg___closed__0_value: LeanStringObject<2> =
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
        m_data: [32, 0],
    };
static mut l_Lean_ppHardSpace_formatter___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppHardSpace_formatter___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_ppHardSpace_formatter___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_ppHardSpace_formatter___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_ppHardSpace_formatter___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppHardSpace_formatter___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_ppDedent_formatter___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ppDedent_formatter___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0_value: LeanStringObject<41> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [116, 101, 114, 109, 82, 101, 103, 105, 115, 116, 101, 114, 95, 112, 97, 114, 115, 101, 114, 95, 97, 108, 105, 97, 115, 40, 75, 105, 110, 100, 58, 61, 95, 41, 95, 95, 95, 95, 95, 95, 0]};
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0_value
) as *mut LeanObject;
static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0_value) as *mut LeanObject,3672263712148064232 as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 116, 104, 101, 110, 0]};
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2_value) as *mut LeanObject,12571085391447129896 as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [114, 101, 103, 105, 115, 116, 101, 114, 95, 112, 97, 114, 115, 101, 114, 95, 97, 108, 105, 97, 115, 32, 0]};
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [107, 105, 110, 100, 0]};
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 8) as u16, other: 1, tag: 6 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7_value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 7 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_termParser_formatter___redArg___closed__1_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [41, 32, 0]};
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_group_formatter___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_optional_formatter___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_strLit_formatter___closed__1_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value) as *mut LeanObject,17761616517784022991 as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_optional_formatter___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_ident_formatter___closed__1_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 108, 71, 116, 0]};
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29_value) as *mut LeanObject,17597206043415342265 as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_optional_formatter___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35_value
) as *mut LeanObject;
pub static l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value) as *mut LeanObject,((( 1022 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35_value) as *mut LeanObject] };
static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36_value
) as *mut LeanObject;
pub static mut l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29____________:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36_value
) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 111, 110, 45, 111, 118, 101, 114, 108, 111, 97, 100, 101, 100, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 110, 97, 109, 101, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 70, 111, 114, 109, 97, 116, 116, 101, 114, 46, 114, 101, 103, 105, 115, 116, 101, 114, 65, 108, 105, 97, 115, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [70, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value) as *mut LeanObject,7217738091093750654 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 80, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 46, 114, 101, 103, 105, 115, 116, 101, 114, 65, 108, 105, 97, 115, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value) as *mut LeanObject,4356502393917455154 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 97, 109, 101, 100, 65, 114, 103, 117, 109, 101, 110, 116, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [107, 105, 110, 100, 63, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12_value) as *mut LeanObject,13532862018704899050 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 111, 109, 101, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value) as *mut LeanObject,15308379890181982757 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [79, 112, 116, 105, 111, 110, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19_value) as *mut LeanObject,18184376426117065311 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value) as *mut LeanObject,4893146552088433753 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [100, 111, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value) as *mut LeanObject,5817315006727311029 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value) as *mut LeanObject,3326968124746134365 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value) as *mut LeanObject,940684074193935882 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value) as *mut LeanObject,5573444893818005634 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [80, 97, 114, 115, 101, 114, 46, 114, 101, 103, 105, 115, 116, 101, 114, 65, 108, 105, 97, 115, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 103, 105, 115, 116, 101, 114, 65, 108, 105, 97, 115, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,6907480769838958894 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value) as *mut LeanObject,14759640638895077076 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value) as *mut LeanObject,13638960199343220561 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 111, 117, 98, 108, 101, 81, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value) as *mut LeanObject,11323065835382012354 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 111, 105, 99, 101, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42_value) as *mut LeanObject,11985596712582660667 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 101, 114, 109, 123, 125, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44_value) as *mut LeanObject,5126085667538439468 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_value) as *mut LeanObject,2026475204632980274 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value) as *mut LeanObject,5018042693327868416 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [111, 112, 116, 69, 108, 108, 105, 112, 115, 105, 115, 0]};
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value) as *mut LeanObject;
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value) as *mut LeanObject,11580369617518985485 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61: *mut LeanObject = core::ptr::null_mut();
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value) as *mut LeanObject,9368229134555052249 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_fill___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_group___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Extra_0__Lean_initFn___lam__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l_Lean_Parser_patternIgnore_formatter___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value) as *mut LeanObject,7000476957016433988 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value) as *mut LeanObject,211807283801307390 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value) as *mut LeanObject,8165513851075404995 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_ppDedentIfGrouped_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value) as *mut LeanObject,2710995909225096690 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_ppDedent_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value) as *mut LeanObject,2962757659044384496 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_ppIndent_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value) as *mut LeanObject,3595567918023170837 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value) as *mut LeanObject,12555850061918943318 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value) as *mut LeanObject,15964447885077099669 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_ppGroup_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value) as *mut LeanObject,4227538229121138037 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value) as *mut LeanObject,15956630274364582095 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject,1 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_Extra_0__Lean_initFn___lam__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l_Lean_Parser_group_formatter___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_group_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_group_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_patternIgnore_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_patternIgnore_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Parser_leadingNode_formatter___redArg(
    mut v_n_4718_: *mut LeanObject,
    mut v_p_4719_: *mut LeanObject,
    mut v_a_4720_: *mut LeanObject,
    mut v_a_4721_: *mut LeanObject,
    mut v_a_4722_: *mut LeanObject,
    mut v_a_4723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    v___x_4725_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4726_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_node_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_4726_, 0, v_n_4718_);
    lean_closure_set(v___x_4726_, 1, v_p_4719_);
    v___x_4727_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4728_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_4728_, 0, v___x_4726_);
    lean_closure_set(v___x_4728_, 1, v___x_4727_);
    v___x_4729_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(
        v___x_4725_,
        v___x_4728_,
        v_a_4720_,
        v_a_4721_,
        v_a_4722_,
        v_a_4723_,
    );
    return v___x_4729_;
}
pub unsafe fn l_Lean_Parser_leadingNode_formatter___redArg___boxed(
    mut v_n_4730_: *mut LeanObject,
    mut v_p_4731_: *mut LeanObject,
    mut v_a_4732_: *mut LeanObject,
    mut v_a_4733_: *mut LeanObject,
    mut v_a_4734_: *mut LeanObject,
    mut v_a_4735_: *mut LeanObject,
    mut v_a_4736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4737_: *mut LeanObject = core::ptr::null_mut();
    v_res_4737_ = l_Lean_Parser_leadingNode_formatter___redArg(
        v_n_4730_, v_p_4731_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_,
    );
    lean_dec(v_a_4735_);
    lean_dec_ref(v_a_4734_);
    lean_dec(v_a_4733_);
    lean_dec_ref(v_a_4732_);
    return v_res_4737_;
}
pub unsafe fn l_Lean_Parser_leadingNode_formatter(
    mut v_n_4738_: *mut LeanObject,
    mut v_prec_4739_: *mut LeanObject,
    mut v_p_4740_: *mut LeanObject,
    mut v_a_4741_: *mut LeanObject,
    mut v_a_4742_: *mut LeanObject,
    mut v_a_4743_: *mut LeanObject,
    mut v_a_4744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    v___x_4746_ = l_Lean_Parser_leadingNode_formatter___redArg(
        v_n_4738_, v_p_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_,
    );
    return v___x_4746_;
}
pub unsafe fn l_Lean_Parser_leadingNode_formatter___boxed(
    mut v_n_4747_: *mut LeanObject,
    mut v_prec_4748_: *mut LeanObject,
    mut v_p_4749_: *mut LeanObject,
    mut v_a_4750_: *mut LeanObject,
    mut v_a_4751_: *mut LeanObject,
    mut v_a_4752_: *mut LeanObject,
    mut v_a_4753_: *mut LeanObject,
    mut v_a_4754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4755_: *mut LeanObject = core::ptr::null_mut();
    v_res_4755_ = l_Lean_Parser_leadingNode_formatter(
        v_n_4747_,
        v_prec_4748_,
        v_p_4749_,
        v_a_4750_,
        v_a_4751_,
        v_a_4752_,
        v_a_4753_,
    );
    lean_dec(v_a_4753_);
    lean_dec_ref(v_a_4752_);
    lean_dec(v_a_4751_);
    lean_dec_ref(v_a_4750_);
    lean_dec(v_prec_4748_);
    return v_res_4755_;
}
pub unsafe fn l_Lean_Parser_termParser_formatter___redArg(
    mut v_a_4759_: *mut LeanObject,
    mut v_a_4760_: *mut LeanObject,
    mut v_a_4761_: *mut LeanObject,
    mut v_a_4762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    v___x_4764_ = l_Lean_Parser_termParser_formatter___redArg___closed__1;
    v___x_4765_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(
        v___x_4764_,
        v_a_4759_,
        v_a_4760_,
        v_a_4761_,
        v_a_4762_,
    );
    return v___x_4765_;
}
pub unsafe fn l_Lean_Parser_termParser_formatter___redArg___boxed(
    mut v_a_4766_: *mut LeanObject,
    mut v_a_4767_: *mut LeanObject,
    mut v_a_4768_: *mut LeanObject,
    mut v_a_4769_: *mut LeanObject,
    mut v_a_4770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4771_: *mut LeanObject = core::ptr::null_mut();
    v_res_4771_ =
        l_Lean_Parser_termParser_formatter___redArg(v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
    lean_dec(v_a_4769_);
    lean_dec_ref(v_a_4768_);
    lean_dec(v_a_4767_);
    lean_dec_ref(v_a_4766_);
    return v_res_4771_;
}
pub unsafe fn l_Lean_Parser_termParser_formatter(
    mut v_prec_4772_: *mut LeanObject,
    mut v_a_4773_: *mut LeanObject,
    mut v_a_4774_: *mut LeanObject,
    mut v_a_4775_: *mut LeanObject,
    mut v_a_4776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    v___x_4778_ =
        l_Lean_Parser_termParser_formatter___redArg(v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
    return v___x_4778_;
}
pub unsafe fn l_Lean_Parser_termParser_formatter___boxed(
    mut v_prec_4779_: *mut LeanObject,
    mut v_a_4780_: *mut LeanObject,
    mut v_a_4781_: *mut LeanObject,
    mut v_a_4782_: *mut LeanObject,
    mut v_a_4783_: *mut LeanObject,
    mut v_a_4784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4785_: *mut LeanObject = core::ptr::null_mut();
    v_res_4785_ = l_Lean_Parser_termParser_formatter(
        v_prec_4779_,
        v_a_4780_,
        v_a_4781_,
        v_a_4782_,
        v_a_4783_,
    );
    lean_dec(v_a_4783_);
    lean_dec_ref(v_a_4782_);
    lean_dec(v_a_4781_);
    lean_dec_ref(v_a_4780_);
    lean_dec(v_prec_4779_);
    return v_res_4785_;
}
pub unsafe fn l_Lean_Parser_termParser_parenthesizer(
    mut v_prec_4786_: *mut LeanObject,
    mut v_a_4787_: *mut LeanObject,
    mut v_a_4788_: *mut LeanObject,
    mut v_a_4789_: *mut LeanObject,
    mut v_a_4790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    v___x_4792_ = l_Lean_Parser_termParser_formatter___redArg___closed__1;
    v___x_4793_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(
        v___x_4792_,
        v_prec_4786_,
        v_a_4787_,
        v_a_4788_,
        v_a_4789_,
        v_a_4790_,
    );
    return v___x_4793_;
}
pub unsafe fn l_Lean_Parser_termParser_parenthesizer___boxed(
    mut v_prec_4794_: *mut LeanObject,
    mut v_a_4795_: *mut LeanObject,
    mut v_a_4796_: *mut LeanObject,
    mut v_a_4797_: *mut LeanObject,
    mut v_a_4798_: *mut LeanObject,
    mut v_a_4799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4800_: *mut LeanObject = core::ptr::null_mut();
    v_res_4800_ = l_Lean_Parser_termParser_parenthesizer(
        v_prec_4794_,
        v_a_4795_,
        v_a_4796_,
        v_a_4797_,
        v_a_4798_,
    );
    lean_dec(v_a_4798_);
    lean_dec_ref(v_a_4797_);
    lean_dec(v_a_4796_);
    lean_dec_ref(v_a_4795_);
    return v_res_4800_;
}
pub unsafe fn l_Lean_Parser_commandParser_formatter___redArg(
    mut v_a_4804_: *mut LeanObject,
    mut v_a_4805_: *mut LeanObject,
    mut v_a_4806_: *mut LeanObject,
    mut v_a_4807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    v___x_4809_ = l_Lean_Parser_commandParser_formatter___redArg___closed__1;
    v___x_4810_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(
        v___x_4809_,
        v_a_4804_,
        v_a_4805_,
        v_a_4806_,
        v_a_4807_,
    );
    return v___x_4810_;
}
pub unsafe fn l_Lean_Parser_commandParser_formatter___redArg___boxed(
    mut v_a_4811_: *mut LeanObject,
    mut v_a_4812_: *mut LeanObject,
    mut v_a_4813_: *mut LeanObject,
    mut v_a_4814_: *mut LeanObject,
    mut v_a_4815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4816_: *mut LeanObject = core::ptr::null_mut();
    v_res_4816_ =
        l_Lean_Parser_commandParser_formatter___redArg(v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
    lean_dec(v_a_4814_);
    lean_dec_ref(v_a_4813_);
    lean_dec(v_a_4812_);
    lean_dec_ref(v_a_4811_);
    return v_res_4816_;
}
pub unsafe fn l_Lean_Parser_commandParser_formatter(
    mut v_rbp_4817_: *mut LeanObject,
    mut v_a_4818_: *mut LeanObject,
    mut v_a_4819_: *mut LeanObject,
    mut v_a_4820_: *mut LeanObject,
    mut v_a_4821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    v___x_4823_ =
        l_Lean_Parser_commandParser_formatter___redArg(v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_);
    return v___x_4823_;
}
pub unsafe fn l_Lean_Parser_commandParser_formatter___boxed(
    mut v_rbp_4824_: *mut LeanObject,
    mut v_a_4825_: *mut LeanObject,
    mut v_a_4826_: *mut LeanObject,
    mut v_a_4827_: *mut LeanObject,
    mut v_a_4828_: *mut LeanObject,
    mut v_a_4829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4830_: *mut LeanObject = core::ptr::null_mut();
    v_res_4830_ = l_Lean_Parser_commandParser_formatter(
        v_rbp_4824_,
        v_a_4825_,
        v_a_4826_,
        v_a_4827_,
        v_a_4828_,
    );
    lean_dec(v_a_4828_);
    lean_dec_ref(v_a_4827_);
    lean_dec(v_a_4826_);
    lean_dec_ref(v_a_4825_);
    lean_dec(v_rbp_4824_);
    return v_res_4830_;
}
pub unsafe fn l_Lean_Parser_commandParser_parenthesizer(
    mut v_rbp_4831_: *mut LeanObject,
    mut v_a_4832_: *mut LeanObject,
    mut v_a_4833_: *mut LeanObject,
    mut v_a_4834_: *mut LeanObject,
    mut v_a_4835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    v___x_4837_ = l_Lean_Parser_commandParser_formatter___redArg___closed__1;
    v___x_4838_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(
        v___x_4837_,
        v_rbp_4831_,
        v_a_4832_,
        v_a_4833_,
        v_a_4834_,
        v_a_4835_,
    );
    return v___x_4838_;
}
pub unsafe fn l_Lean_Parser_commandParser_parenthesizer___boxed(
    mut v_rbp_4839_: *mut LeanObject,
    mut v_a_4840_: *mut LeanObject,
    mut v_a_4841_: *mut LeanObject,
    mut v_a_4842_: *mut LeanObject,
    mut v_a_4843_: *mut LeanObject,
    mut v_a_4844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4845_: *mut LeanObject = core::ptr::null_mut();
    v_res_4845_ = l_Lean_Parser_commandParser_parenthesizer(
        v_rbp_4839_,
        v_a_4840_,
        v_a_4841_,
        v_a_4842_,
        v_a_4843_,
    );
    lean_dec(v_a_4843_);
    lean_dec_ref(v_a_4842_);
    lean_dec(v_a_4841_);
    lean_dec_ref(v_a_4840_);
    return v_res_4845_;
}
pub unsafe fn l_Lean_Parser_atomic_formatter(
    mut v_p_4846_: *mut LeanObject,
    mut v_a_4847_: *mut LeanObject,
    mut v_a_4848_: *mut LeanObject,
    mut v_a_4849_: *mut LeanObject,
    mut v_a_4850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_4850_);
    lean_inc_ref(v_a_4849_);
    lean_inc(v_a_4848_);
    lean_inc_ref(v_a_4847_);
    v___x_4852_ = lean_apply_5(
        v_p_4846_,
        v_a_4847_,
        v_a_4848_,
        v_a_4849_,
        v_a_4850_,
        lean_box(0),
    );
    return v___x_4852_;
}
pub unsafe fn l_Lean_Parser_atomic_formatter___boxed(
    mut v_p_4853_: *mut LeanObject,
    mut v_a_4854_: *mut LeanObject,
    mut v_a_4855_: *mut LeanObject,
    mut v_a_4856_: *mut LeanObject,
    mut v_a_4857_: *mut LeanObject,
    mut v_a_4858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4859_: *mut LeanObject = core::ptr::null_mut();
    v_res_4859_ =
        l_Lean_Parser_atomic_formatter(v_p_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
    lean_dec(v_a_4857_);
    lean_dec_ref(v_a_4856_);
    lean_dec(v_a_4855_);
    lean_dec_ref(v_a_4854_);
    return v_res_4859_;
}
pub unsafe fn l_Lean_Parser_setExpected_formatter___redArg(
    mut v_p_4860_: *mut LeanObject,
    mut v_a_4861_: *mut LeanObject,
    mut v_a_4862_: *mut LeanObject,
    mut v_a_4863_: *mut LeanObject,
    mut v_a_4864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_4864_);
    lean_inc_ref(v_a_4863_);
    lean_inc(v_a_4862_);
    lean_inc_ref(v_a_4861_);
    v___x_4866_ = lean_apply_5(
        v_p_4860_,
        v_a_4861_,
        v_a_4862_,
        v_a_4863_,
        v_a_4864_,
        lean_box(0),
    );
    return v___x_4866_;
}
pub unsafe fn l_Lean_Parser_setExpected_formatter___redArg___boxed(
    mut v_p_4867_: *mut LeanObject,
    mut v_a_4868_: *mut LeanObject,
    mut v_a_4869_: *mut LeanObject,
    mut v_a_4870_: *mut LeanObject,
    mut v_a_4871_: *mut LeanObject,
    mut v_a_4872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4873_: *mut LeanObject = core::ptr::null_mut();
    v_res_4873_ = l_Lean_Parser_setExpected_formatter___redArg(
        v_p_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_,
    );
    lean_dec(v_a_4871_);
    lean_dec_ref(v_a_4870_);
    lean_dec(v_a_4869_);
    lean_dec_ref(v_a_4868_);
    return v_res_4873_;
}
pub unsafe fn l_Lean_Parser_setExpected_formatter(
    mut v_expected_4874_: *mut LeanObject,
    mut v_p_4875_: *mut LeanObject,
    mut v_a_4876_: *mut LeanObject,
    mut v_a_4877_: *mut LeanObject,
    mut v_a_4878_: *mut LeanObject,
    mut v_a_4879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_4879_);
    lean_inc_ref(v_a_4878_);
    lean_inc(v_a_4877_);
    lean_inc_ref(v_a_4876_);
    v___x_4881_ = lean_apply_5(
        v_p_4875_,
        v_a_4876_,
        v_a_4877_,
        v_a_4878_,
        v_a_4879_,
        lean_box(0),
    );
    return v___x_4881_;
}
pub unsafe fn l_Lean_Parser_setExpected_formatter___boxed(
    mut v_expected_4882_: *mut LeanObject,
    mut v_p_4883_: *mut LeanObject,
    mut v_a_4884_: *mut LeanObject,
    mut v_a_4885_: *mut LeanObject,
    mut v_a_4886_: *mut LeanObject,
    mut v_a_4887_: *mut LeanObject,
    mut v_a_4888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4889_: *mut LeanObject = core::ptr::null_mut();
    v_res_4889_ = l_Lean_Parser_setExpected_formatter(
        v_expected_4882_,
        v_p_4883_,
        v_a_4884_,
        v_a_4885_,
        v_a_4886_,
        v_a_4887_,
    );
    lean_dec(v_a_4887_);
    lean_dec_ref(v_a_4886_);
    lean_dec(v_a_4885_);
    lean_dec_ref(v_a_4884_);
    lean_dec(v_expected_4882_);
    return v_res_4889_;
}
pub unsafe fn l_Lean_Parser_symbol_formatter(
    mut v_sym_4890_: *mut LeanObject,
    mut v_a_4891_: *mut LeanObject,
    mut v_a_4892_: *mut LeanObject,
    mut v_a_4893_: *mut LeanObject,
    mut v_a_4894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    v___x_4896_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_4896_, 0, v_sym_4890_);
    v___x_4897_ = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(
        v___x_4896_,
        v_a_4891_,
        v_a_4892_,
        v_a_4893_,
        v_a_4894_,
    );
    return v___x_4897_;
}
pub unsafe fn l_Lean_Parser_symbol_formatter___boxed(
    mut v_sym_4898_: *mut LeanObject,
    mut v_a_4899_: *mut LeanObject,
    mut v_a_4900_: *mut LeanObject,
    mut v_a_4901_: *mut LeanObject,
    mut v_a_4902_: *mut LeanObject,
    mut v_a_4903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4904_: *mut LeanObject = core::ptr::null_mut();
    v_res_4904_ =
        l_Lean_Parser_symbol_formatter(v_sym_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
    lean_dec(v_a_4902_);
    lean_dec_ref(v_a_4901_);
    lean_dec(v_a_4900_);
    lean_dec_ref(v_a_4899_);
    return v_res_4904_;
}
pub unsafe fn l_Lean_Parser_adaptCacheableContext_formatter___redArg(
    mut v_p_4905_: *mut LeanObject,
    mut v_a_4906_: *mut LeanObject,
    mut v_a_4907_: *mut LeanObject,
    mut v_a_4908_: *mut LeanObject,
    mut v_a_4909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_4909_);
    lean_inc_ref(v_a_4908_);
    lean_inc(v_a_4907_);
    lean_inc_ref(v_a_4906_);
    v___x_4911_ = lean_apply_5(
        v_p_4905_,
        v_a_4906_,
        v_a_4907_,
        v_a_4908_,
        v_a_4909_,
        lean_box(0),
    );
    return v___x_4911_;
}
pub unsafe fn l_Lean_Parser_adaptCacheableContext_formatter___redArg___boxed(
    mut v_p_4912_: *mut LeanObject,
    mut v_a_4913_: *mut LeanObject,
    mut v_a_4914_: *mut LeanObject,
    mut v_a_4915_: *mut LeanObject,
    mut v_a_4916_: *mut LeanObject,
    mut v_a_4917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4918_: *mut LeanObject = core::ptr::null_mut();
    v_res_4918_ = l_Lean_Parser_adaptCacheableContext_formatter___redArg(
        v_p_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_,
    );
    lean_dec(v_a_4916_);
    lean_dec_ref(v_a_4915_);
    lean_dec(v_a_4914_);
    lean_dec_ref(v_a_4913_);
    return v_res_4918_;
}
pub unsafe fn l_Lean_Parser_adaptCacheableContext_formatter(
    mut v_f_4919_: *mut LeanObject,
    mut v_p_4920_: *mut LeanObject,
    mut v_a_4921_: *mut LeanObject,
    mut v_a_4922_: *mut LeanObject,
    mut v_a_4923_: *mut LeanObject,
    mut v_a_4924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_4924_);
    lean_inc_ref(v_a_4923_);
    lean_inc(v_a_4922_);
    lean_inc_ref(v_a_4921_);
    v___x_4926_ = lean_apply_5(
        v_p_4920_,
        v_a_4921_,
        v_a_4922_,
        v_a_4923_,
        v_a_4924_,
        lean_box(0),
    );
    return v___x_4926_;
}
pub unsafe fn l_Lean_Parser_adaptCacheableContext_formatter___boxed(
    mut v_f_4927_: *mut LeanObject,
    mut v_p_4928_: *mut LeanObject,
    mut v_a_4929_: *mut LeanObject,
    mut v_a_4930_: *mut LeanObject,
    mut v_a_4931_: *mut LeanObject,
    mut v_a_4932_: *mut LeanObject,
    mut v_a_4933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4934_: *mut LeanObject = core::ptr::null_mut();
    v_res_4934_ = l_Lean_Parser_adaptCacheableContext_formatter(
        v_f_4927_, v_p_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_,
    );
    lean_dec(v_a_4932_);
    lean_dec_ref(v_a_4931_);
    lean_dec(v_a_4930_);
    lean_dec_ref(v_a_4929_);
    lean_dec_ref(v_f_4927_);
    return v_res_4934_;
}
pub unsafe fn l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg(
    mut v_p_4935_: *mut LeanObject,
    mut v_a_4936_: *mut LeanObject,
    mut v_a_4937_: *mut LeanObject,
    mut v_a_4938_: *mut LeanObject,
    mut v_a_4939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_4939_);
    lean_inc_ref(v_a_4938_);
    lean_inc(v_a_4937_);
    lean_inc_ref(v_a_4936_);
    v___x_4941_ = lean_apply_5(
        v_p_4935_,
        v_a_4936_,
        v_a_4937_,
        v_a_4938_,
        v_a_4939_,
        lean_box(0),
    );
    return v___x_4941_;
}
pub unsafe fn l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg___boxed(
    mut v_p_4942_: *mut LeanObject,
    mut v_a_4943_: *mut LeanObject,
    mut v_a_4944_: *mut LeanObject,
    mut v_a_4945_: *mut LeanObject,
    mut v_a_4946_: *mut LeanObject,
    mut v_a_4947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4948_: *mut LeanObject = core::ptr::null_mut();
    v_res_4948_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg(
        v_p_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_,
    );
    lean_dec(v_a_4946_);
    lean_dec_ref(v_a_4945_);
    lean_dec(v_a_4944_);
    lean_dec_ref(v_a_4943_);
    return v_res_4948_;
}
pub unsafe fn l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(
    mut v_i_4949_: *mut LeanObject,
    mut v_p_4950_: *mut LeanObject,
    mut v_a_4951_: *mut LeanObject,
    mut v_a_4952_: *mut LeanObject,
    mut v_a_4953_: *mut LeanObject,
    mut v_a_4954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_4954_);
    lean_inc_ref(v_a_4953_);
    lean_inc(v_a_4952_);
    lean_inc_ref(v_a_4951_);
    v___x_4956_ = lean_apply_5(
        v_p_4950_,
        v_a_4951_,
        v_a_4952_,
        v_a_4953_,
        v_a_4954_,
        lean_box(0),
    );
    return v___x_4956_;
}
pub unsafe fn l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___boxed(
    mut v_i_4957_: *mut LeanObject,
    mut v_p_4958_: *mut LeanObject,
    mut v_a_4959_: *mut LeanObject,
    mut v_a_4960_: *mut LeanObject,
    mut v_a_4961_: *mut LeanObject,
    mut v_a_4962_: *mut LeanObject,
    mut v_a_4963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4964_: *mut LeanObject = core::ptr::null_mut();
    v_res_4964_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(
        v_i_4957_, v_p_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_,
    );
    lean_dec(v_a_4962_);
    lean_dec_ref(v_a_4961_);
    lean_dec(v_a_4960_);
    lean_dec_ref(v_a_4959_);
    lean_dec(v_i_4957_);
    return v_res_4964_;
}
pub unsafe fn l_Lean_Parser_decQuotDepth_formatter(
    mut v_p_4965_: *mut LeanObject,
    mut v_a_4966_: *mut LeanObject,
    mut v_a_4967_: *mut LeanObject,
    mut v_a_4968_: *mut LeanObject,
    mut v_a_4969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_4969_);
    lean_inc_ref(v_a_4968_);
    lean_inc(v_a_4967_);
    lean_inc_ref(v_a_4966_);
    v___x_4971_ = lean_apply_5(
        v_p_4965_,
        v_a_4966_,
        v_a_4967_,
        v_a_4968_,
        v_a_4969_,
        lean_box(0),
    );
    return v___x_4971_;
}
pub unsafe fn l_Lean_Parser_decQuotDepth_formatter___boxed(
    mut v_p_4972_: *mut LeanObject,
    mut v_a_4973_: *mut LeanObject,
    mut v_a_4974_: *mut LeanObject,
    mut v_a_4975_: *mut LeanObject,
    mut v_a_4976_: *mut LeanObject,
    mut v_a_4977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4978_: *mut LeanObject = core::ptr::null_mut();
    v_res_4978_ =
        l_Lean_Parser_decQuotDepth_formatter(v_p_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_);
    lean_dec(v_a_4976_);
    lean_dec_ref(v_a_4975_);
    lean_dec(v_a_4974_);
    lean_dec_ref(v_a_4973_);
    return v_res_4978_;
}
pub unsafe fn l_Lean_Parser_antiquotNestedExpr_formatter(
    mut v_a_4995_: *mut LeanObject,
    mut v_a_4996_: *mut LeanObject,
    mut v_a_4997_: *mut LeanObject,
    mut v_a_4998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    v___x_5000_ = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
    v___x_5001_ = l_Lean_Parser_antiquotNestedExpr_formatter___closed__8;
    v___x_5002_ = l_Lean_PrettyPrinter_Formatter_node_formatter(
        v___x_5000_,
        v___x_5001_,
        v_a_4995_,
        v_a_4996_,
        v_a_4997_,
        v_a_4998_,
    );
    return v___x_5002_;
}
pub unsafe fn l_Lean_Parser_antiquotNestedExpr_formatter___boxed(
    mut v_a_5003_: *mut LeanObject,
    mut v_a_5004_: *mut LeanObject,
    mut v_a_5005_: *mut LeanObject,
    mut v_a_5006_: *mut LeanObject,
    mut v_a_5007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5008_: *mut LeanObject = core::ptr::null_mut();
    v_res_5008_ =
        l_Lean_Parser_antiquotNestedExpr_formatter(v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_);
    lean_dec(v_a_5006_);
    lean_dec_ref(v_a_5005_);
    lean_dec(v_a_5004_);
    lean_dec_ref(v_a_5003_);
    return v_res_5008_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15()
-> *mut LeanObject {
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    v___x_5018_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_5019_ = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
    v___x_5020_ = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3;
    v___x_5021_ = lean_alloc_closure(
        l_Lean_Parser_antiquotNestedExpr_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5022_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5018_,
        v___x_5019_,
        v___x_5020_,
        v___x_5021_,
    );
    return v___x_5022_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___boxed(
    mut v_a_5023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5024_: *mut LeanObject = core::ptr::null_mut();
    v_res_5024_ = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15();
    return v_res_5024_;
}
pub unsafe fn _init_l_Lean_Parser_antiquotExpr_formatter___closed__2() -> *mut LeanObject {
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    v___x_5028_ = lean_alloc_closure(
        l_Lean_Parser_antiquotNestedExpr_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5029_ = l_Lean_Parser_antiquotExpr_formatter___closed__1;
    v___x_5030_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5030_, 0, v___x_5029_);
    lean_closure_set(v___x_5030_, 1, v___x_5028_);
    return v___x_5030_;
}
pub unsafe fn l_Lean_Parser_antiquotExpr_formatter(
    mut v_a_5031_: *mut LeanObject,
    mut v_a_5032_: *mut LeanObject,
    mut v_a_5033_: *mut LeanObject,
    mut v_a_5034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    v___x_5036_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5037_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_antiquotExpr_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_antiquotExpr_formatter___closed__2_once),
        _init_l_Lean_Parser_antiquotExpr_formatter___closed__2,
    );
    v___x_5038_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_5036_,
        v___x_5037_,
        v_a_5031_,
        v_a_5032_,
        v_a_5033_,
        v_a_5034_,
    );
    return v___x_5038_;
}
pub unsafe fn l_Lean_Parser_antiquotExpr_formatter___boxed(
    mut v_a_5039_: *mut LeanObject,
    mut v_a_5040_: *mut LeanObject,
    mut v_a_5041_: *mut LeanObject,
    mut v_a_5042_: *mut LeanObject,
    mut v_a_5043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5044_: *mut LeanObject = core::ptr::null_mut();
    v_res_5044_ = l_Lean_Parser_antiquotExpr_formatter(v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
    lean_dec(v_a_5042_);
    lean_dec_ref(v_a_5041_);
    lean_dec(v_a_5040_);
    lean_dec_ref(v_a_5039_);
    return v_res_5044_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0(
    mut v_sym_5045_: *mut LeanObject,
    mut v___y_5046_: *mut LeanObject,
    mut v___y_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    v___x_5051_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(
        v_sym_5045_,
        v___y_5046_,
        v___y_5047_,
        v___y_5048_,
        v___y_5049_,
    );
    return v___x_5051_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0___boxed(
    mut v_sym_5052_: *mut LeanObject,
    mut v___y_5053_: *mut LeanObject,
    mut v___y_5054_: *mut LeanObject,
    mut v___y_5055_: *mut LeanObject,
    mut v___y_5056_: *mut LeanObject,
    mut v___y_5057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5058_: *mut LeanObject = core::ptr::null_mut();
    v_res_5058_ = l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0(
        v_sym_5052_,
        v___y_5053_,
        v___y_5054_,
        v___y_5055_,
        v___y_5056_,
    );
    lean_dec(v___y_5056_);
    lean_dec_ref(v___y_5055_);
    lean_dec(v___y_5054_);
    lean_dec_ref(v___y_5053_);
    return v_res_5058_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_formatter___redArg(
    mut v_sym_5059_: *mut LeanObject,
    mut v_a_5060_: *mut LeanObject,
    mut v_a_5061_: *mut LeanObject,
    mut v_a_5062_: *mut LeanObject,
    mut v_a_5063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    v___f_5065_ = lean_alloc_closure(
        l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_5065_, 0, v_sym_5059_);
    v___x_5066_ = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(
        v___f_5065_,
        v_a_5060_,
        v_a_5061_,
        v_a_5062_,
        v_a_5063_,
    );
    return v___x_5066_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_formatter___redArg___boxed(
    mut v_sym_5067_: *mut LeanObject,
    mut v_a_5068_: *mut LeanObject,
    mut v_a_5069_: *mut LeanObject,
    mut v_a_5070_: *mut LeanObject,
    mut v_a_5071_: *mut LeanObject,
    mut v_a_5072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5073_: *mut LeanObject = core::ptr::null_mut();
    v_res_5073_ = l_Lean_Parser_nonReservedSymbol_formatter___redArg(
        v_sym_5067_,
        v_a_5068_,
        v_a_5069_,
        v_a_5070_,
        v_a_5071_,
    );
    lean_dec(v_a_5071_);
    lean_dec_ref(v_a_5070_);
    lean_dec(v_a_5069_);
    lean_dec_ref(v_a_5068_);
    return v_res_5073_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_formatter(
    mut v_sym_5074_: *mut LeanObject,
    mut v_includeIdent_5075_: u8,
    mut v_a_5076_: *mut LeanObject,
    mut v_a_5077_: *mut LeanObject,
    mut v_a_5078_: *mut LeanObject,
    mut v_a_5079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    v___x_5081_ = l_Lean_Parser_nonReservedSymbol_formatter___redArg(
        v_sym_5074_,
        v_a_5076_,
        v_a_5077_,
        v_a_5078_,
        v_a_5079_,
    );
    return v___x_5081_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_formatter___boxed(
    mut v_sym_5082_: *mut LeanObject,
    mut v_includeIdent_5083_: *mut LeanObject,
    mut v_a_5084_: *mut LeanObject,
    mut v_a_5085_: *mut LeanObject,
    mut v_a_5086_: *mut LeanObject,
    mut v_a_5087_: *mut LeanObject,
    mut v_a_5088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeIdent_boxed_5089_: u8 = 0;
    let mut v_res_5090_: *mut LeanObject = core::ptr::null_mut();
    v_includeIdent_boxed_5089_ = (lean_unbox(v_includeIdent_5083_) as u8);
    v_res_5090_ = l_Lean_Parser_nonReservedSymbol_formatter(
        v_sym_5082_,
        v_includeIdent_boxed_5089_,
        v_a_5084_,
        v_a_5085_,
        v_a_5086_,
        v_a_5087_,
    );
    lean_dec(v_a_5087_);
    lean_dec_ref(v_a_5086_);
    lean_dec(v_a_5085_);
    lean_dec_ref(v_a_5084_);
    return v_res_5090_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_formatter___lam__0(
    mut v___y_5091_: *mut LeanObject,
    mut v___y_5092_: *mut LeanObject,
    mut v___y_5093_: *mut LeanObject,
    mut v___y_5094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    v___x_5096_ = l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(v___y_5092_);
    return v___x_5096_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_formatter___lam__0___boxed(
    mut v___y_5097_: *mut LeanObject,
    mut v___y_5098_: *mut LeanObject,
    mut v___y_5099_: *mut LeanObject,
    mut v___y_5100_: *mut LeanObject,
    mut v___y_5101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5102_: *mut LeanObject = core::ptr::null_mut();
    v_res_5102_ = l_Lean_Parser_mkAntiquot_formatter___lam__0(
        v___y_5097_,
        v___y_5098_,
        v___y_5099_,
        v___y_5100_,
    );
    lean_dec(v___y_5100_);
    lean_dec_ref(v___y_5099_);
    lean_dec(v___y_5098_);
    lean_dec_ref(v___y_5097_);
    return v_res_5102_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_formatter___lam__1(
    mut v_anonymous_5109_: u8,
    mut v_name_5110_: *mut LeanObject,
    mut v___f_5111_: *mut LeanObject,
    mut v___f_5112_: *mut LeanObject,
    mut v___y_5113_: *mut LeanObject,
    mut v___y_5114_: *mut LeanObject,
    mut v___y_5115_: *mut LeanObject,
    mut v___y_5116_: *mut LeanObject,
) -> *mut LeanObject {
    if v_anonymous_5109_ == 0 {
        let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_5112_);
        v___x_5118_ = l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1;
        v___x_5119_ = l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3;
        v___x_5120_ = lean_box((v_anonymous_5109_) as usize);
        v___x_5121_ = lean_alloc_closure(
            l_Lean_Parser_nonReservedSymbol_formatter___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5121_, 0, v_name_5110_);
        lean_closure_set(v___x_5121_, 1, v___x_5120_);
        v___x_5122_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5122_, 0, v___x_5119_);
        lean_closure_set(v___x_5122_, 1, v___x_5121_);
        v___x_5123_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5123_, 0, v___f_5111_);
        lean_closure_set(v___x_5123_, 1, v___x_5122_);
        v___x_5124_ = l_Lean_PrettyPrinter_Formatter_node_formatter(
            v___x_5118_,
            v___x_5123_,
            v___y_5113_,
            v___y_5114_,
            v___y_5115_,
            v___y_5116_,
        );
        return v___x_5124_;
    } else {
        let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5127_: u8 = 0;
        let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
        v___x_5125_ = l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1;
        v___x_5126_ = l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3;
        v___x_5127_ = 0;
        v___x_5128_ = lean_box((v___x_5127_) as usize);
        v___x_5129_ = lean_alloc_closure(
            l_Lean_Parser_nonReservedSymbol_formatter___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5129_, 0, v_name_5110_);
        lean_closure_set(v___x_5129_, 1, v___x_5128_);
        v___x_5130_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5130_, 0, v___x_5126_);
        lean_closure_set(v___x_5130_, 1, v___x_5129_);
        v___x_5131_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5131_, 0, v___f_5111_);
        lean_closure_set(v___x_5131_, 1, v___x_5130_);
        v___x_5132_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Formatter_node_formatter___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5132_, 0, v___x_5125_);
        lean_closure_set(v___x_5132_, 1, v___x_5131_);
        v___x_5133_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed
                as *mut core::ffi::c_void,
            5,
            0,
        );
        v___x_5134_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5134_, 0, v___x_5133_);
        lean_closure_set(v___x_5134_, 1, v___f_5112_);
        v___x_5135_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
            v___x_5132_,
            v___x_5134_,
            v___y_5113_,
            v___y_5114_,
            v___y_5115_,
            v___y_5116_,
        );
        return v___x_5135_;
    }
}
pub unsafe fn l_Lean_Parser_mkAntiquot_formatter___lam__1___boxed(
    mut v_anonymous_5136_: *mut LeanObject,
    mut v_name_5137_: *mut LeanObject,
    mut v___f_5138_: *mut LeanObject,
    mut v___f_5139_: *mut LeanObject,
    mut v___y_5140_: *mut LeanObject,
    mut v___y_5141_: *mut LeanObject,
    mut v___y_5142_: *mut LeanObject,
    mut v___y_5143_: *mut LeanObject,
    mut v___y_5144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_anonymous_boxed_5145_: u8 = 0;
    let mut v_res_5146_: *mut LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_5145_ = (lean_unbox(v_anonymous_5136_) as u8);
    v_res_5146_ = l_Lean_Parser_mkAntiquot_formatter___lam__1(
        v_anonymous_boxed_5145_,
        v_name_5137_,
        v___f_5138_,
        v___f_5139_,
        v___y_5140_,
        v___y_5141_,
        v___y_5142_,
        v___y_5143_,
    );
    lean_dec(v___y_5143_);
    lean_dec_ref(v___y_5142_);
    lean_dec(v___y_5141_);
    lean_dec_ref(v___y_5140_);
    return v_res_5146_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_formatter___lam__2(
    mut v___x_5147_: *mut LeanObject,
    mut v___y_5148_: *mut LeanObject,
    mut v___y_5149_: *mut LeanObject,
    mut v___y_5150_: *mut LeanObject,
    mut v___y_5151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    v___x_5153_ = l_Lean_Parser_symbol_formatter(
        v___x_5147_,
        v___y_5148_,
        v___y_5149_,
        v___y_5150_,
        v___y_5151_,
    );
    return v___x_5153_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_formatter___lam__2___boxed(
    mut v___x_5154_: *mut LeanObject,
    mut v___y_5155_: *mut LeanObject,
    mut v___y_5156_: *mut LeanObject,
    mut v___y_5157_: *mut LeanObject,
    mut v___y_5158_: *mut LeanObject,
    mut v___y_5159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5160_: *mut LeanObject = core::ptr::null_mut();
    v_res_5160_ = l_Lean_Parser_mkAntiquot_formatter___lam__2(
        v___x_5154_,
        v___y_5155_,
        v___y_5156_,
        v___y_5157_,
        v___y_5158_,
    );
    lean_dec(v___y_5158_);
    lean_dec_ref(v___y_5157_);
    lean_dec(v___y_5156_);
    lean_dec_ref(v___y_5155_);
    return v_res_5160_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_formatter___lam__3(
    mut v___f_5161_: *mut LeanObject,
    mut v___x_5162_: *mut LeanObject,
    mut v___y_5163_: *mut LeanObject,
    mut v___y_5164_: *mut LeanObject,
    mut v___y_5165_: *mut LeanObject,
    mut v___y_5166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    v___x_5168_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(
        v___f_5161_,
        v___x_5162_,
        v___y_5163_,
        v___y_5164_,
        v___y_5165_,
        v___y_5166_,
    );
    return v___x_5168_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_formatter___lam__3___boxed(
    mut v___f_5169_: *mut LeanObject,
    mut v___x_5170_: *mut LeanObject,
    mut v___y_5171_: *mut LeanObject,
    mut v___y_5172_: *mut LeanObject,
    mut v___y_5173_: *mut LeanObject,
    mut v___y_5174_: *mut LeanObject,
    mut v___y_5175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5176_: *mut LeanObject = core::ptr::null_mut();
    v_res_5176_ = l_Lean_Parser_mkAntiquot_formatter___lam__3(
        v___f_5169_,
        v___x_5170_,
        v___y_5171_,
        v___y_5172_,
        v___y_5173_,
        v___y_5174_,
    );
    lean_dec(v___y_5174_);
    lean_dec_ref(v___y_5173_);
    lean_dec(v___y_5172_);
    lean_dec_ref(v___y_5171_);
    return v_res_5176_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_formatter(
    mut v_name_5195_: *mut LeanObject,
    mut v_kind_5196_: *mut LeanObject,
    mut v_anonymous_5197_: u8,
    mut v_isPseudoKind_5198_: u8,
    mut v_a_5199_: *mut LeanObject,
    mut v_a_5200_: *mut LeanObject,
    mut v_a_5201_: *mut LeanObject,
    mut v_a_5202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5204_ = l_Lean_Parser_mkAntiquot_formatter___closed__0;
                v___f_5205_ = l_Lean_Parser_mkAntiquot_formatter___closed__1;
                v___x_5206_ = lean_box((v_anonymous_5197_) as usize);
                v___y_5207_ = lean_alloc_closure(
                    l_Lean_Parser_mkAntiquot_formatter___lam__1___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___y_5207_, 0, v___x_5206_);
                lean_closure_set(v___y_5207_, 1, v_name_5195_);
                lean_closure_set(v___y_5207_, 2, v___f_5204_);
                lean_closure_set(v___y_5207_, 3, v___f_5205_);
                if v_isPseudoKind_5198_ == 0 {
                    v___x_5221_ = lean_box(0);
                    v___y_5209_ = v___x_5221_;
                    state = 1;
                    continue;
                } else {
                    v___x_5222_ = l_Lean_Parser_mkAntiquot_formatter___closed__10;
                    v___y_5209_ = v___x_5222_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v___y_5209_);
                v___x_5210_ = l_Lean_Name_append(v_kind_5196_, v___y_5209_);
                v___x_5211_ = l_Lean_Parser_mkAntiquot_formatter___closed__3;
                v_kind_5212_ = l_Lean_Name_append(v___x_5210_, v___x_5211_);
                v___f_5213_ = l_Lean_Parser_mkAntiquot_formatter___closed__5;
                v___x_5214_ = l_Lean_Parser_mkAntiquot_formatter___closed__8;
                v___x_5215_ = lean_alloc_closure(
                    l_Lean_Parser_antiquotExpr_formatter___boxed as *mut core::ffi::c_void,
                    5,
                    0,
                );
                v___x_5216_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___x_5216_, 0, v___x_5215_);
                lean_closure_set(v___x_5216_, 1, v___y_5207_);
                v___x_5217_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___x_5217_, 0, v___f_5204_);
                lean_closure_set(v___x_5217_, 1, v___x_5216_);
                v___x_5218_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___x_5218_, 0, v___x_5214_);
                lean_closure_set(v___x_5218_, 1, v___x_5217_);
                v___f_5219_ = lean_alloc_closure(
                    l_Lean_Parser_mkAntiquot_formatter___lam__3___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_5219_, 0, v___f_5213_);
                lean_closure_set(v___f_5219_, 1, v___x_5218_);
                v___x_5220_ = l_Lean_Parser_leadingNode_formatter___redArg(
                    v_kind_5212_,
                    v___f_5219_,
                    v_a_5199_,
                    v_a_5200_,
                    v_a_5201_,
                    v_a_5202_,
                );
                return v___x_5220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_mkAntiquot_formatter___boxed(
    mut v_name_5223_: *mut LeanObject,
    mut v_kind_5224_: *mut LeanObject,
    mut v_anonymous_5225_: *mut LeanObject,
    mut v_isPseudoKind_5226_: *mut LeanObject,
    mut v_a_5227_: *mut LeanObject,
    mut v_a_5228_: *mut LeanObject,
    mut v_a_5229_: *mut LeanObject,
    mut v_a_5230_: *mut LeanObject,
    mut v_a_5231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_anonymous_boxed_5232_: u8 = 0;
    let mut v_isPseudoKind_boxed_5233_: u8 = 0;
    let mut v_res_5234_: *mut LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_5232_ = (lean_unbox(v_anonymous_5225_) as u8);
    v_isPseudoKind_boxed_5233_ = (lean_unbox(v_isPseudoKind_5226_) as u8);
    v_res_5234_ = l_Lean_Parser_mkAntiquot_formatter(
        v_name_5223_,
        v_kind_5224_,
        v_anonymous_boxed_5232_,
        v_isPseudoKind_boxed_5233_,
        v_a_5227_,
        v_a_5228_,
        v_a_5229_,
        v_a_5230_,
    );
    lean_dec(v_a_5230_);
    lean_dec_ref(v_a_5229_);
    lean_dec(v_a_5228_);
    lean_dec_ref(v_a_5227_);
    return v_res_5234_;
}
pub unsafe fn l_Lean_Parser_setExpected_parenthesizer___redArg(
    mut v_p_5235_: *mut LeanObject,
    mut v_a_5236_: *mut LeanObject,
    mut v_a_5237_: *mut LeanObject,
    mut v_a_5238_: *mut LeanObject,
    mut v_a_5239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_5239_);
    lean_inc_ref(v_a_5238_);
    lean_inc(v_a_5237_);
    lean_inc_ref(v_a_5236_);
    v___x_5241_ = lean_apply_5(
        v_p_5235_,
        v_a_5236_,
        v_a_5237_,
        v_a_5238_,
        v_a_5239_,
        lean_box(0),
    );
    return v___x_5241_;
}
pub unsafe fn l_Lean_Parser_setExpected_parenthesizer___redArg___boxed(
    mut v_p_5242_: *mut LeanObject,
    mut v_a_5243_: *mut LeanObject,
    mut v_a_5244_: *mut LeanObject,
    mut v_a_5245_: *mut LeanObject,
    mut v_a_5246_: *mut LeanObject,
    mut v_a_5247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5248_: *mut LeanObject = core::ptr::null_mut();
    v_res_5248_ = l_Lean_Parser_setExpected_parenthesizer___redArg(
        v_p_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_,
    );
    lean_dec(v_a_5246_);
    lean_dec_ref(v_a_5245_);
    lean_dec(v_a_5244_);
    lean_dec_ref(v_a_5243_);
    return v_res_5248_;
}
pub unsafe fn l_Lean_Parser_setExpected_parenthesizer(
    mut v_expected_5249_: *mut LeanObject,
    mut v_p_5250_: *mut LeanObject,
    mut v_a_5251_: *mut LeanObject,
    mut v_a_5252_: *mut LeanObject,
    mut v_a_5253_: *mut LeanObject,
    mut v_a_5254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_5254_);
    lean_inc_ref(v_a_5253_);
    lean_inc(v_a_5252_);
    lean_inc_ref(v_a_5251_);
    v___x_5256_ = lean_apply_5(
        v_p_5250_,
        v_a_5251_,
        v_a_5252_,
        v_a_5253_,
        v_a_5254_,
        lean_box(0),
    );
    return v___x_5256_;
}
pub unsafe fn l_Lean_Parser_setExpected_parenthesizer___boxed(
    mut v_expected_5257_: *mut LeanObject,
    mut v_p_5258_: *mut LeanObject,
    mut v_a_5259_: *mut LeanObject,
    mut v_a_5260_: *mut LeanObject,
    mut v_a_5261_: *mut LeanObject,
    mut v_a_5262_: *mut LeanObject,
    mut v_a_5263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5264_: *mut LeanObject = core::ptr::null_mut();
    v_res_5264_ = l_Lean_Parser_setExpected_parenthesizer(
        v_expected_5257_,
        v_p_5258_,
        v_a_5259_,
        v_a_5260_,
        v_a_5261_,
        v_a_5262_,
    );
    lean_dec(v_a_5262_);
    lean_dec_ref(v_a_5261_);
    lean_dec(v_a_5260_);
    lean_dec_ref(v_a_5259_);
    lean_dec(v_expected_5257_);
    return v_res_5264_;
}
pub unsafe fn l_Lean_Parser_symbol_parenthesizer(
    mut v_sym_5265_: *mut LeanObject,
    mut v_a_5266_: *mut LeanObject,
    mut v_a_5267_: *mut LeanObject,
    mut v_a_5268_: *mut LeanObject,
    mut v_a_5269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    v___x_5271_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5271_, 0, v_sym_5265_);
    v___x_5272_ = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(
        v___x_5271_,
        v_a_5266_,
        v_a_5267_,
        v_a_5268_,
        v_a_5269_,
    );
    return v___x_5272_;
}
pub unsafe fn l_Lean_Parser_symbol_parenthesizer___boxed(
    mut v_sym_5273_: *mut LeanObject,
    mut v_a_5274_: *mut LeanObject,
    mut v_a_5275_: *mut LeanObject,
    mut v_a_5276_: *mut LeanObject,
    mut v_a_5277_: *mut LeanObject,
    mut v_a_5278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5279_: *mut LeanObject = core::ptr::null_mut();
    v_res_5279_ =
        l_Lean_Parser_symbol_parenthesizer(v_sym_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_);
    lean_dec(v_a_5277_);
    lean_dec_ref(v_a_5276_);
    lean_dec(v_a_5275_);
    lean_dec_ref(v_a_5274_);
    return v_res_5279_;
}
pub unsafe fn l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg(
    mut v_p_5280_: *mut LeanObject,
    mut v_a_5281_: *mut LeanObject,
    mut v_a_5282_: *mut LeanObject,
    mut v_a_5283_: *mut LeanObject,
    mut v_a_5284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_5284_);
    lean_inc_ref(v_a_5283_);
    lean_inc(v_a_5282_);
    lean_inc_ref(v_a_5281_);
    v___x_5286_ = lean_apply_5(
        v_p_5280_,
        v_a_5281_,
        v_a_5282_,
        v_a_5283_,
        v_a_5284_,
        lean_box(0),
    );
    return v___x_5286_;
}
pub unsafe fn l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg___boxed(
    mut v_p_5287_: *mut LeanObject,
    mut v_a_5288_: *mut LeanObject,
    mut v_a_5289_: *mut LeanObject,
    mut v_a_5290_: *mut LeanObject,
    mut v_a_5291_: *mut LeanObject,
    mut v_a_5292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5293_: *mut LeanObject = core::ptr::null_mut();
    v_res_5293_ = l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg(
        v_p_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_,
    );
    lean_dec(v_a_5291_);
    lean_dec_ref(v_a_5290_);
    lean_dec(v_a_5289_);
    lean_dec_ref(v_a_5288_);
    return v_res_5293_;
}
pub unsafe fn l_Lean_Parser_adaptCacheableContext_parenthesizer(
    mut v_f_5294_: *mut LeanObject,
    mut v_p_5295_: *mut LeanObject,
    mut v_a_5296_: *mut LeanObject,
    mut v_a_5297_: *mut LeanObject,
    mut v_a_5298_: *mut LeanObject,
    mut v_a_5299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_5299_);
    lean_inc_ref(v_a_5298_);
    lean_inc(v_a_5297_);
    lean_inc_ref(v_a_5296_);
    v___x_5301_ = lean_apply_5(
        v_p_5295_,
        v_a_5296_,
        v_a_5297_,
        v_a_5298_,
        v_a_5299_,
        lean_box(0),
    );
    return v___x_5301_;
}
pub unsafe fn l_Lean_Parser_adaptCacheableContext_parenthesizer___boxed(
    mut v_f_5302_: *mut LeanObject,
    mut v_p_5303_: *mut LeanObject,
    mut v_a_5304_: *mut LeanObject,
    mut v_a_5305_: *mut LeanObject,
    mut v_a_5306_: *mut LeanObject,
    mut v_a_5307_: *mut LeanObject,
    mut v_a_5308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5309_: *mut LeanObject = core::ptr::null_mut();
    v_res_5309_ = l_Lean_Parser_adaptCacheableContext_parenthesizer(
        v_f_5302_, v_p_5303_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_,
    );
    lean_dec(v_a_5307_);
    lean_dec_ref(v_a_5306_);
    lean_dec(v_a_5305_);
    lean_dec_ref(v_a_5304_);
    lean_dec_ref(v_f_5302_);
    return v_res_5309_;
}
pub unsafe fn l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg(
    mut v_p_5310_: *mut LeanObject,
    mut v_a_5311_: *mut LeanObject,
    mut v_a_5312_: *mut LeanObject,
    mut v_a_5313_: *mut LeanObject,
    mut v_a_5314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_5314_);
    lean_inc_ref(v_a_5313_);
    lean_inc(v_a_5312_);
    lean_inc_ref(v_a_5311_);
    v___x_5316_ = lean_apply_5(
        v_p_5310_,
        v_a_5311_,
        v_a_5312_,
        v_a_5313_,
        v_a_5314_,
        lean_box(0),
    );
    return v___x_5316_;
}
pub unsafe fn l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg___boxed(
    mut v_p_5317_: *mut LeanObject,
    mut v_a_5318_: *mut LeanObject,
    mut v_a_5319_: *mut LeanObject,
    mut v_a_5320_: *mut LeanObject,
    mut v_a_5321_: *mut LeanObject,
    mut v_a_5322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5323_: *mut LeanObject = core::ptr::null_mut();
    v_res_5323_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg(
        v_p_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_,
    );
    lean_dec(v_a_5321_);
    lean_dec_ref(v_a_5320_);
    lean_dec(v_a_5319_);
    lean_dec_ref(v_a_5318_);
    return v_res_5323_;
}
pub unsafe fn l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(
    mut v_i_5324_: *mut LeanObject,
    mut v_p_5325_: *mut LeanObject,
    mut v_a_5326_: *mut LeanObject,
    mut v_a_5327_: *mut LeanObject,
    mut v_a_5328_: *mut LeanObject,
    mut v_a_5329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_5329_);
    lean_inc_ref(v_a_5328_);
    lean_inc(v_a_5327_);
    lean_inc_ref(v_a_5326_);
    v___x_5331_ = lean_apply_5(
        v_p_5325_,
        v_a_5326_,
        v_a_5327_,
        v_a_5328_,
        v_a_5329_,
        lean_box(0),
    );
    return v___x_5331_;
}
pub unsafe fn l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___boxed(
    mut v_i_5332_: *mut LeanObject,
    mut v_p_5333_: *mut LeanObject,
    mut v_a_5334_: *mut LeanObject,
    mut v_a_5335_: *mut LeanObject,
    mut v_a_5336_: *mut LeanObject,
    mut v_a_5337_: *mut LeanObject,
    mut v_a_5338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5339_: *mut LeanObject = core::ptr::null_mut();
    v_res_5339_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(
        v_i_5332_, v_p_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_,
    );
    lean_dec(v_a_5337_);
    lean_dec_ref(v_a_5336_);
    lean_dec(v_a_5335_);
    lean_dec_ref(v_a_5334_);
    lean_dec(v_i_5332_);
    return v_res_5339_;
}
pub unsafe fn l_Lean_Parser_decQuotDepth_parenthesizer(
    mut v_p_5340_: *mut LeanObject,
    mut v_a_5341_: *mut LeanObject,
    mut v_a_5342_: *mut LeanObject,
    mut v_a_5343_: *mut LeanObject,
    mut v_a_5344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_5344_);
    lean_inc_ref(v_a_5343_);
    lean_inc(v_a_5342_);
    lean_inc_ref(v_a_5341_);
    v___x_5346_ = lean_apply_5(
        v_p_5340_,
        v_a_5341_,
        v_a_5342_,
        v_a_5343_,
        v_a_5344_,
        lean_box(0),
    );
    return v___x_5346_;
}
pub unsafe fn l_Lean_Parser_decQuotDepth_parenthesizer___boxed(
    mut v_p_5347_: *mut LeanObject,
    mut v_a_5348_: *mut LeanObject,
    mut v_a_5349_: *mut LeanObject,
    mut v_a_5350_: *mut LeanObject,
    mut v_a_5351_: *mut LeanObject,
    mut v_a_5352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5353_: *mut LeanObject = core::ptr::null_mut();
    v_res_5353_ = l_Lean_Parser_decQuotDepth_parenthesizer(
        v_p_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_,
    );
    lean_dec(v_a_5351_);
    lean_dec_ref(v_a_5350_);
    lean_dec(v_a_5349_);
    lean_dec_ref(v_a_5348_);
    return v_res_5353_;
}
pub unsafe fn l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0(
    mut v___x_5354_: *mut LeanObject,
    mut v___y_5355_: *mut LeanObject,
    mut v___y_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    v___x_5360_ = l_Lean_Parser_termParser_parenthesizer(
        v___x_5354_,
        v___y_5355_,
        v___y_5356_,
        v___y_5357_,
        v___y_5358_,
    );
    return v___x_5360_;
}
pub unsafe fn l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0___boxed(
    mut v___x_5361_: *mut LeanObject,
    mut v___y_5362_: *mut LeanObject,
    mut v___y_5363_: *mut LeanObject,
    mut v___y_5364_: *mut LeanObject,
    mut v___y_5365_: *mut LeanObject,
    mut v___y_5366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5367_: *mut LeanObject = core::ptr::null_mut();
    v_res_5367_ = l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0(
        v___x_5361_,
        v___y_5362_,
        v___y_5363_,
        v___y_5364_,
        v___y_5365_,
    );
    lean_dec(v___y_5365_);
    lean_dec_ref(v___y_5364_);
    lean_dec(v___y_5363_);
    lean_dec_ref(v___y_5362_);
    return v_res_5367_;
}
pub unsafe fn l_Lean_Parser_antiquotNestedExpr_parenthesizer(
    mut v_a_5380_: *mut LeanObject,
    mut v_a_5381_: *mut LeanObject,
    mut v_a_5382_: *mut LeanObject,
    mut v_a_5383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    v___x_5385_ = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
    v___x_5386_ = l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4;
    v___x_5387_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(
        v___x_5385_,
        v___x_5386_,
        v_a_5380_,
        v_a_5381_,
        v_a_5382_,
        v_a_5383_,
    );
    return v___x_5387_;
}
pub unsafe fn l_Lean_Parser_antiquotNestedExpr_parenthesizer___boxed(
    mut v_a_5388_: *mut LeanObject,
    mut v_a_5389_: *mut LeanObject,
    mut v_a_5390_: *mut LeanObject,
    mut v_a_5391_: *mut LeanObject,
    mut v_a_5392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5393_: *mut LeanObject = core::ptr::null_mut();
    v_res_5393_ =
        l_Lean_Parser_antiquotNestedExpr_parenthesizer(v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_);
    lean_dec(v_a_5391_);
    lean_dec_ref(v_a_5390_);
    lean_dec(v_a_5389_);
    lean_dec_ref(v_a_5388_);
    return v_res_5393_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35()
-> *mut LeanObject {
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    v___x_5401_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_5402_ = l_Lean_Parser_antiquotNestedExpr_formatter___closed__2;
    v___x_5403_ = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1;
    v___x_5404_ = lean_alloc_closure(
        l_Lean_Parser_antiquotNestedExpr_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5405_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5401_,
        v___x_5402_,
        v___x_5403_,
        v___x_5404_,
    );
    return v___x_5405_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___boxed(
    mut v_a_5406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5407_: *mut LeanObject = core::ptr::null_mut();
    v_res_5407_ = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35();
    return v_res_5407_;
}
pub unsafe fn _init_l_Lean_Parser_antiquotExpr_parenthesizer___closed__1() -> *mut LeanObject {
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    v___x_5410_ = lean_alloc_closure(
        l_Lean_Parser_antiquotNestedExpr_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5411_ = l_Lean_Parser_antiquotExpr_parenthesizer___closed__0;
    v___x_5412_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5412_, 0, v___x_5411_);
    lean_closure_set(v___x_5412_, 1, v___x_5410_);
    return v___x_5412_;
}
pub unsafe fn l_Lean_Parser_antiquotExpr_parenthesizer(
    mut v_a_5413_: *mut LeanObject,
    mut v_a_5414_: *mut LeanObject,
    mut v_a_5415_: *mut LeanObject,
    mut v_a_5416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    v___x_5418_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5419_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_antiquotExpr_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_antiquotExpr_parenthesizer___closed__1_once),
        _init_l_Lean_Parser_antiquotExpr_parenthesizer___closed__1,
    );
    v___x_5420_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(
        v___x_5418_,
        v___x_5419_,
        v_a_5413_,
        v_a_5414_,
        v_a_5415_,
        v_a_5416_,
    );
    return v___x_5420_;
}
pub unsafe fn l_Lean_Parser_antiquotExpr_parenthesizer___boxed(
    mut v_a_5421_: *mut LeanObject,
    mut v_a_5422_: *mut LeanObject,
    mut v_a_5423_: *mut LeanObject,
    mut v_a_5424_: *mut LeanObject,
    mut v_a_5425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5426_: *mut LeanObject = core::ptr::null_mut();
    v_res_5426_ =
        l_Lean_Parser_antiquotExpr_parenthesizer(v_a_5421_, v_a_5422_, v_a_5423_, v_a_5424_);
    lean_dec(v_a_5424_);
    lean_dec_ref(v_a_5423_);
    lean_dec(v_a_5422_);
    lean_dec_ref(v_a_5421_);
    return v_res_5426_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0(
    mut v_sym_5427_: *mut LeanObject,
    mut v___y_5428_: *mut LeanObject,
    mut v___y_5429_: *mut LeanObject,
    mut v___y_5430_: *mut LeanObject,
    mut v___y_5431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    v___x_5433_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(
        v_sym_5427_,
        v___y_5429_,
        v___y_5430_,
        v___y_5431_,
    );
    return v___x_5433_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0___boxed(
    mut v_sym_5434_: *mut LeanObject,
    mut v___y_5435_: *mut LeanObject,
    mut v___y_5436_: *mut LeanObject,
    mut v___y_5437_: *mut LeanObject,
    mut v___y_5438_: *mut LeanObject,
    mut v___y_5439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5440_: *mut LeanObject = core::ptr::null_mut();
    v_res_5440_ = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0(
        v_sym_5434_,
        v___y_5435_,
        v___y_5436_,
        v___y_5437_,
        v___y_5438_,
    );
    lean_dec(v___y_5438_);
    lean_dec_ref(v___y_5437_);
    lean_dec(v___y_5436_);
    lean_dec_ref(v___y_5435_);
    return v_res_5440_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(
    mut v_sym_5441_: *mut LeanObject,
    mut v_a_5442_: *mut LeanObject,
    mut v_a_5443_: *mut LeanObject,
    mut v_a_5444_: *mut LeanObject,
    mut v_a_5445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    v___f_5447_ = lean_alloc_closure(
        l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_5447_, 0, v_sym_5441_);
    v___x_5448_ = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(
        v___f_5447_,
        v_a_5442_,
        v_a_5443_,
        v_a_5444_,
        v_a_5445_,
    );
    return v___x_5448_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___boxed(
    mut v_sym_5449_: *mut LeanObject,
    mut v_a_5450_: *mut LeanObject,
    mut v_a_5451_: *mut LeanObject,
    mut v_a_5452_: *mut LeanObject,
    mut v_a_5453_: *mut LeanObject,
    mut v_a_5454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5455_: *mut LeanObject = core::ptr::null_mut();
    v_res_5455_ = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(
        v_sym_5449_,
        v_a_5450_,
        v_a_5451_,
        v_a_5452_,
        v_a_5453_,
    );
    lean_dec(v_a_5453_);
    lean_dec_ref(v_a_5452_);
    lean_dec(v_a_5451_);
    lean_dec_ref(v_a_5450_);
    return v_res_5455_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_parenthesizer(
    mut v_sym_5456_: *mut LeanObject,
    mut v_includeIdent_5457_: u8,
    mut v_a_5458_: *mut LeanObject,
    mut v_a_5459_: *mut LeanObject,
    mut v_a_5460_: *mut LeanObject,
    mut v_a_5461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    v___x_5463_ = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(
        v_sym_5456_,
        v_a_5458_,
        v_a_5459_,
        v_a_5460_,
        v_a_5461_,
    );
    return v___x_5463_;
}
pub unsafe fn l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(
    mut v_sym_5464_: *mut LeanObject,
    mut v_includeIdent_5465_: *mut LeanObject,
    mut v_a_5466_: *mut LeanObject,
    mut v_a_5467_: *mut LeanObject,
    mut v_a_5468_: *mut LeanObject,
    mut v_a_5469_: *mut LeanObject,
    mut v_a_5470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_includeIdent_boxed_5471_: u8 = 0;
    let mut v_res_5472_: *mut LeanObject = core::ptr::null_mut();
    v_includeIdent_boxed_5471_ = (lean_unbox(v_includeIdent_5465_) as u8);
    v_res_5472_ = l_Lean_Parser_nonReservedSymbol_parenthesizer(
        v_sym_5464_,
        v_includeIdent_boxed_5471_,
        v_a_5466_,
        v_a_5467_,
        v_a_5468_,
        v_a_5469_,
    );
    lean_dec(v_a_5469_);
    lean_dec_ref(v_a_5468_);
    lean_dec(v_a_5467_);
    lean_dec_ref(v_a_5466_);
    return v_res_5472_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(
    mut v___x_5473_: *mut LeanObject,
    mut v___y_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    v___x_5479_ = l_Lean_Parser_symbol_parenthesizer(
        v___x_5473_,
        v___y_5474_,
        v___y_5475_,
        v___y_5476_,
        v___y_5477_,
    );
    return v___x_5479_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed(
    mut v___x_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
    mut v___y_5485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5486_: *mut LeanObject = core::ptr::null_mut();
    v_res_5486_ = l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(
        v___x_5480_,
        v___y_5481_,
        v___y_5482_,
        v___y_5483_,
        v___y_5484_,
    );
    lean_dec(v___y_5484_);
    lean_dec_ref(v___y_5483_);
    lean_dec(v___y_5482_);
    lean_dec_ref(v___y_5481_);
    return v_res_5486_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_parenthesizer___lam__1(
    mut v_anonymous_5489_: u8,
    mut v_name_5490_: *mut LeanObject,
    mut v___x_5491_: *mut LeanObject,
    mut v___f_5492_: *mut LeanObject,
    mut v___y_5493_: *mut LeanObject,
    mut v___y_5494_: *mut LeanObject,
    mut v___y_5495_: *mut LeanObject,
    mut v___y_5496_: *mut LeanObject,
) -> *mut LeanObject {
    if v_anonymous_5489_ == 0 {
        let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_5492_);
        v___x_5498_ = l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1;
        v___x_5499_ = l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0;
        v___x_5500_ = lean_box((v_anonymous_5489_) as usize);
        v___x_5501_ = lean_alloc_closure(
            l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5501_, 0, v_name_5490_);
        lean_closure_set(v___x_5501_, 1, v___x_5500_);
        v___x_5502_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
                as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5502_, 0, v___x_5499_);
        lean_closure_set(v___x_5502_, 1, v___x_5501_);
        v___x_5503_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
                as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5503_, 0, v___x_5491_);
        lean_closure_set(v___x_5503_, 1, v___x_5502_);
        v___x_5504_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(
            v___x_5498_,
            v___x_5503_,
            v___y_5493_,
            v___y_5494_,
            v___y_5495_,
            v___y_5496_,
        );
        return v___x_5504_;
    } else {
        let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5507_: u8 = 0;
        let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
        v___x_5505_ = l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1;
        v___x_5506_ = l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0;
        v___x_5507_ = 0;
        v___x_5508_ = lean_box((v___x_5507_) as usize);
        v___x_5509_ = lean_alloc_closure(
            l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5509_, 0, v_name_5490_);
        lean_closure_set(v___x_5509_, 1, v___x_5508_);
        v___x_5510_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
                as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5510_, 0, v___x_5506_);
        lean_closure_set(v___x_5510_, 1, v___x_5509_);
        v___x_5511_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
                as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5511_, 0, v___x_5491_);
        lean_closure_set(v___x_5511_, 1, v___x_5510_);
        v___x_5512_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5512_, 0, v___x_5505_);
        lean_closure_set(v___x_5512_, 1, v___x_5511_);
        v___x_5513_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed
                as *mut core::ffi::c_void,
            5,
            0,
        );
        v___x_5514_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
                as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_5514_, 0, v___x_5513_);
        lean_closure_set(v___x_5514_, 1, v___f_5492_);
        v___x_5515_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(
            v___x_5512_,
            v___x_5514_,
            v___y_5493_,
            v___y_5494_,
            v___y_5495_,
            v___y_5496_,
        );
        return v___x_5515_;
    }
}
pub unsafe fn l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___boxed(
    mut v_anonymous_5516_: *mut LeanObject,
    mut v_name_5517_: *mut LeanObject,
    mut v___x_5518_: *mut LeanObject,
    mut v___f_5519_: *mut LeanObject,
    mut v___y_5520_: *mut LeanObject,
    mut v___y_5521_: *mut LeanObject,
    mut v___y_5522_: *mut LeanObject,
    mut v___y_5523_: *mut LeanObject,
    mut v___y_5524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_anonymous_boxed_5525_: u8 = 0;
    let mut v_res_5526_: *mut LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_5525_ = (lean_unbox(v_anonymous_5516_) as u8);
    v_res_5526_ = l_Lean_Parser_mkAntiquot_parenthesizer___lam__1(
        v_anonymous_boxed_5525_,
        v_name_5517_,
        v___x_5518_,
        v___f_5519_,
        v___y_5520_,
        v___y_5521_,
        v___y_5522_,
        v___y_5523_,
    );
    lean_dec(v___y_5523_);
    lean_dec_ref(v___y_5522_);
    lean_dec(v___y_5521_);
    lean_dec_ref(v___y_5520_);
    return v_res_5526_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(
    mut v___f_5527_: *mut LeanObject,
    mut v___x_5528_: *mut LeanObject,
    mut v___y_5529_: *mut LeanObject,
    mut v___y_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
    mut v___y_5532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    v___x_5534_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(
        v___f_5527_,
        v___x_5528_,
        v___y_5529_,
        v___y_5530_,
        v___y_5531_,
        v___y_5532_,
    );
    return v___x_5534_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed(
    mut v___f_5535_: *mut LeanObject,
    mut v___x_5536_: *mut LeanObject,
    mut v___y_5537_: *mut LeanObject,
    mut v___y_5538_: *mut LeanObject,
    mut v___y_5539_: *mut LeanObject,
    mut v___y_5540_: *mut LeanObject,
    mut v___y_5541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5542_: *mut LeanObject = core::ptr::null_mut();
    v_res_5542_ = l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(
        v___f_5535_,
        v___x_5536_,
        v___y_5537_,
        v___y_5538_,
        v___y_5539_,
        v___y_5540_,
    );
    lean_dec(v___y_5540_);
    lean_dec_ref(v___y_5539_);
    lean_dec(v___y_5538_);
    lean_dec_ref(v___y_5537_);
    return v_res_5542_;
}
pub unsafe fn _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__3() -> *mut LeanObject {
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    v___x_5548_ = l_Lean_Parser_mkAntiquot_parenthesizer___closed__2;
    v___x_5549_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5550_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5550_, 0, v___x_5549_);
    lean_closure_set(v___x_5550_, 1, v___x_5548_);
    return v___x_5550_;
}
pub unsafe fn _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__4() -> *mut LeanObject {
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    v___x_5551_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_mkAntiquot_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_mkAntiquot_parenthesizer___closed__3_once),
        _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__3,
    );
    v___x_5552_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5552_, 0, v___x_5551_);
    return v___x_5552_;
}
pub unsafe fn l_Lean_Parser_mkAntiquot_parenthesizer(
    mut v_name_5553_: *mut LeanObject,
    mut v_kind_5554_: *mut LeanObject,
    mut v_anonymous_5555_: u8,
    mut v_isPseudoKind_5556_: u8,
    mut v_a_5557_: *mut LeanObject,
    mut v_a_5558_: *mut LeanObject,
    mut v_a_5559_: *mut LeanObject,
    mut v_a_5560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5562_ = l_Lean_Parser_mkAntiquot_parenthesizer___closed__0;
                if v_isPseudoKind_5556_ == 0 {
                    v___x_5580_ = lean_box(0);
                    v___y_5564_ = v___x_5580_;
                    state = 1;
                    continue;
                } else {
                    v___x_5581_ = l_Lean_Parser_mkAntiquot_formatter___closed__10;
                    v___y_5564_ = v___x_5581_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v___y_5564_);
                v___x_5565_ = l_Lean_Name_append(v_kind_5554_, v___y_5564_);
                v___x_5566_ = l_Lean_Parser_mkAntiquot_formatter___closed__3;
                v_kind_5567_ = l_Lean_Name_append(v___x_5565_, v___x_5566_);
                v___x_5568_ = lean_unsigned_to_nat(1024);
                v___f_5569_ = l_Lean_Parser_mkAntiquot_parenthesizer___closed__1;
                v___x_5570_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    5,
                    0,
                );
                v___x_5571_ = lean_box((v_anonymous_5555_) as usize);
                lean_inc_ref(v___x_5570_);
                v___y_5572_ = lean_alloc_closure(
                    l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___y_5572_, 0, v___x_5571_);
                lean_closure_set(v___y_5572_, 1, v_name_5553_);
                lean_closure_set(v___y_5572_, 2, v___x_5570_);
                lean_closure_set(v___y_5572_, 3, v___f_5562_);
                v___x_5573_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Parser_mkAntiquot_parenthesizer___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_Parser_mkAntiquot_parenthesizer___closed__4_once
                    ),
                    _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__4,
                );
                v___x_5574_ = lean_alloc_closure(
                    l_Lean_Parser_antiquotExpr_parenthesizer___boxed as *mut core::ffi::c_void,
                    5,
                    0,
                );
                v___x_5575_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___x_5575_, 0, v___x_5574_);
                lean_closure_set(v___x_5575_, 1, v___y_5572_);
                v___x_5576_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___x_5576_, 0, v___x_5570_);
                lean_closure_set(v___x_5576_, 1, v___x_5575_);
                v___x_5577_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___x_5577_, 0, v___x_5573_);
                lean_closure_set(v___x_5577_, 1, v___x_5576_);
                v___f_5578_ = lean_alloc_closure(
                    l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_5578_, 0, v___f_5569_);
                lean_closure_set(v___f_5578_, 1, v___x_5577_);
                v___x_5579_ = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(
                    v_kind_5567_,
                    v___x_5568_,
                    v___f_5578_,
                    v_a_5557_,
                    v_a_5558_,
                    v_a_5559_,
                    v_a_5560_,
                );
                return v___x_5579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_mkAntiquot_parenthesizer___boxed(
    mut v_name_5582_: *mut LeanObject,
    mut v_kind_5583_: *mut LeanObject,
    mut v_anonymous_5584_: *mut LeanObject,
    mut v_isPseudoKind_5585_: *mut LeanObject,
    mut v_a_5586_: *mut LeanObject,
    mut v_a_5587_: *mut LeanObject,
    mut v_a_5588_: *mut LeanObject,
    mut v_a_5589_: *mut LeanObject,
    mut v_a_5590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_anonymous_boxed_5591_: u8 = 0;
    let mut v_isPseudoKind_boxed_5592_: u8 = 0;
    let mut v_res_5593_: *mut LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_5591_ = (lean_unbox(v_anonymous_5584_) as u8);
    v_isPseudoKind_boxed_5592_ = (lean_unbox(v_isPseudoKind_5585_) as u8);
    v_res_5593_ = l_Lean_Parser_mkAntiquot_parenthesizer(
        v_name_5582_,
        v_kind_5583_,
        v_anonymous_boxed_5591_,
        v_isPseudoKind_boxed_5592_,
        v_a_5586_,
        v_a_5587_,
        v_a_5588_,
        v_a_5589_,
    );
    lean_dec(v_a_5589_);
    lean_dec_ref(v_a_5588_);
    lean_dec(v_a_5587_);
    lean_dec_ref(v_a_5586_);
    return v_res_5593_;
}
pub unsafe fn l_Lean_Parser_nodeWithAntiquot_formatter(
    mut v_name_5594_: *mut LeanObject,
    mut v_kind_5595_: *mut LeanObject,
    mut v_p_5596_: *mut LeanObject,
    mut v_anonymous_5597_: u8,
    mut v_a_5598_: *mut LeanObject,
    mut v_a_5599_: *mut LeanObject,
    mut v_a_5600_: *mut LeanObject,
    mut v_a_5601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5603_: u8 = 0;
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    v___x_5603_ = 0;
    v___x_5604_ = lean_box((v_anonymous_5597_) as usize);
    v___x_5605_ = lean_box((v___x_5603_) as usize);
    lean_inc(v_kind_5595_);
    v___x_5606_ = lean_alloc_closure(
        l_Lean_Parser_mkAntiquot_formatter___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_5606_, 0, v_name_5594_);
    lean_closure_set(v___x_5606_, 1, v_kind_5595_);
    lean_closure_set(v___x_5606_, 2, v___x_5604_);
    lean_closure_set(v___x_5606_, 3, v___x_5605_);
    v___x_5607_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_node_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5607_, 0, v_kind_5595_);
    lean_closure_set(v___x_5607_, 1, v_p_5596_);
    v___x_5608_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_5606_,
        v___x_5607_,
        v_a_5598_,
        v_a_5599_,
        v_a_5600_,
        v_a_5601_,
    );
    return v___x_5608_;
}
pub unsafe fn l_Lean_Parser_nodeWithAntiquot_formatter___boxed(
    mut v_name_5609_: *mut LeanObject,
    mut v_kind_5610_: *mut LeanObject,
    mut v_p_5611_: *mut LeanObject,
    mut v_anonymous_5612_: *mut LeanObject,
    mut v_a_5613_: *mut LeanObject,
    mut v_a_5614_: *mut LeanObject,
    mut v_a_5615_: *mut LeanObject,
    mut v_a_5616_: *mut LeanObject,
    mut v_a_5617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_anonymous_boxed_5618_: u8 = 0;
    let mut v_res_5619_: *mut LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_5618_ = (lean_unbox(v_anonymous_5612_) as u8);
    v_res_5619_ = l_Lean_Parser_nodeWithAntiquot_formatter(
        v_name_5609_,
        v_kind_5610_,
        v_p_5611_,
        v_anonymous_boxed_5618_,
        v_a_5613_,
        v_a_5614_,
        v_a_5615_,
        v_a_5616_,
    );
    lean_dec(v_a_5616_);
    lean_dec_ref(v_a_5615_);
    lean_dec(v_a_5614_);
    lean_dec_ref(v_a_5613_);
    return v_res_5619_;
}
pub unsafe fn l_Lean_Parser_nodeWithAntiquot_parenthesizer(
    mut v_name_5620_: *mut LeanObject,
    mut v_kind_5621_: *mut LeanObject,
    mut v_p_5622_: *mut LeanObject,
    mut v_anonymous_5623_: u8,
    mut v_a_5624_: *mut LeanObject,
    mut v_a_5625_: *mut LeanObject,
    mut v_a_5626_: *mut LeanObject,
    mut v_a_5627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5629_: u8 = 0;
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    v___x_5629_ = 0;
    v___x_5630_ = lean_box((v_anonymous_5623_) as usize);
    v___x_5631_ = lean_box((v___x_5629_) as usize);
    lean_inc(v_kind_5621_);
    v___x_5632_ = lean_alloc_closure(
        l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_5632_, 0, v_name_5620_);
    lean_closure_set(v___x_5632_, 1, v_kind_5621_);
    lean_closure_set(v___x_5632_, 2, v___x_5630_);
    lean_closure_set(v___x_5632_, 3, v___x_5631_);
    v___x_5633_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5633_, 0, v_kind_5621_);
    lean_closure_set(v___x_5633_, 1, v_p_5622_);
    v___x_5634_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_5632_,
        v___x_5633_,
        v_a_5624_,
        v_a_5625_,
        v_a_5626_,
        v_a_5627_,
    );
    return v___x_5634_;
}
pub unsafe fn l_Lean_Parser_nodeWithAntiquot_parenthesizer___boxed(
    mut v_name_5635_: *mut LeanObject,
    mut v_kind_5636_: *mut LeanObject,
    mut v_p_5637_: *mut LeanObject,
    mut v_anonymous_5638_: *mut LeanObject,
    mut v_a_5639_: *mut LeanObject,
    mut v_a_5640_: *mut LeanObject,
    mut v_a_5641_: *mut LeanObject,
    mut v_a_5642_: *mut LeanObject,
    mut v_a_5643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_anonymous_boxed_5644_: u8 = 0;
    let mut v_res_5645_: *mut LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_5644_ = (lean_unbox(v_anonymous_5638_) as u8);
    v_res_5645_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(
        v_name_5635_,
        v_kind_5636_,
        v_p_5637_,
        v_anonymous_boxed_5644_,
        v_a_5639_,
        v_a_5640_,
        v_a_5641_,
        v_a_5642_,
    );
    lean_dec(v_a_5642_);
    lean_dec_ref(v_a_5641_);
    lean_dec(v_a_5640_);
    lean_dec_ref(v_a_5639_);
    return v_res_5645_;
}
pub unsafe fn l_Lean_Parser_mkAntiquotSplice_formatter(
    mut v_kind_5658_: *mut LeanObject,
    mut v_p_5659_: *mut LeanObject,
    mut v_suffix_5660_: *mut LeanObject,
    mut v_a_5661_: *mut LeanObject,
    mut v_a_5662_: *mut LeanObject,
    mut v_a_5663_: *mut LeanObject,
    mut v_a_5664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    v___f_5666_ = l_Lean_Parser_mkAntiquot_formatter___closed__0;
    v___x_5667_ = l_Lean_Parser_mkAntiquotSplice_formatter___closed__1;
    v_kind_5668_ = l_Lean_Name_append(v_kind_5658_, v___x_5667_);
    v___f_5669_ = l_Lean_Parser_mkAntiquot_formatter___closed__5;
    v___x_5670_ = l_Lean_Parser_mkAntiquot_formatter___closed__8;
    v___x_5671_ = l_Lean_Parser_mkAntiquotSplice_formatter___closed__3;
    v___x_5672_ = l_Lean_Parser_mkAntiquotSplice_formatter___closed__5;
    v___x_5673_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_node_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5673_, 0, v___x_5672_);
    lean_closure_set(v___x_5673_, 1, v_p_5659_);
    v___x_5674_ = l_Lean_Parser_mkAntiquotSplice_formatter___closed__7;
    v___x_5675_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5675_, 0, v___x_5674_);
    lean_closure_set(v___x_5675_, 1, v_suffix_5660_);
    v___x_5676_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5676_, 0, v___x_5673_);
    lean_closure_set(v___x_5676_, 1, v___x_5675_);
    v___x_5677_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5677_, 0, v___x_5671_);
    lean_closure_set(v___x_5677_, 1, v___x_5676_);
    v___x_5678_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5678_, 0, v___f_5666_);
    lean_closure_set(v___x_5678_, 1, v___x_5677_);
    v___x_5679_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5679_, 0, v___x_5670_);
    lean_closure_set(v___x_5679_, 1, v___x_5678_);
    v___f_5680_ = lean_alloc_closure(
        l_Lean_Parser_mkAntiquot_formatter___lam__3___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_5680_, 0, v___f_5669_);
    lean_closure_set(v___f_5680_, 1, v___x_5679_);
    v___x_5681_ = l_Lean_Parser_leadingNode_formatter___redArg(
        v_kind_5668_,
        v___f_5680_,
        v_a_5661_,
        v_a_5662_,
        v_a_5663_,
        v_a_5664_,
    );
    return v___x_5681_;
}
pub unsafe fn l_Lean_Parser_mkAntiquotSplice_formatter___boxed(
    mut v_kind_5682_: *mut LeanObject,
    mut v_p_5683_: *mut LeanObject,
    mut v_suffix_5684_: *mut LeanObject,
    mut v_a_5685_: *mut LeanObject,
    mut v_a_5686_: *mut LeanObject,
    mut v_a_5687_: *mut LeanObject,
    mut v_a_5688_: *mut LeanObject,
    mut v_a_5689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5690_: *mut LeanObject = core::ptr::null_mut();
    v_res_5690_ = l_Lean_Parser_mkAntiquotSplice_formatter(
        v_kind_5682_,
        v_p_5683_,
        v_suffix_5684_,
        v_a_5685_,
        v_a_5686_,
        v_a_5687_,
        v_a_5688_,
    );
    lean_dec(v_a_5688_);
    lean_dec_ref(v_a_5687_);
    lean_dec(v_a_5686_);
    lean_dec_ref(v_a_5685_);
    return v_res_5690_;
}
pub unsafe fn l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0(
    mut v_p_5691_: *mut LeanObject,
    mut v___y_5692_: *mut LeanObject,
    mut v___y_5693_: *mut LeanObject,
    mut v___y_5694_: *mut LeanObject,
    mut v___y_5695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    v___x_5697_ = lean_apply_5(
        v_p_5691_,
        v___y_5692_,
        v___y_5693_,
        v___y_5694_,
        v___y_5695_,
        lean_box(0),
    );
    return v___x_5697_;
}
pub unsafe fn l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0___boxed(
    mut v_p_5698_: *mut LeanObject,
    mut v___y_5699_: *mut LeanObject,
    mut v___y_5700_: *mut LeanObject,
    mut v___y_5701_: *mut LeanObject,
    mut v___y_5702_: *mut LeanObject,
    mut v___y_5703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5704_: *mut LeanObject = core::ptr::null_mut();
    v_res_5704_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0(
        v_p_5698_,
        v___y_5699_,
        v___y_5700_,
        v___y_5701_,
        v___y_5702_,
    );
    return v_res_5704_;
}
pub unsafe fn l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(
    mut v_kind_5705_: *mut LeanObject,
    mut v_p_5706_: *mut LeanObject,
    mut v_suffix_5707_: *mut LeanObject,
    mut v_a_5708_: *mut LeanObject,
    mut v_a_5709_: *mut LeanObject,
    mut v_a_5710_: *mut LeanObject,
    mut v_a_5711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_p_5706_);
    v___f_5713_ = lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_5713_, 0, v_p_5706_);
    lean_inc_ref(v_suffix_5707_);
    lean_inc(v_kind_5705_);
    v___x_5714_ = lean_alloc_closure(
        l_Lean_Parser_mkAntiquotSplice_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5714_, 0, v_kind_5705_);
    lean_closure_set(v___x_5714_, 1, v___f_5713_);
    lean_closure_set(v___x_5714_, 2, v_suffix_5707_);
    v___x_5715_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5715_, 0, v_kind_5705_);
    lean_closure_set(v___x_5715_, 1, v_p_5706_);
    lean_closure_set(v___x_5715_, 2, v_suffix_5707_);
    v___x_5716_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_5714_,
        v___x_5715_,
        v_a_5708_,
        v_a_5709_,
        v_a_5710_,
        v_a_5711_,
    );
    return v___x_5716_;
}
pub unsafe fn l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed(
    mut v_kind_5717_: *mut LeanObject,
    mut v_p_5718_: *mut LeanObject,
    mut v_suffix_5719_: *mut LeanObject,
    mut v_a_5720_: *mut LeanObject,
    mut v_a_5721_: *mut LeanObject,
    mut v_a_5722_: *mut LeanObject,
    mut v_a_5723_: *mut LeanObject,
    mut v_a_5724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5725_: *mut LeanObject = core::ptr::null_mut();
    v_res_5725_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(
        v_kind_5717_,
        v_p_5718_,
        v_suffix_5719_,
        v_a_5720_,
        v_a_5721_,
        v_a_5722_,
        v_a_5723_,
    );
    lean_dec(v_a_5723_);
    lean_dec_ref(v_a_5722_);
    lean_dec(v_a_5721_);
    lean_dec_ref(v_a_5720_);
    return v_res_5725_;
}
pub unsafe fn l_Lean_Parser_sepByElemParser_formatter(
    mut v_p_5730_: *mut LeanObject,
    mut v_sep_5731_: *mut LeanObject,
    mut v_a_5732_: *mut LeanObject,
    mut v_a_5733_: *mut LeanObject,
    mut v_a_5734_: *mut LeanObject,
    mut v_a_5735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    v___x_5737_ = lean_unsigned_to_nat(0);
    v___x_5738_ = lean_string_utf8_byte_size(v_sep_5731_);
    v___x_5739_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_5739_, 0, v_sep_5731_);
    lean_ctor_set(v___x_5739_, 1, v___x_5737_);
    lean_ctor_set(v___x_5739_, 2, v___x_5738_);
    v___x_5740_ = l_String_Slice_trimAscii(v___x_5739_);
    v_str_5741_ = lean_ctor_get(v___x_5740_, 0);
    lean_inc_ref(v_str_5741_);
    v_startInclusive_5742_ = lean_ctor_get(v___x_5740_, 1);
    lean_inc(v_startInclusive_5742_);
    v_endExclusive_5743_ = lean_ctor_get(v___x_5740_, 2);
    lean_inc(v_endExclusive_5743_);
    lean_dec_ref(v___x_5740_);
    v___x_5744_ = l_Lean_Parser_sepByElemParser_formatter___closed__1;
    v___x_5745_ =
        lean_string_utf8_extract(v_str_5741_, v_startInclusive_5742_, v_endExclusive_5743_);
    lean_dec(v_endExclusive_5743_);
    lean_dec(v_startInclusive_5742_);
    lean_dec_ref(v_str_5741_);
    v___x_5746_ = l_Lean_Parser_sepByElemParser_formatter___closed__2;
    v___x_5747_ = lean_string_append(v___x_5745_, v___x_5746_);
    v___x_5748_ = lean_alloc_closure(
        l_Lean_Parser_symbol_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5748_, 0, v___x_5747_);
    v___x_5749_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(
        v___x_5744_,
        v_p_5730_,
        v___x_5748_,
        v_a_5732_,
        v_a_5733_,
        v_a_5734_,
        v_a_5735_,
    );
    return v___x_5749_;
}
pub unsafe fn l_Lean_Parser_sepByElemParser_formatter___boxed(
    mut v_p_5750_: *mut LeanObject,
    mut v_sep_5751_: *mut LeanObject,
    mut v_a_5752_: *mut LeanObject,
    mut v_a_5753_: *mut LeanObject,
    mut v_a_5754_: *mut LeanObject,
    mut v_a_5755_: *mut LeanObject,
    mut v_a_5756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5757_: *mut LeanObject = core::ptr::null_mut();
    v_res_5757_ = l_Lean_Parser_sepByElemParser_formatter(
        v_p_5750_,
        v_sep_5751_,
        v_a_5752_,
        v_a_5753_,
        v_a_5754_,
        v_a_5755_,
    );
    lean_dec(v_a_5755_);
    lean_dec_ref(v_a_5754_);
    lean_dec(v_a_5753_);
    lean_dec_ref(v_a_5752_);
    return v_res_5757_;
}
pub unsafe fn l_Lean_Parser_sepBy_formatter___redArg(
    mut v_p_5758_: *mut LeanObject,
    mut v_sep_5759_: *mut LeanObject,
    mut v_psep_5760_: *mut LeanObject,
    mut v_a_5761_: *mut LeanObject,
    mut v_a_5762_: *mut LeanObject,
    mut v_a_5763_: *mut LeanObject,
    mut v_a_5764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    v___x_5766_ = lean_alloc_closure(
        l_Lean_Parser_sepByElemParser_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5766_, 0, v_p_5758_);
    lean_closure_set(v___x_5766_, 1, v_sep_5759_);
    v___x_5767_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(
        v___x_5766_,
        v_psep_5760_,
        v_a_5761_,
        v_a_5762_,
        v_a_5763_,
        v_a_5764_,
    );
    return v___x_5767_;
}
pub unsafe fn l_Lean_Parser_sepBy_formatter___redArg___boxed(
    mut v_p_5768_: *mut LeanObject,
    mut v_sep_5769_: *mut LeanObject,
    mut v_psep_5770_: *mut LeanObject,
    mut v_a_5771_: *mut LeanObject,
    mut v_a_5772_: *mut LeanObject,
    mut v_a_5773_: *mut LeanObject,
    mut v_a_5774_: *mut LeanObject,
    mut v_a_5775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5776_: *mut LeanObject = core::ptr::null_mut();
    v_res_5776_ = l_Lean_Parser_sepBy_formatter___redArg(
        v_p_5768_,
        v_sep_5769_,
        v_psep_5770_,
        v_a_5771_,
        v_a_5772_,
        v_a_5773_,
        v_a_5774_,
    );
    lean_dec(v_a_5774_);
    lean_dec_ref(v_a_5773_);
    lean_dec(v_a_5772_);
    lean_dec_ref(v_a_5771_);
    return v_res_5776_;
}
pub unsafe fn l_Lean_Parser_sepBy_formatter(
    mut v_p_5777_: *mut LeanObject,
    mut v_sep_5778_: *mut LeanObject,
    mut v_psep_5779_: *mut LeanObject,
    mut v_allowTrailingSep_5780_: u8,
    mut v_a_5781_: *mut LeanObject,
    mut v_a_5782_: *mut LeanObject,
    mut v_a_5783_: *mut LeanObject,
    mut v_a_5784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    v___x_5786_ = l_Lean_Parser_sepBy_formatter___redArg(
        v_p_5777_,
        v_sep_5778_,
        v_psep_5779_,
        v_a_5781_,
        v_a_5782_,
        v_a_5783_,
        v_a_5784_,
    );
    return v___x_5786_;
}
pub unsafe fn l_Lean_Parser_sepBy_formatter___boxed(
    mut v_p_5787_: *mut LeanObject,
    mut v_sep_5788_: *mut LeanObject,
    mut v_psep_5789_: *mut LeanObject,
    mut v_allowTrailingSep_5790_: *mut LeanObject,
    mut v_a_5791_: *mut LeanObject,
    mut v_a_5792_: *mut LeanObject,
    mut v_a_5793_: *mut LeanObject,
    mut v_a_5794_: *mut LeanObject,
    mut v_a_5795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowTrailingSep_boxed_5796_: u8 = 0;
    let mut v_res_5797_: *mut LeanObject = core::ptr::null_mut();
    v_allowTrailingSep_boxed_5796_ = (lean_unbox(v_allowTrailingSep_5790_) as u8);
    v_res_5797_ = l_Lean_Parser_sepBy_formatter(
        v_p_5787_,
        v_sep_5788_,
        v_psep_5789_,
        v_allowTrailingSep_boxed_5796_,
        v_a_5791_,
        v_a_5792_,
        v_a_5793_,
        v_a_5794_,
    );
    lean_dec(v_a_5794_);
    lean_dec_ref(v_a_5793_);
    lean_dec(v_a_5792_);
    lean_dec_ref(v_a_5791_);
    return v_res_5797_;
}
pub unsafe fn l_Lean_Parser_mkAntiquotSplice_parenthesizer(
    mut v_kind_5802_: *mut LeanObject,
    mut v_p_5803_: *mut LeanObject,
    mut v_suffix_5804_: *mut LeanObject,
    mut v_a_5805_: *mut LeanObject,
    mut v_a_5806_: *mut LeanObject,
    mut v_a_5807_: *mut LeanObject,
    mut v_a_5808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    v___x_5810_ = l_Lean_Parser_mkAntiquotSplice_formatter___closed__1;
    v_kind_5811_ = l_Lean_Name_append(v_kind_5802_, v___x_5810_);
    v___x_5812_ = lean_unsigned_to_nat(1024);
    v___f_5813_ = l_Lean_Parser_mkAntiquot_parenthesizer___closed__1;
    v___x_5814_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5815_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_mkAntiquot_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_mkAntiquot_parenthesizer___closed__4_once),
        _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__4,
    );
    v___x_5816_ = l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0;
    v___x_5817_ = l_Lean_Parser_mkAntiquotSplice_formatter___closed__5;
    v___x_5818_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5818_, 0, v___x_5817_);
    lean_closure_set(v___x_5818_, 1, v_p_5803_);
    v___x_5819_ = l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1;
    v___x_5820_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5820_, 0, v___x_5819_);
    lean_closure_set(v___x_5820_, 1, v_suffix_5804_);
    v___x_5821_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5821_, 0, v___x_5818_);
    lean_closure_set(v___x_5821_, 1, v___x_5820_);
    v___x_5822_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5822_, 0, v___x_5816_);
    lean_closure_set(v___x_5822_, 1, v___x_5821_);
    v___x_5823_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5823_, 0, v___x_5814_);
    lean_closure_set(v___x_5823_, 1, v___x_5822_);
    v___x_5824_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5824_, 0, v___x_5815_);
    lean_closure_set(v___x_5824_, 1, v___x_5823_);
    v___f_5825_ = lean_alloc_closure(
        l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_5825_, 0, v___f_5813_);
    lean_closure_set(v___f_5825_, 1, v___x_5824_);
    v___x_5826_ = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(
        v_kind_5811_,
        v___x_5812_,
        v___f_5825_,
        v_a_5805_,
        v_a_5806_,
        v_a_5807_,
        v_a_5808_,
    );
    return v___x_5826_;
}
pub unsafe fn l_Lean_Parser_mkAntiquotSplice_parenthesizer___boxed(
    mut v_kind_5827_: *mut LeanObject,
    mut v_p_5828_: *mut LeanObject,
    mut v_suffix_5829_: *mut LeanObject,
    mut v_a_5830_: *mut LeanObject,
    mut v_a_5831_: *mut LeanObject,
    mut v_a_5832_: *mut LeanObject,
    mut v_a_5833_: *mut LeanObject,
    mut v_a_5834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5835_: *mut LeanObject = core::ptr::null_mut();
    v_res_5835_ = l_Lean_Parser_mkAntiquotSplice_parenthesizer(
        v_kind_5827_,
        v_p_5828_,
        v_suffix_5829_,
        v_a_5830_,
        v_a_5831_,
        v_a_5832_,
        v_a_5833_,
    );
    lean_dec(v_a_5833_);
    lean_dec_ref(v_a_5832_);
    lean_dec(v_a_5831_);
    lean_dec_ref(v_a_5830_);
    return v_res_5835_;
}
pub unsafe fn l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0(
    mut v_p_5836_: *mut LeanObject,
    mut v___y_5837_: *mut LeanObject,
    mut v___y_5838_: *mut LeanObject,
    mut v___y_5839_: *mut LeanObject,
    mut v___y_5840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    v___x_5842_ = lean_apply_5(
        v_p_5836_,
        v___y_5837_,
        v___y_5838_,
        v___y_5839_,
        v___y_5840_,
        lean_box(0),
    );
    return v___x_5842_;
}
pub unsafe fn l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0___boxed(
    mut v_p_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
    mut v___y_5845_: *mut LeanObject,
    mut v___y_5846_: *mut LeanObject,
    mut v___y_5847_: *mut LeanObject,
    mut v___y_5848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5849_: *mut LeanObject = core::ptr::null_mut();
    v_res_5849_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0(
        v_p_5843_,
        v___y_5844_,
        v___y_5845_,
        v___y_5846_,
        v___y_5847_,
    );
    return v_res_5849_;
}
pub unsafe fn l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(
    mut v_kind_5850_: *mut LeanObject,
    mut v_p_5851_: *mut LeanObject,
    mut v_suffix_5852_: *mut LeanObject,
    mut v_a_5853_: *mut LeanObject,
    mut v_a_5854_: *mut LeanObject,
    mut v_a_5855_: *mut LeanObject,
    mut v_a_5856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_p_5851_);
    v___f_5858_ = lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_5858_, 0, v_p_5851_);
    lean_inc_ref(v_suffix_5852_);
    lean_inc(v_kind_5850_);
    v___x_5859_ = lean_alloc_closure(
        l_Lean_Parser_mkAntiquotSplice_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5859_, 0, v_kind_5850_);
    lean_closure_set(v___x_5859_, 1, v___f_5858_);
    lean_closure_set(v___x_5859_, 2, v_suffix_5852_);
    v___x_5860_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5860_, 0, v_kind_5850_);
    lean_closure_set(v___x_5860_, 1, v_p_5851_);
    lean_closure_set(v___x_5860_, 2, v_suffix_5852_);
    v___x_5861_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_5859_,
        v___x_5860_,
        v_a_5853_,
        v_a_5854_,
        v_a_5855_,
        v_a_5856_,
    );
    return v___x_5861_;
}
pub unsafe fn l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed(
    mut v_kind_5862_: *mut LeanObject,
    mut v_p_5863_: *mut LeanObject,
    mut v_suffix_5864_: *mut LeanObject,
    mut v_a_5865_: *mut LeanObject,
    mut v_a_5866_: *mut LeanObject,
    mut v_a_5867_: *mut LeanObject,
    mut v_a_5868_: *mut LeanObject,
    mut v_a_5869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5870_: *mut LeanObject = core::ptr::null_mut();
    v_res_5870_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(
        v_kind_5862_,
        v_p_5863_,
        v_suffix_5864_,
        v_a_5865_,
        v_a_5866_,
        v_a_5867_,
        v_a_5868_,
    );
    lean_dec(v_a_5868_);
    lean_dec_ref(v_a_5867_);
    lean_dec(v_a_5866_);
    lean_dec_ref(v_a_5865_);
    return v_res_5870_;
}
pub unsafe fn l_Lean_Parser_sepByElemParser_parenthesizer(
    mut v_p_5871_: *mut LeanObject,
    mut v_sep_5872_: *mut LeanObject,
    mut v_a_5873_: *mut LeanObject,
    mut v_a_5874_: *mut LeanObject,
    mut v_a_5875_: *mut LeanObject,
    mut v_a_5876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    v___x_5878_ = lean_unsigned_to_nat(0);
    v___x_5879_ = lean_string_utf8_byte_size(v_sep_5872_);
    v___x_5880_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_5880_, 0, v_sep_5872_);
    lean_ctor_set(v___x_5880_, 1, v___x_5878_);
    lean_ctor_set(v___x_5880_, 2, v___x_5879_);
    v___x_5881_ = l_String_Slice_trimAscii(v___x_5880_);
    v_str_5882_ = lean_ctor_get(v___x_5881_, 0);
    lean_inc_ref(v_str_5882_);
    v_startInclusive_5883_ = lean_ctor_get(v___x_5881_, 1);
    lean_inc(v_startInclusive_5883_);
    v_endExclusive_5884_ = lean_ctor_get(v___x_5881_, 2);
    lean_inc(v_endExclusive_5884_);
    lean_dec_ref(v___x_5881_);
    v___x_5885_ = l_Lean_Parser_sepByElemParser_formatter___closed__1;
    v___x_5886_ =
        lean_string_utf8_extract(v_str_5882_, v_startInclusive_5883_, v_endExclusive_5884_);
    lean_dec(v_endExclusive_5884_);
    lean_dec(v_startInclusive_5883_);
    lean_dec_ref(v_str_5882_);
    v___x_5887_ = l_Lean_Parser_sepByElemParser_formatter___closed__2;
    v___x_5888_ = lean_string_append(v___x_5886_, v___x_5887_);
    v___x_5889_ = lean_alloc_closure(
        l_Lean_Parser_symbol_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5889_, 0, v___x_5888_);
    v___x_5890_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(
        v___x_5885_,
        v_p_5871_,
        v___x_5889_,
        v_a_5873_,
        v_a_5874_,
        v_a_5875_,
        v_a_5876_,
    );
    return v___x_5890_;
}
pub unsafe fn l_Lean_Parser_sepByElemParser_parenthesizer___boxed(
    mut v_p_5891_: *mut LeanObject,
    mut v_sep_5892_: *mut LeanObject,
    mut v_a_5893_: *mut LeanObject,
    mut v_a_5894_: *mut LeanObject,
    mut v_a_5895_: *mut LeanObject,
    mut v_a_5896_: *mut LeanObject,
    mut v_a_5897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5898_: *mut LeanObject = core::ptr::null_mut();
    v_res_5898_ = l_Lean_Parser_sepByElemParser_parenthesizer(
        v_p_5891_,
        v_sep_5892_,
        v_a_5893_,
        v_a_5894_,
        v_a_5895_,
        v_a_5896_,
    );
    lean_dec(v_a_5896_);
    lean_dec_ref(v_a_5895_);
    lean_dec(v_a_5894_);
    lean_dec_ref(v_a_5893_);
    return v_res_5898_;
}
pub unsafe fn l_Lean_Parser_sepBy_parenthesizer___redArg(
    mut v_p_5899_: *mut LeanObject,
    mut v_sep_5900_: *mut LeanObject,
    mut v_psep_5901_: *mut LeanObject,
    mut v_a_5902_: *mut LeanObject,
    mut v_a_5903_: *mut LeanObject,
    mut v_a_5904_: *mut LeanObject,
    mut v_a_5905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    v___x_5907_ = lean_alloc_closure(
        l_Lean_Parser_sepByElemParser_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5907_, 0, v_p_5899_);
    lean_closure_set(v___x_5907_, 1, v_sep_5900_);
    v___x_5908_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(
        v___x_5907_,
        v_psep_5901_,
        v_a_5902_,
        v_a_5903_,
        v_a_5904_,
        v_a_5905_,
    );
    return v___x_5908_;
}
pub unsafe fn l_Lean_Parser_sepBy_parenthesizer___redArg___boxed(
    mut v_p_5909_: *mut LeanObject,
    mut v_sep_5910_: *mut LeanObject,
    mut v_psep_5911_: *mut LeanObject,
    mut v_a_5912_: *mut LeanObject,
    mut v_a_5913_: *mut LeanObject,
    mut v_a_5914_: *mut LeanObject,
    mut v_a_5915_: *mut LeanObject,
    mut v_a_5916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5917_: *mut LeanObject = core::ptr::null_mut();
    v_res_5917_ = l_Lean_Parser_sepBy_parenthesizer___redArg(
        v_p_5909_,
        v_sep_5910_,
        v_psep_5911_,
        v_a_5912_,
        v_a_5913_,
        v_a_5914_,
        v_a_5915_,
    );
    lean_dec(v_a_5915_);
    lean_dec_ref(v_a_5914_);
    lean_dec(v_a_5913_);
    lean_dec_ref(v_a_5912_);
    return v_res_5917_;
}
pub unsafe fn l_Lean_Parser_sepBy_parenthesizer(
    mut v_p_5918_: *mut LeanObject,
    mut v_sep_5919_: *mut LeanObject,
    mut v_psep_5920_: *mut LeanObject,
    mut v_allowTrailingSep_5921_: u8,
    mut v_a_5922_: *mut LeanObject,
    mut v_a_5923_: *mut LeanObject,
    mut v_a_5924_: *mut LeanObject,
    mut v_a_5925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    v___x_5927_ = l_Lean_Parser_sepBy_parenthesizer___redArg(
        v_p_5918_,
        v_sep_5919_,
        v_psep_5920_,
        v_a_5922_,
        v_a_5923_,
        v_a_5924_,
        v_a_5925_,
    );
    return v___x_5927_;
}
pub unsafe fn l_Lean_Parser_sepBy_parenthesizer___boxed(
    mut v_p_5928_: *mut LeanObject,
    mut v_sep_5929_: *mut LeanObject,
    mut v_psep_5930_: *mut LeanObject,
    mut v_allowTrailingSep_5931_: *mut LeanObject,
    mut v_a_5932_: *mut LeanObject,
    mut v_a_5933_: *mut LeanObject,
    mut v_a_5934_: *mut LeanObject,
    mut v_a_5935_: *mut LeanObject,
    mut v_a_5936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowTrailingSep_boxed_5937_: u8 = 0;
    let mut v_res_5938_: *mut LeanObject = core::ptr::null_mut();
    v_allowTrailingSep_boxed_5937_ = (lean_unbox(v_allowTrailingSep_5931_) as u8);
    v_res_5938_ = l_Lean_Parser_sepBy_parenthesizer(
        v_p_5928_,
        v_sep_5929_,
        v_psep_5930_,
        v_allowTrailingSep_boxed_5937_,
        v_a_5932_,
        v_a_5933_,
        v_a_5934_,
        v_a_5935_,
    );
    lean_dec(v_a_5935_);
    lean_dec_ref(v_a_5934_);
    lean_dec(v_a_5933_);
    lean_dec_ref(v_a_5932_);
    return v_res_5938_;
}
pub unsafe fn l_Lean_Parser_sepBy1_formatter___redArg(
    mut v_p_5939_: *mut LeanObject,
    mut v_sep_5940_: *mut LeanObject,
    mut v_psep_5941_: *mut LeanObject,
    mut v_a_5942_: *mut LeanObject,
    mut v_a_5943_: *mut LeanObject,
    mut v_a_5944_: *mut LeanObject,
    mut v_a_5945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    v___x_5947_ = lean_alloc_closure(
        l_Lean_Parser_sepByElemParser_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5947_, 0, v_p_5939_);
    lean_closure_set(v___x_5947_, 1, v_sep_5940_);
    v___x_5948_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(
        v___x_5947_,
        v_psep_5941_,
        v_a_5942_,
        v_a_5943_,
        v_a_5944_,
        v_a_5945_,
    );
    return v___x_5948_;
}
pub unsafe fn l_Lean_Parser_sepBy1_formatter___redArg___boxed(
    mut v_p_5949_: *mut LeanObject,
    mut v_sep_5950_: *mut LeanObject,
    mut v_psep_5951_: *mut LeanObject,
    mut v_a_5952_: *mut LeanObject,
    mut v_a_5953_: *mut LeanObject,
    mut v_a_5954_: *mut LeanObject,
    mut v_a_5955_: *mut LeanObject,
    mut v_a_5956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5957_: *mut LeanObject = core::ptr::null_mut();
    v_res_5957_ = l_Lean_Parser_sepBy1_formatter___redArg(
        v_p_5949_,
        v_sep_5950_,
        v_psep_5951_,
        v_a_5952_,
        v_a_5953_,
        v_a_5954_,
        v_a_5955_,
    );
    lean_dec(v_a_5955_);
    lean_dec_ref(v_a_5954_);
    lean_dec(v_a_5953_);
    lean_dec_ref(v_a_5952_);
    return v_res_5957_;
}
pub unsafe fn l_Lean_Parser_sepBy1_formatter(
    mut v_p_5958_: *mut LeanObject,
    mut v_sep_5959_: *mut LeanObject,
    mut v_psep_5960_: *mut LeanObject,
    mut v_allowTrailingSep_5961_: u8,
    mut v_a_5962_: *mut LeanObject,
    mut v_a_5963_: *mut LeanObject,
    mut v_a_5964_: *mut LeanObject,
    mut v_a_5965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
    v___x_5967_ = l_Lean_Parser_sepBy1_formatter___redArg(
        v_p_5958_,
        v_sep_5959_,
        v_psep_5960_,
        v_a_5962_,
        v_a_5963_,
        v_a_5964_,
        v_a_5965_,
    );
    return v___x_5967_;
}
pub unsafe fn l_Lean_Parser_sepBy1_formatter___boxed(
    mut v_p_5968_: *mut LeanObject,
    mut v_sep_5969_: *mut LeanObject,
    mut v_psep_5970_: *mut LeanObject,
    mut v_allowTrailingSep_5971_: *mut LeanObject,
    mut v_a_5972_: *mut LeanObject,
    mut v_a_5973_: *mut LeanObject,
    mut v_a_5974_: *mut LeanObject,
    mut v_a_5975_: *mut LeanObject,
    mut v_a_5976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowTrailingSep_boxed_5977_: u8 = 0;
    let mut v_res_5978_: *mut LeanObject = core::ptr::null_mut();
    v_allowTrailingSep_boxed_5977_ = (lean_unbox(v_allowTrailingSep_5971_) as u8);
    v_res_5978_ = l_Lean_Parser_sepBy1_formatter(
        v_p_5968_,
        v_sep_5969_,
        v_psep_5970_,
        v_allowTrailingSep_boxed_5977_,
        v_a_5972_,
        v_a_5973_,
        v_a_5974_,
        v_a_5975_,
    );
    lean_dec(v_a_5975_);
    lean_dec_ref(v_a_5974_);
    lean_dec(v_a_5973_);
    lean_dec_ref(v_a_5972_);
    return v_res_5978_;
}
pub unsafe fn l_Lean_Parser_sepBy1_parenthesizer___redArg(
    mut v_p_5979_: *mut LeanObject,
    mut v_sep_5980_: *mut LeanObject,
    mut v_psep_5981_: *mut LeanObject,
    mut v_a_5982_: *mut LeanObject,
    mut v_a_5983_: *mut LeanObject,
    mut v_a_5984_: *mut LeanObject,
    mut v_a_5985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    v___x_5987_ = lean_alloc_closure(
        l_Lean_Parser_sepByElemParser_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5987_, 0, v_p_5979_);
    lean_closure_set(v___x_5987_, 1, v_sep_5980_);
    v___x_5988_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(
        v___x_5987_,
        v_psep_5981_,
        v_a_5982_,
        v_a_5983_,
        v_a_5984_,
        v_a_5985_,
    );
    return v___x_5988_;
}
pub unsafe fn l_Lean_Parser_sepBy1_parenthesizer___redArg___boxed(
    mut v_p_5989_: *mut LeanObject,
    mut v_sep_5990_: *mut LeanObject,
    mut v_psep_5991_: *mut LeanObject,
    mut v_a_5992_: *mut LeanObject,
    mut v_a_5993_: *mut LeanObject,
    mut v_a_5994_: *mut LeanObject,
    mut v_a_5995_: *mut LeanObject,
    mut v_a_5996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5997_: *mut LeanObject = core::ptr::null_mut();
    v_res_5997_ = l_Lean_Parser_sepBy1_parenthesizer___redArg(
        v_p_5989_,
        v_sep_5990_,
        v_psep_5991_,
        v_a_5992_,
        v_a_5993_,
        v_a_5994_,
        v_a_5995_,
    );
    lean_dec(v_a_5995_);
    lean_dec_ref(v_a_5994_);
    lean_dec(v_a_5993_);
    lean_dec_ref(v_a_5992_);
    return v_res_5997_;
}
pub unsafe fn l_Lean_Parser_sepBy1_parenthesizer(
    mut v_p_5998_: *mut LeanObject,
    mut v_sep_5999_: *mut LeanObject,
    mut v_psep_6000_: *mut LeanObject,
    mut v_allowTrailingSep_6001_: u8,
    mut v_a_6002_: *mut LeanObject,
    mut v_a_6003_: *mut LeanObject,
    mut v_a_6004_: *mut LeanObject,
    mut v_a_6005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    v___x_6007_ = l_Lean_Parser_sepBy1_parenthesizer___redArg(
        v_p_5998_,
        v_sep_5999_,
        v_psep_6000_,
        v_a_6002_,
        v_a_6003_,
        v_a_6004_,
        v_a_6005_,
    );
    return v___x_6007_;
}
pub unsafe fn l_Lean_Parser_sepBy1_parenthesizer___boxed(
    mut v_p_6008_: *mut LeanObject,
    mut v_sep_6009_: *mut LeanObject,
    mut v_psep_6010_: *mut LeanObject,
    mut v_allowTrailingSep_6011_: *mut LeanObject,
    mut v_a_6012_: *mut LeanObject,
    mut v_a_6013_: *mut LeanObject,
    mut v_a_6014_: *mut LeanObject,
    mut v_a_6015_: *mut LeanObject,
    mut v_a_6016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowTrailingSep_boxed_6017_: u8 = 0;
    let mut v_res_6018_: *mut LeanObject = core::ptr::null_mut();
    v_allowTrailingSep_boxed_6017_ = (lean_unbox(v_allowTrailingSep_6011_) as u8);
    v_res_6018_ = l_Lean_Parser_sepBy1_parenthesizer(
        v_p_6008_,
        v_sep_6009_,
        v_psep_6010_,
        v_allowTrailingSep_boxed_6017_,
        v_a_6012_,
        v_a_6013_,
        v_a_6014_,
        v_a_6015_,
    );
    lean_dec(v_a_6015_);
    lean_dec_ref(v_a_6014_);
    lean_dec(v_a_6013_);
    lean_dec_ref(v_a_6012_);
    return v_res_6018_;
}
pub unsafe fn l_Lean_Parser_unicodeSymbol_formatter(
    mut v_sym_6019_: *mut LeanObject,
    mut v_asciiSym_6020_: *mut LeanObject,
    mut v_preserveForPP_6021_: u8,
    mut v_a_6022_: *mut LeanObject,
    mut v_a_6023_: *mut LeanObject,
    mut v_a_6024_: *mut LeanObject,
    mut v_a_6025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    v___x_6027_ = lean_box((v_preserveForPP_6021_) as usize);
    v___x_6028_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_6028_, 0, v_sym_6019_);
    lean_closure_set(v___x_6028_, 1, v_asciiSym_6020_);
    lean_closure_set(v___x_6028_, 2, v___x_6027_);
    v___x_6029_ = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(
        v___x_6028_,
        v_a_6022_,
        v_a_6023_,
        v_a_6024_,
        v_a_6025_,
    );
    return v___x_6029_;
}
pub unsafe fn l_Lean_Parser_unicodeSymbol_formatter___boxed(
    mut v_sym_6030_: *mut LeanObject,
    mut v_asciiSym_6031_: *mut LeanObject,
    mut v_preserveForPP_6032_: *mut LeanObject,
    mut v_a_6033_: *mut LeanObject,
    mut v_a_6034_: *mut LeanObject,
    mut v_a_6035_: *mut LeanObject,
    mut v_a_6036_: *mut LeanObject,
    mut v_a_6037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_preserveForPP_boxed_6038_: u8 = 0;
    let mut v_res_6039_: *mut LeanObject = core::ptr::null_mut();
    v_preserveForPP_boxed_6038_ = (lean_unbox(v_preserveForPP_6032_) as u8);
    v_res_6039_ = l_Lean_Parser_unicodeSymbol_formatter(
        v_sym_6030_,
        v_asciiSym_6031_,
        v_preserveForPP_boxed_6038_,
        v_a_6033_,
        v_a_6034_,
        v_a_6035_,
        v_a_6036_,
    );
    lean_dec(v_a_6036_);
    lean_dec_ref(v_a_6035_);
    lean_dec(v_a_6034_);
    lean_dec_ref(v_a_6033_);
    return v_res_6039_;
}
pub unsafe fn l_Lean_Parser_unicodeSymbol_parenthesizer(
    mut v_sym_6040_: *mut LeanObject,
    mut v_asciiSym_6041_: *mut LeanObject,
    mut v_preserveForPP_6042_: u8,
    mut v_a_6043_: *mut LeanObject,
    mut v_a_6044_: *mut LeanObject,
    mut v_a_6045_: *mut LeanObject,
    mut v_a_6046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    v___x_6048_ = lean_box((v_preserveForPP_6042_) as usize);
    v___x_6049_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_6049_, 0, v_sym_6040_);
    lean_closure_set(v___x_6049_, 1, v_asciiSym_6041_);
    lean_closure_set(v___x_6049_, 2, v___x_6048_);
    v___x_6050_ = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(
        v___x_6049_,
        v_a_6043_,
        v_a_6044_,
        v_a_6045_,
        v_a_6046_,
    );
    return v___x_6050_;
}
pub unsafe fn l_Lean_Parser_unicodeSymbol_parenthesizer___boxed(
    mut v_sym_6051_: *mut LeanObject,
    mut v_asciiSym_6052_: *mut LeanObject,
    mut v_preserveForPP_6053_: *mut LeanObject,
    mut v_a_6054_: *mut LeanObject,
    mut v_a_6055_: *mut LeanObject,
    mut v_a_6056_: *mut LeanObject,
    mut v_a_6057_: *mut LeanObject,
    mut v_a_6058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_preserveForPP_boxed_6059_: u8 = 0;
    let mut v_res_6060_: *mut LeanObject = core::ptr::null_mut();
    v_preserveForPP_boxed_6059_ = (lean_unbox(v_preserveForPP_6053_) as u8);
    v_res_6060_ = l_Lean_Parser_unicodeSymbol_parenthesizer(
        v_sym_6051_,
        v_asciiSym_6052_,
        v_preserveForPP_boxed_6059_,
        v_a_6054_,
        v_a_6055_,
        v_a_6056_,
        v_a_6057_,
    );
    lean_dec(v_a_6057_);
    lean_dec_ref(v_a_6056_);
    lean_dec(v_a_6055_);
    lean_dec_ref(v_a_6054_);
    return v_res_6060_;
}
pub unsafe fn l_Lean_Parser_withCache_formatter___redArg(
    mut v_p_6061_: *mut LeanObject,
    mut v_a_6062_: *mut LeanObject,
    mut v_a_6063_: *mut LeanObject,
    mut v_a_6064_: *mut LeanObject,
    mut v_a_6065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6065_);
    lean_inc_ref(v_a_6064_);
    lean_inc(v_a_6063_);
    lean_inc_ref(v_a_6062_);
    v___x_6067_ = lean_apply_5(
        v_p_6061_,
        v_a_6062_,
        v_a_6063_,
        v_a_6064_,
        v_a_6065_,
        lean_box(0),
    );
    return v___x_6067_;
}
pub unsafe fn l_Lean_Parser_withCache_formatter___redArg___boxed(
    mut v_p_6068_: *mut LeanObject,
    mut v_a_6069_: *mut LeanObject,
    mut v_a_6070_: *mut LeanObject,
    mut v_a_6071_: *mut LeanObject,
    mut v_a_6072_: *mut LeanObject,
    mut v_a_6073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6074_: *mut LeanObject = core::ptr::null_mut();
    v_res_6074_ = l_Lean_Parser_withCache_formatter___redArg(
        v_p_6068_, v_a_6069_, v_a_6070_, v_a_6071_, v_a_6072_,
    );
    lean_dec(v_a_6072_);
    lean_dec_ref(v_a_6071_);
    lean_dec(v_a_6070_);
    lean_dec_ref(v_a_6069_);
    return v_res_6074_;
}
pub unsafe fn l_Lean_Parser_withCache_formatter(
    mut v_parserName_6075_: *mut LeanObject,
    mut v_p_6076_: *mut LeanObject,
    mut v_a_6077_: *mut LeanObject,
    mut v_a_6078_: *mut LeanObject,
    mut v_a_6079_: *mut LeanObject,
    mut v_a_6080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6080_);
    lean_inc_ref(v_a_6079_);
    lean_inc(v_a_6078_);
    lean_inc_ref(v_a_6077_);
    v___x_6082_ = lean_apply_5(
        v_p_6076_,
        v_a_6077_,
        v_a_6078_,
        v_a_6079_,
        v_a_6080_,
        lean_box(0),
    );
    return v___x_6082_;
}
pub unsafe fn l_Lean_Parser_withCache_formatter___boxed(
    mut v_parserName_6083_: *mut LeanObject,
    mut v_p_6084_: *mut LeanObject,
    mut v_a_6085_: *mut LeanObject,
    mut v_a_6086_: *mut LeanObject,
    mut v_a_6087_: *mut LeanObject,
    mut v_a_6088_: *mut LeanObject,
    mut v_a_6089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6090_: *mut LeanObject = core::ptr::null_mut();
    v_res_6090_ = l_Lean_Parser_withCache_formatter(
        v_parserName_6083_,
        v_p_6084_,
        v_a_6085_,
        v_a_6086_,
        v_a_6087_,
        v_a_6088_,
    );
    lean_dec(v_a_6088_);
    lean_dec_ref(v_a_6087_);
    lean_dec(v_a_6086_);
    lean_dec_ref(v_a_6085_);
    lean_dec(v_parserName_6083_);
    return v_res_6090_;
}
pub unsafe fn l_Lean_Parser_withCache_parenthesizer___redArg(
    mut v_p_6091_: *mut LeanObject,
    mut v_a_6092_: *mut LeanObject,
    mut v_a_6093_: *mut LeanObject,
    mut v_a_6094_: *mut LeanObject,
    mut v_a_6095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6095_);
    lean_inc_ref(v_a_6094_);
    lean_inc(v_a_6093_);
    lean_inc_ref(v_a_6092_);
    v___x_6097_ = lean_apply_5(
        v_p_6091_,
        v_a_6092_,
        v_a_6093_,
        v_a_6094_,
        v_a_6095_,
        lean_box(0),
    );
    return v___x_6097_;
}
pub unsafe fn l_Lean_Parser_withCache_parenthesizer___redArg___boxed(
    mut v_p_6098_: *mut LeanObject,
    mut v_a_6099_: *mut LeanObject,
    mut v_a_6100_: *mut LeanObject,
    mut v_a_6101_: *mut LeanObject,
    mut v_a_6102_: *mut LeanObject,
    mut v_a_6103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6104_: *mut LeanObject = core::ptr::null_mut();
    v_res_6104_ = l_Lean_Parser_withCache_parenthesizer___redArg(
        v_p_6098_, v_a_6099_, v_a_6100_, v_a_6101_, v_a_6102_,
    );
    lean_dec(v_a_6102_);
    lean_dec_ref(v_a_6101_);
    lean_dec(v_a_6100_);
    lean_dec_ref(v_a_6099_);
    return v_res_6104_;
}
pub unsafe fn l_Lean_Parser_withCache_parenthesizer(
    mut v_parserName_6105_: *mut LeanObject,
    mut v_p_6106_: *mut LeanObject,
    mut v_a_6107_: *mut LeanObject,
    mut v_a_6108_: *mut LeanObject,
    mut v_a_6109_: *mut LeanObject,
    mut v_a_6110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6110_);
    lean_inc_ref(v_a_6109_);
    lean_inc(v_a_6108_);
    lean_inc_ref(v_a_6107_);
    v___x_6112_ = lean_apply_5(
        v_p_6106_,
        v_a_6107_,
        v_a_6108_,
        v_a_6109_,
        v_a_6110_,
        lean_box(0),
    );
    return v___x_6112_;
}
pub unsafe fn l_Lean_Parser_withCache_parenthesizer___boxed(
    mut v_parserName_6113_: *mut LeanObject,
    mut v_p_6114_: *mut LeanObject,
    mut v_a_6115_: *mut LeanObject,
    mut v_a_6116_: *mut LeanObject,
    mut v_a_6117_: *mut LeanObject,
    mut v_a_6118_: *mut LeanObject,
    mut v_a_6119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6120_: *mut LeanObject = core::ptr::null_mut();
    v_res_6120_ = l_Lean_Parser_withCache_parenthesizer(
        v_parserName_6113_,
        v_p_6114_,
        v_a_6115_,
        v_a_6116_,
        v_a_6117_,
        v_a_6118_,
    );
    lean_dec(v_a_6118_);
    lean_dec_ref(v_a_6117_);
    lean_dec(v_a_6116_);
    lean_dec_ref(v_a_6115_);
    lean_dec(v_parserName_6113_);
    return v_res_6120_;
}
pub unsafe fn l_Lean_Parser_withResetCache_formatter(
    mut v_p_6121_: *mut LeanObject,
    mut v_a_6122_: *mut LeanObject,
    mut v_a_6123_: *mut LeanObject,
    mut v_a_6124_: *mut LeanObject,
    mut v_a_6125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6125_);
    lean_inc_ref(v_a_6124_);
    lean_inc(v_a_6123_);
    lean_inc_ref(v_a_6122_);
    v___x_6127_ = lean_apply_5(
        v_p_6121_,
        v_a_6122_,
        v_a_6123_,
        v_a_6124_,
        v_a_6125_,
        lean_box(0),
    );
    return v___x_6127_;
}
pub unsafe fn l_Lean_Parser_withResetCache_formatter___boxed(
    mut v_p_6128_: *mut LeanObject,
    mut v_a_6129_: *mut LeanObject,
    mut v_a_6130_: *mut LeanObject,
    mut v_a_6131_: *mut LeanObject,
    mut v_a_6132_: *mut LeanObject,
    mut v_a_6133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6134_: *mut LeanObject = core::ptr::null_mut();
    v_res_6134_ = l_Lean_Parser_withResetCache_formatter(
        v_p_6128_, v_a_6129_, v_a_6130_, v_a_6131_, v_a_6132_,
    );
    lean_dec(v_a_6132_);
    lean_dec_ref(v_a_6131_);
    lean_dec(v_a_6130_);
    lean_dec_ref(v_a_6129_);
    return v_res_6134_;
}
pub unsafe fn l_Lean_Parser_withResetCache_parenthesizer(
    mut v_p_6135_: *mut LeanObject,
    mut v_a_6136_: *mut LeanObject,
    mut v_a_6137_: *mut LeanObject,
    mut v_a_6138_: *mut LeanObject,
    mut v_a_6139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6139_);
    lean_inc_ref(v_a_6138_);
    lean_inc(v_a_6137_);
    lean_inc_ref(v_a_6136_);
    v___x_6141_ = lean_apply_5(
        v_p_6135_,
        v_a_6136_,
        v_a_6137_,
        v_a_6138_,
        v_a_6139_,
        lean_box(0),
    );
    return v___x_6141_;
}
pub unsafe fn l_Lean_Parser_withResetCache_parenthesizer___boxed(
    mut v_p_6142_: *mut LeanObject,
    mut v_a_6143_: *mut LeanObject,
    mut v_a_6144_: *mut LeanObject,
    mut v_a_6145_: *mut LeanObject,
    mut v_a_6146_: *mut LeanObject,
    mut v_a_6147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6148_: *mut LeanObject = core::ptr::null_mut();
    v_res_6148_ = l_Lean_Parser_withResetCache_parenthesizer(
        v_p_6142_, v_a_6143_, v_a_6144_, v_a_6145_, v_a_6146_,
    );
    lean_dec(v_a_6146_);
    lean_dec_ref(v_a_6145_);
    lean_dec(v_a_6144_);
    lean_dec_ref(v_a_6143_);
    return v_res_6148_;
}
pub unsafe fn l_Lean_Parser_withPosition_formatter(
    mut v_p_6149_: *mut LeanObject,
    mut v_a_6150_: *mut LeanObject,
    mut v_a_6151_: *mut LeanObject,
    mut v_a_6152_: *mut LeanObject,
    mut v_a_6153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6153_);
    lean_inc_ref(v_a_6152_);
    lean_inc(v_a_6151_);
    lean_inc_ref(v_a_6150_);
    v___x_6155_ = lean_apply_5(
        v_p_6149_,
        v_a_6150_,
        v_a_6151_,
        v_a_6152_,
        v_a_6153_,
        lean_box(0),
    );
    return v___x_6155_;
}
pub unsafe fn l_Lean_Parser_withPosition_formatter___boxed(
    mut v_p_6156_: *mut LeanObject,
    mut v_a_6157_: *mut LeanObject,
    mut v_a_6158_: *mut LeanObject,
    mut v_a_6159_: *mut LeanObject,
    mut v_a_6160_: *mut LeanObject,
    mut v_a_6161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6162_: *mut LeanObject = core::ptr::null_mut();
    v_res_6162_ =
        l_Lean_Parser_withPosition_formatter(v_p_6156_, v_a_6157_, v_a_6158_, v_a_6159_, v_a_6160_);
    lean_dec(v_a_6160_);
    lean_dec_ref(v_a_6159_);
    lean_dec(v_a_6158_);
    lean_dec_ref(v_a_6157_);
    return v_res_6162_;
}
pub unsafe fn l_Lean_Parser_withPositionAfterLinebreak_formatter(
    mut v_p_6163_: *mut LeanObject,
    mut v_a_6164_: *mut LeanObject,
    mut v_a_6165_: *mut LeanObject,
    mut v_a_6166_: *mut LeanObject,
    mut v_a_6167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6167_);
    lean_inc_ref(v_a_6166_);
    lean_inc(v_a_6165_);
    lean_inc_ref(v_a_6164_);
    v___x_6169_ = lean_apply_5(
        v_p_6163_,
        v_a_6164_,
        v_a_6165_,
        v_a_6166_,
        v_a_6167_,
        lean_box(0),
    );
    return v___x_6169_;
}
pub unsafe fn l_Lean_Parser_withPositionAfterLinebreak_formatter___boxed(
    mut v_p_6170_: *mut LeanObject,
    mut v_a_6171_: *mut LeanObject,
    mut v_a_6172_: *mut LeanObject,
    mut v_a_6173_: *mut LeanObject,
    mut v_a_6174_: *mut LeanObject,
    mut v_a_6175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6176_: *mut LeanObject = core::ptr::null_mut();
    v_res_6176_ = l_Lean_Parser_withPositionAfterLinebreak_formatter(
        v_p_6170_, v_a_6171_, v_a_6172_, v_a_6173_, v_a_6174_,
    );
    lean_dec(v_a_6174_);
    lean_dec_ref(v_a_6173_);
    lean_dec(v_a_6172_);
    lean_dec_ref(v_a_6171_);
    return v_res_6176_;
}
pub unsafe fn l_Lean_Parser_withoutPosition_formatter(
    mut v_p_6177_: *mut LeanObject,
    mut v_a_6178_: *mut LeanObject,
    mut v_a_6179_: *mut LeanObject,
    mut v_a_6180_: *mut LeanObject,
    mut v_a_6181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6181_);
    lean_inc_ref(v_a_6180_);
    lean_inc(v_a_6179_);
    lean_inc_ref(v_a_6178_);
    v___x_6183_ = lean_apply_5(
        v_p_6177_,
        v_a_6178_,
        v_a_6179_,
        v_a_6180_,
        v_a_6181_,
        lean_box(0),
    );
    return v___x_6183_;
}
pub unsafe fn l_Lean_Parser_withoutPosition_formatter___boxed(
    mut v_p_6184_: *mut LeanObject,
    mut v_a_6185_: *mut LeanObject,
    mut v_a_6186_: *mut LeanObject,
    mut v_a_6187_: *mut LeanObject,
    mut v_a_6188_: *mut LeanObject,
    mut v_a_6189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6190_: *mut LeanObject = core::ptr::null_mut();
    v_res_6190_ = l_Lean_Parser_withoutPosition_formatter(
        v_p_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_,
    );
    lean_dec(v_a_6188_);
    lean_dec_ref(v_a_6187_);
    lean_dec(v_a_6186_);
    lean_dec_ref(v_a_6185_);
    return v_res_6190_;
}
pub unsafe fn l_Lean_Parser_withoutPosition_parenthesizer(
    mut v_p_6191_: *mut LeanObject,
    mut v_a_6192_: *mut LeanObject,
    mut v_a_6193_: *mut LeanObject,
    mut v_a_6194_: *mut LeanObject,
    mut v_a_6195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6197_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6195_);
    lean_inc_ref(v_a_6194_);
    lean_inc(v_a_6193_);
    lean_inc_ref(v_a_6192_);
    v___x_6197_ = lean_apply_5(
        v_p_6191_,
        v_a_6192_,
        v_a_6193_,
        v_a_6194_,
        v_a_6195_,
        lean_box(0),
    );
    return v___x_6197_;
}
pub unsafe fn l_Lean_Parser_withoutPosition_parenthesizer___boxed(
    mut v_p_6198_: *mut LeanObject,
    mut v_a_6199_: *mut LeanObject,
    mut v_a_6200_: *mut LeanObject,
    mut v_a_6201_: *mut LeanObject,
    mut v_a_6202_: *mut LeanObject,
    mut v_a_6203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6204_: *mut LeanObject = core::ptr::null_mut();
    v_res_6204_ = l_Lean_Parser_withoutPosition_parenthesizer(
        v_p_6198_, v_a_6199_, v_a_6200_, v_a_6201_, v_a_6202_,
    );
    lean_dec(v_a_6202_);
    lean_dec_ref(v_a_6201_);
    lean_dec(v_a_6200_);
    lean_dec_ref(v_a_6199_);
    return v_res_6204_;
}
pub unsafe fn l_Lean_Parser_withForbidden_formatter___redArg(
    mut v_p_6205_: *mut LeanObject,
    mut v_a_6206_: *mut LeanObject,
    mut v_a_6207_: *mut LeanObject,
    mut v_a_6208_: *mut LeanObject,
    mut v_a_6209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6211_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6209_);
    lean_inc_ref(v_a_6208_);
    lean_inc(v_a_6207_);
    lean_inc_ref(v_a_6206_);
    v___x_6211_ = lean_apply_5(
        v_p_6205_,
        v_a_6206_,
        v_a_6207_,
        v_a_6208_,
        v_a_6209_,
        lean_box(0),
    );
    return v___x_6211_;
}
pub unsafe fn l_Lean_Parser_withForbidden_formatter___redArg___boxed(
    mut v_p_6212_: *mut LeanObject,
    mut v_a_6213_: *mut LeanObject,
    mut v_a_6214_: *mut LeanObject,
    mut v_a_6215_: *mut LeanObject,
    mut v_a_6216_: *mut LeanObject,
    mut v_a_6217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6218_: *mut LeanObject = core::ptr::null_mut();
    v_res_6218_ = l_Lean_Parser_withForbidden_formatter___redArg(
        v_p_6212_, v_a_6213_, v_a_6214_, v_a_6215_, v_a_6216_,
    );
    lean_dec(v_a_6216_);
    lean_dec_ref(v_a_6215_);
    lean_dec(v_a_6214_);
    lean_dec_ref(v_a_6213_);
    return v_res_6218_;
}
pub unsafe fn l_Lean_Parser_withForbidden_formatter(
    mut v_tk_6219_: *mut LeanObject,
    mut v_p_6220_: *mut LeanObject,
    mut v_a_6221_: *mut LeanObject,
    mut v_a_6222_: *mut LeanObject,
    mut v_a_6223_: *mut LeanObject,
    mut v_a_6224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6224_);
    lean_inc_ref(v_a_6223_);
    lean_inc(v_a_6222_);
    lean_inc_ref(v_a_6221_);
    v___x_6226_ = lean_apply_5(
        v_p_6220_,
        v_a_6221_,
        v_a_6222_,
        v_a_6223_,
        v_a_6224_,
        lean_box(0),
    );
    return v___x_6226_;
}
pub unsafe fn l_Lean_Parser_withForbidden_formatter___boxed(
    mut v_tk_6227_: *mut LeanObject,
    mut v_p_6228_: *mut LeanObject,
    mut v_a_6229_: *mut LeanObject,
    mut v_a_6230_: *mut LeanObject,
    mut v_a_6231_: *mut LeanObject,
    mut v_a_6232_: *mut LeanObject,
    mut v_a_6233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6234_: *mut LeanObject = core::ptr::null_mut();
    v_res_6234_ = l_Lean_Parser_withForbidden_formatter(
        v_tk_6227_, v_p_6228_, v_a_6229_, v_a_6230_, v_a_6231_, v_a_6232_,
    );
    lean_dec(v_a_6232_);
    lean_dec_ref(v_a_6231_);
    lean_dec(v_a_6230_);
    lean_dec_ref(v_a_6229_);
    lean_dec_ref(v_tk_6227_);
    return v_res_6234_;
}
pub unsafe fn l_Lean_Parser_withForbidden_parenthesizer___redArg(
    mut v_p_6235_: *mut LeanObject,
    mut v_a_6236_: *mut LeanObject,
    mut v_a_6237_: *mut LeanObject,
    mut v_a_6238_: *mut LeanObject,
    mut v_a_6239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6239_);
    lean_inc_ref(v_a_6238_);
    lean_inc(v_a_6237_);
    lean_inc_ref(v_a_6236_);
    v___x_6241_ = lean_apply_5(
        v_p_6235_,
        v_a_6236_,
        v_a_6237_,
        v_a_6238_,
        v_a_6239_,
        lean_box(0),
    );
    return v___x_6241_;
}
pub unsafe fn l_Lean_Parser_withForbidden_parenthesizer___redArg___boxed(
    mut v_p_6242_: *mut LeanObject,
    mut v_a_6243_: *mut LeanObject,
    mut v_a_6244_: *mut LeanObject,
    mut v_a_6245_: *mut LeanObject,
    mut v_a_6246_: *mut LeanObject,
    mut v_a_6247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6248_: *mut LeanObject = core::ptr::null_mut();
    v_res_6248_ = l_Lean_Parser_withForbidden_parenthesizer___redArg(
        v_p_6242_, v_a_6243_, v_a_6244_, v_a_6245_, v_a_6246_,
    );
    lean_dec(v_a_6246_);
    lean_dec_ref(v_a_6245_);
    lean_dec(v_a_6244_);
    lean_dec_ref(v_a_6243_);
    return v_res_6248_;
}
pub unsafe fn l_Lean_Parser_withForbidden_parenthesizer(
    mut v_tk_6249_: *mut LeanObject,
    mut v_p_6250_: *mut LeanObject,
    mut v_a_6251_: *mut LeanObject,
    mut v_a_6252_: *mut LeanObject,
    mut v_a_6253_: *mut LeanObject,
    mut v_a_6254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6254_);
    lean_inc_ref(v_a_6253_);
    lean_inc(v_a_6252_);
    lean_inc_ref(v_a_6251_);
    v___x_6256_ = lean_apply_5(
        v_p_6250_,
        v_a_6251_,
        v_a_6252_,
        v_a_6253_,
        v_a_6254_,
        lean_box(0),
    );
    return v___x_6256_;
}
pub unsafe fn l_Lean_Parser_withForbidden_parenthesizer___boxed(
    mut v_tk_6257_: *mut LeanObject,
    mut v_p_6258_: *mut LeanObject,
    mut v_a_6259_: *mut LeanObject,
    mut v_a_6260_: *mut LeanObject,
    mut v_a_6261_: *mut LeanObject,
    mut v_a_6262_: *mut LeanObject,
    mut v_a_6263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6264_: *mut LeanObject = core::ptr::null_mut();
    v_res_6264_ = l_Lean_Parser_withForbidden_parenthesizer(
        v_tk_6257_, v_p_6258_, v_a_6259_, v_a_6260_, v_a_6261_, v_a_6262_,
    );
    lean_dec(v_a_6262_);
    lean_dec_ref(v_a_6261_);
    lean_dec(v_a_6260_);
    lean_dec_ref(v_a_6259_);
    lean_dec_ref(v_tk_6257_);
    return v_res_6264_;
}
pub unsafe fn l_Lean_Parser_withoutForbidden_formatter(
    mut v_p_6265_: *mut LeanObject,
    mut v_a_6266_: *mut LeanObject,
    mut v_a_6267_: *mut LeanObject,
    mut v_a_6268_: *mut LeanObject,
    mut v_a_6269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6269_);
    lean_inc_ref(v_a_6268_);
    lean_inc(v_a_6267_);
    lean_inc_ref(v_a_6266_);
    v___x_6271_ = lean_apply_5(
        v_p_6265_,
        v_a_6266_,
        v_a_6267_,
        v_a_6268_,
        v_a_6269_,
        lean_box(0),
    );
    return v___x_6271_;
}
pub unsafe fn l_Lean_Parser_withoutForbidden_formatter___boxed(
    mut v_p_6272_: *mut LeanObject,
    mut v_a_6273_: *mut LeanObject,
    mut v_a_6274_: *mut LeanObject,
    mut v_a_6275_: *mut LeanObject,
    mut v_a_6276_: *mut LeanObject,
    mut v_a_6277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6278_: *mut LeanObject = core::ptr::null_mut();
    v_res_6278_ = l_Lean_Parser_withoutForbidden_formatter(
        v_p_6272_, v_a_6273_, v_a_6274_, v_a_6275_, v_a_6276_,
    );
    lean_dec(v_a_6276_);
    lean_dec_ref(v_a_6275_);
    lean_dec(v_a_6274_);
    lean_dec_ref(v_a_6273_);
    return v_res_6278_;
}
pub unsafe fn l_Lean_Parser_withoutForbidden_parenthesizer(
    mut v_p_6279_: *mut LeanObject,
    mut v_a_6280_: *mut LeanObject,
    mut v_a_6281_: *mut LeanObject,
    mut v_a_6282_: *mut LeanObject,
    mut v_a_6283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6285_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6283_);
    lean_inc_ref(v_a_6282_);
    lean_inc(v_a_6281_);
    lean_inc_ref(v_a_6280_);
    v___x_6285_ = lean_apply_5(
        v_p_6279_,
        v_a_6280_,
        v_a_6281_,
        v_a_6282_,
        v_a_6283_,
        lean_box(0),
    );
    return v___x_6285_;
}
pub unsafe fn l_Lean_Parser_withoutForbidden_parenthesizer___boxed(
    mut v_p_6286_: *mut LeanObject,
    mut v_a_6287_: *mut LeanObject,
    mut v_a_6288_: *mut LeanObject,
    mut v_a_6289_: *mut LeanObject,
    mut v_a_6290_: *mut LeanObject,
    mut v_a_6291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6292_: *mut LeanObject = core::ptr::null_mut();
    v_res_6292_ = l_Lean_Parser_withoutForbidden_parenthesizer(
        v_p_6286_, v_a_6287_, v_a_6288_, v_a_6289_, v_a_6290_,
    );
    lean_dec(v_a_6290_);
    lean_dec_ref(v_a_6289_);
    lean_dec(v_a_6288_);
    lean_dec_ref(v_a_6287_);
    return v_res_6292_;
}
pub unsafe fn l_Lean_Parser_incQuotDepth_formatter(
    mut v_p_6293_: *mut LeanObject,
    mut v_a_6294_: *mut LeanObject,
    mut v_a_6295_: *mut LeanObject,
    mut v_a_6296_: *mut LeanObject,
    mut v_a_6297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6297_);
    lean_inc_ref(v_a_6296_);
    lean_inc(v_a_6295_);
    lean_inc_ref(v_a_6294_);
    v___x_6299_ = lean_apply_5(
        v_p_6293_,
        v_a_6294_,
        v_a_6295_,
        v_a_6296_,
        v_a_6297_,
        lean_box(0),
    );
    return v___x_6299_;
}
pub unsafe fn l_Lean_Parser_incQuotDepth_formatter___boxed(
    mut v_p_6300_: *mut LeanObject,
    mut v_a_6301_: *mut LeanObject,
    mut v_a_6302_: *mut LeanObject,
    mut v_a_6303_: *mut LeanObject,
    mut v_a_6304_: *mut LeanObject,
    mut v_a_6305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6306_: *mut LeanObject = core::ptr::null_mut();
    v_res_6306_ =
        l_Lean_Parser_incQuotDepth_formatter(v_p_6300_, v_a_6301_, v_a_6302_, v_a_6303_, v_a_6304_);
    lean_dec(v_a_6304_);
    lean_dec_ref(v_a_6303_);
    lean_dec(v_a_6302_);
    lean_dec_ref(v_a_6301_);
    return v_res_6306_;
}
pub unsafe fn l_Lean_Parser_incQuotDepth_parenthesizer(
    mut v_p_6307_: *mut LeanObject,
    mut v_a_6308_: *mut LeanObject,
    mut v_a_6309_: *mut LeanObject,
    mut v_a_6310_: *mut LeanObject,
    mut v_a_6311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6311_);
    lean_inc_ref(v_a_6310_);
    lean_inc(v_a_6309_);
    lean_inc_ref(v_a_6308_);
    v___x_6313_ = lean_apply_5(
        v_p_6307_,
        v_a_6308_,
        v_a_6309_,
        v_a_6310_,
        v_a_6311_,
        lean_box(0),
    );
    return v___x_6313_;
}
pub unsafe fn l_Lean_Parser_incQuotDepth_parenthesizer___boxed(
    mut v_p_6314_: *mut LeanObject,
    mut v_a_6315_: *mut LeanObject,
    mut v_a_6316_: *mut LeanObject,
    mut v_a_6317_: *mut LeanObject,
    mut v_a_6318_: *mut LeanObject,
    mut v_a_6319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6320_: *mut LeanObject = core::ptr::null_mut();
    v_res_6320_ = l_Lean_Parser_incQuotDepth_parenthesizer(
        v_p_6314_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_,
    );
    lean_dec(v_a_6318_);
    lean_dec_ref(v_a_6317_);
    lean_dec(v_a_6316_);
    lean_dec_ref(v_a_6315_);
    return v_res_6320_;
}
pub unsafe fn l_Lean_Parser_suppressInsideQuot_formatter(
    mut v_00___6321_: *mut LeanObject,
    mut v_a_6322_: *mut LeanObject,
    mut v_a_6323_: *mut LeanObject,
    mut v_a_6324_: *mut LeanObject,
    mut v_a_6325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6325_);
    lean_inc_ref(v_a_6324_);
    lean_inc(v_a_6323_);
    lean_inc_ref(v_a_6322_);
    v___x_6327_ = lean_apply_5(
        v_00___6321_,
        v_a_6322_,
        v_a_6323_,
        v_a_6324_,
        v_a_6325_,
        lean_box(0),
    );
    return v___x_6327_;
}
pub unsafe fn l_Lean_Parser_suppressInsideQuot_formatter___boxed(
    mut v_00___6328_: *mut LeanObject,
    mut v_a_6329_: *mut LeanObject,
    mut v_a_6330_: *mut LeanObject,
    mut v_a_6331_: *mut LeanObject,
    mut v_a_6332_: *mut LeanObject,
    mut v_a_6333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6334_: *mut LeanObject = core::ptr::null_mut();
    v_res_6334_ = l_Lean_Parser_suppressInsideQuot_formatter(
        v_00___6328_,
        v_a_6329_,
        v_a_6330_,
        v_a_6331_,
        v_a_6332_,
    );
    lean_dec(v_a_6332_);
    lean_dec_ref(v_a_6331_);
    lean_dec(v_a_6330_);
    lean_dec_ref(v_a_6329_);
    return v_res_6334_;
}
pub unsafe fn l_Lean_Parser_suppressInsideQuot_parenthesizer(
    mut v_00___6335_: *mut LeanObject,
    mut v_a_6336_: *mut LeanObject,
    mut v_a_6337_: *mut LeanObject,
    mut v_a_6338_: *mut LeanObject,
    mut v_a_6339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6339_);
    lean_inc_ref(v_a_6338_);
    lean_inc(v_a_6337_);
    lean_inc_ref(v_a_6336_);
    v___x_6341_ = lean_apply_5(
        v_00___6335_,
        v_a_6336_,
        v_a_6337_,
        v_a_6338_,
        v_a_6339_,
        lean_box(0),
    );
    return v___x_6341_;
}
pub unsafe fn l_Lean_Parser_suppressInsideQuot_parenthesizer___boxed(
    mut v_00___6342_: *mut LeanObject,
    mut v_a_6343_: *mut LeanObject,
    mut v_a_6344_: *mut LeanObject,
    mut v_a_6345_: *mut LeanObject,
    mut v_a_6346_: *mut LeanObject,
    mut v_a_6347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6348_: *mut LeanObject = core::ptr::null_mut();
    v_res_6348_ = l_Lean_Parser_suppressInsideQuot_parenthesizer(
        v_00___6342_,
        v_a_6343_,
        v_a_6344_,
        v_a_6345_,
        v_a_6346_,
    );
    lean_dec(v_a_6346_);
    lean_dec_ref(v_a_6345_);
    lean_dec(v_a_6344_);
    lean_dec_ref(v_a_6343_);
    return v_res_6348_;
}
pub unsafe fn l_Lean_Parser_evalInsideQuot_formatter___redArg(
    mut v_p_6349_: *mut LeanObject,
    mut v_a_6350_: *mut LeanObject,
    mut v_a_6351_: *mut LeanObject,
    mut v_a_6352_: *mut LeanObject,
    mut v_a_6353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6353_);
    lean_inc_ref(v_a_6352_);
    lean_inc(v_a_6351_);
    lean_inc_ref(v_a_6350_);
    v___x_6355_ = lean_apply_5(
        v_p_6349_,
        v_a_6350_,
        v_a_6351_,
        v_a_6352_,
        v_a_6353_,
        lean_box(0),
    );
    return v___x_6355_;
}
pub unsafe fn l_Lean_Parser_evalInsideQuot_formatter___redArg___boxed(
    mut v_p_6356_: *mut LeanObject,
    mut v_a_6357_: *mut LeanObject,
    mut v_a_6358_: *mut LeanObject,
    mut v_a_6359_: *mut LeanObject,
    mut v_a_6360_: *mut LeanObject,
    mut v_a_6361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6362_: *mut LeanObject = core::ptr::null_mut();
    v_res_6362_ = l_Lean_Parser_evalInsideQuot_formatter___redArg(
        v_p_6356_, v_a_6357_, v_a_6358_, v_a_6359_, v_a_6360_,
    );
    lean_dec(v_a_6360_);
    lean_dec_ref(v_a_6359_);
    lean_dec(v_a_6358_);
    lean_dec_ref(v_a_6357_);
    return v_res_6362_;
}
pub unsafe fn l_Lean_Parser_evalInsideQuot_formatter(
    mut v_declName_6363_: *mut LeanObject,
    mut v_p_6364_: *mut LeanObject,
    mut v_a_6365_: *mut LeanObject,
    mut v_a_6366_: *mut LeanObject,
    mut v_a_6367_: *mut LeanObject,
    mut v_a_6368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6368_);
    lean_inc_ref(v_a_6367_);
    lean_inc(v_a_6366_);
    lean_inc_ref(v_a_6365_);
    v___x_6370_ = lean_apply_5(
        v_p_6364_,
        v_a_6365_,
        v_a_6366_,
        v_a_6367_,
        v_a_6368_,
        lean_box(0),
    );
    return v___x_6370_;
}
pub unsafe fn l_Lean_Parser_evalInsideQuot_formatter___boxed(
    mut v_declName_6371_: *mut LeanObject,
    mut v_p_6372_: *mut LeanObject,
    mut v_a_6373_: *mut LeanObject,
    mut v_a_6374_: *mut LeanObject,
    mut v_a_6375_: *mut LeanObject,
    mut v_a_6376_: *mut LeanObject,
    mut v_a_6377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6378_: *mut LeanObject = core::ptr::null_mut();
    v_res_6378_ = l_Lean_Parser_evalInsideQuot_formatter(
        v_declName_6371_,
        v_p_6372_,
        v_a_6373_,
        v_a_6374_,
        v_a_6375_,
        v_a_6376_,
    );
    lean_dec(v_a_6376_);
    lean_dec_ref(v_a_6375_);
    lean_dec(v_a_6374_);
    lean_dec_ref(v_a_6373_);
    lean_dec(v_declName_6371_);
    return v_res_6378_;
}
pub unsafe fn l_Lean_Parser_evalInsideQuot_parenthesizer___redArg(
    mut v_p_6379_: *mut LeanObject,
    mut v_a_6380_: *mut LeanObject,
    mut v_a_6381_: *mut LeanObject,
    mut v_a_6382_: *mut LeanObject,
    mut v_a_6383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6383_);
    lean_inc_ref(v_a_6382_);
    lean_inc(v_a_6381_);
    lean_inc_ref(v_a_6380_);
    v___x_6385_ = lean_apply_5(
        v_p_6379_,
        v_a_6380_,
        v_a_6381_,
        v_a_6382_,
        v_a_6383_,
        lean_box(0),
    );
    return v___x_6385_;
}
pub unsafe fn l_Lean_Parser_evalInsideQuot_parenthesizer___redArg___boxed(
    mut v_p_6386_: *mut LeanObject,
    mut v_a_6387_: *mut LeanObject,
    mut v_a_6388_: *mut LeanObject,
    mut v_a_6389_: *mut LeanObject,
    mut v_a_6390_: *mut LeanObject,
    mut v_a_6391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6392_: *mut LeanObject = core::ptr::null_mut();
    v_res_6392_ = l_Lean_Parser_evalInsideQuot_parenthesizer___redArg(
        v_p_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_,
    );
    lean_dec(v_a_6390_);
    lean_dec_ref(v_a_6389_);
    lean_dec(v_a_6388_);
    lean_dec_ref(v_a_6387_);
    return v_res_6392_;
}
pub unsafe fn l_Lean_Parser_evalInsideQuot_parenthesizer(
    mut v_declName_6393_: *mut LeanObject,
    mut v_p_6394_: *mut LeanObject,
    mut v_a_6395_: *mut LeanObject,
    mut v_a_6396_: *mut LeanObject,
    mut v_a_6397_: *mut LeanObject,
    mut v_a_6398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6398_);
    lean_inc_ref(v_a_6397_);
    lean_inc(v_a_6396_);
    lean_inc_ref(v_a_6395_);
    v___x_6400_ = lean_apply_5(
        v_p_6394_,
        v_a_6395_,
        v_a_6396_,
        v_a_6397_,
        v_a_6398_,
        lean_box(0),
    );
    return v___x_6400_;
}
pub unsafe fn l_Lean_Parser_evalInsideQuot_parenthesizer___boxed(
    mut v_declName_6401_: *mut LeanObject,
    mut v_p_6402_: *mut LeanObject,
    mut v_a_6403_: *mut LeanObject,
    mut v_a_6404_: *mut LeanObject,
    mut v_a_6405_: *mut LeanObject,
    mut v_a_6406_: *mut LeanObject,
    mut v_a_6407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6408_: *mut LeanObject = core::ptr::null_mut();
    v_res_6408_ = l_Lean_Parser_evalInsideQuot_parenthesizer(
        v_declName_6401_,
        v_p_6402_,
        v_a_6403_,
        v_a_6404_,
        v_a_6405_,
        v_a_6406_,
    );
    lean_dec(v_a_6406_);
    lean_dec_ref(v_a_6405_);
    lean_dec(v_a_6404_);
    lean_dec_ref(v_a_6403_);
    lean_dec(v_declName_6401_);
    return v_res_6408_;
}
pub unsafe fn l_Lean_Parser_withOpen_formatter(
    mut v_p_6409_: *mut LeanObject,
    mut v_a_6410_: *mut LeanObject,
    mut v_a_6411_: *mut LeanObject,
    mut v_a_6412_: *mut LeanObject,
    mut v_a_6413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6415_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6413_);
    lean_inc_ref(v_a_6412_);
    lean_inc(v_a_6411_);
    lean_inc_ref(v_a_6410_);
    v___x_6415_ = lean_apply_5(
        v_p_6409_,
        v_a_6410_,
        v_a_6411_,
        v_a_6412_,
        v_a_6413_,
        lean_box(0),
    );
    return v___x_6415_;
}
pub unsafe fn l_Lean_Parser_withOpen_formatter___boxed(
    mut v_p_6416_: *mut LeanObject,
    mut v_a_6417_: *mut LeanObject,
    mut v_a_6418_: *mut LeanObject,
    mut v_a_6419_: *mut LeanObject,
    mut v_a_6420_: *mut LeanObject,
    mut v_a_6421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6422_: *mut LeanObject = core::ptr::null_mut();
    v_res_6422_ =
        l_Lean_Parser_withOpen_formatter(v_p_6416_, v_a_6417_, v_a_6418_, v_a_6419_, v_a_6420_);
    lean_dec(v_a_6420_);
    lean_dec_ref(v_a_6419_);
    lean_dec(v_a_6418_);
    lean_dec_ref(v_a_6417_);
    return v_res_6422_;
}
pub unsafe fn l_Lean_Parser_withOpen_parenthesizer(
    mut v_p_6423_: *mut LeanObject,
    mut v_a_6424_: *mut LeanObject,
    mut v_a_6425_: *mut LeanObject,
    mut v_a_6426_: *mut LeanObject,
    mut v_a_6427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6427_);
    lean_inc_ref(v_a_6426_);
    lean_inc(v_a_6425_);
    lean_inc_ref(v_a_6424_);
    v___x_6429_ = lean_apply_5(
        v_p_6423_,
        v_a_6424_,
        v_a_6425_,
        v_a_6426_,
        v_a_6427_,
        lean_box(0),
    );
    return v___x_6429_;
}
pub unsafe fn l_Lean_Parser_withOpen_parenthesizer___boxed(
    mut v_p_6430_: *mut LeanObject,
    mut v_a_6431_: *mut LeanObject,
    mut v_a_6432_: *mut LeanObject,
    mut v_a_6433_: *mut LeanObject,
    mut v_a_6434_: *mut LeanObject,
    mut v_a_6435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6436_: *mut LeanObject = core::ptr::null_mut();
    v_res_6436_ =
        l_Lean_Parser_withOpen_parenthesizer(v_p_6430_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_);
    lean_dec(v_a_6434_);
    lean_dec_ref(v_a_6433_);
    lean_dec(v_a_6432_);
    lean_dec_ref(v_a_6431_);
    return v_res_6436_;
}
pub unsafe fn l_Lean_Parser_withOpenDecl_formatter(
    mut v_p_6437_: *mut LeanObject,
    mut v_a_6438_: *mut LeanObject,
    mut v_a_6439_: *mut LeanObject,
    mut v_a_6440_: *mut LeanObject,
    mut v_a_6441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6441_);
    lean_inc_ref(v_a_6440_);
    lean_inc(v_a_6439_);
    lean_inc_ref(v_a_6438_);
    v___x_6443_ = lean_apply_5(
        v_p_6437_,
        v_a_6438_,
        v_a_6439_,
        v_a_6440_,
        v_a_6441_,
        lean_box(0),
    );
    return v___x_6443_;
}
pub unsafe fn l_Lean_Parser_withOpenDecl_formatter___boxed(
    mut v_p_6444_: *mut LeanObject,
    mut v_a_6445_: *mut LeanObject,
    mut v_a_6446_: *mut LeanObject,
    mut v_a_6447_: *mut LeanObject,
    mut v_a_6448_: *mut LeanObject,
    mut v_a_6449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6450_: *mut LeanObject = core::ptr::null_mut();
    v_res_6450_ =
        l_Lean_Parser_withOpenDecl_formatter(v_p_6444_, v_a_6445_, v_a_6446_, v_a_6447_, v_a_6448_);
    lean_dec(v_a_6448_);
    lean_dec_ref(v_a_6447_);
    lean_dec(v_a_6446_);
    lean_dec_ref(v_a_6445_);
    return v_res_6450_;
}
pub unsafe fn l_Lean_Parser_withOpenDecl_parenthesizer(
    mut v_p_6451_: *mut LeanObject,
    mut v_a_6452_: *mut LeanObject,
    mut v_a_6453_: *mut LeanObject,
    mut v_a_6454_: *mut LeanObject,
    mut v_a_6455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6455_);
    lean_inc_ref(v_a_6454_);
    lean_inc(v_a_6453_);
    lean_inc_ref(v_a_6452_);
    v___x_6457_ = lean_apply_5(
        v_p_6451_,
        v_a_6452_,
        v_a_6453_,
        v_a_6454_,
        v_a_6455_,
        lean_box(0),
    );
    return v___x_6457_;
}
pub unsafe fn l_Lean_Parser_withOpenDecl_parenthesizer___boxed(
    mut v_p_6458_: *mut LeanObject,
    mut v_a_6459_: *mut LeanObject,
    mut v_a_6460_: *mut LeanObject,
    mut v_a_6461_: *mut LeanObject,
    mut v_a_6462_: *mut LeanObject,
    mut v_a_6463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6464_: *mut LeanObject = core::ptr::null_mut();
    v_res_6464_ = l_Lean_Parser_withOpenDecl_parenthesizer(
        v_p_6458_, v_a_6459_, v_a_6460_, v_a_6461_, v_a_6462_,
    );
    lean_dec(v_a_6462_);
    lean_dec_ref(v_a_6461_);
    lean_dec(v_a_6460_);
    lean_dec_ref(v_a_6459_);
    return v_res_6464_;
}
pub unsafe fn l_Lean_Parser_dbgTraceState_formatter___redArg(
    mut v_p_6465_: *mut LeanObject,
    mut v_a_6466_: *mut LeanObject,
    mut v_a_6467_: *mut LeanObject,
    mut v_a_6468_: *mut LeanObject,
    mut v_a_6469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6469_);
    lean_inc_ref(v_a_6468_);
    lean_inc(v_a_6467_);
    lean_inc_ref(v_a_6466_);
    v___x_6471_ = lean_apply_5(
        v_p_6465_,
        v_a_6466_,
        v_a_6467_,
        v_a_6468_,
        v_a_6469_,
        lean_box(0),
    );
    return v___x_6471_;
}
pub unsafe fn l_Lean_Parser_dbgTraceState_formatter___redArg___boxed(
    mut v_p_6472_: *mut LeanObject,
    mut v_a_6473_: *mut LeanObject,
    mut v_a_6474_: *mut LeanObject,
    mut v_a_6475_: *mut LeanObject,
    mut v_a_6476_: *mut LeanObject,
    mut v_a_6477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6478_: *mut LeanObject = core::ptr::null_mut();
    v_res_6478_ = l_Lean_Parser_dbgTraceState_formatter___redArg(
        v_p_6472_, v_a_6473_, v_a_6474_, v_a_6475_, v_a_6476_,
    );
    lean_dec(v_a_6476_);
    lean_dec_ref(v_a_6475_);
    lean_dec(v_a_6474_);
    lean_dec_ref(v_a_6473_);
    return v_res_6478_;
}
pub unsafe fn l_Lean_Parser_dbgTraceState_formatter(
    mut v_label_6479_: *mut LeanObject,
    mut v_p_6480_: *mut LeanObject,
    mut v_a_6481_: *mut LeanObject,
    mut v_a_6482_: *mut LeanObject,
    mut v_a_6483_: *mut LeanObject,
    mut v_a_6484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6484_);
    lean_inc_ref(v_a_6483_);
    lean_inc(v_a_6482_);
    lean_inc_ref(v_a_6481_);
    v___x_6486_ = lean_apply_5(
        v_p_6480_,
        v_a_6481_,
        v_a_6482_,
        v_a_6483_,
        v_a_6484_,
        lean_box(0),
    );
    return v___x_6486_;
}
pub unsafe fn l_Lean_Parser_dbgTraceState_formatter___boxed(
    mut v_label_6487_: *mut LeanObject,
    mut v_p_6488_: *mut LeanObject,
    mut v_a_6489_: *mut LeanObject,
    mut v_a_6490_: *mut LeanObject,
    mut v_a_6491_: *mut LeanObject,
    mut v_a_6492_: *mut LeanObject,
    mut v_a_6493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6494_: *mut LeanObject = core::ptr::null_mut();
    v_res_6494_ = l_Lean_Parser_dbgTraceState_formatter(
        v_label_6487_,
        v_p_6488_,
        v_a_6489_,
        v_a_6490_,
        v_a_6491_,
        v_a_6492_,
    );
    lean_dec(v_a_6492_);
    lean_dec_ref(v_a_6491_);
    lean_dec(v_a_6490_);
    lean_dec_ref(v_a_6489_);
    lean_dec_ref(v_label_6487_);
    return v_res_6494_;
}
pub unsafe fn l_Lean_Parser_dbgTraceState_parenthesizer___redArg(
    mut v_p_6495_: *mut LeanObject,
    mut v_a_6496_: *mut LeanObject,
    mut v_a_6497_: *mut LeanObject,
    mut v_a_6498_: *mut LeanObject,
    mut v_a_6499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6501_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6499_);
    lean_inc_ref(v_a_6498_);
    lean_inc(v_a_6497_);
    lean_inc_ref(v_a_6496_);
    v___x_6501_ = lean_apply_5(
        v_p_6495_,
        v_a_6496_,
        v_a_6497_,
        v_a_6498_,
        v_a_6499_,
        lean_box(0),
    );
    return v___x_6501_;
}
pub unsafe fn l_Lean_Parser_dbgTraceState_parenthesizer___redArg___boxed(
    mut v_p_6502_: *mut LeanObject,
    mut v_a_6503_: *mut LeanObject,
    mut v_a_6504_: *mut LeanObject,
    mut v_a_6505_: *mut LeanObject,
    mut v_a_6506_: *mut LeanObject,
    mut v_a_6507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6508_: *mut LeanObject = core::ptr::null_mut();
    v_res_6508_ = l_Lean_Parser_dbgTraceState_parenthesizer___redArg(
        v_p_6502_, v_a_6503_, v_a_6504_, v_a_6505_, v_a_6506_,
    );
    lean_dec(v_a_6506_);
    lean_dec_ref(v_a_6505_);
    lean_dec(v_a_6504_);
    lean_dec_ref(v_a_6503_);
    return v_res_6508_;
}
pub unsafe fn l_Lean_Parser_dbgTraceState_parenthesizer(
    mut v_label_6509_: *mut LeanObject,
    mut v_p_6510_: *mut LeanObject,
    mut v_a_6511_: *mut LeanObject,
    mut v_a_6512_: *mut LeanObject,
    mut v_a_6513_: *mut LeanObject,
    mut v_a_6514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6514_);
    lean_inc_ref(v_a_6513_);
    lean_inc(v_a_6512_);
    lean_inc_ref(v_a_6511_);
    v___x_6516_ = lean_apply_5(
        v_p_6510_,
        v_a_6511_,
        v_a_6512_,
        v_a_6513_,
        v_a_6514_,
        lean_box(0),
    );
    return v___x_6516_;
}
pub unsafe fn l_Lean_Parser_dbgTraceState_parenthesizer___boxed(
    mut v_label_6517_: *mut LeanObject,
    mut v_p_6518_: *mut LeanObject,
    mut v_a_6519_: *mut LeanObject,
    mut v_a_6520_: *mut LeanObject,
    mut v_a_6521_: *mut LeanObject,
    mut v_a_6522_: *mut LeanObject,
    mut v_a_6523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6524_: *mut LeanObject = core::ptr::null_mut();
    v_res_6524_ = l_Lean_Parser_dbgTraceState_parenthesizer(
        v_label_6517_,
        v_p_6518_,
        v_a_6519_,
        v_a_6520_,
        v_a_6521_,
        v_a_6522_,
    );
    lean_dec(v_a_6522_);
    lean_dec_ref(v_a_6521_);
    lean_dec(v_a_6520_);
    lean_dec_ref(v_a_6519_);
    lean_dec_ref(v_label_6517_);
    return v_res_6524_;
}
pub unsafe fn l_Lean_Parser_optional_formatter(
    mut v_p_6531_: *mut LeanObject,
    mut v_a_6532_: *mut LeanObject,
    mut v_a_6533_: *mut LeanObject,
    mut v_a_6534_: *mut LeanObject,
    mut v_a_6535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    v___x_6537_ = l_Lean_Parser_optional_formatter___closed__1;
    v___x_6538_ = l_Lean_Parser_optional_formatter___closed__3;
    v___x_6539_ = lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_6539_, 0, v___x_6537_);
    lean_closure_set(v___x_6539_, 1, v_p_6531_);
    lean_closure_set(v___x_6539_, 2, v___x_6538_);
    v___x_6540_ = l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter(
        v___x_6539_,
        v_a_6532_,
        v_a_6533_,
        v_a_6534_,
        v_a_6535_,
    );
    return v___x_6540_;
}
pub unsafe fn l_Lean_Parser_optional_formatter___boxed(
    mut v_p_6541_: *mut LeanObject,
    mut v_a_6542_: *mut LeanObject,
    mut v_a_6543_: *mut LeanObject,
    mut v_a_6544_: *mut LeanObject,
    mut v_a_6545_: *mut LeanObject,
    mut v_a_6546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6547_: *mut LeanObject = core::ptr::null_mut();
    v_res_6547_ =
        l_Lean_Parser_optional_formatter(v_p_6541_, v_a_6542_, v_a_6543_, v_a_6544_, v_a_6545_);
    lean_dec(v_a_6545_);
    lean_dec_ref(v_a_6544_);
    lean_dec(v_a_6543_);
    lean_dec_ref(v_a_6542_);
    return v_res_6547_;
}
pub unsafe fn l_Lean_Parser_optional_parenthesizer(
    mut v_p_6550_: *mut LeanObject,
    mut v_a_6551_: *mut LeanObject,
    mut v_a_6552_: *mut LeanObject,
    mut v_a_6553_: *mut LeanObject,
    mut v_a_6554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    v___x_6556_ = l_Lean_Parser_optional_formatter___closed__1;
    v___x_6557_ = l_Lean_Parser_optional_parenthesizer___closed__0;
    v___x_6558_ = lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_6558_, 0, v___x_6556_);
    lean_closure_set(v___x_6558_, 1, v_p_6550_);
    lean_closure_set(v___x_6558_, 2, v___x_6557_);
    v___x_6559_ = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(
        v___x_6558_,
        v_a_6551_,
        v_a_6552_,
        v_a_6553_,
        v_a_6554_,
    );
    return v___x_6559_;
}
pub unsafe fn l_Lean_Parser_optional_parenthesizer___boxed(
    mut v_p_6560_: *mut LeanObject,
    mut v_a_6561_: *mut LeanObject,
    mut v_a_6562_: *mut LeanObject,
    mut v_a_6563_: *mut LeanObject,
    mut v_a_6564_: *mut LeanObject,
    mut v_a_6565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6566_: *mut LeanObject = core::ptr::null_mut();
    v_res_6566_ =
        l_Lean_Parser_optional_parenthesizer(v_p_6560_, v_a_6561_, v_a_6562_, v_a_6563_, v_a_6564_);
    lean_dec(v_a_6564_);
    lean_dec_ref(v_a_6563_);
    lean_dec(v_a_6562_);
    lean_dec_ref(v_a_6561_);
    return v_res_6566_;
}
pub unsafe fn _init_l_Lean_Parser_optional___closed__0() -> *mut LeanObject {
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    v___x_6567_ = l_Lean_Parser_optional_formatter___closed__2;
    v___x_6568_ = l_Lean_Parser_symbol(v___x_6567_);
    return v___x_6568_;
}
pub unsafe fn l_Lean_Parser_optional(mut v_p_6569_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    v___x_6570_ = l_Lean_Parser_optional_formatter___closed__1;
    v___x_6571_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_optional___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_optional___closed__0_once),
        _init_l_Lean_Parser_optional___closed__0,
    );
    v___x_6572_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_6570_, v_p_6569_, v___x_6571_);
    v___x_6573_ = l_Lean_Parser_optionalNoAntiquot(v___x_6572_);
    return v___x_6573_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1()
-> *mut LeanObject {
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    v___x_6580_ = l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0;
    v___x_6581_ = l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1;
    v___x_6582_ = l_Lean_addBuiltinDocString(v___x_6580_, v___x_6581_);
    return v___x_6582_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___boxed(
    mut v_a_6583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6584_: *mut LeanObject = core::ptr::null_mut();
    v_res_6584_ = l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1();
    return v_res_6584_;
}
pub unsafe fn l_Lean_Parser_many_formatter(
    mut v_p_6590_: *mut LeanObject,
    mut v_a_6591_: *mut LeanObject,
    mut v_a_6592_: *mut LeanObject,
    mut v_a_6593_: *mut LeanObject,
    mut v_a_6594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    v___x_6596_ = l_Lean_Parser_many_formatter___closed__1;
    v___x_6597_ = l_Lean_Parser_many_formatter___closed__2;
    v___x_6598_ = lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_6598_, 0, v___x_6596_);
    lean_closure_set(v___x_6598_, 1, v_p_6590_);
    lean_closure_set(v___x_6598_, 2, v___x_6597_);
    v___x_6599_ = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(
        v___x_6598_,
        v_a_6591_,
        v_a_6592_,
        v_a_6593_,
        v_a_6594_,
    );
    return v___x_6599_;
}
pub unsafe fn l_Lean_Parser_many_formatter___boxed(
    mut v_p_6600_: *mut LeanObject,
    mut v_a_6601_: *mut LeanObject,
    mut v_a_6602_: *mut LeanObject,
    mut v_a_6603_: *mut LeanObject,
    mut v_a_6604_: *mut LeanObject,
    mut v_a_6605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6606_: *mut LeanObject = core::ptr::null_mut();
    v_res_6606_ =
        l_Lean_Parser_many_formatter(v_p_6600_, v_a_6601_, v_a_6602_, v_a_6603_, v_a_6604_);
    lean_dec(v_a_6604_);
    lean_dec_ref(v_a_6603_);
    lean_dec(v_a_6602_);
    lean_dec_ref(v_a_6601_);
    return v_res_6606_;
}
pub unsafe fn l_Lean_Parser_many_parenthesizer(
    mut v_p_6609_: *mut LeanObject,
    mut v_a_6610_: *mut LeanObject,
    mut v_a_6611_: *mut LeanObject,
    mut v_a_6612_: *mut LeanObject,
    mut v_a_6613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut LeanObject = core::ptr::null_mut();
    v___x_6615_ = l_Lean_Parser_many_formatter___closed__1;
    v___x_6616_ = l_Lean_Parser_many_parenthesizer___closed__0;
    v___x_6617_ = lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_6617_, 0, v___x_6615_);
    lean_closure_set(v___x_6617_, 1, v_p_6609_);
    lean_closure_set(v___x_6617_, 2, v___x_6616_);
    v___x_6618_ = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(
        v___x_6617_,
        v_a_6610_,
        v_a_6611_,
        v_a_6612_,
        v_a_6613_,
    );
    return v___x_6618_;
}
pub unsafe fn l_Lean_Parser_many_parenthesizer___boxed(
    mut v_p_6619_: *mut LeanObject,
    mut v_a_6620_: *mut LeanObject,
    mut v_a_6621_: *mut LeanObject,
    mut v_a_6622_: *mut LeanObject,
    mut v_a_6623_: *mut LeanObject,
    mut v_a_6624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6625_: *mut LeanObject = core::ptr::null_mut();
    v_res_6625_ =
        l_Lean_Parser_many_parenthesizer(v_p_6619_, v_a_6620_, v_a_6621_, v_a_6622_, v_a_6623_);
    lean_dec(v_a_6623_);
    lean_dec_ref(v_a_6622_);
    lean_dec(v_a_6621_);
    lean_dec_ref(v_a_6620_);
    return v_res_6625_;
}
pub unsafe fn _init_l_Lean_Parser_many___closed__0() -> *mut LeanObject {
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    v___x_6626_ = l_Lean_Parser_sepByElemParser_formatter___closed__2;
    v___x_6627_ = l_Lean_Parser_symbol(v___x_6626_);
    return v___x_6627_;
}
pub unsafe fn l_Lean_Parser_many(mut v_p_6628_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    v___x_6629_ = l_Lean_Parser_many_formatter___closed__1;
    v___x_6630_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_many___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_many___closed__0_once),
        _init_l_Lean_Parser_many___closed__0,
    );
    v___x_6631_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_6629_, v_p_6628_, v___x_6630_);
    v___x_6632_ = l_Lean_Parser_manyNoAntiquot(v___x_6631_);
    return v___x_6632_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1()
-> *mut LeanObject {
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    v___x_6639_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0;
    v___x_6640_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1;
    v___x_6641_ = l_Lean_addBuiltinDocString(v___x_6639_, v___x_6640_);
    return v___x_6641_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___boxed(
    mut v_a_6642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6643_: *mut LeanObject = core::ptr::null_mut();
    v_res_6643_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1();
    return v_res_6643_;
}
pub unsafe fn l_Lean_Parser_many1_formatter(
    mut v_p_6644_: *mut LeanObject,
    mut v_a_6645_: *mut LeanObject,
    mut v_a_6646_: *mut LeanObject,
    mut v_a_6647_: *mut LeanObject,
    mut v_a_6648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
    v___x_6650_ = l_Lean_Parser_many_formatter___closed__1;
    v___x_6651_ = l_Lean_Parser_many_formatter___closed__2;
    v___x_6652_ = lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_6652_, 0, v___x_6650_);
    lean_closure_set(v___x_6652_, 1, v_p_6644_);
    lean_closure_set(v___x_6652_, 2, v___x_6651_);
    v___x_6653_ = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(
        v___x_6652_,
        v_a_6645_,
        v_a_6646_,
        v_a_6647_,
        v_a_6648_,
    );
    return v___x_6653_;
}
pub unsafe fn l_Lean_Parser_many1_formatter___boxed(
    mut v_p_6654_: *mut LeanObject,
    mut v_a_6655_: *mut LeanObject,
    mut v_a_6656_: *mut LeanObject,
    mut v_a_6657_: *mut LeanObject,
    mut v_a_6658_: *mut LeanObject,
    mut v_a_6659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6660_: *mut LeanObject = core::ptr::null_mut();
    v_res_6660_ =
        l_Lean_Parser_many1_formatter(v_p_6654_, v_a_6655_, v_a_6656_, v_a_6657_, v_a_6658_);
    lean_dec(v_a_6658_);
    lean_dec_ref(v_a_6657_);
    lean_dec(v_a_6656_);
    lean_dec_ref(v_a_6655_);
    return v_res_6660_;
}
pub unsafe fn l_Lean_Parser_many1_parenthesizer(
    mut v_p_6661_: *mut LeanObject,
    mut v_a_6662_: *mut LeanObject,
    mut v_a_6663_: *mut LeanObject,
    mut v_a_6664_: *mut LeanObject,
    mut v_a_6665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    v___x_6667_ = l_Lean_Parser_many_formatter___closed__1;
    v___x_6668_ = l_Lean_Parser_many_parenthesizer___closed__0;
    v___x_6669_ = lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_6669_, 0, v___x_6667_);
    lean_closure_set(v___x_6669_, 1, v_p_6661_);
    lean_closure_set(v___x_6669_, 2, v___x_6668_);
    v___x_6670_ = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(
        v___x_6669_,
        v_a_6662_,
        v_a_6663_,
        v_a_6664_,
        v_a_6665_,
    );
    return v___x_6670_;
}
pub unsafe fn l_Lean_Parser_many1_parenthesizer___boxed(
    mut v_p_6671_: *mut LeanObject,
    mut v_a_6672_: *mut LeanObject,
    mut v_a_6673_: *mut LeanObject,
    mut v_a_6674_: *mut LeanObject,
    mut v_a_6675_: *mut LeanObject,
    mut v_a_6676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6677_: *mut LeanObject = core::ptr::null_mut();
    v_res_6677_ =
        l_Lean_Parser_many1_parenthesizer(v_p_6671_, v_a_6672_, v_a_6673_, v_a_6674_, v_a_6675_);
    lean_dec(v_a_6675_);
    lean_dec_ref(v_a_6674_);
    lean_dec(v_a_6673_);
    lean_dec_ref(v_a_6672_);
    return v_res_6677_;
}
pub unsafe fn l_Lean_Parser_many1(mut v_p_6678_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    v___x_6679_ = l_Lean_Parser_many_formatter___closed__1;
    v___x_6680_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_many___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_many___closed__0_once),
        _init_l_Lean_Parser_many___closed__0,
    );
    v___x_6681_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_6679_, v_p_6678_, v___x_6680_);
    v___x_6682_ = l_Lean_Parser_many1NoAntiquot(v___x_6681_);
    return v___x_6682_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1()
-> *mut LeanObject {
    let mut v___x_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    v___x_6690_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1;
    v___x_6691_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2;
    v___x_6692_ = l_Lean_addBuiltinDocString(v___x_6690_, v___x_6691_);
    return v___x_6692_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___boxed(
    mut v_a_6693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6694_: *mut LeanObject = core::ptr::null_mut();
    v_res_6694_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1();
    return v_res_6694_;
}
pub unsafe fn l_Lean_Parser_ident_formatter(
    mut v_a_6705_: *mut LeanObject,
    mut v_a_6706_: *mut LeanObject,
    mut v_a_6707_: *mut LeanObject,
    mut v_a_6708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut LeanObject = core::ptr::null_mut();
    v___x_6710_ = l_Lean_Parser_ident_formatter___closed__2;
    v___x_6711_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_6712_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_6710_,
        v___x_6711_,
        v_a_6705_,
        v_a_6706_,
        v_a_6707_,
        v_a_6708_,
    );
    return v___x_6712_;
}
pub unsafe fn l_Lean_Parser_ident_formatter___boxed(
    mut v_a_6713_: *mut LeanObject,
    mut v_a_6714_: *mut LeanObject,
    mut v_a_6715_: *mut LeanObject,
    mut v_a_6716_: *mut LeanObject,
    mut v_a_6717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6718_: *mut LeanObject = core::ptr::null_mut();
    v_res_6718_ = l_Lean_Parser_ident_formatter(v_a_6713_, v_a_6714_, v_a_6715_, v_a_6716_);
    lean_dec(v_a_6716_);
    lean_dec_ref(v_a_6715_);
    lean_dec(v_a_6714_);
    lean_dec_ref(v_a_6713_);
    return v_res_6718_;
}
pub unsafe fn l_Lean_Parser_ident_parenthesizer(
    mut v_a_6726_: *mut LeanObject,
    mut v_a_6727_: *mut LeanObject,
    mut v_a_6728_: *mut LeanObject,
    mut v_a_6729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut LeanObject = core::ptr::null_mut();
    v___x_6731_ = l_Lean_Parser_ident_parenthesizer___closed__0;
    v___x_6732_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_6733_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_6731_,
        v___x_6732_,
        v_a_6726_,
        v_a_6727_,
        v_a_6728_,
        v_a_6729_,
    );
    return v___x_6733_;
}
pub unsafe fn l_Lean_Parser_ident_parenthesizer___boxed(
    mut v_a_6734_: *mut LeanObject,
    mut v_a_6735_: *mut LeanObject,
    mut v_a_6736_: *mut LeanObject,
    mut v_a_6737_: *mut LeanObject,
    mut v_a_6738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6739_: *mut LeanObject = core::ptr::null_mut();
    v_res_6739_ = l_Lean_Parser_ident_parenthesizer(v_a_6734_, v_a_6735_, v_a_6736_, v_a_6737_);
    lean_dec(v_a_6737_);
    lean_dec_ref(v_a_6736_);
    lean_dec(v_a_6735_);
    lean_dec_ref(v_a_6734_);
    return v_res_6739_;
}
pub unsafe fn _init_l_Lean_Parser_ident___closed__0() -> *mut LeanObject {
    let mut v___x_6740_: u8 = 0;
    let mut v___x_6741_: u8 = 0;
    let mut v___x_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut LeanObject = core::ptr::null_mut();
    v___x_6740_ = 0;
    v___x_6741_ = 1;
    v___x_6742_ = l_Lean_Parser_ident_formatter___closed__1;
    v___x_6743_ = l_Lean_Parser_ident_formatter___closed__0;
    v___x_6744_ = l_Lean_Parser_mkAntiquot(v___x_6743_, v___x_6742_, v___x_6741_, v___x_6740_);
    return v___x_6744_;
}
pub unsafe fn _init_l_Lean_Parser_ident___closed__1() -> *mut LeanObject {
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut LeanObject = core::ptr::null_mut();
    v___x_6745_ = l_Lean_Parser_identNoAntiquot;
    v___x_6746_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_ident___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_ident___closed__0_once),
        _init_l_Lean_Parser_ident___closed__0,
    );
    v___x_6747_ = l_Lean_Parser_withAntiquot(v___x_6746_, v___x_6745_);
    return v___x_6747_;
}
pub unsafe fn _init_l_Lean_Parser_ident() -> *mut LeanObject {
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    v___x_6748_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_ident___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_ident___closed__1_once),
        _init_l_Lean_Parser_ident___closed__1,
    );
    return v___x_6748_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1()
-> *mut LeanObject {
    let mut v___x_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut LeanObject = core::ptr::null_mut();
    v___x_6755_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0;
    v___x_6756_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1;
    v___x_6757_ = l_Lean_addBuiltinDocString(v___x_6755_, v___x_6756_);
    return v___x_6757_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___boxed(
    mut v_a_6758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6759_: *mut LeanObject = core::ptr::null_mut();
    v_res_6759_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1();
    return v_res_6759_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2()
-> *mut LeanObject {
    let mut v___x_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut LeanObject = core::ptr::null_mut();
    v___x_6763_ = lean_alloc_closure(
        l_Lean_Parser_ident_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___f_6764_ = l_Lean_Parser_mkAntiquot_formatter___closed__0;
    v___x_6765_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_6765_, 0, v___f_6764_);
    lean_closure_set(v___x_6765_, 1, v___x_6763_);
    return v___x_6765_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3()
-> *mut LeanObject {
    let mut v___x_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    v___x_6766_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2_once
        ),
        _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2,
    );
    v___x_6767_ = l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1;
    v___x_6768_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_6768_, 0, v___x_6767_);
    lean_closure_set(v___x_6768_, 1, v___x_6766_);
    return v___x_6768_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4()
-> *mut LeanObject {
    let mut v___x_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    v___x_6769_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3_once
        ),
        _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3,
    );
    v___f_6770_ = l_Lean_Parser_mkAntiquot_formatter___closed__0;
    v___x_6771_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_6771_, 0, v___f_6770_);
    lean_closure_set(v___x_6771_, 1, v___x_6769_);
    return v___x_6771_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5()
-> *mut LeanObject {
    let mut v___x_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    v___x_6772_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4_once
        ),
        _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4,
    );
    v___x_6773_ = lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_6773_, 0, v___x_6772_);
    return v___x_6773_;
}
pub unsafe fn l_Lean_Parser_identWithPartialTrailingDot_formatter(
    mut v_a_6774_: *mut LeanObject,
    mut v_a_6775_: *mut LeanObject,
    mut v_a_6776_: *mut LeanObject,
    mut v_a_6777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut LeanObject = core::ptr::null_mut();
    v___x_6779_ = lean_alloc_closure(
        l_Lean_Parser_ident_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_6780_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5_once
        ),
        _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5,
    );
    v___x_6781_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(
        v___x_6779_,
        v___x_6780_,
        v_a_6774_,
        v_a_6775_,
        v_a_6776_,
        v_a_6777_,
    );
    return v___x_6781_;
}
pub unsafe fn l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed(
    mut v_a_6782_: *mut LeanObject,
    mut v_a_6783_: *mut LeanObject,
    mut v_a_6784_: *mut LeanObject,
    mut v_a_6785_: *mut LeanObject,
    mut v_a_6786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6787_: *mut LeanObject = core::ptr::null_mut();
    v_res_6787_ = l_Lean_Parser_identWithPartialTrailingDot_formatter(
        v_a_6782_, v_a_6783_, v_a_6784_, v_a_6785_,
    );
    lean_dec(v_a_6785_);
    lean_dec_ref(v_a_6784_);
    lean_dec(v_a_6783_);
    lean_dec_ref(v_a_6782_);
    return v_res_6787_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1()
-> *mut LeanObject {
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut LeanObject = core::ptr::null_mut();
    v___x_6790_ = lean_alloc_closure(
        l_Lean_Parser_ident_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_6791_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_6792_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_6792_, 0, v___x_6791_);
    lean_closure_set(v___x_6792_, 1, v___x_6790_);
    return v___x_6792_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2()
-> *mut LeanObject {
    let mut v___x_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut LeanObject = core::ptr::null_mut();
    v___x_6793_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1_once
        ),
        _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1,
    );
    v___x_6794_ = l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0;
    v___x_6795_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_6795_, 0, v___x_6794_);
    lean_closure_set(v___x_6795_, 1, v___x_6793_);
    return v___x_6795_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3()
-> *mut LeanObject {
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut LeanObject = core::ptr::null_mut();
    v___x_6796_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2_once
        ),
        _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2,
    );
    v___x_6797_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_6798_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_6798_, 0, v___x_6797_);
    lean_closure_set(v___x_6798_, 1, v___x_6796_);
    return v___x_6798_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4()
-> *mut LeanObject {
    let mut v___x_6799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut LeanObject = core::ptr::null_mut();
    v___x_6799_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3_once
        ),
        _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3,
    );
    v___x_6800_ = lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_6800_, 0, v___x_6799_);
    return v___x_6800_;
}
pub unsafe fn l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(
    mut v_a_6801_: *mut LeanObject,
    mut v_a_6802_: *mut LeanObject,
    mut v_a_6803_: *mut LeanObject,
    mut v_a_6804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    v___x_6806_ = lean_alloc_closure(
        l_Lean_Parser_ident_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_6807_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4_once
        ),
        _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4,
    );
    v___x_6808_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(
        v___x_6806_,
        v___x_6807_,
        v_a_6801_,
        v_a_6802_,
        v_a_6803_,
        v_a_6804_,
    );
    return v___x_6808_;
}
pub unsafe fn l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed(
    mut v_a_6809_: *mut LeanObject,
    mut v_a_6810_: *mut LeanObject,
    mut v_a_6811_: *mut LeanObject,
    mut v_a_6812_: *mut LeanObject,
    mut v_a_6813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6814_: *mut LeanObject = core::ptr::null_mut();
    v_res_6814_ = l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(
        v_a_6809_, v_a_6810_, v_a_6811_, v_a_6812_,
    );
    lean_dec(v_a_6812_);
    lean_dec_ref(v_a_6811_);
    lean_dec(v_a_6810_);
    lean_dec_ref(v_a_6809_);
    return v_res_6814_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot___closed__1() -> *mut LeanObject {
    let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut LeanObject = core::ptr::null_mut();
    v___x_6816_ = l_Lean_Parser_identWithPartialTrailingDot___closed__0;
    v___x_6817_ = l_Lean_Parser_checkNoWsBefore(v___x_6816_);
    return v___x_6817_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot___closed__2() -> *mut LeanObject {
    let mut v___x_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut LeanObject = core::ptr::null_mut();
    v___x_6818_ = l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0;
    v___x_6819_ = l_Lean_Parser_symbol(v___x_6818_);
    return v___x_6819_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot___closed__3() -> *mut LeanObject {
    let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut LeanObject = core::ptr::null_mut();
    v___x_6820_ = l_Lean_Parser_ident;
    v___x_6821_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__1_once),
        _init_l_Lean_Parser_identWithPartialTrailingDot___closed__1,
    );
    v___x_6822_ = l_Lean_Parser_andthen(v___x_6821_, v___x_6820_);
    return v___x_6822_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot___closed__4() -> *mut LeanObject {
    let mut v___x_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    v___x_6823_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__3_once),
        _init_l_Lean_Parser_identWithPartialTrailingDot___closed__3,
    );
    v___x_6824_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__2_once),
        _init_l_Lean_Parser_identWithPartialTrailingDot___closed__2,
    );
    v___x_6825_ = l_Lean_Parser_andthen(v___x_6824_, v___x_6823_);
    return v___x_6825_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot___closed__5() -> *mut LeanObject {
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    v___x_6826_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__4_once),
        _init_l_Lean_Parser_identWithPartialTrailingDot___closed__4,
    );
    v___x_6827_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__1_once),
        _init_l_Lean_Parser_identWithPartialTrailingDot___closed__1,
    );
    v___x_6828_ = l_Lean_Parser_andthen(v___x_6827_, v___x_6826_);
    return v___x_6828_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot___closed__6() -> *mut LeanObject {
    let mut v___x_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut LeanObject = core::ptr::null_mut();
    v___x_6829_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__5_once),
        _init_l_Lean_Parser_identWithPartialTrailingDot___closed__5,
    );
    v___x_6830_ = l_Lean_Parser_optional(v___x_6829_);
    return v___x_6830_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot___closed__7() -> *mut LeanObject {
    let mut v___x_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut LeanObject = core::ptr::null_mut();
    v___x_6831_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__6_once),
        _init_l_Lean_Parser_identWithPartialTrailingDot___closed__6,
    );
    v___x_6832_ = l_Lean_Parser_ident;
    v___x_6833_ = l_Lean_Parser_andthen(v___x_6832_, v___x_6831_);
    return v___x_6833_;
}
pub unsafe fn _init_l_Lean_Parser_identWithPartialTrailingDot() -> *mut LeanObject {
    let mut v___x_6834_: *mut LeanObject = core::ptr::null_mut();
    v___x_6834_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_identWithPartialTrailingDot___closed__7_once),
        _init_l_Lean_Parser_identWithPartialTrailingDot___closed__7,
    );
    return v___x_6834_;
}
pub unsafe fn l_Lean_Parser_rawIdent_formatter(
    mut v_a_6835_: *mut LeanObject,
    mut v_a_6836_: *mut LeanObject,
    mut v_a_6837_: *mut LeanObject,
    mut v_a_6838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut LeanObject = core::ptr::null_mut();
    v___x_6840_ = l_Lean_Parser_ident_formatter___closed__2;
    v___x_6841_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_6842_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_6840_,
        v___x_6841_,
        v_a_6835_,
        v_a_6836_,
        v_a_6837_,
        v_a_6838_,
    );
    return v___x_6842_;
}
pub unsafe fn l_Lean_Parser_rawIdent_formatter___boxed(
    mut v_a_6843_: *mut LeanObject,
    mut v_a_6844_: *mut LeanObject,
    mut v_a_6845_: *mut LeanObject,
    mut v_a_6846_: *mut LeanObject,
    mut v_a_6847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6848_: *mut LeanObject = core::ptr::null_mut();
    v_res_6848_ = l_Lean_Parser_rawIdent_formatter(v_a_6843_, v_a_6844_, v_a_6845_, v_a_6846_);
    lean_dec(v_a_6846_);
    lean_dec_ref(v_a_6845_);
    lean_dec(v_a_6844_);
    lean_dec_ref(v_a_6843_);
    return v_res_6848_;
}
pub unsafe fn l_Lean_Parser_rawIdent_parenthesizer___lam__0(
    mut v___y_6849_: *mut LeanObject,
    mut v___y_6850_: *mut LeanObject,
    mut v___y_6851_: *mut LeanObject,
    mut v___y_6852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6854_: *mut LeanObject = core::ptr::null_mut();
    v___x_6854_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_6850_);
    return v___x_6854_;
}
pub unsafe fn l_Lean_Parser_rawIdent_parenthesizer___lam__0___boxed(
    mut v___y_6855_: *mut LeanObject,
    mut v___y_6856_: *mut LeanObject,
    mut v___y_6857_: *mut LeanObject,
    mut v___y_6858_: *mut LeanObject,
    mut v___y_6859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6860_: *mut LeanObject = core::ptr::null_mut();
    v_res_6860_ = l_Lean_Parser_rawIdent_parenthesizer___lam__0(
        v___y_6855_,
        v___y_6856_,
        v___y_6857_,
        v___y_6858_,
    );
    lean_dec(v___y_6858_);
    lean_dec_ref(v___y_6857_);
    lean_dec(v___y_6856_);
    lean_dec_ref(v___y_6855_);
    return v_res_6860_;
}
pub unsafe fn l_Lean_Parser_rawIdent_parenthesizer(
    mut v_a_6862_: *mut LeanObject,
    mut v_a_6863_: *mut LeanObject,
    mut v_a_6864_: *mut LeanObject,
    mut v_a_6865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut LeanObject = core::ptr::null_mut();
    v___f_6867_ = l_Lean_Parser_rawIdent_parenthesizer___closed__0;
    v___x_6868_ = l_Lean_Parser_ident_parenthesizer___closed__0;
    v___x_6869_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_6868_,
        v___f_6867_,
        v_a_6862_,
        v_a_6863_,
        v_a_6864_,
        v_a_6865_,
    );
    return v___x_6869_;
}
pub unsafe fn l_Lean_Parser_rawIdent_parenthesizer___boxed(
    mut v_a_6870_: *mut LeanObject,
    mut v_a_6871_: *mut LeanObject,
    mut v_a_6872_: *mut LeanObject,
    mut v_a_6873_: *mut LeanObject,
    mut v_a_6874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6875_: *mut LeanObject = core::ptr::null_mut();
    v_res_6875_ = l_Lean_Parser_rawIdent_parenthesizer(v_a_6870_, v_a_6871_, v_a_6872_, v_a_6873_);
    lean_dec(v_a_6873_);
    lean_dec_ref(v_a_6872_);
    lean_dec(v_a_6871_);
    lean_dec_ref(v_a_6870_);
    return v_res_6875_;
}
pub unsafe fn _init_l_Lean_Parser_rawIdent___closed__0() -> *mut LeanObject {
    let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
    v___x_6876_ = l_Lean_Parser_rawIdentNoAntiquot;
    v___x_6877_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_ident___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_ident___closed__0_once),
        _init_l_Lean_Parser_ident___closed__0,
    );
    v___x_6878_ = l_Lean_Parser_withAntiquot(v___x_6877_, v___x_6876_);
    return v___x_6878_;
}
pub unsafe fn _init_l_Lean_Parser_rawIdent() -> *mut LeanObject {
    let mut v___x_6879_: *mut LeanObject = core::ptr::null_mut();
    v___x_6879_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_rawIdent___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_rawIdent___closed__0_once),
        _init_l_Lean_Parser_rawIdent___closed__0,
    );
    return v___x_6879_;
}
pub unsafe fn l_Lean_Parser_hygieneInfo_formatter(
    mut v_a_6889_: *mut LeanObject,
    mut v_a_6890_: *mut LeanObject,
    mut v_a_6891_: *mut LeanObject,
    mut v_a_6892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
    v___f_6894_ = l_Lean_Parser_mkAntiquot_formatter___closed__1;
    v___x_6895_ = l_Lean_Parser_hygieneInfo_formatter___closed__2;
    v___x_6896_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_6895_,
        v___f_6894_,
        v_a_6889_,
        v_a_6890_,
        v_a_6891_,
        v_a_6892_,
    );
    return v___x_6896_;
}
pub unsafe fn l_Lean_Parser_hygieneInfo_formatter___boxed(
    mut v_a_6897_: *mut LeanObject,
    mut v_a_6898_: *mut LeanObject,
    mut v_a_6899_: *mut LeanObject,
    mut v_a_6900_: *mut LeanObject,
    mut v_a_6901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6902_: *mut LeanObject = core::ptr::null_mut();
    v_res_6902_ = l_Lean_Parser_hygieneInfo_formatter(v_a_6897_, v_a_6898_, v_a_6899_, v_a_6900_);
    lean_dec(v_a_6900_);
    lean_dec_ref(v_a_6899_);
    lean_dec(v_a_6898_);
    lean_dec_ref(v_a_6897_);
    return v_res_6902_;
}
pub unsafe fn l_Lean_Parser_hygieneInfo_parenthesizer(
    mut v_a_6909_: *mut LeanObject,
    mut v_a_6910_: *mut LeanObject,
    mut v_a_6911_: *mut LeanObject,
    mut v_a_6912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut LeanObject = core::ptr::null_mut();
    v___f_6914_ = l_Lean_Parser_mkAntiquot_parenthesizer___closed__0;
    v___x_6915_ = l_Lean_Parser_hygieneInfo_parenthesizer___closed__0;
    v___x_6916_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_6915_,
        v___f_6914_,
        v_a_6909_,
        v_a_6910_,
        v_a_6911_,
        v_a_6912_,
    );
    return v___x_6916_;
}
pub unsafe fn l_Lean_Parser_hygieneInfo_parenthesizer___boxed(
    mut v_a_6917_: *mut LeanObject,
    mut v_a_6918_: *mut LeanObject,
    mut v_a_6919_: *mut LeanObject,
    mut v_a_6920_: *mut LeanObject,
    mut v_a_6921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6922_: *mut LeanObject = core::ptr::null_mut();
    v_res_6922_ =
        l_Lean_Parser_hygieneInfo_parenthesizer(v_a_6917_, v_a_6918_, v_a_6919_, v_a_6920_);
    lean_dec(v_a_6920_);
    lean_dec_ref(v_a_6919_);
    lean_dec(v_a_6918_);
    lean_dec_ref(v_a_6917_);
    return v_res_6922_;
}
pub unsafe fn _init_l_Lean_Parser_hygieneInfo___closed__0() -> *mut LeanObject {
    let mut v___x_6923_: u8 = 0;
    let mut v___x_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
    v___x_6923_ = 0;
    v___x_6924_ = l_Lean_Parser_hygieneInfo_formatter___closed__1;
    v___x_6925_ = l_Lean_Parser_hygieneInfo_formatter___closed__0;
    v___x_6926_ = l_Lean_Parser_mkAntiquot(v___x_6925_, v___x_6924_, v___x_6923_, v___x_6923_);
    return v___x_6926_;
}
pub unsafe fn _init_l_Lean_Parser_hygieneInfo___closed__1() -> *mut LeanObject {
    let mut v___x_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut LeanObject = core::ptr::null_mut();
    v___x_6927_ = l_Lean_Parser_hygieneInfoNoAntiquot;
    v___x_6928_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_hygieneInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_hygieneInfo___closed__0_once),
        _init_l_Lean_Parser_hygieneInfo___closed__0,
    );
    v___x_6929_ = l_Lean_Parser_withAntiquot(v___x_6928_, v___x_6927_);
    return v___x_6929_;
}
pub unsafe fn _init_l_Lean_Parser_hygieneInfo() -> *mut LeanObject {
    let mut v___x_6930_: *mut LeanObject = core::ptr::null_mut();
    v___x_6930_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_hygieneInfo___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_hygieneInfo___closed__1_once),
        _init_l_Lean_Parser_hygieneInfo___closed__1,
    );
    return v___x_6930_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1()
-> *mut LeanObject {
    let mut v___x_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: *mut LeanObject = core::ptr::null_mut();
    v___x_6937_ = l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0;
    v___x_6938_ = l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1;
    v___x_6939_ = l_Lean_addBuiltinDocString(v___x_6937_, v___x_6938_);
    return v___x_6939_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___boxed(
    mut v_a_6940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6941_: *mut LeanObject = core::ptr::null_mut();
    v_res_6941_ = l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1();
    return v_res_6941_;
}
pub unsafe fn l_Lean_Parser_numLit_formatter(
    mut v_a_6952_: *mut LeanObject,
    mut v_a_6953_: *mut LeanObject,
    mut v_a_6954_: *mut LeanObject,
    mut v_a_6955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    v___x_6957_ = l_Lean_Parser_numLit_formatter___closed__2;
    v___x_6958_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_6959_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_6957_,
        v___x_6958_,
        v_a_6952_,
        v_a_6953_,
        v_a_6954_,
        v_a_6955_,
    );
    return v___x_6959_;
}
pub unsafe fn l_Lean_Parser_numLit_formatter___boxed(
    mut v_a_6960_: *mut LeanObject,
    mut v_a_6961_: *mut LeanObject,
    mut v_a_6962_: *mut LeanObject,
    mut v_a_6963_: *mut LeanObject,
    mut v_a_6964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6965_: *mut LeanObject = core::ptr::null_mut();
    v_res_6965_ = l_Lean_Parser_numLit_formatter(v_a_6960_, v_a_6961_, v_a_6962_, v_a_6963_);
    lean_dec(v_a_6963_);
    lean_dec_ref(v_a_6962_);
    lean_dec(v_a_6961_);
    lean_dec_ref(v_a_6960_);
    return v_res_6965_;
}
pub unsafe fn l_Lean_Parser_numLit_parenthesizer(
    mut v_a_6973_: *mut LeanObject,
    mut v_a_6974_: *mut LeanObject,
    mut v_a_6975_: *mut LeanObject,
    mut v_a_6976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut LeanObject = core::ptr::null_mut();
    v___f_6978_ = l_Lean_Parser_rawIdent_parenthesizer___closed__0;
    v___x_6979_ = l_Lean_Parser_numLit_parenthesizer___closed__0;
    v___x_6980_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_6979_,
        v___f_6978_,
        v_a_6973_,
        v_a_6974_,
        v_a_6975_,
        v_a_6976_,
    );
    return v___x_6980_;
}
pub unsafe fn l_Lean_Parser_numLit_parenthesizer___boxed(
    mut v_a_6981_: *mut LeanObject,
    mut v_a_6982_: *mut LeanObject,
    mut v_a_6983_: *mut LeanObject,
    mut v_a_6984_: *mut LeanObject,
    mut v_a_6985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6986_: *mut LeanObject = core::ptr::null_mut();
    v_res_6986_ = l_Lean_Parser_numLit_parenthesizer(v_a_6981_, v_a_6982_, v_a_6983_, v_a_6984_);
    lean_dec(v_a_6984_);
    lean_dec_ref(v_a_6983_);
    lean_dec(v_a_6982_);
    lean_dec_ref(v_a_6981_);
    return v_res_6986_;
}
pub unsafe fn _init_l_Lean_Parser_numLit___closed__0() -> *mut LeanObject {
    let mut v___x_6987_: u8 = 0;
    let mut v___x_6988_: u8 = 0;
    let mut v___x_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut LeanObject = core::ptr::null_mut();
    v___x_6987_ = 0;
    v___x_6988_ = 1;
    v___x_6989_ = l_Lean_Parser_numLit_formatter___closed__1;
    v___x_6990_ = l_Lean_Parser_numLit_formatter___closed__0;
    v___x_6991_ = l_Lean_Parser_mkAntiquot(v___x_6990_, v___x_6989_, v___x_6988_, v___x_6987_);
    return v___x_6991_;
}
pub unsafe fn _init_l_Lean_Parser_numLit___closed__1() -> *mut LeanObject {
    let mut v___x_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    v___x_6992_ = l_Lean_Parser_numLitNoAntiquot;
    v___x_6993_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_numLit___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_numLit___closed__0_once),
        _init_l_Lean_Parser_numLit___closed__0,
    );
    v___x_6994_ = l_Lean_Parser_withAntiquot(v___x_6993_, v___x_6992_);
    return v___x_6994_;
}
pub unsafe fn _init_l_Lean_Parser_numLit() -> *mut LeanObject {
    let mut v___x_6995_: *mut LeanObject = core::ptr::null_mut();
    v___x_6995_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_numLit___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_numLit___closed__1_once),
        _init_l_Lean_Parser_numLit___closed__1,
    );
    return v___x_6995_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1()
-> *mut LeanObject {
    let mut v___x_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    v___x_7003_ = l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1;
    v___x_7004_ = l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2;
    v___x_7005_ = l_Lean_addBuiltinDocString(v___x_7003_, v___x_7004_);
    return v___x_7005_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___boxed(
    mut v_a_7006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7007_: *mut LeanObject = core::ptr::null_mut();
    v_res_7007_ = l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1();
    return v_res_7007_;
}
pub unsafe fn _init_l_Lean_Parser_hexnum___closed__2() -> *mut LeanObject {
    let mut v___x_7011_: u8 = 0;
    let mut v___x_7012_: u8 = 0;
    let mut v___x_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut LeanObject = core::ptr::null_mut();
    v___x_7011_ = 0;
    v___x_7012_ = 1;
    v___x_7013_ = l_Lean_Parser_hexnum___closed__1;
    v___x_7014_ = l_Lean_Parser_hexnum___closed__0;
    v___x_7015_ = l_Lean_Parser_mkAntiquot(v___x_7014_, v___x_7013_, v___x_7012_, v___x_7011_);
    return v___x_7015_;
}
pub unsafe fn _init_l_Lean_Parser_hexnum___closed__3() -> *mut LeanObject {
    let mut v___x_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut LeanObject = core::ptr::null_mut();
    v___x_7016_ = l_Lean_Parser_hexnumNoAntiquot;
    v___x_7017_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_hexnum___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_hexnum___closed__2_once),
        _init_l_Lean_Parser_hexnum___closed__2,
    );
    v___x_7018_ = l_Lean_Parser_withAntiquot(v___x_7017_, v___x_7016_);
    return v___x_7018_;
}
pub unsafe fn _init_l_Lean_Parser_hexnum() -> *mut LeanObject {
    let mut v___x_7019_: *mut LeanObject = core::ptr::null_mut();
    v___x_7019_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_hexnum___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_hexnum___closed__3_once),
        _init_l_Lean_Parser_hexnum___closed__3,
    );
    return v___x_7019_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1()
-> *mut LeanObject {
    let mut v___x_7026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: *mut LeanObject = core::ptr::null_mut();
    v___x_7026_ = l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0;
    v___x_7027_ = l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1;
    v___x_7028_ = l_Lean_addBuiltinDocString(v___x_7026_, v___x_7027_);
    return v___x_7028_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___boxed(
    mut v_a_7029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7030_: *mut LeanObject = core::ptr::null_mut();
    v_res_7030_ = l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1();
    return v_res_7030_;
}
pub unsafe fn l_Lean_Parser_scientificLit_formatter(
    mut v_a_7041_: *mut LeanObject,
    mut v_a_7042_: *mut LeanObject,
    mut v_a_7043_: *mut LeanObject,
    mut v_a_7044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut LeanObject = core::ptr::null_mut();
    v___x_7046_ = l_Lean_Parser_scientificLit_formatter___closed__2;
    v___x_7047_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7048_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_7046_,
        v___x_7047_,
        v_a_7041_,
        v_a_7042_,
        v_a_7043_,
        v_a_7044_,
    );
    return v___x_7048_;
}
pub unsafe fn l_Lean_Parser_scientificLit_formatter___boxed(
    mut v_a_7049_: *mut LeanObject,
    mut v_a_7050_: *mut LeanObject,
    mut v_a_7051_: *mut LeanObject,
    mut v_a_7052_: *mut LeanObject,
    mut v_a_7053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7054_: *mut LeanObject = core::ptr::null_mut();
    v_res_7054_ = l_Lean_Parser_scientificLit_formatter(v_a_7049_, v_a_7050_, v_a_7051_, v_a_7052_);
    lean_dec(v_a_7052_);
    lean_dec_ref(v_a_7051_);
    lean_dec(v_a_7050_);
    lean_dec_ref(v_a_7049_);
    return v_res_7054_;
}
pub unsafe fn l_Lean_Parser_scientificLit_parenthesizer(
    mut v_a_7062_: *mut LeanObject,
    mut v_a_7063_: *mut LeanObject,
    mut v_a_7064_: *mut LeanObject,
    mut v_a_7065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut LeanObject = core::ptr::null_mut();
    v___f_7067_ = l_Lean_Parser_rawIdent_parenthesizer___closed__0;
    v___x_7068_ = l_Lean_Parser_scientificLit_parenthesizer___closed__0;
    v___x_7069_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_7068_,
        v___f_7067_,
        v_a_7062_,
        v_a_7063_,
        v_a_7064_,
        v_a_7065_,
    );
    return v___x_7069_;
}
pub unsafe fn l_Lean_Parser_scientificLit_parenthesizer___boxed(
    mut v_a_7070_: *mut LeanObject,
    mut v_a_7071_: *mut LeanObject,
    mut v_a_7072_: *mut LeanObject,
    mut v_a_7073_: *mut LeanObject,
    mut v_a_7074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7075_: *mut LeanObject = core::ptr::null_mut();
    v_res_7075_ =
        l_Lean_Parser_scientificLit_parenthesizer(v_a_7070_, v_a_7071_, v_a_7072_, v_a_7073_);
    lean_dec(v_a_7073_);
    lean_dec_ref(v_a_7072_);
    lean_dec(v_a_7071_);
    lean_dec_ref(v_a_7070_);
    return v_res_7075_;
}
pub unsafe fn _init_l_Lean_Parser_scientificLit___closed__0() -> *mut LeanObject {
    let mut v___x_7076_: u8 = 0;
    let mut v___x_7077_: u8 = 0;
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    v___x_7076_ = 0;
    v___x_7077_ = 1;
    v___x_7078_ = l_Lean_Parser_scientificLit_formatter___closed__1;
    v___x_7079_ = l_Lean_Parser_scientificLit_formatter___closed__0;
    v___x_7080_ = l_Lean_Parser_mkAntiquot(v___x_7079_, v___x_7078_, v___x_7077_, v___x_7076_);
    return v___x_7080_;
}
pub unsafe fn _init_l_Lean_Parser_scientificLit___closed__1() -> *mut LeanObject {
    let mut v___x_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut LeanObject = core::ptr::null_mut();
    v___x_7081_ = l_Lean_Parser_scientificLitNoAntiquot;
    v___x_7082_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_scientificLit___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_scientificLit___closed__0_once),
        _init_l_Lean_Parser_scientificLit___closed__0,
    );
    v___x_7083_ = l_Lean_Parser_withAntiquot(v___x_7082_, v___x_7081_);
    return v___x_7083_;
}
pub unsafe fn _init_l_Lean_Parser_scientificLit() -> *mut LeanObject {
    let mut v___x_7084_: *mut LeanObject = core::ptr::null_mut();
    v___x_7084_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_scientificLit___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_scientificLit___closed__1_once),
        _init_l_Lean_Parser_scientificLit___closed__1,
    );
    return v___x_7084_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1()
-> *mut LeanObject {
    let mut v___x_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    v___x_7092_ = l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1;
    v___x_7093_ = l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2;
    v___x_7094_ = l_Lean_addBuiltinDocString(v___x_7092_, v___x_7093_);
    return v___x_7094_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___boxed(
    mut v_a_7095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7096_: *mut LeanObject = core::ptr::null_mut();
    v_res_7096_ = l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1();
    return v_res_7096_;
}
pub unsafe fn l_Lean_Parser_strLit_formatter(
    mut v_a_7107_: *mut LeanObject,
    mut v_a_7108_: *mut LeanObject,
    mut v_a_7109_: *mut LeanObject,
    mut v_a_7110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut LeanObject = core::ptr::null_mut();
    v___x_7112_ = l_Lean_Parser_strLit_formatter___closed__2;
    v___x_7113_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7114_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_7112_,
        v___x_7113_,
        v_a_7107_,
        v_a_7108_,
        v_a_7109_,
        v_a_7110_,
    );
    return v___x_7114_;
}
pub unsafe fn l_Lean_Parser_strLit_formatter___boxed(
    mut v_a_7115_: *mut LeanObject,
    mut v_a_7116_: *mut LeanObject,
    mut v_a_7117_: *mut LeanObject,
    mut v_a_7118_: *mut LeanObject,
    mut v_a_7119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7120_: *mut LeanObject = core::ptr::null_mut();
    v_res_7120_ = l_Lean_Parser_strLit_formatter(v_a_7115_, v_a_7116_, v_a_7117_, v_a_7118_);
    lean_dec(v_a_7118_);
    lean_dec_ref(v_a_7117_);
    lean_dec(v_a_7116_);
    lean_dec_ref(v_a_7115_);
    return v_res_7120_;
}
pub unsafe fn l_Lean_Parser_strLit_parenthesizer(
    mut v_a_7128_: *mut LeanObject,
    mut v_a_7129_: *mut LeanObject,
    mut v_a_7130_: *mut LeanObject,
    mut v_a_7131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
    v___f_7133_ = l_Lean_Parser_rawIdent_parenthesizer___closed__0;
    v___x_7134_ = l_Lean_Parser_strLit_parenthesizer___closed__0;
    v___x_7135_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_7134_,
        v___f_7133_,
        v_a_7128_,
        v_a_7129_,
        v_a_7130_,
        v_a_7131_,
    );
    return v___x_7135_;
}
pub unsafe fn l_Lean_Parser_strLit_parenthesizer___boxed(
    mut v_a_7136_: *mut LeanObject,
    mut v_a_7137_: *mut LeanObject,
    mut v_a_7138_: *mut LeanObject,
    mut v_a_7139_: *mut LeanObject,
    mut v_a_7140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7141_: *mut LeanObject = core::ptr::null_mut();
    v_res_7141_ = l_Lean_Parser_strLit_parenthesizer(v_a_7136_, v_a_7137_, v_a_7138_, v_a_7139_);
    lean_dec(v_a_7139_);
    lean_dec_ref(v_a_7138_);
    lean_dec(v_a_7137_);
    lean_dec_ref(v_a_7136_);
    return v_res_7141_;
}
pub unsafe fn _init_l_Lean_Parser_strLit___closed__0() -> *mut LeanObject {
    let mut v___x_7142_: u8 = 0;
    let mut v___x_7143_: u8 = 0;
    let mut v___x_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7146_: *mut LeanObject = core::ptr::null_mut();
    v___x_7142_ = 0;
    v___x_7143_ = 1;
    v___x_7144_ = l_Lean_Parser_strLit_formatter___closed__1;
    v___x_7145_ = l_Lean_Parser_strLit_formatter___closed__0;
    v___x_7146_ = l_Lean_Parser_mkAntiquot(v___x_7145_, v___x_7144_, v___x_7143_, v___x_7142_);
    return v___x_7146_;
}
pub unsafe fn _init_l_Lean_Parser_strLit___closed__1() -> *mut LeanObject {
    let mut v___x_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut LeanObject = core::ptr::null_mut();
    v___x_7147_ = l_Lean_Parser_strLitNoAntiquot;
    v___x_7148_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_strLit___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_strLit___closed__0_once),
        _init_l_Lean_Parser_strLit___closed__0,
    );
    v___x_7149_ = l_Lean_Parser_withAntiquot(v___x_7148_, v___x_7147_);
    return v___x_7149_;
}
pub unsafe fn _init_l_Lean_Parser_strLit() -> *mut LeanObject {
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    v___x_7150_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_strLit___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_strLit___closed__1_once),
        _init_l_Lean_Parser_strLit___closed__1,
    );
    return v___x_7150_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1()
-> *mut LeanObject {
    let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
    v___x_7158_ = l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1;
    v___x_7159_ = l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2;
    v___x_7160_ = l_Lean_addBuiltinDocString(v___x_7158_, v___x_7159_);
    return v___x_7160_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___boxed(
    mut v_a_7161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7162_: *mut LeanObject = core::ptr::null_mut();
    v_res_7162_ = l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1();
    return v_res_7162_;
}
pub unsafe fn l_Lean_Parser_charLit_formatter(
    mut v_a_7173_: *mut LeanObject,
    mut v_a_7174_: *mut LeanObject,
    mut v_a_7175_: *mut LeanObject,
    mut v_a_7176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut LeanObject = core::ptr::null_mut();
    v___x_7178_ = l_Lean_Parser_charLit_formatter___closed__2;
    v___x_7179_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7180_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_7178_,
        v___x_7179_,
        v_a_7173_,
        v_a_7174_,
        v_a_7175_,
        v_a_7176_,
    );
    return v___x_7180_;
}
pub unsafe fn l_Lean_Parser_charLit_formatter___boxed(
    mut v_a_7181_: *mut LeanObject,
    mut v_a_7182_: *mut LeanObject,
    mut v_a_7183_: *mut LeanObject,
    mut v_a_7184_: *mut LeanObject,
    mut v_a_7185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7186_: *mut LeanObject = core::ptr::null_mut();
    v_res_7186_ = l_Lean_Parser_charLit_formatter(v_a_7181_, v_a_7182_, v_a_7183_, v_a_7184_);
    lean_dec(v_a_7184_);
    lean_dec_ref(v_a_7183_);
    lean_dec(v_a_7182_);
    lean_dec_ref(v_a_7181_);
    return v_res_7186_;
}
pub unsafe fn l_Lean_Parser_charLit_parenthesizer(
    mut v_a_7194_: *mut LeanObject,
    mut v_a_7195_: *mut LeanObject,
    mut v_a_7196_: *mut LeanObject,
    mut v_a_7197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7201_: *mut LeanObject = core::ptr::null_mut();
    v___f_7199_ = l_Lean_Parser_rawIdent_parenthesizer___closed__0;
    v___x_7200_ = l_Lean_Parser_charLit_parenthesizer___closed__0;
    v___x_7201_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_7200_,
        v___f_7199_,
        v_a_7194_,
        v_a_7195_,
        v_a_7196_,
        v_a_7197_,
    );
    return v___x_7201_;
}
pub unsafe fn l_Lean_Parser_charLit_parenthesizer___boxed(
    mut v_a_7202_: *mut LeanObject,
    mut v_a_7203_: *mut LeanObject,
    mut v_a_7204_: *mut LeanObject,
    mut v_a_7205_: *mut LeanObject,
    mut v_a_7206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7207_: *mut LeanObject = core::ptr::null_mut();
    v_res_7207_ = l_Lean_Parser_charLit_parenthesizer(v_a_7202_, v_a_7203_, v_a_7204_, v_a_7205_);
    lean_dec(v_a_7205_);
    lean_dec_ref(v_a_7204_);
    lean_dec(v_a_7203_);
    lean_dec_ref(v_a_7202_);
    return v_res_7207_;
}
pub unsafe fn _init_l_Lean_Parser_charLit___closed__0() -> *mut LeanObject {
    let mut v___x_7208_: u8 = 0;
    let mut v___x_7209_: u8 = 0;
    let mut v___x_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7212_: *mut LeanObject = core::ptr::null_mut();
    v___x_7208_ = 0;
    v___x_7209_ = 1;
    v___x_7210_ = l_Lean_Parser_charLit_formatter___closed__1;
    v___x_7211_ = l_Lean_Parser_charLit_formatter___closed__0;
    v___x_7212_ = l_Lean_Parser_mkAntiquot(v___x_7211_, v___x_7210_, v___x_7209_, v___x_7208_);
    return v___x_7212_;
}
pub unsafe fn _init_l_Lean_Parser_charLit___closed__1() -> *mut LeanObject {
    let mut v___x_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut LeanObject = core::ptr::null_mut();
    v___x_7213_ = l_Lean_Parser_charLitNoAntiquot;
    v___x_7214_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_charLit___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_charLit___closed__0_once),
        _init_l_Lean_Parser_charLit___closed__0,
    );
    v___x_7215_ = l_Lean_Parser_withAntiquot(v___x_7214_, v___x_7213_);
    return v___x_7215_;
}
pub unsafe fn _init_l_Lean_Parser_charLit() -> *mut LeanObject {
    let mut v___x_7216_: *mut LeanObject = core::ptr::null_mut();
    v___x_7216_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_charLit___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_charLit___closed__1_once),
        _init_l_Lean_Parser_charLit___closed__1,
    );
    return v___x_7216_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1()
-> *mut LeanObject {
    let mut v___x_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7226_: *mut LeanObject = core::ptr::null_mut();
    v___x_7224_ = l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1;
    v___x_7225_ = l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2;
    v___x_7226_ = l_Lean_addBuiltinDocString(v___x_7224_, v___x_7225_);
    return v___x_7226_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___boxed(
    mut v_a_7227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7228_: *mut LeanObject = core::ptr::null_mut();
    v_res_7228_ = l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1();
    return v_res_7228_;
}
pub unsafe fn l_Lean_Parser_nameLit_formatter(
    mut v_a_7239_: *mut LeanObject,
    mut v_a_7240_: *mut LeanObject,
    mut v_a_7241_: *mut LeanObject,
    mut v_a_7242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7246_: *mut LeanObject = core::ptr::null_mut();
    v___x_7244_ = l_Lean_Parser_nameLit_formatter___closed__2;
    v___x_7245_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7246_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_7244_,
        v___x_7245_,
        v_a_7239_,
        v_a_7240_,
        v_a_7241_,
        v_a_7242_,
    );
    return v___x_7246_;
}
pub unsafe fn l_Lean_Parser_nameLit_formatter___boxed(
    mut v_a_7247_: *mut LeanObject,
    mut v_a_7248_: *mut LeanObject,
    mut v_a_7249_: *mut LeanObject,
    mut v_a_7250_: *mut LeanObject,
    mut v_a_7251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7252_: *mut LeanObject = core::ptr::null_mut();
    v_res_7252_ = l_Lean_Parser_nameLit_formatter(v_a_7247_, v_a_7248_, v_a_7249_, v_a_7250_);
    lean_dec(v_a_7250_);
    lean_dec_ref(v_a_7249_);
    lean_dec(v_a_7248_);
    lean_dec_ref(v_a_7247_);
    return v_res_7252_;
}
pub unsafe fn l_Lean_Parser_nameLit_parenthesizer(
    mut v_a_7260_: *mut LeanObject,
    mut v_a_7261_: *mut LeanObject,
    mut v_a_7262_: *mut LeanObject,
    mut v_a_7263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: *mut LeanObject = core::ptr::null_mut();
    v___f_7265_ = l_Lean_Parser_rawIdent_parenthesizer___closed__0;
    v___x_7266_ = l_Lean_Parser_nameLit_parenthesizer___closed__0;
    v___x_7267_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_7266_,
        v___f_7265_,
        v_a_7260_,
        v_a_7261_,
        v_a_7262_,
        v_a_7263_,
    );
    return v___x_7267_;
}
pub unsafe fn l_Lean_Parser_nameLit_parenthesizer___boxed(
    mut v_a_7268_: *mut LeanObject,
    mut v_a_7269_: *mut LeanObject,
    mut v_a_7270_: *mut LeanObject,
    mut v_a_7271_: *mut LeanObject,
    mut v_a_7272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7273_: *mut LeanObject = core::ptr::null_mut();
    v_res_7273_ = l_Lean_Parser_nameLit_parenthesizer(v_a_7268_, v_a_7269_, v_a_7270_, v_a_7271_);
    lean_dec(v_a_7271_);
    lean_dec_ref(v_a_7270_);
    lean_dec(v_a_7269_);
    lean_dec_ref(v_a_7268_);
    return v_res_7273_;
}
pub unsafe fn _init_l_Lean_Parser_nameLit___closed__0() -> *mut LeanObject {
    let mut v___x_7274_: u8 = 0;
    let mut v___x_7275_: u8 = 0;
    let mut v___x_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7278_: *mut LeanObject = core::ptr::null_mut();
    v___x_7274_ = 0;
    v___x_7275_ = 1;
    v___x_7276_ = l_Lean_Parser_nameLit_formatter___closed__1;
    v___x_7277_ = l_Lean_Parser_nameLit_formatter___closed__0;
    v___x_7278_ = l_Lean_Parser_mkAntiquot(v___x_7277_, v___x_7276_, v___x_7275_, v___x_7274_);
    return v___x_7278_;
}
pub unsafe fn _init_l_Lean_Parser_nameLit___closed__1() -> *mut LeanObject {
    let mut v___x_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: *mut LeanObject = core::ptr::null_mut();
    v___x_7279_ = l_Lean_Parser_nameLitNoAntiquot;
    v___x_7280_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_nameLit___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_nameLit___closed__0_once),
        _init_l_Lean_Parser_nameLit___closed__0,
    );
    v___x_7281_ = l_Lean_Parser_withAntiquot(v___x_7280_, v___x_7279_);
    return v___x_7281_;
}
pub unsafe fn _init_l_Lean_Parser_nameLit() -> *mut LeanObject {
    let mut v___x_7282_: *mut LeanObject = core::ptr::null_mut();
    v___x_7282_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_nameLit___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_nameLit___closed__1_once),
        _init_l_Lean_Parser_nameLit___closed__1,
    );
    return v___x_7282_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1()
-> *mut LeanObject {
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut LeanObject = core::ptr::null_mut();
    v___x_7290_ = l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1;
    v___x_7291_ = l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2;
    v___x_7292_ = l_Lean_addBuiltinDocString(v___x_7290_, v___x_7291_);
    return v___x_7292_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___boxed(
    mut v_a_7293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7294_: *mut LeanObject = core::ptr::null_mut();
    v_res_7294_ = l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1();
    return v_res_7294_;
}
pub unsafe fn l_Lean_Parser_group_formatter(
    mut v_p_7298_: *mut LeanObject,
    mut v_a_7299_: *mut LeanObject,
    mut v_a_7300_: *mut LeanObject,
    mut v_a_7301_: *mut LeanObject,
    mut v_a_7302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7305_: *mut LeanObject = core::ptr::null_mut();
    v___x_7304_ = l_Lean_Parser_group_formatter___closed__1;
    v___x_7305_ = l_Lean_PrettyPrinter_Formatter_node_formatter(
        v___x_7304_,
        v_p_7298_,
        v_a_7299_,
        v_a_7300_,
        v_a_7301_,
        v_a_7302_,
    );
    return v___x_7305_;
}
pub unsafe fn l_Lean_Parser_group_formatter___boxed(
    mut v_p_7306_: *mut LeanObject,
    mut v_a_7307_: *mut LeanObject,
    mut v_a_7308_: *mut LeanObject,
    mut v_a_7309_: *mut LeanObject,
    mut v_a_7310_: *mut LeanObject,
    mut v_a_7311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7312_: *mut LeanObject = core::ptr::null_mut();
    v_res_7312_ =
        l_Lean_Parser_group_formatter(v_p_7306_, v_a_7307_, v_a_7308_, v_a_7309_, v_a_7310_);
    lean_dec(v_a_7310_);
    lean_dec_ref(v_a_7309_);
    lean_dec(v_a_7308_);
    lean_dec_ref(v_a_7307_);
    return v_res_7312_;
}
pub unsafe fn l_Lean_Parser_group_parenthesizer(
    mut v_p_7313_: *mut LeanObject,
    mut v_a_7314_: *mut LeanObject,
    mut v_a_7315_: *mut LeanObject,
    mut v_a_7316_: *mut LeanObject,
    mut v_a_7317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: *mut LeanObject = core::ptr::null_mut();
    v___x_7319_ = l_Lean_Parser_group_formatter___closed__1;
    v___x_7320_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(
        v___x_7319_,
        v_p_7313_,
        v_a_7314_,
        v_a_7315_,
        v_a_7316_,
        v_a_7317_,
    );
    return v___x_7320_;
}
pub unsafe fn l_Lean_Parser_group_parenthesizer___boxed(
    mut v_p_7321_: *mut LeanObject,
    mut v_a_7322_: *mut LeanObject,
    mut v_a_7323_: *mut LeanObject,
    mut v_a_7324_: *mut LeanObject,
    mut v_a_7325_: *mut LeanObject,
    mut v_a_7326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7327_: *mut LeanObject = core::ptr::null_mut();
    v_res_7327_ =
        l_Lean_Parser_group_parenthesizer(v_p_7321_, v_a_7322_, v_a_7323_, v_a_7324_, v_a_7325_);
    lean_dec(v_a_7325_);
    lean_dec_ref(v_a_7324_);
    lean_dec(v_a_7323_);
    lean_dec_ref(v_a_7322_);
    return v_res_7327_;
}
pub unsafe fn l_Lean_Parser_group(mut v_p_7328_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7330_: *mut LeanObject = core::ptr::null_mut();
    v___x_7329_ = l_Lean_Parser_group_formatter___closed__1;
    v___x_7330_ = l_Lean_Parser_node(v___x_7329_, v_p_7328_);
    return v___x_7330_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1()
-> *mut LeanObject {
    let mut v___x_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut LeanObject = core::ptr::null_mut();
    v___x_7337_ = l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0;
    v___x_7338_ = l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1;
    v___x_7339_ = l_Lean_addBuiltinDocString(v___x_7337_, v___x_7338_);
    return v___x_7339_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___boxed(
    mut v_a_7340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7341_: *mut LeanObject = core::ptr::null_mut();
    v_res_7341_ = l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1();
    return v_res_7341_;
}
pub unsafe fn l_Lean_Parser_many1Indent_formatter(
    mut v_p_7342_: *mut LeanObject,
    mut v_a_7343_: *mut LeanObject,
    mut v_a_7344_: *mut LeanObject,
    mut v_a_7345_: *mut LeanObject,
    mut v_a_7346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut LeanObject = core::ptr::null_mut();
    v___x_7348_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7349_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_7349_, 0, v___x_7348_);
    lean_closure_set(v___x_7349_, 1, v_p_7342_);
    v___x_7350_ =
        l_Lean_Parser_many1_formatter(v___x_7349_, v_a_7343_, v_a_7344_, v_a_7345_, v_a_7346_);
    return v___x_7350_;
}
pub unsafe fn l_Lean_Parser_many1Indent_formatter___boxed(
    mut v_p_7351_: *mut LeanObject,
    mut v_a_7352_: *mut LeanObject,
    mut v_a_7353_: *mut LeanObject,
    mut v_a_7354_: *mut LeanObject,
    mut v_a_7355_: *mut LeanObject,
    mut v_a_7356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7357_: *mut LeanObject = core::ptr::null_mut();
    v_res_7357_ =
        l_Lean_Parser_many1Indent_formatter(v_p_7351_, v_a_7352_, v_a_7353_, v_a_7354_, v_a_7355_);
    lean_dec(v_a_7355_);
    lean_dec_ref(v_a_7354_);
    lean_dec(v_a_7353_);
    lean_dec_ref(v_a_7352_);
    return v_res_7357_;
}
pub unsafe fn l_Lean_Parser_many1Indent_parenthesizer(
    mut v_p_7358_: *mut LeanObject,
    mut v_a_7359_: *mut LeanObject,
    mut v_a_7360_: *mut LeanObject,
    mut v_a_7361_: *mut LeanObject,
    mut v_a_7362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
    v___x_7364_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7365_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_7365_, 0, v___x_7364_);
    lean_closure_set(v___x_7365_, 1, v_p_7358_);
    v___x_7366_ = lean_alloc_closure(
        l_Lean_Parser_many1_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_7366_, 0, v___x_7365_);
    v___x_7367_ = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(
        v___x_7366_,
        v_a_7359_,
        v_a_7360_,
        v_a_7361_,
        v_a_7362_,
    );
    return v___x_7367_;
}
pub unsafe fn l_Lean_Parser_many1Indent_parenthesizer___boxed(
    mut v_p_7368_: *mut LeanObject,
    mut v_a_7369_: *mut LeanObject,
    mut v_a_7370_: *mut LeanObject,
    mut v_a_7371_: *mut LeanObject,
    mut v_a_7372_: *mut LeanObject,
    mut v_a_7373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7374_: *mut LeanObject = core::ptr::null_mut();
    v_res_7374_ = l_Lean_Parser_many1Indent_parenthesizer(
        v_p_7368_, v_a_7369_, v_a_7370_, v_a_7371_, v_a_7372_,
    );
    lean_dec(v_a_7372_);
    lean_dec_ref(v_a_7371_);
    lean_dec(v_a_7370_);
    lean_dec_ref(v_a_7369_);
    return v_res_7374_;
}
pub unsafe fn _init_l_Lean_Parser_many1Indent___closed__1() -> *mut LeanObject {
    let mut v___x_7376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: *mut LeanObject = core::ptr::null_mut();
    v___x_7376_ = l_Lean_Parser_many1Indent___closed__0;
    v___x_7377_ = l_Lean_Parser_checkColGe(v___x_7376_);
    return v___x_7377_;
}
pub unsafe fn l_Lean_Parser_many1Indent(mut v_p_7378_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut LeanObject = core::ptr::null_mut();
    v___x_7379_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_many1Indent___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_many1Indent___closed__1_once),
        _init_l_Lean_Parser_many1Indent___closed__1,
    );
    v___x_7380_ = l_Lean_Parser_andthen(v___x_7379_, v_p_7378_);
    v___x_7381_ = l_Lean_Parser_many1(v___x_7380_);
    v___x_7382_ = l_Lean_Parser_withPosition(v___x_7381_);
    return v___x_7382_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1()
-> *mut LeanObject {
    let mut v___x_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut LeanObject = core::ptr::null_mut();
    v___x_7390_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1;
    v___x_7391_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2;
    v___x_7392_ = l_Lean_addBuiltinDocString(v___x_7390_, v___x_7391_);
    return v___x_7392_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___boxed(
    mut v_a_7393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7394_: *mut LeanObject = core::ptr::null_mut();
    v_res_7394_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1();
    return v_res_7394_;
}
pub unsafe fn l_Lean_Parser_manyIndent_formatter(
    mut v_p_7395_: *mut LeanObject,
    mut v_a_7396_: *mut LeanObject,
    mut v_a_7397_: *mut LeanObject,
    mut v_a_7398_: *mut LeanObject,
    mut v_a_7399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut LeanObject = core::ptr::null_mut();
    v___x_7401_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7402_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_7402_, 0, v___x_7401_);
    lean_closure_set(v___x_7402_, 1, v_p_7395_);
    v___x_7403_ =
        l_Lean_Parser_many_formatter(v___x_7402_, v_a_7396_, v_a_7397_, v_a_7398_, v_a_7399_);
    return v___x_7403_;
}
pub unsafe fn l_Lean_Parser_manyIndent_formatter___boxed(
    mut v_p_7404_: *mut LeanObject,
    mut v_a_7405_: *mut LeanObject,
    mut v_a_7406_: *mut LeanObject,
    mut v_a_7407_: *mut LeanObject,
    mut v_a_7408_: *mut LeanObject,
    mut v_a_7409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7410_: *mut LeanObject = core::ptr::null_mut();
    v_res_7410_ =
        l_Lean_Parser_manyIndent_formatter(v_p_7404_, v_a_7405_, v_a_7406_, v_a_7407_, v_a_7408_);
    lean_dec(v_a_7408_);
    lean_dec_ref(v_a_7407_);
    lean_dec(v_a_7406_);
    lean_dec_ref(v_a_7405_);
    return v_res_7410_;
}
pub unsafe fn l_Lean_Parser_manyIndent_parenthesizer(
    mut v_p_7411_: *mut LeanObject,
    mut v_a_7412_: *mut LeanObject,
    mut v_a_7413_: *mut LeanObject,
    mut v_a_7414_: *mut LeanObject,
    mut v_a_7415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7420_: *mut LeanObject = core::ptr::null_mut();
    v___x_7417_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7418_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_7418_, 0, v___x_7417_);
    lean_closure_set(v___x_7418_, 1, v_p_7411_);
    v___x_7419_ = lean_alloc_closure(
        l_Lean_Parser_many_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_7419_, 0, v___x_7418_);
    v___x_7420_ = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(
        v___x_7419_,
        v_a_7412_,
        v_a_7413_,
        v_a_7414_,
        v_a_7415_,
    );
    return v___x_7420_;
}
pub unsafe fn l_Lean_Parser_manyIndent_parenthesizer___boxed(
    mut v_p_7421_: *mut LeanObject,
    mut v_a_7422_: *mut LeanObject,
    mut v_a_7423_: *mut LeanObject,
    mut v_a_7424_: *mut LeanObject,
    mut v_a_7425_: *mut LeanObject,
    mut v_a_7426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7427_: *mut LeanObject = core::ptr::null_mut();
    v_res_7427_ = l_Lean_Parser_manyIndent_parenthesizer(
        v_p_7421_, v_a_7422_, v_a_7423_, v_a_7424_, v_a_7425_,
    );
    lean_dec(v_a_7425_);
    lean_dec_ref(v_a_7424_);
    lean_dec(v_a_7423_);
    lean_dec_ref(v_a_7422_);
    return v_res_7427_;
}
pub unsafe fn l_Lean_Parser_manyIndent(mut v_p_7428_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: *mut LeanObject = core::ptr::null_mut();
    v___x_7429_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_many1Indent___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_many1Indent___closed__1_once),
        _init_l_Lean_Parser_many1Indent___closed__1,
    );
    v___x_7430_ = l_Lean_Parser_andthen(v___x_7429_, v_p_7428_);
    v___x_7431_ = l_Lean_Parser_many(v___x_7430_);
    v___x_7432_ = l_Lean_Parser_withPosition(v___x_7431_);
    return v___x_7432_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1()
-> *mut LeanObject {
    let mut v___x_7440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7442_: *mut LeanObject = core::ptr::null_mut();
    v___x_7440_ = l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1;
    v___x_7441_ = l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2;
    v___x_7442_ = l_Lean_addBuiltinDocString(v___x_7440_, v___x_7441_);
    return v___x_7442_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___boxed(
    mut v_a_7443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7444_: *mut LeanObject = core::ptr::null_mut();
    v_res_7444_ = l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1();
    return v_res_7444_;
}
pub unsafe fn _init_l_Lean_Parser_sepByIndent___closed__0() -> *mut LeanObject {
    let mut v___x_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: *mut LeanObject = core::ptr::null_mut();
    v___x_7445_ = l_Lean_Parser_many1Indent___closed__0;
    v___x_7446_ = l_Lean_Parser_checkColEq(v___x_7445_);
    return v___x_7446_;
}
pub unsafe fn _init_l_Lean_Parser_sepByIndent___closed__2() -> *mut LeanObject {
    let mut v___x_7448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
    v___x_7448_ = l_Lean_Parser_sepByIndent___closed__1;
    v___x_7449_ = l_Lean_Parser_checkLinebreakBefore(v___x_7448_);
    return v___x_7449_;
}
pub unsafe fn _init_l_Lean_Parser_sepByIndent___closed__3() -> *mut LeanObject {
    let mut v___x_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7452_: *mut LeanObject = core::ptr::null_mut();
    v___x_7450_ = l_Lean_Parser_pushNone;
    v___x_7451_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent___closed__2_once),
        _init_l_Lean_Parser_sepByIndent___closed__2,
    );
    v___x_7452_ = l_Lean_Parser_andthen(v___x_7451_, v___x_7450_);
    return v___x_7452_;
}
pub unsafe fn _init_l_Lean_Parser_sepByIndent___closed__4() -> *mut LeanObject {
    let mut v___x_7453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7455_: *mut LeanObject = core::ptr::null_mut();
    v___x_7453_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent___closed__3_once),
        _init_l_Lean_Parser_sepByIndent___closed__3,
    );
    v___x_7454_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent___closed__0_once),
        _init_l_Lean_Parser_sepByIndent___closed__0,
    );
    v___x_7455_ = l_Lean_Parser_andthen(v___x_7454_, v___x_7453_);
    return v___x_7455_;
}
pub unsafe fn l_Lean_Parser_sepByIndent(
    mut v_p_7456_: *mut LeanObject,
    mut v_sep_7457_: *mut LeanObject,
    mut v_psep_7458_: *mut LeanObject,
    mut v_allowTrailingSep_7459_: u8,
) -> *mut LeanObject {
    let mut v___x_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7468_: *mut LeanObject = core::ptr::null_mut();
    v___x_7460_ = l_Lean_Parser_sepByElemParser_formatter___closed__1;
    v___x_7461_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_many___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_many___closed__0_once),
        _init_l_Lean_Parser_many___closed__0,
    );
    v_p_7462_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_7460_, v_p_7456_, v___x_7461_);
    v___x_7463_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_many1Indent___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_many1Indent___closed__1_once),
        _init_l_Lean_Parser_many1Indent___closed__1,
    );
    v___x_7464_ = l_Lean_Parser_andthen(v___x_7463_, v_p_7462_);
    v___x_7465_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent___closed__4_once),
        _init_l_Lean_Parser_sepByIndent___closed__4,
    );
    v___x_7466_ = l_Lean_Parser_orelse(v_psep_7458_, v___x_7465_);
    v___x_7467_ = l_Lean_Parser_sepBy(
        v___x_7464_,
        v_sep_7457_,
        v___x_7466_,
        v_allowTrailingSep_7459_,
    );
    v___x_7468_ = l_Lean_Parser_withPosition(v___x_7467_);
    return v___x_7468_;
}
pub unsafe fn l_Lean_Parser_sepByIndent___boxed(
    mut v_p_7469_: *mut LeanObject,
    mut v_sep_7470_: *mut LeanObject,
    mut v_psep_7471_: *mut LeanObject,
    mut v_allowTrailingSep_7472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowTrailingSep_boxed_7473_: u8 = 0;
    let mut v_res_7474_: *mut LeanObject = core::ptr::null_mut();
    v_allowTrailingSep_boxed_7473_ = (lean_unbox(v_allowTrailingSep_7472_) as u8);
    v_res_7474_ = l_Lean_Parser_sepByIndent(
        v_p_7469_,
        v_sep_7470_,
        v_psep_7471_,
        v_allowTrailingSep_boxed_7473_,
    );
    return v_res_7474_;
}
pub unsafe fn l_Lean_Parser_sepBy1Indent(
    mut v_p_7475_: *mut LeanObject,
    mut v_sep_7476_: *mut LeanObject,
    mut v_psep_7477_: *mut LeanObject,
    mut v_allowTrailingSep_7478_: u8,
) -> *mut LeanObject {
    let mut v___x_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: *mut LeanObject = core::ptr::null_mut();
    v___x_7479_ = l_Lean_Parser_sepByElemParser_formatter___closed__1;
    v___x_7480_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_many___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_many___closed__0_once),
        _init_l_Lean_Parser_many___closed__0,
    );
    v_p_7481_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_7479_, v_p_7475_, v___x_7480_);
    v___x_7482_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_many1Indent___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_many1Indent___closed__1_once),
        _init_l_Lean_Parser_many1Indent___closed__1,
    );
    v___x_7483_ = l_Lean_Parser_andthen(v___x_7482_, v_p_7481_);
    v___x_7484_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent___closed__4_once),
        _init_l_Lean_Parser_sepByIndent___closed__4,
    );
    v___x_7485_ = l_Lean_Parser_orelse(v_psep_7477_, v___x_7484_);
    v___x_7486_ = l_Lean_Parser_sepBy1(
        v___x_7483_,
        v_sep_7476_,
        v___x_7485_,
        v_allowTrailingSep_7478_,
    );
    v___x_7487_ = l_Lean_Parser_withPosition(v___x_7486_);
    return v___x_7487_;
}
pub unsafe fn l_Lean_Parser_sepBy1Indent___boxed(
    mut v_p_7488_: *mut LeanObject,
    mut v_sep_7489_: *mut LeanObject,
    mut v_psep_7490_: *mut LeanObject,
    mut v_allowTrailingSep_7491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowTrailingSep_boxed_7492_: u8 = 0;
    let mut v_res_7493_: *mut LeanObject = core::ptr::null_mut();
    v_allowTrailingSep_boxed_7492_ = (lean_unbox(v_allowTrailingSep_7491_) as u8);
    v_res_7493_ = l_Lean_Parser_sepBy1Indent(
        v_p_7488_,
        v_sep_7489_,
        v_psep_7490_,
        v_allowTrailingSep_boxed_7492_,
    );
    return v_res_7493_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(
    mut v___y_7494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxTrav_7497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cur_7498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7499_: *mut LeanObject = core::ptr::null_mut();
    v___x_7496_ = lean_st_ref_get(v___y_7494_);
    v_stxTrav_7497_ = lean_ctor_get(v___x_7496_, 0);
    lean_inc_ref(v_stxTrav_7497_);
    lean_dec(v___x_7496_);
    v_cur_7498_ = lean_ctor_get(v_stxTrav_7497_, 0);
    lean_inc(v_cur_7498_);
    lean_dec_ref(v_stxTrav_7497_);
    v___x_7499_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7499_, 0, v_cur_7498_);
    return v___x_7499_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg___boxed(
    mut v___y_7500_: *mut LeanObject,
    mut v___y_7501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7502_: *mut LeanObject = core::ptr::null_mut();
    v_res_7502_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(v___y_7500_);
    lean_dec(v___y_7500_);
    return v_res_7502_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0(
    mut v___y_7503_: *mut LeanObject,
    mut v___y_7504_: *mut LeanObject,
    mut v___y_7505_: *mut LeanObject,
    mut v___y_7506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7508_: *mut LeanObject = core::ptr::null_mut();
    v___x_7508_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(v___y_7504_);
    return v___x_7508_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___boxed(
    mut v___y_7509_: *mut LeanObject,
    mut v___y_7510_: *mut LeanObject,
    mut v___y_7511_: *mut LeanObject,
    mut v___y_7512_: *mut LeanObject,
    mut v___y_7513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7514_: *mut LeanObject = core::ptr::null_mut();
    v_res_7514_ =
        l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0(
            v___y_7509_,
            v___y_7510_,
            v___y_7511_,
            v___y_7512_,
        );
    lean_dec(v___y_7512_);
    lean_dec_ref(v___y_7511_);
    lean_dec(v___y_7510_);
    lean_dec_ref(v___y_7509_);
    return v_res_7514_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(
    mut v___y_7515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxTrav_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leadWord_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leadWordIdent_7520_: u8 = 0;
    let mut v_isUngrouped_7521_: u8 = 0;
    let mut v_mustBeGrouped_7522_: u8 = 0;
    let mut v_stack_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7526_: u8 = 0;
    let mut v___x_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7517_ = lean_st_ref_take(v___y_7515_);
                v_stxTrav_7518_ = lean_ctor_get(v___x_7517_, 0);
                v_leadWord_7519_ = lean_ctor_get(v___x_7517_, 1);
                v_leadWordIdent_7520_ = lean_ctor_get_uint8(
                    v___x_7517_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isUngrouped_7521_ = lean_ctor_get_uint8(
                    v___x_7517_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_mustBeGrouped_7522_ = lean_ctor_get_uint8(
                    v___x_7517_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_stack_7523_ = lean_ctor_get(v___x_7517_, 2);
                v_isSharedCheck_7534_ = (!lean_is_exclusive(v___x_7517_)) as u8;
                if v_isSharedCheck_7534_ == 0 {
                    v___x_7525_ = v___x_7517_;
                    v_isShared_7526_ = v_isSharedCheck_7534_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stack_7523_);
                    lean_inc(v_leadWord_7519_);
                    lean_inc(v_stxTrav_7518_);
                    lean_dec(v___x_7517_);
                    v___x_7525_ = lean_box(0);
                    v_isShared_7526_ = v_isSharedCheck_7534_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7527_ = l_Lean_Syntax_Traverser_left(v_stxTrav_7518_);
                if v_isShared_7526_ == 0 {
                    lean_ctor_set(v___x_7525_, 0, v___x_7527_);
                    v___x_7529_ = v___x_7525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7533_ = lean_alloc_ctor(0, 3, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7533_, 0, v___x_7527_);
                    lean_ctor_set(v_reuseFailAlloc_7533_, 1, v_leadWord_7519_);
                    lean_ctor_set(v_reuseFailAlloc_7533_, 2, v_stack_7523_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7533_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_leadWordIdent_7520_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7533_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isUngrouped_7521_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7533_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_mustBeGrouped_7522_,
                    );
                    v___x_7529_ = v_reuseFailAlloc_7533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7530_ = lean_st_ref_set(v___y_7515_, v___x_7529_);
                v___x_7531_ = lean_box(0);
                v___x_7532_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7532_, 0, v___x_7531_);
                return v___x_7532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg___boxed(
    mut v___y_7535_: *mut LeanObject,
    mut v___y_7536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7537_: *mut LeanObject = core::ptr::null_mut();
    v_res_7537_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(v___y_7535_);
    lean_dec(v___y_7535_);
    return v_res_7537_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2(
    mut v___y_7538_: *mut LeanObject,
    mut v___y_7539_: *mut LeanObject,
    mut v___y_7540_: *mut LeanObject,
    mut v___y_7541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7543_: *mut LeanObject = core::ptr::null_mut();
    v___x_7543_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(v___y_7539_);
    return v___x_7543_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___boxed(
    mut v___y_7544_: *mut LeanObject,
    mut v___y_7545_: *mut LeanObject,
    mut v___y_7546_: *mut LeanObject,
    mut v___y_7547_: *mut LeanObject,
    mut v___y_7548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7549_: *mut LeanObject = core::ptr::null_mut();
    v_res_7549_ =
        l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2(
            v___y_7544_,
            v___y_7545_,
            v___y_7546_,
            v___y_7547_,
        );
    lean_dec(v___y_7547_);
    lean_dec_ref(v___y_7546_);
    lean_dec(v___y_7545_);
    lean_dec_ref(v___y_7544_);
    return v_res_7549_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(
    mut v_pSep_7553_: *mut LeanObject,
    mut v___x_7554_: *mut LeanObject,
    mut v_p_7555_: *mut LeanObject,
    mut v_as_x27_7556_: *mut LeanObject,
    mut v_b_7557_: *mut LeanObject,
    mut v___y_7558_: *mut LeanObject,
    mut v___y_7559_: *mut LeanObject,
    mut v___y_7560_: *mut LeanObject,
    mut v___y_7561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: u8 = 0;
    let mut v___x_7574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7580_: u8 = 0;
    let mut v_id_7581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: u8 = 0;
    let mut v___x_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7586_: u8 = 0;
    let mut v___x_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: u8 = 0;
    let mut v___x_7590_: u8 = 0;
    let mut v___x_7591_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_7556_) == 0 {
                    lean_dec_ref(v_p_7555_);
                    lean_dec_ref(v_pSep_7553_);
                    v___x_7563_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7563_, 0, v_b_7557_);
                    return v___x_7563_;
                } else {
                    v_head_7564_ = lean_ctor_get(v_as_x27_7556_, 0);
                    v_tail_7565_ = lean_ctor_get(v_as_x27_7556_, 1);
                    v___x_7566_ = lean_box(0);
                    v___x_7570_ = lean_unsigned_to_nat(0);
                    v___x_7571_ = lean_unsigned_to_nat(2);
                    v___x_7572_ = lean_nat_mod(v_head_7564_, v___x_7571_);
                    v___x_7573_ = lean_nat_dec_eq(v___x_7572_, v___x_7570_);
                    lean_dec(v___x_7572_);
                    if v___x_7573_ == 0 {
                        v___x_7574_ = lean_st_ref_get(v___y_7559_);
                        lean_inc_ref(v_pSep_7553_);
                        lean_inc(v___y_7561_);
                        lean_inc_ref(v___y_7560_);
                        lean_inc(v___y_7559_);
                        lean_inc_ref(v___y_7558_);
                        v___x_7575_ = lean_apply_5(
                            v_pSep_7553_,
                            v___y_7558_,
                            v___y_7559_,
                            v___y_7560_,
                            v___y_7561_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_7575_) == 0 {
                            lean_dec_ref_known(v___x_7575_, 1);
                            lean_dec(v___x_7574_);
                            v_as_x27_7556_ = v_tail_7565_;
                            v_b_7557_ = v___x_7566_;
                            state = 0;
                            continue;
                        } else {
                            v_a_7577_ = lean_ctor_get(v___x_7575_, 0);
                            lean_inc(v_a_7577_);
                            v___x_7578_ = l_Lean_PrettyPrinter_backtrackExceptionId;
                            v___x_7589_ = l_Lean_Exception_isInterrupt(v_a_7577_);
                            if v___x_7589_ == 0 {
                                lean_inc(v_a_7577_);
                                v___x_7590_ = l_Lean_Exception_isRuntime(v_a_7577_);
                                v___y_7580_ = v___x_7590_;
                                state = 2;
                                continue;
                            } else {
                                v___y_7580_ = v___x_7589_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_inc_ref(v_p_7555_);
                        lean_inc(v___y_7561_);
                        lean_inc_ref(v___y_7560_);
                        lean_inc(v___y_7559_);
                        lean_inc_ref(v___y_7558_);
                        v___x_7591_ = lean_apply_5(
                            v_p_7555_,
                            v___y_7558_,
                            v___y_7559_,
                            v___y_7560_,
                            v___y_7561_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_7591_) == 0 {
                            lean_dec_ref_known(v___x_7591_, 1);
                            v_as_x27_7556_ = v_tail_7565_;
                            v_b_7557_ = v___x_7566_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_p_7555_);
                            lean_dec_ref(v_pSep_7553_);
                            return v___x_7591_;
                        }
                    }
                }
            }
            1 => {
                v___x_7568_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(v___y_7559_);
                lean_dec_ref(v___x_7568_);
                v_as_x27_7556_ = v_tail_7565_;
                v_b_7557_ = v___x_7566_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_7580_ == 0 {
                    if lean_obj_tag(v_a_7577_) == 0 {
                        lean_dec_ref_known(v_a_7577_, 2);
                        lean_dec(v___x_7574_);
                        lean_dec_ref(v_p_7555_);
                        lean_dec_ref(v_pSep_7553_);
                        return v___x_7575_;
                    } else {
                        v_id_7581_ = lean_ctor_get(v_a_7577_, 0);
                        lean_inc(v_id_7581_);
                        lean_dec_ref_known(v_a_7577_, 2);
                        v___x_7582_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___x_7578_, v_id_7581_);
                        lean_dec(v_id_7581_);
                        if v___x_7582_ == 0 {
                            lean_dec(v___x_7574_);
                            lean_dec_ref(v_p_7555_);
                            lean_dec_ref(v_pSep_7553_);
                            return v___x_7575_;
                        } else {
                            lean_dec_ref_known(v___x_7575_, 1);
                            v___x_7583_ = lean_st_ref_set(v___y_7559_, v___x_7574_);
                            v___x_7584_ = lean_unsigned_to_nat(1);
                            v___x_7585_ = lean_nat_sub(v___x_7554_, v___x_7584_);
                            v___x_7586_ = lean_nat_dec_eq(v_head_7564_, v___x_7585_);
                            lean_dec(v___x_7585_);
                            if v___x_7586_ == 0 {
                                v___x_7587_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1;
                                v___x_7588_ =
                                    l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(
                                        v___x_7587_,
                                        v___y_7559_,
                                    );
                                if lean_obj_tag(v___x_7588_) == 0 {
                                    lean_dec_ref_known(v___x_7588_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref(v_p_7555_);
                                    lean_dec_ref(v_pSep_7553_);
                                    return v___x_7588_;
                                }
                            } else {
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_7577_);
                    lean_dec(v___x_7574_);
                    lean_dec_ref(v_p_7555_);
                    lean_dec_ref(v_pSep_7553_);
                    return v___x_7575_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___boxed(
    mut v_pSep_7593_: *mut LeanObject,
    mut v___x_7594_: *mut LeanObject,
    mut v_p_7595_: *mut LeanObject,
    mut v_as_x27_7596_: *mut LeanObject,
    mut v_b_7597_: *mut LeanObject,
    mut v___y_7598_: *mut LeanObject,
    mut v___y_7599_: *mut LeanObject,
    mut v___y_7600_: *mut LeanObject,
    mut v___y_7601_: *mut LeanObject,
    mut v___y_7602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7603_: *mut LeanObject = core::ptr::null_mut();
    v_res_7603_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(
        v_pSep_7593_,
        v___x_7594_,
        v_p_7595_,
        v_as_x27_7596_,
        v_b_7597_,
        v___y_7598_,
        v___y_7599_,
        v___y_7600_,
        v___y_7601_,
    );
    lean_dec(v___y_7601_);
    lean_dec_ref(v___y_7600_);
    lean_dec(v___y_7599_);
    lean_dec_ref(v___y_7598_);
    lean_dec(v_as_x27_7596_);
    lean_dec(v___x_7594_);
    return v_res_7603_;
}
pub unsafe fn l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(
    mut v_pSep_7604_: *mut LeanObject,
    mut v___x_7605_: *mut LeanObject,
    mut v_p_7606_: *mut LeanObject,
    mut v___x_7607_: *mut LeanObject,
    mut v___x_7608_: *mut LeanObject,
    mut v___y_7609_: *mut LeanObject,
    mut v___y_7610_: *mut LeanObject,
    mut v___y_7611_: *mut LeanObject,
    mut v___y_7612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7617_: u8 = 0;
    let mut v___x_7619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7621_: u8 = 0;
    let mut v_unused_7622_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7614_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(v_pSep_7604_, v___x_7605_, v_p_7606_, v___x_7607_, v___x_7608_, v___y_7609_, v___y_7610_, v___y_7611_, v___y_7612_);
                if lean_obj_tag(v___x_7614_) == 0 {
                    v_isSharedCheck_7621_ = (!lean_is_exclusive(v___x_7614_)) as u8;
                    if v_isSharedCheck_7621_ == 0 {
                        v_unused_7622_ = lean_ctor_get(v___x_7614_, 0);
                        lean_dec(v_unused_7622_);
                        v___x_7616_ = v___x_7614_;
                        v_isShared_7617_ = v_isSharedCheck_7621_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_7614_);
                        v___x_7616_ = lean_box(0);
                        v_isShared_7617_ = v_isSharedCheck_7621_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_7614_;
                }
            }
            1 => {
                if v_isShared_7617_ == 0 {
                    lean_ctor_set(v___x_7616_, 0, v___x_7608_);
                    v___x_7619_ = v___x_7616_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7620_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7620_, 0, v___x_7608_);
                    v___x_7619_ = v_reuseFailAlloc_7620_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_sepByIndent_formatter___redArg___lam__0___boxed(
    mut v_pSep_7623_: *mut LeanObject,
    mut v___x_7624_: *mut LeanObject,
    mut v_p_7625_: *mut LeanObject,
    mut v___x_7626_: *mut LeanObject,
    mut v___x_7627_: *mut LeanObject,
    mut v___y_7628_: *mut LeanObject,
    mut v___y_7629_: *mut LeanObject,
    mut v___y_7630_: *mut LeanObject,
    mut v___y_7631_: *mut LeanObject,
    mut v___y_7632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7633_: *mut LeanObject = core::ptr::null_mut();
    v_res_7633_ = l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(
        v_pSep_7623_,
        v___x_7624_,
        v_p_7625_,
        v___x_7626_,
        v___x_7627_,
        v___y_7628_,
        v___y_7629_,
        v___y_7630_,
        v___y_7631_,
    );
    lean_dec(v___y_7631_);
    lean_dec_ref(v___y_7630_);
    lean_dec(v___y_7629_);
    lean_dec_ref(v___y_7628_);
    lean_dec(v___x_7626_);
    lean_dec(v___x_7624_);
    return v_res_7633_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(
    mut v_a_7634_: *mut LeanObject,
    mut v_as_7635_: *mut LeanObject,
    mut v_i_7636_: *mut LeanObject,
    mut v_j_7637_: *mut LeanObject,
    mut v_bs_7638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_7639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7640_: u8 = 0;
    let mut v_one_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7644_: u8 = 0;
    let mut v___x_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7650_: u8 = 0;
    let mut v___x_7651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7654_: u8 = 0;
    let mut v___x_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: u8 = 0;
    let mut v___x_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7639_ = lean_unsigned_to_nat(0);
                v_isZero_7640_ = lean_nat_dec_eq(v_i_7636_, v_zero_7639_);
                if v_isZero_7640_ == 1 {
                    lean_dec(v_j_7637_);
                    lean_dec(v_i_7636_);
                    return v_bs_7638_;
                } else {
                    v_one_7641_ = lean_unsigned_to_nat(1);
                    v_n_7642_ = lean_nat_sub(v_i_7636_, v_one_7641_);
                    lean_dec(v_i_7636_);
                    v___x_7655_ = lean_unsigned_to_nat(2);
                    v___x_7656_ = lean_nat_mod(v_j_7637_, v___x_7655_);
                    v___x_7657_ = lean_nat_dec_eq(v___x_7656_, v_one_7641_);
                    lean_dec(v___x_7656_);
                    if v___x_7657_ == 0 {
                        v___y_7650_ = v___x_7657_;
                        state = 2;
                        continue;
                    } else {
                        v___x_7658_ = lean_array_fget_borrowed(v_as_7635_, v_j_7637_);
                        lean_inc(v___x_7658_);
                        v___x_7659_ = l_Lean_Syntax_matchesNull(v___x_7658_, v_zero_7639_);
                        v___y_7650_ = v___x_7659_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7645_ = lean_nat_add(v_j_7637_, v_one_7641_);
                lean_dec(v_j_7637_);
                v___x_7646_ = lean_box((v___y_7644_) as usize);
                v___x_7647_ = lean_array_push(v_bs_7638_, v___x_7646_);
                v_i_7636_ = v_n_7642_;
                v_j_7637_ = v___x_7645_;
                v_bs_7638_ = v___x_7647_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_7650_ == 0 {
                    v___y_7644_ = v___y_7650_;
                    state = 1;
                    continue;
                } else {
                    v___x_7651_ = l_Lean_Syntax_getArgs(v_a_7634_);
                    v___x_7652_ = lean_array_get_size(v___x_7651_);
                    lean_dec_ref(v___x_7651_);
                    v___x_7653_ = lean_nat_sub(v___x_7652_, v_one_7641_);
                    v___x_7654_ = lean_nat_dec_eq(v_j_7637_, v___x_7653_);
                    lean_dec(v___x_7653_);
                    if v___x_7654_ == 0 {
                        v___y_7644_ = v___y_7650_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7644_ = v_isZero_7640_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg___boxed(
    mut v_a_7660_: *mut LeanObject,
    mut v_as_7661_: *mut LeanObject,
    mut v_i_7662_: *mut LeanObject,
    mut v_j_7663_: *mut LeanObject,
    mut v_bs_7664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7665_: *mut LeanObject = core::ptr::null_mut();
    v_res_7665_ =
        l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(
            v_a_7660_, v_as_7661_, v_i_7662_, v_j_7663_, v_bs_7664_,
        );
    lean_dec_ref(v_as_7661_);
    lean_dec(v_a_7660_);
    return v_res_7665_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(
    mut v_as_7666_: *mut LeanObject,
    mut v_i_7667_: usize,
    mut v_stop_7668_: usize,
) -> u8 {
    let mut v___x_7669_: u8 = 0;
    let mut v___x_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: u8 = 0;
    let mut v___x_7672_: usize = 0;
    let mut v___x_7673_: usize = 0;
    let mut v___x_7675_: u8 = 0;
    let mut v___x_7676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7669_ = lean_usize_dec_eq(v_i_7667_, v_stop_7668_);
                if v___x_7669_ == 0 {
                    v___x_7670_ = lean_array_uget_borrowed(v_as_7666_, v_i_7667_);
                    v___x_7671_ = (lean_unbox(v___x_7670_) as u8);
                    if v___x_7671_ == 0 {
                        v___x_7672_ = 1usize;
                        v___x_7673_ = lean_usize_add(v_i_7667_, v___x_7672_);
                        v_i_7667_ = v___x_7673_;
                        state = 0;
                        continue;
                    } else {
                        v___x_7675_ = (lean_unbox(v___x_7670_) as u8);
                        return v___x_7675_;
                    }
                } else {
                    v___x_7676_ = 0;
                    return v___x_7676_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4___boxed(
    mut v_as_7677_: *mut LeanObject,
    mut v_i_7678_: *mut LeanObject,
    mut v_stop_7679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7680_: usize = 0;
    let mut v_stop_boxed_7681_: usize = 0;
    let mut v_res_7682_: u8 = 0;
    let mut v_r_7683_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7680_ = lean_unbox_usize(v_i_7678_);
    lean_dec(v_i_7678_);
    v_stop_boxed_7681_ = lean_unbox_usize(v_stop_7679_);
    lean_dec(v_stop_7679_);
    v_res_7682_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(v_as_7677_, v_i_boxed_7680_, v_stop_boxed_7681_);
    lean_dec_ref(v_as_7677_);
    v_r_7683_ = lean_box((v_res_7682_) as usize);
    return v_r_7683_;
}
pub unsafe fn l_Lean_Parser_sepByIndent_formatter___redArg(
    mut v_p_7684_: *mut LeanObject,
    mut v_pSep_7685_: *mut LeanObject,
    mut v_a_7686_: *mut LeanObject,
    mut v_a_7687_: *mut LeanObject,
    mut v_a_7688_: *mut LeanObject,
    mut v_a_7689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7696_: u8 = 0;
    let mut v___x_7697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7704_: u8 = 0;
    let mut v___x_7706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7709_: u8 = 0;
    let mut v_unused_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: u8 = 0;
    let mut v___x_7716_: usize = 0;
    let mut v___x_7717_: usize = 0;
    let mut v___x_7718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7691_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(v_a_7687_);
                v_a_7692_ = lean_ctor_get(v___x_7691_, 0);
                lean_inc(v_a_7692_);
                lean_dec_ref(v___x_7691_);
                v___x_7693_ = l_Lean_Syntax_getArgs(v_a_7692_);
                v___x_7694_ = lean_array_get_size(v___x_7693_);
                v___x_7711_ = lean_unsigned_to_nat(0);
                v___x_7712_ = lean_mk_empty_array_with_capacity(v___x_7694_);
                v___x_7713_ = l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(v_a_7692_, v___x_7693_, v___x_7694_, v___x_7711_, v___x_7712_);
                lean_dec_ref(v___x_7693_);
                lean_dec(v_a_7692_);
                v___x_7714_ = lean_array_get_size(v___x_7713_);
                v___x_7715_ = lean_nat_dec_lt(v___x_7711_, v___x_7714_);
                if v___x_7715_ == 0 {
                    lean_dec_ref(v___x_7713_);
                    v___y_7696_ = v___x_7715_;
                    state = 1;
                    continue;
                } else {
                    if v___x_7715_ == 0 {
                        lean_dec_ref(v___x_7713_);
                        v___y_7696_ = v___x_7715_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7716_ = 0usize;
                        v___x_7717_ = lean_usize_of_nat(v___x_7714_);
                        v___x_7718_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(v___x_7713_, v___x_7716_, v___x_7717_);
                        lean_dec_ref(v___x_7713_);
                        v___y_7696_ = v___x_7718_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7697_ = l_List_range(v___x_7694_);
                v___x_7698_ = l_List_reverse___redArg(v___x_7697_);
                v___x_7699_ = lean_box(0);
                v___f_7700_ = lean_alloc_closure(
                    l_Lean_Parser_sepByIndent_formatter___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    10,
                    5,
                );
                lean_closure_set(v___f_7700_, 0, v_pSep_7685_);
                lean_closure_set(v___f_7700_, 1, v___x_7694_);
                lean_closure_set(v___f_7700_, 2, v_p_7684_);
                lean_closure_set(v___f_7700_, 3, v___x_7698_);
                lean_closure_set(v___f_7700_, 4, v___x_7699_);
                v___x_7701_ = l_Lean_PrettyPrinter_Formatter_visitArgs(
                    v___f_7700_,
                    v_a_7686_,
                    v_a_7687_,
                    v_a_7688_,
                    v_a_7689_,
                );
                if lean_obj_tag(v___x_7701_) == 0 {
                    v_isSharedCheck_7709_ = (!lean_is_exclusive(v___x_7701_)) as u8;
                    if v_isSharedCheck_7709_ == 0 {
                        v_unused_7710_ = lean_ctor_get(v___x_7701_, 0);
                        lean_dec(v_unused_7710_);
                        v___x_7703_ = v___x_7701_;
                        v_isShared_7704_ = v_isSharedCheck_7709_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_7701_);
                        v___x_7703_ = lean_box(0);
                        v_isShared_7704_ = v_isSharedCheck_7709_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_7701_;
                }
            }
            2 => {
                if v___y_7696_ == 0 {
                    if v_isShared_7704_ == 0 {
                        lean_ctor_set(v___x_7703_, 0, v___x_7699_);
                        v___x_7706_ = v___x_7703_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7707_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7707_, 0, v___x_7699_);
                        v___x_7706_ = v_reuseFailAlloc_7707_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7703_);
                    v___x_7708_ =
                        l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(v___y_7696_, v_a_7687_);
                    return v___x_7708_;
                }
            }
            3 => {
                return v___x_7706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_sepByIndent_formatter___redArg___boxed(
    mut v_p_7719_: *mut LeanObject,
    mut v_pSep_7720_: *mut LeanObject,
    mut v_a_7721_: *mut LeanObject,
    mut v_a_7722_: *mut LeanObject,
    mut v_a_7723_: *mut LeanObject,
    mut v_a_7724_: *mut LeanObject,
    mut v_a_7725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7726_: *mut LeanObject = core::ptr::null_mut();
    v_res_7726_ = l_Lean_Parser_sepByIndent_formatter___redArg(
        v_p_7719_,
        v_pSep_7720_,
        v_a_7721_,
        v_a_7722_,
        v_a_7723_,
        v_a_7724_,
    );
    lean_dec(v_a_7724_);
    lean_dec_ref(v_a_7723_);
    lean_dec(v_a_7722_);
    lean_dec_ref(v_a_7721_);
    return v_res_7726_;
}
pub unsafe fn l_Lean_Parser_sepByIndent_formatter(
    mut v_p_7727_: *mut LeanObject,
    mut v___sep_7728_: *mut LeanObject,
    mut v_pSep_7729_: *mut LeanObject,
    mut v_a_7730_: *mut LeanObject,
    mut v_a_7731_: *mut LeanObject,
    mut v_a_7732_: *mut LeanObject,
    mut v_a_7733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7735_: *mut LeanObject = core::ptr::null_mut();
    v___x_7735_ = l_Lean_Parser_sepByIndent_formatter___redArg(
        v_p_7727_,
        v_pSep_7729_,
        v_a_7730_,
        v_a_7731_,
        v_a_7732_,
        v_a_7733_,
    );
    return v___x_7735_;
}
pub unsafe fn l_Lean_Parser_sepByIndent_formatter___boxed(
    mut v_p_7736_: *mut LeanObject,
    mut v___sep_7737_: *mut LeanObject,
    mut v_pSep_7738_: *mut LeanObject,
    mut v_a_7739_: *mut LeanObject,
    mut v_a_7740_: *mut LeanObject,
    mut v_a_7741_: *mut LeanObject,
    mut v_a_7742_: *mut LeanObject,
    mut v_a_7743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7744_: *mut LeanObject = core::ptr::null_mut();
    v_res_7744_ = l_Lean_Parser_sepByIndent_formatter(
        v_p_7736_,
        v___sep_7737_,
        v_pSep_7738_,
        v_a_7739_,
        v_a_7740_,
        v_a_7741_,
        v_a_7742_,
    );
    lean_dec(v_a_7742_);
    lean_dec_ref(v_a_7741_);
    lean_dec(v_a_7740_);
    lean_dec_ref(v_a_7739_);
    lean_dec_ref(v___sep_7737_);
    return v_res_7744_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1(
    mut v_a_7745_: *mut LeanObject,
    mut v_as_7746_: *mut LeanObject,
    mut v_i_7747_: *mut LeanObject,
    mut v_j_7748_: *mut LeanObject,
    mut v_inv_7749_: *mut LeanObject,
    mut v_bs_7750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7751_: *mut LeanObject = core::ptr::null_mut();
    v___x_7751_ =
        l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(
            v_a_7745_, v_as_7746_, v_i_7747_, v_j_7748_, v_bs_7750_,
        );
    return v___x_7751_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___boxed(
    mut v_a_7752_: *mut LeanObject,
    mut v_as_7753_: *mut LeanObject,
    mut v_i_7754_: *mut LeanObject,
    mut v_j_7755_: *mut LeanObject,
    mut v_inv_7756_: *mut LeanObject,
    mut v_bs_7757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7758_: *mut LeanObject = core::ptr::null_mut();
    v_res_7758_ = l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1(
        v_a_7752_,
        v_as_7753_,
        v_i_7754_,
        v_j_7755_,
        v_inv_7756_,
        v_bs_7757_,
    );
    lean_dec_ref(v_as_7753_);
    lean_dec(v_a_7752_);
    return v_res_7758_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3(
    mut v_pSep_7759_: *mut LeanObject,
    mut v___x_7760_: *mut LeanObject,
    mut v_p_7761_: *mut LeanObject,
    mut v_as_7762_: *mut LeanObject,
    mut v_as_x27_7763_: *mut LeanObject,
    mut v_b_7764_: *mut LeanObject,
    mut v_a_7765_: *mut LeanObject,
    mut v___y_7766_: *mut LeanObject,
    mut v___y_7767_: *mut LeanObject,
    mut v___y_7768_: *mut LeanObject,
    mut v___y_7769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7771_: *mut LeanObject = core::ptr::null_mut();
    v___x_7771_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(
        v_pSep_7759_,
        v___x_7760_,
        v_p_7761_,
        v_as_x27_7763_,
        v_b_7764_,
        v___y_7766_,
        v___y_7767_,
        v___y_7768_,
        v___y_7769_,
    );
    return v___x_7771_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___boxed(
    mut v_pSep_7772_: *mut LeanObject,
    mut v___x_7773_: *mut LeanObject,
    mut v_p_7774_: *mut LeanObject,
    mut v_as_7775_: *mut LeanObject,
    mut v_as_x27_7776_: *mut LeanObject,
    mut v_b_7777_: *mut LeanObject,
    mut v_a_7778_: *mut LeanObject,
    mut v___y_7779_: *mut LeanObject,
    mut v___y_7780_: *mut LeanObject,
    mut v___y_7781_: *mut LeanObject,
    mut v___y_7782_: *mut LeanObject,
    mut v___y_7783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7784_: *mut LeanObject = core::ptr::null_mut();
    v_res_7784_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3(
        v_pSep_7772_,
        v___x_7773_,
        v_p_7774_,
        v_as_7775_,
        v_as_x27_7776_,
        v_b_7777_,
        v_a_7778_,
        v___y_7779_,
        v___y_7780_,
        v___y_7781_,
        v___y_7782_,
    );
    lean_dec(v___y_7782_);
    lean_dec_ref(v___y_7781_);
    lean_dec(v___y_7780_);
    lean_dec_ref(v___y_7779_);
    lean_dec(v_as_x27_7776_);
    lean_dec(v_as_7775_);
    lean_dec(v___x_7773_);
    return v_res_7784_;
}
pub unsafe fn l_Lean_Parser_sepBy1Indent_formatter___redArg(
    mut v_p_7785_: *mut LeanObject,
    mut v_pSep_7786_: *mut LeanObject,
    mut v_a_7787_: *mut LeanObject,
    mut v_a_7788_: *mut LeanObject,
    mut v_a_7789_: *mut LeanObject,
    mut v_a_7790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7792_: *mut LeanObject = core::ptr::null_mut();
    v___x_7792_ = l_Lean_Parser_sepByIndent_formatter___redArg(
        v_p_7785_,
        v_pSep_7786_,
        v_a_7787_,
        v_a_7788_,
        v_a_7789_,
        v_a_7790_,
    );
    return v___x_7792_;
}
pub unsafe fn l_Lean_Parser_sepBy1Indent_formatter___redArg___boxed(
    mut v_p_7793_: *mut LeanObject,
    mut v_pSep_7794_: *mut LeanObject,
    mut v_a_7795_: *mut LeanObject,
    mut v_a_7796_: *mut LeanObject,
    mut v_a_7797_: *mut LeanObject,
    mut v_a_7798_: *mut LeanObject,
    mut v_a_7799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7800_: *mut LeanObject = core::ptr::null_mut();
    v_res_7800_ = l_Lean_Parser_sepBy1Indent_formatter___redArg(
        v_p_7793_,
        v_pSep_7794_,
        v_a_7795_,
        v_a_7796_,
        v_a_7797_,
        v_a_7798_,
    );
    lean_dec(v_a_7798_);
    lean_dec_ref(v_a_7797_);
    lean_dec(v_a_7796_);
    lean_dec_ref(v_a_7795_);
    return v_res_7800_;
}
pub unsafe fn l_Lean_Parser_sepBy1Indent_formatter(
    mut v_p_7801_: *mut LeanObject,
    mut v___sep_7802_: *mut LeanObject,
    mut v_pSep_7803_: *mut LeanObject,
    mut v_a_7804_: *mut LeanObject,
    mut v_a_7805_: *mut LeanObject,
    mut v_a_7806_: *mut LeanObject,
    mut v_a_7807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7809_: *mut LeanObject = core::ptr::null_mut();
    v___x_7809_ = l_Lean_Parser_sepByIndent_formatter___redArg(
        v_p_7801_,
        v_pSep_7803_,
        v_a_7804_,
        v_a_7805_,
        v_a_7806_,
        v_a_7807_,
    );
    return v___x_7809_;
}
pub unsafe fn l_Lean_Parser_sepBy1Indent_formatter___boxed(
    mut v_p_7810_: *mut LeanObject,
    mut v___sep_7811_: *mut LeanObject,
    mut v_pSep_7812_: *mut LeanObject,
    mut v_a_7813_: *mut LeanObject,
    mut v_a_7814_: *mut LeanObject,
    mut v_a_7815_: *mut LeanObject,
    mut v_a_7816_: *mut LeanObject,
    mut v_a_7817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7818_: *mut LeanObject = core::ptr::null_mut();
    v_res_7818_ = l_Lean_Parser_sepBy1Indent_formatter(
        v_p_7810_,
        v___sep_7811_,
        v_pSep_7812_,
        v_a_7813_,
        v_a_7814_,
        v_a_7815_,
        v_a_7816_,
    );
    lean_dec(v_a_7816_);
    lean_dec_ref(v_a_7815_);
    lean_dec(v_a_7814_);
    lean_dec_ref(v_a_7813_);
    lean_dec_ref(v___sep_7811_);
    return v_res_7818_;
}
pub unsafe fn _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__0() -> *mut LeanObject {
    let mut v___f_7819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut LeanObject = core::ptr::null_mut();
    v___f_7819_ = l_Lean_Parser_mkAntiquot_parenthesizer___closed__0;
    v___x_7820_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7821_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_7821_, 0, v___x_7820_);
    lean_closure_set(v___x_7821_, 1, v___f_7819_);
    return v___x_7821_;
}
pub unsafe fn _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__1() -> *mut LeanObject {
    let mut v___x_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7824_: *mut LeanObject = core::ptr::null_mut();
    v___x_7822_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent_parenthesizer___closed__0_once),
        _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__0,
    );
    v___x_7823_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7824_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_7824_, 0, v___x_7823_);
    lean_closure_set(v___x_7824_, 1, v___x_7822_);
    return v___x_7824_;
}
pub unsafe fn l_Lean_Parser_sepByIndent_parenthesizer(
    mut v_p_7825_: *mut LeanObject,
    mut v_sep_7826_: *mut LeanObject,
    mut v_psep_7827_: *mut LeanObject,
    mut v_allowTrailingSep_7828_: u8,
    mut v_a_7829_: *mut LeanObject,
    mut v_a_7830_: *mut LeanObject,
    mut v_a_7831_: *mut LeanObject,
    mut v_a_7832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut LeanObject = core::ptr::null_mut();
    v___x_7834_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7835_ = l_Lean_Parser_sepByElemParser_formatter___closed__1;
    v___x_7836_ = l_Lean_Parser_many_parenthesizer___closed__0;
    v___x_7837_ = lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_7837_, 0, v___x_7835_);
    lean_closure_set(v___x_7837_, 1, v_p_7825_);
    lean_closure_set(v___x_7837_, 2, v___x_7836_);
    v___x_7838_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_7838_, 0, v___x_7834_);
    lean_closure_set(v___x_7838_, 1, v___x_7837_);
    v___x_7839_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent_parenthesizer___closed__1_once),
        _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__1,
    );
    v___x_7840_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_7840_, 0, v_psep_7827_);
    lean_closure_set(v___x_7840_, 1, v___x_7839_);
    v___x_7841_ = lean_box((v_allowTrailingSep_7828_) as usize);
    v___x_7842_ = lean_alloc_closure(
        l_Lean_Parser_sepBy_parenthesizer___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_7842_, 0, v___x_7838_);
    lean_closure_set(v___x_7842_, 1, v_sep_7826_);
    lean_closure_set(v___x_7842_, 2, v___x_7840_);
    lean_closure_set(v___x_7842_, 3, v___x_7841_);
    v___x_7843_ = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(
        v___x_7842_,
        v_a_7829_,
        v_a_7830_,
        v_a_7831_,
        v_a_7832_,
    );
    return v___x_7843_;
}
pub unsafe fn l_Lean_Parser_sepByIndent_parenthesizer___boxed(
    mut v_p_7844_: *mut LeanObject,
    mut v_sep_7845_: *mut LeanObject,
    mut v_psep_7846_: *mut LeanObject,
    mut v_allowTrailingSep_7847_: *mut LeanObject,
    mut v_a_7848_: *mut LeanObject,
    mut v_a_7849_: *mut LeanObject,
    mut v_a_7850_: *mut LeanObject,
    mut v_a_7851_: *mut LeanObject,
    mut v_a_7852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowTrailingSep_boxed_7853_: u8 = 0;
    let mut v_res_7854_: *mut LeanObject = core::ptr::null_mut();
    v_allowTrailingSep_boxed_7853_ = (lean_unbox(v_allowTrailingSep_7847_) as u8);
    v_res_7854_ = l_Lean_Parser_sepByIndent_parenthesizer(
        v_p_7844_,
        v_sep_7845_,
        v_psep_7846_,
        v_allowTrailingSep_boxed_7853_,
        v_a_7848_,
        v_a_7849_,
        v_a_7850_,
        v_a_7851_,
    );
    lean_dec(v_a_7851_);
    lean_dec_ref(v_a_7850_);
    lean_dec(v_a_7849_);
    lean_dec_ref(v_a_7848_);
    return v_res_7854_;
}
pub unsafe fn l_Lean_Parser_sepBy1Indent_parenthesizer(
    mut v_p_7855_: *mut LeanObject,
    mut v_sep_7856_: *mut LeanObject,
    mut v_psep_7857_: *mut LeanObject,
    mut v_allowTrailingSep_7858_: u8,
    mut v_a_7859_: *mut LeanObject,
    mut v_a_7860_: *mut LeanObject,
    mut v_a_7861_: *mut LeanObject,
    mut v_a_7862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7873_: *mut LeanObject = core::ptr::null_mut();
    v___x_7864_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_7865_ = l_Lean_Parser_sepByElemParser_formatter___closed__1;
    v___x_7866_ = l_Lean_Parser_many_parenthesizer___closed__0;
    v___x_7867_ = lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_7867_, 0, v___x_7865_);
    lean_closure_set(v___x_7867_, 1, v_p_7855_);
    lean_closure_set(v___x_7867_, 2, v___x_7866_);
    v___x_7868_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_7868_, 0, v___x_7864_);
    lean_closure_set(v___x_7868_, 1, v___x_7867_);
    v___x_7869_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_sepByIndent_parenthesizer___closed__1_once),
        _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__1,
    );
    v___x_7870_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_7870_, 0, v_psep_7857_);
    lean_closure_set(v___x_7870_, 1, v___x_7869_);
    v___x_7871_ = lean_box((v_allowTrailingSep_7858_) as usize);
    v___x_7872_ = lean_alloc_closure(
        l_Lean_Parser_sepBy1_parenthesizer___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_7872_, 0, v___x_7868_);
    lean_closure_set(v___x_7872_, 1, v_sep_7856_);
    lean_closure_set(v___x_7872_, 2, v___x_7870_);
    lean_closure_set(v___x_7872_, 3, v___x_7871_);
    v___x_7873_ = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(
        v___x_7872_,
        v_a_7859_,
        v_a_7860_,
        v_a_7861_,
        v_a_7862_,
    );
    return v___x_7873_;
}
pub unsafe fn l_Lean_Parser_sepBy1Indent_parenthesizer___boxed(
    mut v_p_7874_: *mut LeanObject,
    mut v_sep_7875_: *mut LeanObject,
    mut v_psep_7876_: *mut LeanObject,
    mut v_allowTrailingSep_7877_: *mut LeanObject,
    mut v_a_7878_: *mut LeanObject,
    mut v_a_7879_: *mut LeanObject,
    mut v_a_7880_: *mut LeanObject,
    mut v_a_7881_: *mut LeanObject,
    mut v_a_7882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowTrailingSep_boxed_7883_: u8 = 0;
    let mut v_res_7884_: *mut LeanObject = core::ptr::null_mut();
    v_allowTrailingSep_boxed_7883_ = (lean_unbox(v_allowTrailingSep_7877_) as u8);
    v_res_7884_ = l_Lean_Parser_sepBy1Indent_parenthesizer(
        v_p_7874_,
        v_sep_7875_,
        v_psep_7876_,
        v_allowTrailingSep_boxed_7883_,
        v_a_7878_,
        v_a_7879_,
        v_a_7880_,
        v_a_7881_,
    );
    lean_dec(v_a_7881_);
    lean_dec_ref(v_a_7880_);
    lean_dec(v_a_7879_);
    lean_dec_ref(v_a_7878_);
    return v_res_7884_;
}
pub unsafe fn l_Lean_Parser_notSymbol_formatter___redArg() -> *mut LeanObject {
    let mut v___x_7886_: *mut LeanObject = core::ptr::null_mut();
    v___x_7886_ = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg();
    return v___x_7886_;
}
pub unsafe fn l_Lean_Parser_notSymbol_formatter___redArg___boxed(
    mut v_a_7887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7888_: *mut LeanObject = core::ptr::null_mut();
    v_res_7888_ = l_Lean_Parser_notSymbol_formatter___redArg();
    return v_res_7888_;
}
pub unsafe fn l_Lean_Parser_notSymbol_formatter(
    mut v_s_7889_: *mut LeanObject,
    mut v_a_7890_: *mut LeanObject,
    mut v_a_7891_: *mut LeanObject,
    mut v_a_7892_: *mut LeanObject,
    mut v_a_7893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7895_: *mut LeanObject = core::ptr::null_mut();
    v___x_7895_ = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg();
    return v___x_7895_;
}
pub unsafe fn l_Lean_Parser_notSymbol_formatter___boxed(
    mut v_s_7896_: *mut LeanObject,
    mut v_a_7897_: *mut LeanObject,
    mut v_a_7898_: *mut LeanObject,
    mut v_a_7899_: *mut LeanObject,
    mut v_a_7900_: *mut LeanObject,
    mut v_a_7901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7902_: *mut LeanObject = core::ptr::null_mut();
    v_res_7902_ =
        l_Lean_Parser_notSymbol_formatter(v_s_7896_, v_a_7897_, v_a_7898_, v_a_7899_, v_a_7900_);
    lean_dec(v_a_7900_);
    lean_dec_ref(v_a_7899_);
    lean_dec(v_a_7898_);
    lean_dec_ref(v_a_7897_);
    lean_dec_ref(v_s_7896_);
    return v_res_7902_;
}
pub unsafe fn l_Lean_Parser_notSymbol_parenthesizer___redArg() -> *mut LeanObject {
    let mut v___x_7904_: *mut LeanObject = core::ptr::null_mut();
    v___x_7904_ = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg();
    return v___x_7904_;
}
pub unsafe fn l_Lean_Parser_notSymbol_parenthesizer___redArg___boxed(
    mut v_a_7905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7906_: *mut LeanObject = core::ptr::null_mut();
    v_res_7906_ = l_Lean_Parser_notSymbol_parenthesizer___redArg();
    return v_res_7906_;
}
pub unsafe fn l_Lean_Parser_notSymbol_parenthesizer(
    mut v_s_7907_: *mut LeanObject,
    mut v_a_7908_: *mut LeanObject,
    mut v_a_7909_: *mut LeanObject,
    mut v_a_7910_: *mut LeanObject,
    mut v_a_7911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7913_: *mut LeanObject = core::ptr::null_mut();
    v___x_7913_ = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg();
    return v___x_7913_;
}
pub unsafe fn l_Lean_Parser_notSymbol_parenthesizer___boxed(
    mut v_s_7914_: *mut LeanObject,
    mut v_a_7915_: *mut LeanObject,
    mut v_a_7916_: *mut LeanObject,
    mut v_a_7917_: *mut LeanObject,
    mut v_a_7918_: *mut LeanObject,
    mut v_a_7919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7920_: *mut LeanObject = core::ptr::null_mut();
    v_res_7920_ = l_Lean_Parser_notSymbol_parenthesizer(
        v_s_7914_, v_a_7915_, v_a_7916_, v_a_7917_, v_a_7918_,
    );
    lean_dec(v_a_7918_);
    lean_dec_ref(v_a_7917_);
    lean_dec(v_a_7916_);
    lean_dec_ref(v_a_7915_);
    lean_dec_ref(v_s_7914_);
    return v_res_7920_;
}
pub unsafe fn l_Lean_Parser_notSymbol(mut v_s_7921_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7923_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_s_7921_);
    v___x_7922_ = l_Lean_Parser_symbol(v_s_7921_);
    v___x_7923_ = l_Lean_Parser_notFollowedBy(v___x_7922_, v_s_7921_);
    return v___x_7923_;
}
pub unsafe fn l_Lean_Parser_patternIgnore_formatter(
    mut v_p_7927_: *mut LeanObject,
    mut v_a_7928_: *mut LeanObject,
    mut v_a_7929_: *mut LeanObject,
    mut v_a_7930_: *mut LeanObject,
    mut v_a_7931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7934_: *mut LeanObject = core::ptr::null_mut();
    v___x_7933_ = l_Lean_Parser_patternIgnore_formatter___closed__1;
    v___x_7934_ = l_Lean_PrettyPrinter_Formatter_node_formatter(
        v___x_7933_,
        v_p_7927_,
        v_a_7928_,
        v_a_7929_,
        v_a_7930_,
        v_a_7931_,
    );
    return v___x_7934_;
}
pub unsafe fn l_Lean_Parser_patternIgnore_formatter___boxed(
    mut v_p_7935_: *mut LeanObject,
    mut v_a_7936_: *mut LeanObject,
    mut v_a_7937_: *mut LeanObject,
    mut v_a_7938_: *mut LeanObject,
    mut v_a_7939_: *mut LeanObject,
    mut v_a_7940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7941_: *mut LeanObject = core::ptr::null_mut();
    v_res_7941_ = l_Lean_Parser_patternIgnore_formatter(
        v_p_7935_, v_a_7936_, v_a_7937_, v_a_7938_, v_a_7939_,
    );
    lean_dec(v_a_7939_);
    lean_dec_ref(v_a_7938_);
    lean_dec(v_a_7937_);
    lean_dec_ref(v_a_7936_);
    return v_res_7941_;
}
pub unsafe fn l_Lean_Parser_patternIgnore_parenthesizer(
    mut v_p_7942_: *mut LeanObject,
    mut v_a_7943_: *mut LeanObject,
    mut v_a_7944_: *mut LeanObject,
    mut v_a_7945_: *mut LeanObject,
    mut v_a_7946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7949_: *mut LeanObject = core::ptr::null_mut();
    v___x_7948_ = l_Lean_Parser_patternIgnore_formatter___closed__1;
    v___x_7949_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(
        v___x_7948_,
        v_p_7942_,
        v_a_7943_,
        v_a_7944_,
        v_a_7945_,
        v_a_7946_,
    );
    return v___x_7949_;
}
pub unsafe fn l_Lean_Parser_patternIgnore_parenthesizer___boxed(
    mut v_p_7950_: *mut LeanObject,
    mut v_a_7951_: *mut LeanObject,
    mut v_a_7952_: *mut LeanObject,
    mut v_a_7953_: *mut LeanObject,
    mut v_a_7954_: *mut LeanObject,
    mut v_a_7955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7956_: *mut LeanObject = core::ptr::null_mut();
    v_res_7956_ = l_Lean_Parser_patternIgnore_parenthesizer(
        v_p_7950_, v_a_7951_, v_a_7952_, v_a_7953_, v_a_7954_,
    );
    lean_dec(v_a_7954_);
    lean_dec_ref(v_a_7953_);
    lean_dec(v_a_7952_);
    lean_dec_ref(v_a_7951_);
    return v_res_7956_;
}
pub unsafe fn l_Lean_Parser_patternIgnore(mut v_p_7957_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut LeanObject = core::ptr::null_mut();
    v___x_7958_ = l_Lean_Parser_patternIgnore_formatter___closed__1;
    v___x_7959_ = l_Lean_Parser_node(v___x_7958_, v_p_7957_);
    return v___x_7959_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1()
-> *mut LeanObject {
    let mut v___x_7966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7968_: *mut LeanObject = core::ptr::null_mut();
    v___x_7966_ = l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0;
    v___x_7967_ = l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1;
    v___x_7968_ = l_Lean_addBuiltinDocString(v___x_7966_, v___x_7967_);
    return v___x_7968_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___boxed(
    mut v_a_7969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7970_: *mut LeanObject = core::ptr::null_mut();
    v_res_7970_ = l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1();
    return v_res_7970_;
}
pub unsafe fn _init_l_Lean_Parser_ppHardSpace() -> *mut LeanObject {
    let mut v___x_7971_: *mut LeanObject = core::ptr::null_mut();
    v___x_7971_ = l_Lean_Parser_skip;
    return v___x_7971_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1()
-> *mut LeanObject {
    let mut v___x_7979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7981_: *mut LeanObject = core::ptr::null_mut();
    v___x_7979_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1;
    v___x_7980_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2;
    v___x_7981_ = l_Lean_addBuiltinDocString(v___x_7979_, v___x_7980_);
    return v___x_7981_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___boxed(
    mut v_a_7982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7983_: *mut LeanObject = core::ptr::null_mut();
    v_res_7983_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1();
    return v_res_7983_;
}
pub unsafe fn _init_l_Lean_Parser_ppSpace() -> *mut LeanObject {
    let mut v___x_7984_: *mut LeanObject = core::ptr::null_mut();
    v___x_7984_ = l_Lean_Parser_skip;
    return v___x_7984_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1()
-> *mut LeanObject {
    let mut v___x_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7994_: *mut LeanObject = core::ptr::null_mut();
    v___x_7992_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1;
    v___x_7993_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2;
    v___x_7994_ = l_Lean_addBuiltinDocString(v___x_7992_, v___x_7993_);
    return v___x_7994_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___boxed(
    mut v_a_7995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7996_: *mut LeanObject = core::ptr::null_mut();
    v_res_7996_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1();
    return v_res_7996_;
}
pub unsafe fn _init_l_Lean_Parser_ppLine() -> *mut LeanObject {
    let mut v___x_7997_: *mut LeanObject = core::ptr::null_mut();
    v___x_7997_ = l_Lean_Parser_skip;
    return v___x_7997_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1()
-> *mut LeanObject {
    let mut v___x_8005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8007_: *mut LeanObject = core::ptr::null_mut();
    v___x_8005_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1;
    v___x_8006_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2;
    v___x_8007_ = l_Lean_addBuiltinDocString(v___x_8005_, v___x_8006_);
    return v___x_8007_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___boxed(
    mut v_a_8008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8009_: *mut LeanObject = core::ptr::null_mut();
    v_res_8009_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1();
    return v_res_8009_;
}
pub unsafe fn l_Lean_Parser_ppRealFill(mut v_a_8010_: *mut LeanObject) -> *mut LeanObject {
    lean_inc_ref(v_a_8010_);
    return v_a_8010_;
}
pub unsafe fn l_Lean_Parser_ppRealFill___boxed(mut v_a_8011_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_8012_: *mut LeanObject = core::ptr::null_mut();
    v_res_8012_ = l_Lean_Parser_ppRealFill(v_a_8011_);
    lean_dec_ref(v_a_8011_);
    return v_res_8012_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1()
-> *mut LeanObject {
    let mut v___x_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8022_: *mut LeanObject = core::ptr::null_mut();
    v___x_8020_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1;
    v___x_8021_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2;
    v___x_8022_ = l_Lean_addBuiltinDocString(v___x_8020_, v___x_8021_);
    return v___x_8022_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___boxed(
    mut v_a_8023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8024_: *mut LeanObject = core::ptr::null_mut();
    v_res_8024_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1();
    return v_res_8024_;
}
pub unsafe fn l_Lean_Parser_ppRealGroup(mut v_a_8025_: *mut LeanObject) -> *mut LeanObject {
    lean_inc_ref(v_a_8025_);
    return v_a_8025_;
}
pub unsafe fn l_Lean_Parser_ppRealGroup___boxed(mut v_a_8026_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_8027_: *mut LeanObject = core::ptr::null_mut();
    v_res_8027_ = l_Lean_Parser_ppRealGroup(v_a_8026_);
    lean_dec_ref(v_a_8026_);
    return v_res_8027_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1()
-> *mut LeanObject {
    let mut v___x_8035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut LeanObject = core::ptr::null_mut();
    v___x_8035_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1;
    v___x_8036_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2;
    v___x_8037_ = l_Lean_addBuiltinDocString(v___x_8035_, v___x_8036_);
    return v___x_8037_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___boxed(
    mut v_a_8038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8039_: *mut LeanObject = core::ptr::null_mut();
    v_res_8039_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1();
    return v_res_8039_;
}
pub unsafe fn l_Lean_Parser_ppIndent(mut v_a_8040_: *mut LeanObject) -> *mut LeanObject {
    lean_inc_ref(v_a_8040_);
    return v_a_8040_;
}
pub unsafe fn l_Lean_Parser_ppIndent___boxed(mut v_a_8041_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_8042_: *mut LeanObject = core::ptr::null_mut();
    v_res_8042_ = l_Lean_Parser_ppIndent(v_a_8041_);
    lean_dec_ref(v_a_8041_);
    return v_res_8042_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1()
-> *mut LeanObject {
    let mut v___x_8050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8052_: *mut LeanObject = core::ptr::null_mut();
    v___x_8050_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1;
    v___x_8051_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2;
    v___x_8052_ = l_Lean_addBuiltinDocString(v___x_8050_, v___x_8051_);
    return v___x_8052_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___boxed(
    mut v_a_8053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8054_: *mut LeanObject = core::ptr::null_mut();
    v_res_8054_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1();
    return v_res_8054_;
}
pub unsafe fn l_Lean_Parser_ppGroup(mut v_p_8055_: *mut LeanObject) -> *mut LeanObject {
    lean_inc_ref(v_p_8055_);
    return v_p_8055_;
}
pub unsafe fn l_Lean_Parser_ppGroup___boxed(mut v_p_8056_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_8057_: *mut LeanObject = core::ptr::null_mut();
    v_res_8057_ = l_Lean_Parser_ppGroup(v_p_8056_);
    lean_dec_ref(v_p_8056_);
    return v_res_8057_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1()
-> *mut LeanObject {
    let mut v___x_8065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8067_: *mut LeanObject = core::ptr::null_mut();
    v___x_8065_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1;
    v___x_8066_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2;
    v___x_8067_ = l_Lean_addBuiltinDocString(v___x_8065_, v___x_8066_);
    return v___x_8067_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___boxed(
    mut v_a_8068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8069_: *mut LeanObject = core::ptr::null_mut();
    v_res_8069_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1();
    return v_res_8069_;
}
pub unsafe fn l_Lean_Parser_ppDedent(mut v_a_8070_: *mut LeanObject) -> *mut LeanObject {
    lean_inc_ref(v_a_8070_);
    return v_a_8070_;
}
pub unsafe fn l_Lean_Parser_ppDedent___boxed(mut v_a_8071_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_8072_: *mut LeanObject = core::ptr::null_mut();
    v_res_8072_ = l_Lean_Parser_ppDedent(v_a_8071_);
    lean_dec_ref(v_a_8071_);
    return v_res_8072_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1()
-> *mut LeanObject {
    let mut v___x_8080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8082_: *mut LeanObject = core::ptr::null_mut();
    v___x_8080_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1;
    v___x_8081_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2;
    v___x_8082_ = l_Lean_addBuiltinDocString(v___x_8080_, v___x_8081_);
    return v___x_8082_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___boxed(
    mut v_a_8083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8084_: *mut LeanObject = core::ptr::null_mut();
    v_res_8084_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1();
    return v_res_8084_;
}
pub unsafe fn _init_l_Lean_Parser_ppAllowUngrouped() -> *mut LeanObject {
    let mut v___x_8085_: *mut LeanObject = core::ptr::null_mut();
    v___x_8085_ = l_Lean_Parser_skip;
    return v___x_8085_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1()
-> *mut LeanObject {
    let mut v___x_8093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8095_: *mut LeanObject = core::ptr::null_mut();
    v___x_8093_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1;
    v___x_8094_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2;
    v___x_8095_ = l_Lean_addBuiltinDocString(v___x_8093_, v___x_8094_);
    return v___x_8095_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___boxed(
    mut v_a_8096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8097_: *mut LeanObject = core::ptr::null_mut();
    v_res_8097_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1();
    return v_res_8097_;
}
pub unsafe fn l_Lean_Parser_ppDedentIfGrouped(mut v_a_8098_: *mut LeanObject) -> *mut LeanObject {
    lean_inc_ref(v_a_8098_);
    return v_a_8098_;
}
pub unsafe fn l_Lean_Parser_ppDedentIfGrouped___boxed(
    mut v_a_8099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8100_: *mut LeanObject = core::ptr::null_mut();
    v_res_8100_ = l_Lean_Parser_ppDedentIfGrouped(v_a_8099_);
    lean_dec_ref(v_a_8099_);
    return v_res_8100_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1()
-> *mut LeanObject {
    let mut v___x_8108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8110_: *mut LeanObject = core::ptr::null_mut();
    v___x_8108_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1;
    v___x_8109_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2;
    v___x_8110_ = l_Lean_addBuiltinDocString(v___x_8108_, v___x_8109_);
    return v___x_8110_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___boxed(
    mut v_a_8111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8112_: *mut LeanObject = core::ptr::null_mut();
    v_res_8112_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1();
    return v_res_8112_;
}
pub unsafe fn _init_l_Lean_Parser_ppHardLineUnlessUngrouped() -> *mut LeanObject {
    let mut v___x_8113_: *mut LeanObject = core::ptr::null_mut();
    v___x_8113_ = l_Lean_Parser_skip;
    return v___x_8113_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1()
-> *mut LeanObject {
    let mut v___x_8121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8123_: *mut LeanObject = core::ptr::null_mut();
    v___x_8121_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1;
    v___x_8122_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2;
    v___x_8123_ = l_Lean_addBuiltinDocString(v___x_8121_, v___x_8122_);
    return v___x_8123_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___boxed(
    mut v_a_8124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8125_: *mut LeanObject = core::ptr::null_mut();
    v_res_8125_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1();
    return v_res_8125_;
}
pub unsafe fn l_Lean_ppHardSpace_formatter___redArg(
    mut v_a_8129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8132_: *mut LeanObject = core::ptr::null_mut();
    v___x_8131_ = l_Lean_ppHardSpace_formatter___redArg___closed__1;
    v___x_8132_ = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(v___x_8131_, v_a_8129_);
    return v___x_8132_;
}
pub unsafe fn l_Lean_ppHardSpace_formatter___redArg___boxed(
    mut v_a_8133_: *mut LeanObject,
    mut v_a_8134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8135_: *mut LeanObject = core::ptr::null_mut();
    v_res_8135_ = l_Lean_ppHardSpace_formatter___redArg(v_a_8133_);
    lean_dec(v_a_8133_);
    return v_res_8135_;
}
pub unsafe fn l_Lean_ppHardSpace_formatter(
    mut v_a_8136_: *mut LeanObject,
    mut v_a_8137_: *mut LeanObject,
    mut v_a_8138_: *mut LeanObject,
    mut v_a_8139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8141_: *mut LeanObject = core::ptr::null_mut();
    v___x_8141_ = l_Lean_ppHardSpace_formatter___redArg(v_a_8137_);
    return v___x_8141_;
}
pub unsafe fn l_Lean_ppHardSpace_formatter___boxed(
    mut v_a_8142_: *mut LeanObject,
    mut v_a_8143_: *mut LeanObject,
    mut v_a_8144_: *mut LeanObject,
    mut v_a_8145_: *mut LeanObject,
    mut v_a_8146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8147_: *mut LeanObject = core::ptr::null_mut();
    v_res_8147_ = l_Lean_ppHardSpace_formatter(v_a_8142_, v_a_8143_, v_a_8144_, v_a_8145_);
    lean_dec(v_a_8145_);
    lean_dec_ref(v_a_8144_);
    lean_dec(v_a_8143_);
    lean_dec_ref(v_a_8142_);
    return v_res_8147_;
}
pub unsafe fn l_Lean_ppSpace_formatter___redArg(mut v_a_8148_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8150_: *mut LeanObject = core::ptr::null_mut();
    v___x_8150_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v_a_8148_);
    return v___x_8150_;
}
pub unsafe fn l_Lean_ppSpace_formatter___redArg___boxed(
    mut v_a_8151_: *mut LeanObject,
    mut v_a_8152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8153_: *mut LeanObject = core::ptr::null_mut();
    v_res_8153_ = l_Lean_ppSpace_formatter___redArg(v_a_8151_);
    lean_dec(v_a_8151_);
    return v_res_8153_;
}
pub unsafe fn l_Lean_ppSpace_formatter(
    mut v_a_8154_: *mut LeanObject,
    mut v_a_8155_: *mut LeanObject,
    mut v_a_8156_: *mut LeanObject,
    mut v_a_8157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8159_: *mut LeanObject = core::ptr::null_mut();
    v___x_8159_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v_a_8155_);
    return v___x_8159_;
}
pub unsafe fn l_Lean_ppSpace_formatter___boxed(
    mut v_a_8160_: *mut LeanObject,
    mut v_a_8161_: *mut LeanObject,
    mut v_a_8162_: *mut LeanObject,
    mut v_a_8163_: *mut LeanObject,
    mut v_a_8164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8165_: *mut LeanObject = core::ptr::null_mut();
    v_res_8165_ = l_Lean_ppSpace_formatter(v_a_8160_, v_a_8161_, v_a_8162_, v_a_8163_);
    lean_dec(v_a_8163_);
    lean_dec_ref(v_a_8162_);
    lean_dec(v_a_8161_);
    lean_dec_ref(v_a_8160_);
    return v_res_8165_;
}
pub unsafe fn l_Lean_ppLine_formatter___redArg(mut v_a_8166_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8169_: *mut LeanObject = core::ptr::null_mut();
    v___x_8168_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1;
    v___x_8169_ = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(v___x_8168_, v_a_8166_);
    return v___x_8169_;
}
pub unsafe fn l_Lean_ppLine_formatter___redArg___boxed(
    mut v_a_8170_: *mut LeanObject,
    mut v_a_8171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8172_: *mut LeanObject = core::ptr::null_mut();
    v_res_8172_ = l_Lean_ppLine_formatter___redArg(v_a_8170_);
    lean_dec(v_a_8170_);
    return v_res_8172_;
}
pub unsafe fn l_Lean_ppLine_formatter(
    mut v_a_8173_: *mut LeanObject,
    mut v_a_8174_: *mut LeanObject,
    mut v_a_8175_: *mut LeanObject,
    mut v_a_8176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8178_: *mut LeanObject = core::ptr::null_mut();
    v___x_8178_ = l_Lean_ppLine_formatter___redArg(v_a_8174_);
    return v___x_8178_;
}
pub unsafe fn l_Lean_ppLine_formatter___boxed(
    mut v_a_8179_: *mut LeanObject,
    mut v_a_8180_: *mut LeanObject,
    mut v_a_8181_: *mut LeanObject,
    mut v_a_8182_: *mut LeanObject,
    mut v_a_8183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8184_: *mut LeanObject = core::ptr::null_mut();
    v_res_8184_ = l_Lean_ppLine_formatter(v_a_8179_, v_a_8180_, v_a_8181_, v_a_8182_);
    lean_dec(v_a_8182_);
    lean_dec_ref(v_a_8181_);
    lean_dec(v_a_8180_);
    lean_dec_ref(v_a_8179_);
    return v_res_8184_;
}
pub unsafe fn l_Lean_ppRealFill_formatter(
    mut v_p_8185_: *mut LeanObject,
    mut v_a_8186_: *mut LeanObject,
    mut v_a_8187_: *mut LeanObject,
    mut v_a_8188_: *mut LeanObject,
    mut v_a_8189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8191_: *mut LeanObject = core::ptr::null_mut();
    v___x_8191_ =
        l_Lean_PrettyPrinter_Formatter_fill(v_p_8185_, v_a_8186_, v_a_8187_, v_a_8188_, v_a_8189_);
    return v___x_8191_;
}
pub unsafe fn l_Lean_ppRealFill_formatter___boxed(
    mut v_p_8192_: *mut LeanObject,
    mut v_a_8193_: *mut LeanObject,
    mut v_a_8194_: *mut LeanObject,
    mut v_a_8195_: *mut LeanObject,
    mut v_a_8196_: *mut LeanObject,
    mut v_a_8197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8198_: *mut LeanObject = core::ptr::null_mut();
    v_res_8198_ =
        l_Lean_ppRealFill_formatter(v_p_8192_, v_a_8193_, v_a_8194_, v_a_8195_, v_a_8196_);
    lean_dec(v_a_8196_);
    lean_dec_ref(v_a_8195_);
    lean_dec(v_a_8194_);
    lean_dec_ref(v_a_8193_);
    return v_res_8198_;
}
pub unsafe fn l_Lean_ppRealGroup_formatter(
    mut v_p_8199_: *mut LeanObject,
    mut v_a_8200_: *mut LeanObject,
    mut v_a_8201_: *mut LeanObject,
    mut v_a_8202_: *mut LeanObject,
    mut v_a_8203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8205_: *mut LeanObject = core::ptr::null_mut();
    v___x_8205_ =
        l_Lean_PrettyPrinter_Formatter_group(v_p_8199_, v_a_8200_, v_a_8201_, v_a_8202_, v_a_8203_);
    return v___x_8205_;
}
pub unsafe fn l_Lean_ppRealGroup_formatter___boxed(
    mut v_p_8206_: *mut LeanObject,
    mut v_a_8207_: *mut LeanObject,
    mut v_a_8208_: *mut LeanObject,
    mut v_a_8209_: *mut LeanObject,
    mut v_a_8210_: *mut LeanObject,
    mut v_a_8211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8212_: *mut LeanObject = core::ptr::null_mut();
    v_res_8212_ =
        l_Lean_ppRealGroup_formatter(v_p_8206_, v_a_8207_, v_a_8208_, v_a_8209_, v_a_8210_);
    lean_dec(v_a_8210_);
    lean_dec_ref(v_a_8209_);
    lean_dec(v_a_8208_);
    lean_dec_ref(v_a_8207_);
    return v_res_8212_;
}
pub unsafe fn l_Lean_ppIndent_formatter(
    mut v_p_8213_: *mut LeanObject,
    mut v_a_8214_: *mut LeanObject,
    mut v_a_8215_: *mut LeanObject,
    mut v_a_8216_: *mut LeanObject,
    mut v_a_8217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8220_: *mut LeanObject = core::ptr::null_mut();
    v___x_8219_ = lean_box(0);
    v___x_8220_ = l_Lean_PrettyPrinter_Formatter_indent(
        v_p_8213_,
        v___x_8219_,
        v_a_8214_,
        v_a_8215_,
        v_a_8216_,
        v_a_8217_,
    );
    return v___x_8220_;
}
pub unsafe fn l_Lean_ppIndent_formatter___boxed(
    mut v_p_8221_: *mut LeanObject,
    mut v_a_8222_: *mut LeanObject,
    mut v_a_8223_: *mut LeanObject,
    mut v_a_8224_: *mut LeanObject,
    mut v_a_8225_: *mut LeanObject,
    mut v_a_8226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8227_: *mut LeanObject = core::ptr::null_mut();
    v_res_8227_ = l_Lean_ppIndent_formatter(v_p_8221_, v_a_8222_, v_a_8223_, v_a_8224_, v_a_8225_);
    lean_dec(v_a_8225_);
    lean_dec_ref(v_a_8224_);
    lean_dec(v_a_8223_);
    lean_dec_ref(v_a_8222_);
    return v_res_8227_;
}
pub unsafe fn _init_l_Lean_ppDedent_formatter___closed__0() -> *mut LeanObject {
    let mut v___x_8228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8229_: *mut LeanObject = core::ptr::null_mut();
    v___x_8228_ = lean_unsigned_to_nat(0);
    v___x_8229_ = lean_nat_to_int(v___x_8228_);
    return v___x_8229_;
}
pub unsafe fn l_Lean_ppDedent_formatter(
    mut v_p_8230_: *mut LeanObject,
    mut v_a_8231_: *mut LeanObject,
    mut v_a_8232_: *mut LeanObject,
    mut v_a_8233_: *mut LeanObject,
    mut v_a_8234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_8236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8242_: *mut LeanObject = core::ptr::null_mut();
    v_options_8236_ = lean_ctor_get(v_a_8233_, 2);
    v___x_8237_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ppDedent_formatter___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ppDedent_formatter___closed__0_once),
        _init_l_Lean_ppDedent_formatter___closed__0,
    );
    v___x_8238_ = l_Std_Format_getIndent(v_options_8236_);
    v___x_8239_ = lean_nat_to_int(v___x_8238_);
    v___x_8240_ = lean_int_sub(v___x_8237_, v___x_8239_);
    lean_dec(v___x_8239_);
    v___x_8241_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8241_, 0, v___x_8240_);
    v___x_8242_ = l_Lean_PrettyPrinter_Formatter_indent(
        v_p_8230_,
        v___x_8241_,
        v_a_8231_,
        v_a_8232_,
        v_a_8233_,
        v_a_8234_,
    );
    return v___x_8242_;
}
pub unsafe fn l_Lean_ppDedent_formatter___boxed(
    mut v_p_8243_: *mut LeanObject,
    mut v_a_8244_: *mut LeanObject,
    mut v_a_8245_: *mut LeanObject,
    mut v_a_8246_: *mut LeanObject,
    mut v_a_8247_: *mut LeanObject,
    mut v_a_8248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8249_: *mut LeanObject = core::ptr::null_mut();
    v_res_8249_ = l_Lean_ppDedent_formatter(v_p_8243_, v_a_8244_, v_a_8245_, v_a_8246_, v_a_8247_);
    lean_dec(v_a_8247_);
    lean_dec_ref(v_a_8246_);
    lean_dec(v_a_8245_);
    lean_dec_ref(v_a_8244_);
    return v_res_8249_;
}
pub unsafe fn l_Lean_ppAllowUngrouped_formatter___redArg(
    mut v_a_8250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxTrav_8253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leadWord_8254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leadWordIdent_8255_: u8 = 0;
    let mut v_isUngrouped_8256_: u8 = 0;
    let mut v_stack_8257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8260_: u8 = 0;
    let mut v___x_8261_: u8 = 0;
    let mut v___x_8263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8252_ = lean_st_ref_take(v_a_8250_);
                v_stxTrav_8253_ = lean_ctor_get(v___x_8252_, 0);
                v_leadWord_8254_ = lean_ctor_get(v___x_8252_, 1);
                v_leadWordIdent_8255_ = lean_ctor_get_uint8(
                    v___x_8252_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isUngrouped_8256_ = lean_ctor_get_uint8(
                    v___x_8252_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_stack_8257_ = lean_ctor_get(v___x_8252_, 2);
                v_isSharedCheck_8268_ = (!lean_is_exclusive(v___x_8252_)) as u8;
                if v_isSharedCheck_8268_ == 0 {
                    v___x_8259_ = v___x_8252_;
                    v_isShared_8260_ = v_isSharedCheck_8268_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stack_8257_);
                    lean_inc(v_leadWord_8254_);
                    lean_inc(v_stxTrav_8253_);
                    lean_dec(v___x_8252_);
                    v___x_8259_ = lean_box(0);
                    v_isShared_8260_ = v_isSharedCheck_8268_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8261_ = 0;
                if v_isShared_8260_ == 0 {
                    v___x_8263_ = v___x_8259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8267_ = lean_alloc_ctor(0, 3, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8267_, 0, v_stxTrav_8253_);
                    lean_ctor_set(v_reuseFailAlloc_8267_, 1, v_leadWord_8254_);
                    lean_ctor_set(v_reuseFailAlloc_8267_, 2, v_stack_8257_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8267_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_leadWordIdent_8255_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8267_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isUngrouped_8256_,
                    );
                    v___x_8263_ = v_reuseFailAlloc_8267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_8263_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    v___x_8261_,
                );
                v___x_8264_ = lean_st_ref_set(v_a_8250_, v___x_8263_);
                v___x_8265_ = lean_box(0);
                v___x_8266_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8266_, 0, v___x_8265_);
                return v___x_8266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ppAllowUngrouped_formatter___redArg___boxed(
    mut v_a_8269_: *mut LeanObject,
    mut v_a_8270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8271_: *mut LeanObject = core::ptr::null_mut();
    v_res_8271_ = l_Lean_ppAllowUngrouped_formatter___redArg(v_a_8269_);
    lean_dec(v_a_8269_);
    return v_res_8271_;
}
pub unsafe fn l_Lean_ppAllowUngrouped_formatter(
    mut v_a_8272_: *mut LeanObject,
    mut v_a_8273_: *mut LeanObject,
    mut v_a_8274_: *mut LeanObject,
    mut v_a_8275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8277_: *mut LeanObject = core::ptr::null_mut();
    v___x_8277_ = l_Lean_ppAllowUngrouped_formatter___redArg(v_a_8273_);
    return v___x_8277_;
}
pub unsafe fn l_Lean_ppAllowUngrouped_formatter___boxed(
    mut v_a_8278_: *mut LeanObject,
    mut v_a_8279_: *mut LeanObject,
    mut v_a_8280_: *mut LeanObject,
    mut v_a_8281_: *mut LeanObject,
    mut v_a_8282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8283_: *mut LeanObject = core::ptr::null_mut();
    v_res_8283_ = l_Lean_ppAllowUngrouped_formatter(v_a_8278_, v_a_8279_, v_a_8280_, v_a_8281_);
    lean_dec(v_a_8281_);
    lean_dec_ref(v_a_8280_);
    lean_dec(v_a_8279_);
    lean_dec_ref(v_a_8278_);
    return v_res_8283_;
}
pub unsafe fn l_Lean_ppDedentIfGrouped_formatter(
    mut v_p_8284_: *mut LeanObject,
    mut v_a_8285_: *mut LeanObject,
    mut v_a_8286_: *mut LeanObject,
    mut v_a_8287_: *mut LeanObject,
    mut v_a_8288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8293_: u8 = 0;
    let mut v___x_8294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isUngrouped_8295_: u8 = 0;
    let mut v___x_8296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxTrav_8304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leadWord_8305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leadWordIdent_8306_: u8 = 0;
    let mut v_isUngrouped_8307_: u8 = 0;
    let mut v_mustBeGrouped_8308_: u8 = 0;
    let mut v_stack_8309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8314_: u8 = 0;
    let mut v___x_8316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8317_: u8 = 0;
    let mut v_options_8318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_8320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_8321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8330_: u8 = 0;
    let mut v_unused_8331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8338_: u8 = 0;
    let mut v_unused_8339_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8290_ = l_Lean_PrettyPrinter_Formatter_concat(
                    v_p_8284_, v_a_8285_, v_a_8286_, v_a_8287_, v_a_8288_,
                );
                if lean_obj_tag(v___x_8290_) == 0 {
                    v_isSharedCheck_8338_ = (!lean_is_exclusive(v___x_8290_)) as u8;
                    if v_isSharedCheck_8338_ == 0 {
                        v_unused_8339_ = lean_ctor_get(v___x_8290_, 0);
                        lean_dec(v_unused_8339_);
                        v___x_8292_ = v___x_8290_;
                        v_isShared_8293_ = v_isSharedCheck_8338_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_8290_);
                        v___x_8292_ = lean_box(0);
                        v_isShared_8293_ = v_isSharedCheck_8338_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_8290_;
                }
            }
            1 => {
                v___x_8294_ = lean_st_ref_get(v_a_8286_);
                v_isUngrouped_8295_ = lean_ctor_get_uint8(
                    v___x_8294_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                lean_dec(v___x_8294_);
                if v_isUngrouped_8295_ == 0 {
                    v___x_8296_ = lean_st_ref_take(v_a_8286_);
                    v_stxTrav_8304_ = lean_ctor_get(v___x_8296_, 0);
                    lean_inc_ref(v_stxTrav_8304_);
                    v_leadWord_8305_ = lean_ctor_get(v___x_8296_, 1);
                    lean_inc_ref(v_leadWord_8305_);
                    v_leadWordIdent_8306_ = lean_ctor_get_uint8(
                        v___x_8296_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_isUngrouped_8307_ = lean_ctor_get_uint8(
                        v___x_8296_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_mustBeGrouped_8308_ = lean_ctor_get_uint8(
                        v___x_8296_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_stack_8309_ = lean_ctor_get(v___x_8296_, 2);
                    lean_inc_ref(v_stack_8309_);
                    v___x_8310_ = lean_box(0);
                    v___x_8311_ = lean_array_get_size(v_stack_8309_);
                    v___x_8312_ = lean_unsigned_to_nat(1);
                    v___x_8313_ = lean_nat_sub(v___x_8311_, v___x_8312_);
                    v___x_8314_ = lean_nat_dec_lt(v___x_8313_, v___x_8311_);
                    if v___x_8314_ == 0 {
                        lean_dec(v___x_8313_);
                        lean_dec_ref(v_stack_8309_);
                        lean_dec_ref(v_leadWord_8305_);
                        lean_dec_ref(v_stxTrav_8304_);
                        v_fst_8298_ = v___x_8310_;
                        v_snd_8299_ = v___x_8296_;
                        state = 2;
                        continue;
                    } else {
                        v_isSharedCheck_8330_ = (!lean_is_exclusive(v___x_8296_)) as u8;
                        if v_isSharedCheck_8330_ == 0 {
                            v_unused_8331_ = lean_ctor_get(v___x_8296_, 2);
                            lean_dec(v_unused_8331_);
                            v_unused_8332_ = lean_ctor_get(v___x_8296_, 1);
                            lean_dec(v_unused_8332_);
                            v_unused_8333_ = lean_ctor_get(v___x_8296_, 0);
                            lean_dec(v_unused_8333_);
                            v___x_8316_ = v___x_8296_;
                            v_isShared_8317_ = v_isSharedCheck_8330_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v___x_8296_);
                            v___x_8316_ = lean_box(0);
                            v_isShared_8317_ = v_isSharedCheck_8330_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_8334_ = lean_box(0);
                    if v_isShared_8293_ == 0 {
                        lean_ctor_set(v___x_8292_, 0, v___x_8334_);
                        v___x_8336_ = v___x_8292_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_8337_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8337_, 0, v___x_8334_);
                        v___x_8336_ = v_reuseFailAlloc_8337_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8300_ = lean_st_ref_set(v_a_8286_, v_snd_8299_);
                if v_isShared_8293_ == 0 {
                    lean_ctor_set(v___x_8292_, 0, v_fst_8298_);
                    v___x_8302_ = v___x_8292_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8303_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8303_, 0, v_fst_8298_);
                    v___x_8302_ = v_reuseFailAlloc_8303_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8302_;
            }
            4 => {
                v_options_8318_ = lean_ctor_get(v_a_8287_, 2);
                v___x_8319_ = l_Std_Format_getIndent(v_options_8318_);
                v_v_8320_ = lean_array_fget(v_stack_8309_, v___x_8313_);
                v_xs_x27_8321_ = lean_array_fset(v_stack_8309_, v___x_8313_, v___x_8310_);
                v___x_8322_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_ppDedent_formatter___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_ppDedent_formatter___closed__0_once),
                    _init_l_Lean_ppDedent_formatter___closed__0,
                );
                v___x_8323_ = lean_nat_to_int(v___x_8319_);
                v___x_8324_ = lean_int_sub(v___x_8322_, v___x_8323_);
                lean_dec(v___x_8323_);
                v___x_8325_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_8325_, 0, v___x_8324_);
                lean_ctor_set(v___x_8325_, 1, v_v_8320_);
                v___x_8326_ = lean_array_fset(v_xs_x27_8321_, v___x_8313_, v___x_8325_);
                lean_dec(v___x_8313_);
                if v_isShared_8317_ == 0 {
                    lean_ctor_set(v___x_8316_, 2, v___x_8326_);
                    v___x_8328_ = v___x_8316_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8329_ = lean_alloc_ctor(0, 3, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8329_, 0, v_stxTrav_8304_);
                    lean_ctor_set(v_reuseFailAlloc_8329_, 1, v_leadWord_8305_);
                    lean_ctor_set(v_reuseFailAlloc_8329_, 2, v___x_8326_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8329_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_leadWordIdent_8306_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8329_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isUngrouped_8307_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8329_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_mustBeGrouped_8308_,
                    );
                    v___x_8328_ = v_reuseFailAlloc_8329_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fst_8298_ = v___x_8310_;
                v_snd_8299_ = v___x_8328_;
                state = 2;
                continue;
            }
            6 => {
                return v___x_8336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ppDedentIfGrouped_formatter___boxed(
    mut v_p_8340_: *mut LeanObject,
    mut v_a_8341_: *mut LeanObject,
    mut v_a_8342_: *mut LeanObject,
    mut v_a_8343_: *mut LeanObject,
    mut v_a_8344_: *mut LeanObject,
    mut v_a_8345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8346_: *mut LeanObject = core::ptr::null_mut();
    v_res_8346_ =
        l_Lean_ppDedentIfGrouped_formatter(v_p_8340_, v_a_8341_, v_a_8342_, v_a_8343_, v_a_8344_);
    lean_dec(v_a_8344_);
    lean_dec_ref(v_a_8343_);
    lean_dec(v_a_8342_);
    lean_dec_ref(v_a_8341_);
    return v_res_8346_;
}
pub unsafe fn l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(
    mut v_a_8347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isUngrouped_8350_: u8 = 0;
    v___x_8349_ = lean_st_ref_get(v_a_8347_);
    v_isUngrouped_8350_ = lean_ctor_get_uint8(
        v___x_8349_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
    );
    lean_dec(v___x_8349_);
    if v_isUngrouped_8350_ == 0 {
        let mut v___x_8351_: *mut LeanObject = core::ptr::null_mut();
        v___x_8351_ = l_Lean_ppLine_formatter___redArg(v_a_8347_);
        return v___x_8351_;
    } else {
        let mut v___x_8352_: *mut LeanObject = core::ptr::null_mut();
        v___x_8352_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v_a_8347_);
        return v___x_8352_;
    }
}
pub unsafe fn l_Lean_ppHardLineUnlessUngrouped_formatter___redArg___boxed(
    mut v_a_8353_: *mut LeanObject,
    mut v_a_8354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8355_: *mut LeanObject = core::ptr::null_mut();
    v_res_8355_ = l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(v_a_8353_);
    lean_dec(v_a_8353_);
    return v_res_8355_;
}
pub unsafe fn l_Lean_ppHardLineUnlessUngrouped_formatter(
    mut v_a_8356_: *mut LeanObject,
    mut v_a_8357_: *mut LeanObject,
    mut v_a_8358_: *mut LeanObject,
    mut v_a_8359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8361_: *mut LeanObject = core::ptr::null_mut();
    v___x_8361_ = l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(v_a_8357_);
    return v___x_8361_;
}
pub unsafe fn l_Lean_ppHardLineUnlessUngrouped_formatter___boxed(
    mut v_a_8362_: *mut LeanObject,
    mut v_a_8363_: *mut LeanObject,
    mut v_a_8364_: *mut LeanObject,
    mut v_a_8365_: *mut LeanObject,
    mut v_a_8366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8367_: *mut LeanObject = core::ptr::null_mut();
    v_res_8367_ =
        l_Lean_ppHardLineUnlessUngrouped_formatter(v_a_8362_, v_a_8363_, v_a_8364_, v_a_8365_);
    lean_dec(v_a_8365_);
    lean_dec_ref(v_a_8364_);
    lean_dec(v_a_8363_);
    lean_dec_ref(v_a_8362_);
    return v_res_8367_;
}
pub unsafe fn l_Lean_Parser_ppHardSpace_parenthesizer___redArg() -> *mut LeanObject {
    let mut v___x_8369_: *mut LeanObject = core::ptr::null_mut();
    v___x_8369_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
    return v___x_8369_;
}
pub unsafe fn l_Lean_Parser_ppHardSpace_parenthesizer___redArg___boxed(
    mut v_a_8370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8371_: *mut LeanObject = core::ptr::null_mut();
    v_res_8371_ = l_Lean_Parser_ppHardSpace_parenthesizer___redArg();
    return v_res_8371_;
}
pub unsafe fn l_Lean_Parser_ppHardSpace_parenthesizer(
    mut v_a_8372_: *mut LeanObject,
    mut v_a_8373_: *mut LeanObject,
    mut v_a_8374_: *mut LeanObject,
    mut v_a_8375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8377_: *mut LeanObject = core::ptr::null_mut();
    v___x_8377_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
    return v___x_8377_;
}
pub unsafe fn l_Lean_Parser_ppHardSpace_parenthesizer___boxed(
    mut v_a_8378_: *mut LeanObject,
    mut v_a_8379_: *mut LeanObject,
    mut v_a_8380_: *mut LeanObject,
    mut v_a_8381_: *mut LeanObject,
    mut v_a_8382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8383_: *mut LeanObject = core::ptr::null_mut();
    v_res_8383_ =
        l_Lean_Parser_ppHardSpace_parenthesizer(v_a_8378_, v_a_8379_, v_a_8380_, v_a_8381_);
    lean_dec(v_a_8381_);
    lean_dec_ref(v_a_8380_);
    lean_dec(v_a_8379_);
    lean_dec_ref(v_a_8378_);
    return v_res_8383_;
}
pub unsafe fn l_Lean_Parser_ppSpace_parenthesizer___redArg() -> *mut LeanObject {
    let mut v___x_8385_: *mut LeanObject = core::ptr::null_mut();
    v___x_8385_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
    return v___x_8385_;
}
pub unsafe fn l_Lean_Parser_ppSpace_parenthesizer___redArg___boxed(
    mut v_a_8386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8387_: *mut LeanObject = core::ptr::null_mut();
    v_res_8387_ = l_Lean_Parser_ppSpace_parenthesizer___redArg();
    return v_res_8387_;
}
pub unsafe fn l_Lean_Parser_ppSpace_parenthesizer(
    mut v_a_8388_: *mut LeanObject,
    mut v_a_8389_: *mut LeanObject,
    mut v_a_8390_: *mut LeanObject,
    mut v_a_8391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8393_: *mut LeanObject = core::ptr::null_mut();
    v___x_8393_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
    return v___x_8393_;
}
pub unsafe fn l_Lean_Parser_ppSpace_parenthesizer___boxed(
    mut v_a_8394_: *mut LeanObject,
    mut v_a_8395_: *mut LeanObject,
    mut v_a_8396_: *mut LeanObject,
    mut v_a_8397_: *mut LeanObject,
    mut v_a_8398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8399_: *mut LeanObject = core::ptr::null_mut();
    v_res_8399_ = l_Lean_Parser_ppSpace_parenthesizer(v_a_8394_, v_a_8395_, v_a_8396_, v_a_8397_);
    lean_dec(v_a_8397_);
    lean_dec_ref(v_a_8396_);
    lean_dec(v_a_8395_);
    lean_dec_ref(v_a_8394_);
    return v_res_8399_;
}
pub unsafe fn l_Lean_Parser_ppLine_parenthesizer___redArg() -> *mut LeanObject {
    let mut v___x_8401_: *mut LeanObject = core::ptr::null_mut();
    v___x_8401_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
    return v___x_8401_;
}
pub unsafe fn l_Lean_Parser_ppLine_parenthesizer___redArg___boxed(
    mut v_a_8402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8403_: *mut LeanObject = core::ptr::null_mut();
    v_res_8403_ = l_Lean_Parser_ppLine_parenthesizer___redArg();
    return v_res_8403_;
}
pub unsafe fn l_Lean_Parser_ppLine_parenthesizer(
    mut v_a_8404_: *mut LeanObject,
    mut v_a_8405_: *mut LeanObject,
    mut v_a_8406_: *mut LeanObject,
    mut v_a_8407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8409_: *mut LeanObject = core::ptr::null_mut();
    v___x_8409_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
    return v___x_8409_;
}
pub unsafe fn l_Lean_Parser_ppLine_parenthesizer___boxed(
    mut v_a_8410_: *mut LeanObject,
    mut v_a_8411_: *mut LeanObject,
    mut v_a_8412_: *mut LeanObject,
    mut v_a_8413_: *mut LeanObject,
    mut v_a_8414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8415_: *mut LeanObject = core::ptr::null_mut();
    v_res_8415_ = l_Lean_Parser_ppLine_parenthesizer(v_a_8410_, v_a_8411_, v_a_8412_, v_a_8413_);
    lean_dec(v_a_8413_);
    lean_dec_ref(v_a_8412_);
    lean_dec(v_a_8411_);
    lean_dec_ref(v_a_8410_);
    return v_res_8415_;
}
pub unsafe fn l_Lean_Parser_ppGroup_formatter(
    mut v_p_8416_: *mut LeanObject,
    mut v_a_8417_: *mut LeanObject,
    mut v_a_8418_: *mut LeanObject,
    mut v_a_8419_: *mut LeanObject,
    mut v_a_8420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8423_: *mut LeanObject = core::ptr::null_mut();
    v___x_8422_ = lean_alloc_closure(
        l_Lean_ppIndent_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_8422_, 0, v_p_8416_);
    v___x_8423_ = l_Lean_PrettyPrinter_Formatter_fill(
        v___x_8422_,
        v_a_8417_,
        v_a_8418_,
        v_a_8419_,
        v_a_8420_,
    );
    return v___x_8423_;
}
pub unsafe fn l_Lean_Parser_ppGroup_formatter___boxed(
    mut v_p_8424_: *mut LeanObject,
    mut v_a_8425_: *mut LeanObject,
    mut v_a_8426_: *mut LeanObject,
    mut v_a_8427_: *mut LeanObject,
    mut v_a_8428_: *mut LeanObject,
    mut v_a_8429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8430_: *mut LeanObject = core::ptr::null_mut();
    v_res_8430_ =
        l_Lean_Parser_ppGroup_formatter(v_p_8424_, v_a_8425_, v_a_8426_, v_a_8427_, v_a_8428_);
    lean_dec(v_a_8428_);
    lean_dec_ref(v_a_8427_);
    lean_dec(v_a_8426_);
    lean_dec_ref(v_a_8425_);
    return v_res_8430_;
}
pub unsafe fn l_Lean_Parser_ppRealFill_parenthesizer(
    mut v_a_8431_: *mut LeanObject,
    mut v_a_8432_: *mut LeanObject,
    mut v_a_8433_: *mut LeanObject,
    mut v_a_8434_: *mut LeanObject,
    mut v_a_8435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8437_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_8435_);
    lean_inc_ref(v_a_8434_);
    lean_inc(v_a_8433_);
    lean_inc_ref(v_a_8432_);
    v___x_8437_ = lean_apply_5(
        v_a_8431_,
        v_a_8432_,
        v_a_8433_,
        v_a_8434_,
        v_a_8435_,
        lean_box(0),
    );
    return v___x_8437_;
}
pub unsafe fn l_Lean_Parser_ppRealFill_parenthesizer___boxed(
    mut v_a_8438_: *mut LeanObject,
    mut v_a_8439_: *mut LeanObject,
    mut v_a_8440_: *mut LeanObject,
    mut v_a_8441_: *mut LeanObject,
    mut v_a_8442_: *mut LeanObject,
    mut v_a_8443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8444_: *mut LeanObject = core::ptr::null_mut();
    v_res_8444_ = l_Lean_Parser_ppRealFill_parenthesizer(
        v_a_8438_, v_a_8439_, v_a_8440_, v_a_8441_, v_a_8442_,
    );
    lean_dec(v_a_8442_);
    lean_dec_ref(v_a_8441_);
    lean_dec(v_a_8440_);
    lean_dec_ref(v_a_8439_);
    return v_res_8444_;
}
pub unsafe fn l_Lean_Parser_ppIndent_parenthesizer(
    mut v_a_8445_: *mut LeanObject,
    mut v_a_8446_: *mut LeanObject,
    mut v_a_8447_: *mut LeanObject,
    mut v_a_8448_: *mut LeanObject,
    mut v_a_8449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8451_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_8449_);
    lean_inc_ref(v_a_8448_);
    lean_inc(v_a_8447_);
    lean_inc_ref(v_a_8446_);
    v___x_8451_ = lean_apply_5(
        v_a_8445_,
        v_a_8446_,
        v_a_8447_,
        v_a_8448_,
        v_a_8449_,
        lean_box(0),
    );
    return v___x_8451_;
}
pub unsafe fn l_Lean_Parser_ppIndent_parenthesizer___boxed(
    mut v_a_8452_: *mut LeanObject,
    mut v_a_8453_: *mut LeanObject,
    mut v_a_8454_: *mut LeanObject,
    mut v_a_8455_: *mut LeanObject,
    mut v_a_8456_: *mut LeanObject,
    mut v_a_8457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8458_: *mut LeanObject = core::ptr::null_mut();
    v_res_8458_ =
        l_Lean_Parser_ppIndent_parenthesizer(v_a_8452_, v_a_8453_, v_a_8454_, v_a_8455_, v_a_8456_);
    lean_dec(v_a_8456_);
    lean_dec_ref(v_a_8455_);
    lean_dec(v_a_8454_);
    lean_dec_ref(v_a_8453_);
    return v_res_8458_;
}
pub unsafe fn l_Lean_Parser_ppGroup_parenthesizer(
    mut v_p_8459_: *mut LeanObject,
    mut v_a_8460_: *mut LeanObject,
    mut v_a_8461_: *mut LeanObject,
    mut v_a_8462_: *mut LeanObject,
    mut v_a_8463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8465_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_8463_);
    lean_inc_ref(v_a_8462_);
    lean_inc(v_a_8461_);
    lean_inc_ref(v_a_8460_);
    v___x_8465_ = lean_apply_5(
        v_p_8459_,
        v_a_8460_,
        v_a_8461_,
        v_a_8462_,
        v_a_8463_,
        lean_box(0),
    );
    return v___x_8465_;
}
pub unsafe fn l_Lean_Parser_ppGroup_parenthesizer___boxed(
    mut v_p_8466_: *mut LeanObject,
    mut v_a_8467_: *mut LeanObject,
    mut v_a_8468_: *mut LeanObject,
    mut v_a_8469_: *mut LeanObject,
    mut v_a_8470_: *mut LeanObject,
    mut v_a_8471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8472_: *mut LeanObject = core::ptr::null_mut();
    v_res_8472_ =
        l_Lean_Parser_ppGroup_parenthesizer(v_p_8466_, v_a_8467_, v_a_8468_, v_a_8469_, v_a_8470_);
    lean_dec(v_a_8470_);
    lean_dec_ref(v_a_8469_);
    lean_dec(v_a_8468_);
    lean_dec_ref(v_a_8467_);
    return v_res_8472_;
}
pub unsafe fn l_Lean_Parser_ppRealGroup_parenthesizer(
    mut v_a_8473_: *mut LeanObject,
    mut v_a_8474_: *mut LeanObject,
    mut v_a_8475_: *mut LeanObject,
    mut v_a_8476_: *mut LeanObject,
    mut v_a_8477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8479_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_8477_);
    lean_inc_ref(v_a_8476_);
    lean_inc(v_a_8475_);
    lean_inc_ref(v_a_8474_);
    v___x_8479_ = lean_apply_5(
        v_a_8473_,
        v_a_8474_,
        v_a_8475_,
        v_a_8476_,
        v_a_8477_,
        lean_box(0),
    );
    return v___x_8479_;
}
pub unsafe fn l_Lean_Parser_ppRealGroup_parenthesizer___boxed(
    mut v_a_8480_: *mut LeanObject,
    mut v_a_8481_: *mut LeanObject,
    mut v_a_8482_: *mut LeanObject,
    mut v_a_8483_: *mut LeanObject,
    mut v_a_8484_: *mut LeanObject,
    mut v_a_8485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8486_: *mut LeanObject = core::ptr::null_mut();
    v_res_8486_ = l_Lean_Parser_ppRealGroup_parenthesizer(
        v_a_8480_, v_a_8481_, v_a_8482_, v_a_8483_, v_a_8484_,
    );
    lean_dec(v_a_8484_);
    lean_dec_ref(v_a_8483_);
    lean_dec(v_a_8482_);
    lean_dec_ref(v_a_8481_);
    return v_res_8486_;
}
pub unsafe fn l_Lean_Parser_ppDedent_parenthesizer(
    mut v_a_8487_: *mut LeanObject,
    mut v_a_8488_: *mut LeanObject,
    mut v_a_8489_: *mut LeanObject,
    mut v_a_8490_: *mut LeanObject,
    mut v_a_8491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8493_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_8491_);
    lean_inc_ref(v_a_8490_);
    lean_inc(v_a_8489_);
    lean_inc_ref(v_a_8488_);
    v___x_8493_ = lean_apply_5(
        v_a_8487_,
        v_a_8488_,
        v_a_8489_,
        v_a_8490_,
        v_a_8491_,
        lean_box(0),
    );
    return v___x_8493_;
}
pub unsafe fn l_Lean_Parser_ppDedent_parenthesizer___boxed(
    mut v_a_8494_: *mut LeanObject,
    mut v_a_8495_: *mut LeanObject,
    mut v_a_8496_: *mut LeanObject,
    mut v_a_8497_: *mut LeanObject,
    mut v_a_8498_: *mut LeanObject,
    mut v_a_8499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8500_: *mut LeanObject = core::ptr::null_mut();
    v_res_8500_ =
        l_Lean_Parser_ppDedent_parenthesizer(v_a_8494_, v_a_8495_, v_a_8496_, v_a_8497_, v_a_8498_);
    lean_dec(v_a_8498_);
    lean_dec_ref(v_a_8497_);
    lean_dec(v_a_8496_);
    lean_dec_ref(v_a_8495_);
    return v_res_8500_;
}
pub unsafe fn l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg() -> *mut LeanObject {
    let mut v___x_8502_: *mut LeanObject = core::ptr::null_mut();
    v___x_8502_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
    return v___x_8502_;
}
pub unsafe fn l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg___boxed(
    mut v_a_8503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8504_: *mut LeanObject = core::ptr::null_mut();
    v_res_8504_ = l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg();
    return v_res_8504_;
}
pub unsafe fn l_Lean_Parser_ppAllowUngrouped_parenthesizer(
    mut v_a_8505_: *mut LeanObject,
    mut v_a_8506_: *mut LeanObject,
    mut v_a_8507_: *mut LeanObject,
    mut v_a_8508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8510_: *mut LeanObject = core::ptr::null_mut();
    v___x_8510_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
    return v___x_8510_;
}
pub unsafe fn l_Lean_Parser_ppAllowUngrouped_parenthesizer___boxed(
    mut v_a_8511_: *mut LeanObject,
    mut v_a_8512_: *mut LeanObject,
    mut v_a_8513_: *mut LeanObject,
    mut v_a_8514_: *mut LeanObject,
    mut v_a_8515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8516_: *mut LeanObject = core::ptr::null_mut();
    v_res_8516_ =
        l_Lean_Parser_ppAllowUngrouped_parenthesizer(v_a_8511_, v_a_8512_, v_a_8513_, v_a_8514_);
    lean_dec(v_a_8514_);
    lean_dec_ref(v_a_8513_);
    lean_dec(v_a_8512_);
    lean_dec_ref(v_a_8511_);
    return v_res_8516_;
}
pub unsafe fn l_Lean_Parser_ppDedentIfGrouped_parenthesizer(
    mut v_a_8517_: *mut LeanObject,
    mut v_a_8518_: *mut LeanObject,
    mut v_a_8519_: *mut LeanObject,
    mut v_a_8520_: *mut LeanObject,
    mut v_a_8521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8523_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_8521_);
    lean_inc_ref(v_a_8520_);
    lean_inc(v_a_8519_);
    lean_inc_ref(v_a_8518_);
    v___x_8523_ = lean_apply_5(
        v_a_8517_,
        v_a_8518_,
        v_a_8519_,
        v_a_8520_,
        v_a_8521_,
        lean_box(0),
    );
    return v___x_8523_;
}
pub unsafe fn l_Lean_Parser_ppDedentIfGrouped_parenthesizer___boxed(
    mut v_a_8524_: *mut LeanObject,
    mut v_a_8525_: *mut LeanObject,
    mut v_a_8526_: *mut LeanObject,
    mut v_a_8527_: *mut LeanObject,
    mut v_a_8528_: *mut LeanObject,
    mut v_a_8529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8530_: *mut LeanObject = core::ptr::null_mut();
    v_res_8530_ = l_Lean_Parser_ppDedentIfGrouped_parenthesizer(
        v_a_8524_, v_a_8525_, v_a_8526_, v_a_8527_, v_a_8528_,
    );
    lean_dec(v_a_8528_);
    lean_dec_ref(v_a_8527_);
    lean_dec(v_a_8526_);
    lean_dec_ref(v_a_8525_);
    return v_res_8530_;
}
pub unsafe fn l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg() -> *mut LeanObject {
    let mut v___x_8532_: *mut LeanObject = core::ptr::null_mut();
    v___x_8532_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
    return v___x_8532_;
}
pub unsafe fn l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg___boxed(
    mut v_a_8533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8534_: *mut LeanObject = core::ptr::null_mut();
    v_res_8534_ = l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg();
    return v_res_8534_;
}
pub unsafe fn l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(
    mut v_a_8535_: *mut LeanObject,
    mut v_a_8536_: *mut LeanObject,
    mut v_a_8537_: *mut LeanObject,
    mut v_a_8538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8540_: *mut LeanObject = core::ptr::null_mut();
    v___x_8540_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
    return v___x_8540_;
}
pub unsafe fn l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___boxed(
    mut v_a_8541_: *mut LeanObject,
    mut v_a_8542_: *mut LeanObject,
    mut v_a_8543_: *mut LeanObject,
    mut v_a_8544_: *mut LeanObject,
    mut v_a_8545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8546_: *mut LeanObject = core::ptr::null_mut();
    v_res_8546_ = l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(
        v_a_8541_, v_a_8542_, v_a_8543_, v_a_8544_,
    );
    lean_dec(v_a_8544_);
    lean_dec_ref(v_a_8543_);
    lean_dec(v_a_8542_);
    lean_dec_ref(v_a_8541_);
    return v_res_8546_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1()
-> *mut LeanObject {
    let mut v___x_8647_: *mut LeanObject = core::ptr::null_mut();
    v___x_8647_ = l_Array_mkArray0(lean_box(0));
    return v___x_8647_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3()
-> *mut LeanObject {
    let mut v___x_8649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8650_: *mut LeanObject = core::ptr::null_mut();
    v___x_8649_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2;
    v___x_8650_ = l_String_toRawSubstring_x27(v___x_8649_);
    return v___x_8650_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8()
-> *mut LeanObject {
    let mut v___x_8656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8657_: *mut LeanObject = core::ptr::null_mut();
    v___x_8656_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7;
    v___x_8657_ = l_String_toRawSubstring_x27(v___x_8656_);
    return v___x_8657_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13()
-> *mut LeanObject {
    let mut v___x_8663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8664_: *mut LeanObject = core::ptr::null_mut();
    v___x_8663_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12;
    v___x_8664_ = l_String_toRawSubstring_x27(v___x_8663_);
    return v___x_8664_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17()
-> *mut LeanObject {
    let mut v___x_8669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8670_: *mut LeanObject = core::ptr::null_mut();
    v___x_8669_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16;
    v___x_8670_ = l_String_toRawSubstring_x27(v___x_8669_);
    return v___x_8670_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34()
-> *mut LeanObject {
    let mut v___x_8710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8711_: *mut LeanObject = core::ptr::null_mut();
    v___x_8710_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33;
    v___x_8711_ = l_String_toRawSubstring_x27(v___x_8710_);
    return v___x_8711_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41()
-> *mut LeanObject {
    let mut v___x_8727_: u8 = 0;
    let mut v___x_8728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8729_: *mut LeanObject = core::ptr::null_mut();
    v___x_8727_ = 0;
    v___x_8728_ = lean_box(0);
    v___x_8729_ = l_Lean_SourceInfo_fromRef(v___x_8728_, v___x_8727_);
    return v___x_8729_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47()
-> *mut LeanObject {
    let mut v___x_8737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8739_: *mut LeanObject = core::ptr::null_mut();
    v___x_8737_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46;
    v___x_8738_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41);
    v___x_8739_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_8739_, 0, v___x_8738_);
    lean_ctor_set(v___x_8739_, 1, v___x_8737_);
    return v___x_8739_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49()
-> *mut LeanObject {
    let mut v___x_8741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8743_: *mut LeanObject = core::ptr::null_mut();
    v___x_8741_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48;
    v___x_8742_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41);
    v___x_8743_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_8743_, 0, v___x_8742_);
    lean_ctor_set(v___x_8743_, 1, v___x_8741_);
    return v___x_8743_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50()
-> *mut LeanObject {
    let mut v___x_8744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8748_: *mut LeanObject = core::ptr::null_mut();
    v___x_8744_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49);
    v___x_8745_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47);
    v___x_8746_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45;
    v___x_8747_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41);
    v___x_8748_ = l_Lean_Syntax_node2(v___x_8747_, v___x_8746_, v___x_8745_, v___x_8744_);
    return v___x_8748_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53()
-> *mut LeanObject {
    let mut v___x_8755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8758_: *mut LeanObject = core::ptr::null_mut();
    v___x_8755_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1);
    v___x_8756_ = l_Lean_Parser_mkAntiquotSplice_formatter___closed__5;
    v___x_8757_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41);
    v___x_8758_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_8758_, 0, v___x_8757_);
    lean_ctor_set(v___x_8758_, 1, v___x_8756_);
    lean_ctor_set(v___x_8758_, 2, v___x_8755_);
    return v___x_8758_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56()
-> *mut LeanObject {
    let mut v___x_8765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8768_: *mut LeanObject = core::ptr::null_mut();
    v___x_8765_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53);
    v___x_8766_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55;
    v___x_8767_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41);
    v___x_8768_ = l_Lean_Syntax_node1(v___x_8767_, v___x_8766_, v___x_8765_);
    return v___x_8768_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59()
-> *mut LeanObject {
    let mut v___x_8775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8778_: *mut LeanObject = core::ptr::null_mut();
    v___x_8775_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53);
    v___x_8776_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58;
    v___x_8777_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41);
    v___x_8778_ = l_Lean_Syntax_node1(v___x_8777_, v___x_8776_, v___x_8775_);
    return v___x_8778_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60()
-> *mut LeanObject {
    let mut v___x_8779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8786_: *mut LeanObject = core::ptr::null_mut();
    v___x_8779_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49);
    v___x_8780_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59);
    v___x_8781_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56);
    v___x_8782_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53);
    v___x_8783_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47);
    v___x_8784_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52;
    v___x_8785_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41);
    v___x_8786_ = l_Lean_Syntax_node6(
        v___x_8785_,
        v___x_8784_,
        v___x_8783_,
        v___x_8782_,
        v___x_8781_,
        v___x_8780_,
        v___x_8782_,
        v___x_8779_,
    );
    return v___x_8786_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61()
-> *mut LeanObject {
    let mut v___x_8787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8791_: *mut LeanObject = core::ptr::null_mut();
    v___x_8787_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60);
    v___x_8788_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50);
    v___x_8789_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43;
    v___x_8790_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41);
    v___x_8791_ = l_Lean_Syntax_node2(v___x_8790_, v___x_8789_, v___x_8788_, v___x_8787_);
    return v___x_8791_;
}
pub unsafe fn l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1(
    mut v_x_8797_: *mut LeanObject,
    mut v_a_8798_: *mut LeanObject,
    mut v_a_8799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_8801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8830_: u8 = 0;
    let mut v___y_8831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8904_: u8 = 0;
    let mut v___y_8905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_8949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_8950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8952_: u8 = 0;
    let mut v___x_8953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_8989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_9009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9035_: u8 = 0;
    let mut v___x_9037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9039_: u8 = 0;
    let mut v___y_9041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9052_: u8 = 0;
    let mut v___x_9054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9056_: u8 = 0;
    let mut v_kind_x3f_9058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_9064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9072_: u8 = 0;
    let mut v___x_9074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9076_: u8 = 0;
    let mut v___x_9077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9078_: u8 = 0;
    let mut v___x_9079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9083_: u8 = 0;
    let mut v___x_9084_: u8 = 0;
    let mut v___x_9085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9090_: u8 = 0;
    let mut v___x_9091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_9094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9096_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8805_ = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0;
                v___x_9077_ = l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1;
                lean_inc(v_x_8797_);
                v___x_9078_ = l_Lean_Syntax_isOfKind(v_x_8797_, v___x_9077_);
                if v___x_9078_ == 0 {
                    lean_dec(v_x_8797_);
                    v___x_9079_ = lean_box(1);
                    v___x_9080_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_9080_, 0, v___x_9079_);
                    lean_ctor_set(v___x_9080_, 1, v_a_8799_);
                    return v___x_9080_;
                } else {
                    v___x_9081_ = lean_unsigned_to_nat(1);
                    v___x_9082_ = l_Lean_Syntax_getArg(v_x_8797_, v___x_9081_);
                    v___x_9083_ = l_Lean_Syntax_isNone(v___x_9082_);
                    if v___x_9083_ == 0 {
                        lean_inc(v___x_9082_);
                        v___x_9084_ = l_Lean_Syntax_matchesNull(v___x_9082_, v___x_9081_);
                        if v___x_9084_ == 0 {
                            lean_dec(v___x_9082_);
                            lean_dec(v_x_8797_);
                            v___x_9085_ = lean_box(1);
                            v___x_9086_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_9086_, 0, v___x_9085_);
                            lean_ctor_set(v___x_9086_, 1, v_a_8799_);
                            return v___x_9086_;
                        } else {
                            v___x_9087_ = lean_unsigned_to_nat(0);
                            v___x_9088_ = l_Lean_Syntax_getArg(v___x_9082_, v___x_9087_);
                            lean_dec(v___x_9082_);
                            v___x_9089_ = l_Lean_Parser_group_formatter___closed__1;
                            lean_inc(v___x_9088_);
                            v___x_9090_ = l_Lean_Syntax_isOfKind(v___x_9088_, v___x_9089_);
                            if v___x_9090_ == 0 {
                                lean_dec(v___x_9088_);
                                lean_dec(v_x_8797_);
                                v___x_9091_ = lean_box(1);
                                v___x_9092_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_9092_, 0, v___x_9091_);
                                lean_ctor_set(v___x_9092_, 1, v_a_8799_);
                                return v___x_9092_;
                            } else {
                                v___x_9093_ = lean_unsigned_to_nat(3);
                                v_kind_x3f_9094_ = l_Lean_Syntax_getArg(v___x_9088_, v___x_9093_);
                                lean_dec(v___x_9088_);
                                v___x_9095_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_9095_, 0, v_kind_x3f_9094_);
                                v_kind_x3f_9058_ = v___x_9095_;
                                v___y_9059_ = v_a_8798_;
                                v___y_9060_ = v_a_8799_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_9082_);
                        v___x_9096_ = lean_box(0);
                        v_kind_x3f_9058_ = v___x_9096_;
                        v___y_9059_ = v_a_8798_;
                        v___y_9060_ = v_a_8799_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8803_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0;
                v___x_8804_ =
                    l_Lean_Macro_throwError___redArg(v___x_8803_, v___y_8801_, v___y_8802_);
                return v___x_8804_;
            }
            2 => {
                lean_inc_n(v___y_8824_, 6);
                lean_inc_n(v___y_8811_, 21);
                v___x_8834_ = l_Lean_Syntax_node1(v___y_8811_, v___y_8824_, v___y_8833_);
                lean_inc_n(v___y_8832_, 4);
                v___x_8835_ =
                    l_Lean_Syntax_node2(v___y_8811_, v___y_8832_, v___y_8831_, v___x_8834_);
                v___x_8836_ = l_Lean_Parser_antiquotNestedExpr_formatter___closed__5;
                v___x_8837_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8837_, 0, v___y_8811_);
                lean_ctor_set(v___x_8837_, 1, v___x_8836_);
                v___x_8838_ = l_Lean_Syntax_node5(
                    v___y_8811_,
                    v___y_8825_,
                    v___y_8829_,
                    v___y_8817_,
                    v___y_8822_,
                    v___x_8835_,
                    v___x_8837_,
                );
                lean_inc(v___y_8826_);
                lean_inc_n(v___y_8808_, 2);
                v___x_8839_ = l_Lean_Syntax_node5(
                    v___y_8811_,
                    v___y_8824_,
                    v___y_8808_,
                    v___y_8819_,
                    v___y_8826_,
                    v___y_8810_,
                    v___x_8838_,
                );
                v___x_8840_ =
                    l_Lean_Syntax_node2(v___y_8811_, v___y_8832_, v___y_8821_, v___x_8839_);
                lean_inc_n(v___y_8828_, 3);
                v___x_8841_ = l_Lean_Syntax_node1(v___y_8811_, v___y_8828_, v___x_8840_);
                v___x_8842_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1);
                v___x_8843_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_8843_, 0, v___y_8811_);
                lean_ctor_set(v___x_8843_, 1, v___y_8824_);
                lean_ctor_set(v___x_8843_, 2, v___x_8842_);
                lean_inc_ref_n(v___x_8843_, 2);
                lean_inc_n(v___y_8813_, 3);
                v___x_8844_ =
                    l_Lean_Syntax_node2(v___y_8811_, v___y_8813_, v___x_8841_, v___x_8843_);
                v___x_8845_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3);
                v___x_8846_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4;
                v___x_8847_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5;
                lean_inc_ref_n(v___y_8816_, 4);
                v___x_8848_ = l_Lean_Name_mkStr3(v___x_8846_, v___x_8847_, v___y_8816_);
                lean_inc(v___y_8815_);
                lean_inc(v___y_8814_);
                v___x_8849_ = l_Lean_addMacroScope(v___y_8814_, v___x_8848_, v___y_8815_);
                v___x_8850_ =
                    l_Lean_Name_mkStr4(v___x_8805_, v___x_8846_, v___x_8847_, v___y_8816_);
                lean_inc(v___y_8818_);
                v___x_8851_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_8851_, 0, v___x_8850_);
                lean_ctor_set(v___x_8851_, 1, v___y_8818_);
                lean_inc_n(v___y_8809_, 2);
                v___x_8852_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_8852_, 0, v___x_8851_);
                lean_ctor_set(v___x_8852_, 1, v___y_8809_);
                v___x_8853_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_8853_, 0, v___y_8811_);
                lean_ctor_set(v___x_8853_, 1, v___x_8845_);
                lean_ctor_set(v___x_8853_, 2, v___x_8849_);
                lean_ctor_set(v___x_8853_, 3, v___x_8852_);
                v___x_8854_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6;
                lean_inc(v___y_8807_);
                v___x_8855_ = l_Lean_Name_append(v___y_8807_, v___x_8854_);
                v___x_8856_ = l_Lean_mkIdentFrom(v___y_8826_, v___x_8855_, v___y_8830_);
                v___x_8857_ =
                    l_Lean_Syntax_node2(v___y_8811_, v___y_8824_, v___y_8808_, v___x_8856_);
                v___x_8858_ =
                    l_Lean_Syntax_node2(v___y_8811_, v___y_8832_, v___x_8853_, v___x_8857_);
                v___x_8859_ = l_Lean_Syntax_node1(v___y_8811_, v___y_8828_, v___x_8858_);
                v___x_8860_ =
                    l_Lean_Syntax_node2(v___y_8811_, v___y_8813_, v___x_8859_, v___x_8843_);
                v___x_8861_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8);
                v___x_8862_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9;
                v___x_8863_ = l_Lean_Name_mkStr3(v___x_8846_, v___x_8862_, v___y_8816_);
                v___x_8864_ = l_Lean_addMacroScope(v___y_8814_, v___x_8863_, v___y_8815_);
                v___x_8865_ =
                    l_Lean_Name_mkStr4(v___x_8805_, v___x_8846_, v___x_8862_, v___y_8816_);
                v___x_8866_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_8866_, 0, v___x_8865_);
                lean_ctor_set(v___x_8866_, 1, v___y_8818_);
                v___x_8867_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_8867_, 0, v___x_8866_);
                lean_ctor_set(v___x_8867_, 1, v___y_8809_);
                v___x_8868_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_8868_, 0, v___y_8811_);
                lean_ctor_set(v___x_8868_, 1, v___x_8861_);
                lean_ctor_set(v___x_8868_, 2, v___x_8864_);
                lean_ctor_set(v___x_8868_, 3, v___x_8867_);
                v___x_8869_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10;
                v___x_8870_ = l_Lean_Name_append(v___y_8807_, v___x_8869_);
                v___x_8871_ = l_Lean_mkIdentFrom(v___y_8826_, v___x_8870_, v___y_8830_);
                lean_dec(v___y_8826_);
                v___x_8872_ =
                    l_Lean_Syntax_node2(v___y_8811_, v___y_8824_, v___y_8808_, v___x_8871_);
                v___x_8873_ =
                    l_Lean_Syntax_node2(v___y_8811_, v___y_8832_, v___x_8868_, v___x_8872_);
                v___x_8874_ = l_Lean_Syntax_node1(v___y_8811_, v___y_8828_, v___x_8873_);
                v___x_8875_ =
                    l_Lean_Syntax_node2(v___y_8811_, v___y_8813_, v___x_8874_, v___x_8843_);
                v___x_8876_ = l_Lean_Syntax_node3(
                    v___y_8811_,
                    v___y_8824_,
                    v___x_8844_,
                    v___x_8860_,
                    v___x_8875_,
                );
                lean_inc(v___y_8827_);
                v___x_8877_ = l_Lean_Syntax_node1(v___y_8811_, v___y_8827_, v___x_8876_);
                lean_inc(v___y_8823_);
                v___x_8878_ =
                    l_Lean_Syntax_node2(v___y_8811_, v___y_8823_, v___y_8812_, v___x_8877_);
                v___x_8879_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8879_, 0, v___x_8878_);
                lean_ctor_set(v___x_8879_, 1, v___y_8820_);
                return v___x_8879_;
            }
            3 => {
                v___x_8907_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11;
                lean_inc_ref(v___y_8886_);
                lean_inc_ref(v___y_8888_);
                v___x_8908_ =
                    l_Lean_Name_mkStr4(v___x_8805_, v___y_8888_, v___y_8886_, v___x_8907_);
                v___x_8909_ = l_Lean_Parser_antiquotNestedExpr_formatter___closed__3;
                lean_inc_n(v___y_8887_, 4);
                v___x_8910_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8910_, 0, v___y_8887_);
                lean_ctor_set(v___x_8910_, 1, v___x_8909_);
                v___x_8911_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13);
                v___x_8912_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14;
                lean_inc_n(v___y_8892_, 2);
                lean_inc_n(v___y_8891_, 2);
                v___x_8913_ = l_Lean_addMacroScope(v___y_8891_, v___x_8912_, v___y_8892_);
                lean_inc_n(v___y_8884_, 2);
                v___x_8914_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_8914_, 0, v___y_8887_);
                lean_ctor_set(v___x_8914_, 1, v___x_8911_);
                lean_ctor_set(v___x_8914_, 2, v___x_8913_);
                lean_ctor_set(v___x_8914_, 3, v___y_8884_);
                v___x_8915_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15;
                v___x_8916_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8916_, 0, v___y_8887_);
                lean_ctor_set(v___x_8916_, 1, v___x_8915_);
                v___x_8917_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17);
                v___x_8918_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18;
                v___x_8919_ = l_Lean_addMacroScope(v___y_8891_, v___x_8918_, v___y_8892_);
                v___x_8920_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20;
                lean_inc(v___y_8895_);
                v___x_8921_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_8921_, 0, v___x_8920_);
                lean_ctor_set(v___x_8921_, 1, v___y_8895_);
                v___x_8922_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_8922_, 0, v___x_8921_);
                lean_ctor_set(v___x_8922_, 1, v___y_8884_);
                v___x_8923_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_8923_, 0, v___y_8887_);
                lean_ctor_set(v___x_8923_, 1, v___x_8917_);
                lean_ctor_set(v___x_8923_, 2, v___x_8919_);
                lean_ctor_set(v___x_8923_, 3, v___x_8922_);
                if lean_obj_tag(v___y_8881_) == 0 {
                    lean_inc(v___y_8894_);
                    lean_inc(v___y_8895_);
                    v___x_8924_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                        v___y_8895_,
                        v___y_8894_,
                    );
                    if lean_obj_tag(v___x_8924_) == 0 {
                        v___x_8925_ = l_Lean_quoteNameMk(v___y_8894_);
                        v___y_8807_ = v___y_8882_;
                        v___y_8808_ = v___y_8883_;
                        v___y_8809_ = v___y_8884_;
                        v___y_8810_ = v___y_8906_;
                        v___y_8811_ = v___y_8887_;
                        v___y_8812_ = v___y_8889_;
                        v___y_8813_ = v___y_8890_;
                        v___y_8814_ = v___y_8891_;
                        v___y_8815_ = v___y_8892_;
                        v___y_8816_ = v___y_8893_;
                        v___y_8817_ = v___x_8914_;
                        v___y_8818_ = v___y_8895_;
                        v___y_8819_ = v___y_8896_;
                        v___y_8820_ = v___y_8897_;
                        v___y_8821_ = v___y_8898_;
                        v___y_8822_ = v___x_8916_;
                        v___y_8823_ = v___y_8899_;
                        v___y_8824_ = v___y_8900_;
                        v___y_8825_ = v___x_8908_;
                        v___y_8826_ = v___y_8901_;
                        v___y_8827_ = v___y_8902_;
                        v___y_8828_ = v___y_8903_;
                        v___y_8829_ = v___x_8910_;
                        v___y_8830_ = v___y_8904_;
                        v___y_8831_ = v___x_8923_;
                        v___y_8832_ = v___y_8905_;
                        v___y_8833_ = v___x_8925_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___y_8894_);
                        v_val_8926_ = lean_ctor_get(v___x_8924_, 0);
                        lean_inc(v_val_8926_);
                        lean_dec_ref_known(v___x_8924_, 1);
                        v___x_8927_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21;
                        lean_inc_ref(v___y_8886_);
                        lean_inc_ref(v___y_8888_);
                        v___x_8928_ =
                            l_Lean_Name_mkStr4(v___x_8805_, v___y_8888_, v___y_8886_, v___x_8927_);
                        v___x_8929_ =
                            l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0;
                        v___x_8930_ = lean_string_intercalate(v___x_8929_, v_val_8926_);
                        lean_inc_ref(v___y_8885_);
                        v___x_8931_ = lean_string_append(v___y_8885_, v___x_8930_);
                        lean_dec_ref(v___x_8930_);
                        v___x_8932_ = lean_box(2);
                        v___x_8933_ = l_Lean_Syntax_mkNameLit(v___x_8931_, v___x_8932_);
                        v___x_8934_ = lean_unsigned_to_nat(1);
                        v___x_8935_ = lean_mk_empty_array_with_capacity(v___x_8934_);
                        v___x_8936_ = lean_array_push(v___x_8935_, v___x_8933_);
                        v___x_8937_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_8937_, 0, v___x_8932_);
                        lean_ctor_set(v___x_8937_, 1, v___x_8928_);
                        lean_ctor_set(v___x_8937_, 2, v___x_8936_);
                        v___y_8807_ = v___y_8882_;
                        v___y_8808_ = v___y_8883_;
                        v___y_8809_ = v___y_8884_;
                        v___y_8810_ = v___y_8906_;
                        v___y_8811_ = v___y_8887_;
                        v___y_8812_ = v___y_8889_;
                        v___y_8813_ = v___y_8890_;
                        v___y_8814_ = v___y_8891_;
                        v___y_8815_ = v___y_8892_;
                        v___y_8816_ = v___y_8893_;
                        v___y_8817_ = v___x_8914_;
                        v___y_8818_ = v___y_8895_;
                        v___y_8819_ = v___y_8896_;
                        v___y_8820_ = v___y_8897_;
                        v___y_8821_ = v___y_8898_;
                        v___y_8822_ = v___x_8916_;
                        v___y_8823_ = v___y_8899_;
                        v___y_8824_ = v___y_8900_;
                        v___y_8825_ = v___x_8908_;
                        v___y_8826_ = v___y_8901_;
                        v___y_8827_ = v___y_8902_;
                        v___y_8828_ = v___y_8903_;
                        v___y_8829_ = v___x_8910_;
                        v___y_8830_ = v___y_8904_;
                        v___y_8831_ = v___x_8923_;
                        v___y_8832_ = v___y_8905_;
                        v___y_8833_ = v___x_8937_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___y_8894_);
                    v_val_8938_ = lean_ctor_get(v___y_8881_, 0);
                    lean_inc(v_val_8938_);
                    lean_dec_ref_known(v___y_8881_, 1);
                    v___y_8807_ = v___y_8882_;
                    v___y_8808_ = v___y_8883_;
                    v___y_8809_ = v___y_8884_;
                    v___y_8810_ = v___y_8906_;
                    v___y_8811_ = v___y_8887_;
                    v___y_8812_ = v___y_8889_;
                    v___y_8813_ = v___y_8890_;
                    v___y_8814_ = v___y_8891_;
                    v___y_8815_ = v___y_8892_;
                    v___y_8816_ = v___y_8893_;
                    v___y_8817_ = v___x_8914_;
                    v___y_8818_ = v___y_8895_;
                    v___y_8819_ = v___y_8896_;
                    v___y_8820_ = v___y_8897_;
                    v___y_8821_ = v___y_8898_;
                    v___y_8822_ = v___x_8916_;
                    v___y_8823_ = v___y_8899_;
                    v___y_8824_ = v___y_8900_;
                    v___y_8825_ = v___x_8908_;
                    v___y_8826_ = v___y_8901_;
                    v___y_8827_ = v___y_8902_;
                    v___y_8828_ = v___y_8903_;
                    v___y_8829_ = v___x_8910_;
                    v___y_8830_ = v___y_8904_;
                    v___y_8831_ = v___x_8923_;
                    v___y_8832_ = v___y_8905_;
                    v___y_8833_ = v_val_8938_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_quotContext_8949_ = lean_ctor_get(v___y_8947_, 1);
                v_currMacroScope_8950_ = lean_ctor_get(v___y_8947_, 2);
                v_ref_8951_ = lean_ctor_get(v___y_8947_, 5);
                v___x_8952_ = 0;
                v___x_8953_ = l_Lean_SourceInfo_fromRef(v_ref_8951_, v___x_8952_);
                v___x_8954_ = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1;
                v___x_8955_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22;
                v___x_8956_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23;
                v___x_8957_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24;
                lean_inc_n(v___x_8953_, 4);
                v___x_8958_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8958_, 0, v___x_8953_);
                lean_ctor_set(v___x_8958_, 1, v___x_8956_);
                v___x_8959_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26;
                v___x_8960_ = l_Lean_Parser_mkAntiquotSplice_formatter___closed__5;
                v___x_8961_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28;
                v___x_8962_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30;
                v___x_8963_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32;
                v___x_8964_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34);
                v___x_8965_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35;
                v___x_8966_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36;
                lean_inc(v_currMacroScope_8950_);
                lean_inc(v_quotContext_8949_);
                v___x_8967_ =
                    l_Lean_addMacroScope(v_quotContext_8949_, v___x_8966_, v_currMacroScope_8950_);
                v___x_8968_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37;
                lean_inc(v___y_8946_);
                v___x_8969_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_8969_, 0, v___x_8968_);
                lean_ctor_set(v___x_8969_, 1, v___y_8946_);
                v___x_8970_ = lean_box(0);
                v___x_8971_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_8971_, 0, v___x_8969_);
                lean_ctor_set(v___x_8971_, 1, v___x_8970_);
                v___x_8972_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_8972_, 0, v___x_8953_);
                lean_ctor_set(v___x_8972_, 1, v___x_8964_);
                lean_ctor_set(v___x_8972_, 2, v___x_8967_);
                lean_ctor_set(v___x_8972_, 3, v___x_8971_);
                v___x_8973_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39;
                v___x_8974_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
                v___x_8975_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8975_, 0, v___x_8953_);
                lean_ctor_set(v___x_8975_, 1, v___x_8974_);
                lean_inc(v___y_8942_);
                lean_inc_ref(v___x_8975_);
                v___x_8976_ = l_Lean_Syntax_node3(
                    v___x_8953_,
                    v___x_8973_,
                    v___x_8975_,
                    v___x_8975_,
                    v___y_8942_,
                );
                if lean_obj_tag(v___y_8944_) == 0 {
                    v___x_8977_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61_once), _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61);
                    lean_inc(v_currMacroScope_8950_);
                    lean_inc(v_quotContext_8949_);
                    v___y_8881_ = v___y_8941_;
                    v___y_8882_ = v___y_8943_;
                    v___y_8883_ = v___y_8948_;
                    v___y_8884_ = v___x_8970_;
                    v___y_8885_ = v___x_8974_;
                    v___y_8886_ = v___x_8955_;
                    v___y_8887_ = v___x_8953_;
                    v___y_8888_ = v___x_8954_;
                    v___y_8889_ = v___x_8958_;
                    v___y_8890_ = v___x_8961_;
                    v___y_8891_ = v_quotContext_8949_;
                    v___y_8892_ = v_currMacroScope_8950_;
                    v___y_8893_ = v___x_8965_;
                    v___y_8894_ = v___y_8945_;
                    v___y_8895_ = v___y_8946_;
                    v___y_8896_ = v___x_8976_;
                    v___y_8897_ = v___y_8940_;
                    v___y_8898_ = v___x_8972_;
                    v___y_8899_ = v___x_8957_;
                    v___y_8900_ = v___x_8960_;
                    v___y_8901_ = v___y_8942_;
                    v___y_8902_ = v___x_8959_;
                    v___y_8903_ = v___x_8962_;
                    v___y_8904_ = v___x_8952_;
                    v___y_8905_ = v___x_8963_;
                    v___y_8906_ = v___x_8977_;
                    state = 3;
                    continue;
                } else {
                    v_val_8978_ = lean_ctor_get(v___y_8944_, 0);
                    lean_inc(v_val_8978_);
                    lean_dec_ref_known(v___y_8944_, 1);
                    lean_inc(v_currMacroScope_8950_);
                    lean_inc(v_quotContext_8949_);
                    v___y_8881_ = v___y_8941_;
                    v___y_8882_ = v___y_8943_;
                    v___y_8883_ = v___y_8948_;
                    v___y_8884_ = v___x_8970_;
                    v___y_8885_ = v___x_8974_;
                    v___y_8886_ = v___x_8955_;
                    v___y_8887_ = v___x_8953_;
                    v___y_8888_ = v___x_8954_;
                    v___y_8889_ = v___x_8958_;
                    v___y_8890_ = v___x_8961_;
                    v___y_8891_ = v_quotContext_8949_;
                    v___y_8892_ = v_currMacroScope_8950_;
                    v___y_8893_ = v___x_8965_;
                    v___y_8894_ = v___y_8945_;
                    v___y_8895_ = v___y_8946_;
                    v___y_8896_ = v___x_8976_;
                    v___y_8897_ = v___y_8940_;
                    v___y_8898_ = v___x_8972_;
                    v___y_8899_ = v___x_8957_;
                    v___y_8900_ = v___x_8960_;
                    v___y_8901_ = v___y_8942_;
                    v___y_8902_ = v___x_8959_;
                    v___y_8903_ = v___x_8962_;
                    v___y_8904_ = v___x_8952_;
                    v___y_8905_ = v___x_8963_;
                    v___y_8906_ = v_val_8978_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_8986_ = l_Lean_TSyntax_getId(v___y_8981_);
                lean_inc(v___x_8986_);
                v___x_8987_ = l_Lean_Macro_resolveGlobalName(v___x_8986_, v___y_8984_, v___y_8982_);
                if lean_obj_tag(v___x_8987_) == 0 {
                    v_a_8988_ = lean_ctor_get(v___x_8987_, 0);
                    lean_inc(v_a_8988_);
                    if lean_obj_tag(v_a_8988_) == 1 {
                        v_head_8989_ = lean_ctor_get(v_a_8988_, 0);
                        lean_inc(v_head_8989_);
                        v_snd_8990_ = lean_ctor_get(v_head_8989_, 1);
                        lean_inc(v_snd_8990_);
                        if lean_obj_tag(v_snd_8990_) == 0 {
                            v_tail_8991_ = lean_ctor_get(v_a_8988_, 1);
                            lean_inc(v_tail_8991_);
                            lean_dec_ref_known(v_a_8988_, 2);
                            if lean_obj_tag(v_tail_8991_) == 0 {
                                if lean_obj_tag(v___y_8985_) == 0 {
                                    v_a_8992_ = lean_ctor_get(v___x_8987_, 1);
                                    lean_inc(v_a_8992_);
                                    lean_dec_ref_known(v___x_8987_, 2);
                                    v_fst_8993_ = lean_ctor_get(v_head_8989_, 0);
                                    lean_inc(v_fst_8993_);
                                    lean_dec(v_head_8989_);
                                    lean_inc(v___x_8986_);
                                    v___x_8994_ =
                                        l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                            v_snd_8990_,
                                            v___x_8986_,
                                        );
                                    if lean_obj_tag(v___x_8994_) == 0 {
                                        lean_inc(v___x_8986_);
                                        v___x_8995_ = l_Lean_quoteNameMk(v___x_8986_);
                                        v___y_8940_ = v_a_8992_;
                                        v___y_8941_ = v___y_8980_;
                                        v___y_8942_ = v___y_8981_;
                                        v___y_8943_ = v___x_8986_;
                                        v___y_8944_ = v___y_8983_;
                                        v___y_8945_ = v_fst_8993_;
                                        v___y_8946_ = v_snd_8990_;
                                        v___y_8947_ = v___y_8984_;
                                        v___y_8948_ = v___x_8995_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v_val_8996_ = lean_ctor_get(v___x_8994_, 0);
                                        lean_inc(v_val_8996_);
                                        lean_dec_ref_known(v___x_8994_, 1);
                                        v___x_8997_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62;
                                        v___x_8998_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
                                        v___x_8999_ = l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0;
                                        v___x_9000_ =
                                            lean_string_intercalate(v___x_8999_, v_val_8996_);
                                        v___x_9001_ = lean_string_append(v___x_8998_, v___x_9000_);
                                        lean_dec_ref(v___x_9000_);
                                        v___x_9002_ = lean_box(2);
                                        v___x_9003_ =
                                            l_Lean_Syntax_mkNameLit(v___x_9001_, v___x_9002_);
                                        v___x_9004_ = lean_unsigned_to_nat(1);
                                        v___x_9005_ =
                                            lean_mk_empty_array_with_capacity(v___x_9004_);
                                        v___x_9006_ = lean_array_push(v___x_9005_, v___x_9003_);
                                        v___x_9007_ = lean_alloc_ctor(1, 3, (0) as u32);
                                        lean_ctor_set(v___x_9007_, 0, v___x_9002_);
                                        lean_ctor_set(v___x_9007_, 1, v___x_8997_);
                                        lean_ctor_set(v___x_9007_, 2, v___x_9006_);
                                        v___y_8940_ = v_a_8992_;
                                        v___y_8941_ = v___y_8980_;
                                        v___y_8942_ = v___y_8981_;
                                        v___y_8943_ = v___x_8986_;
                                        v___y_8944_ = v___y_8983_;
                                        v___y_8945_ = v_fst_8993_;
                                        v___y_8946_ = v_snd_8990_;
                                        v___y_8947_ = v___y_8984_;
                                        v___y_8948_ = v___x_9007_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    v_a_9008_ = lean_ctor_get(v___x_8987_, 1);
                                    lean_inc(v_a_9008_);
                                    lean_dec_ref_known(v___x_8987_, 2);
                                    v_fst_9009_ = lean_ctor_get(v_head_8989_, 0);
                                    lean_inc(v_fst_9009_);
                                    lean_dec(v_head_8989_);
                                    v_val_9010_ = lean_ctor_get(v___y_8985_, 0);
                                    lean_inc(v_val_9010_);
                                    lean_dec_ref_known(v___y_8985_, 1);
                                    v___x_9011_ = l_Lean_TSyntax_getString(v_val_9010_);
                                    lean_dec(v_val_9010_);
                                    v___x_9012_ = lean_box(0);
                                    v___x_9013_ =
                                        l_Lean_Name_str___override(v___x_9012_, v___x_9011_);
                                    lean_inc(v___x_9013_);
                                    v___x_9014_ =
                                        l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                            v_snd_8990_,
                                            v___x_9013_,
                                        );
                                    if lean_obj_tag(v___x_9014_) == 0 {
                                        v___x_9015_ = l_Lean_quoteNameMk(v___x_9013_);
                                        v___y_8940_ = v_a_9008_;
                                        v___y_8941_ = v___y_8980_;
                                        v___y_8942_ = v___y_8981_;
                                        v___y_8943_ = v___x_8986_;
                                        v___y_8944_ = v___y_8983_;
                                        v___y_8945_ = v_fst_9009_;
                                        v___y_8946_ = v_snd_8990_;
                                        v___y_8947_ = v___y_8984_;
                                        v___y_8948_ = v___x_9015_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec(v___x_9013_);
                                        v_val_9016_ = lean_ctor_get(v___x_9014_, 0);
                                        lean_inc(v_val_9016_);
                                        lean_dec_ref_known(v___x_9014_, 1);
                                        v___x_9017_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62;
                                        v___x_9018_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
                                        v___x_9019_ = l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0;
                                        v___x_9020_ =
                                            lean_string_intercalate(v___x_9019_, v_val_9016_);
                                        v___x_9021_ = lean_string_append(v___x_9018_, v___x_9020_);
                                        lean_dec_ref(v___x_9020_);
                                        v___x_9022_ = lean_box(2);
                                        v___x_9023_ =
                                            l_Lean_Syntax_mkNameLit(v___x_9021_, v___x_9022_);
                                        v___x_9024_ = lean_unsigned_to_nat(1);
                                        v___x_9025_ =
                                            lean_mk_empty_array_with_capacity(v___x_9024_);
                                        v___x_9026_ = lean_array_push(v___x_9025_, v___x_9023_);
                                        v___x_9027_ = lean_alloc_ctor(1, 3, (0) as u32);
                                        lean_ctor_set(v___x_9027_, 0, v___x_9022_);
                                        lean_ctor_set(v___x_9027_, 1, v___x_9017_);
                                        lean_ctor_set(v___x_9027_, 2, v___x_9026_);
                                        v___y_8940_ = v_a_9008_;
                                        v___y_8941_ = v___y_8980_;
                                        v___y_8942_ = v___y_8981_;
                                        v___y_8943_ = v___x_8986_;
                                        v___y_8944_ = v___y_8983_;
                                        v___y_8945_ = v_fst_9009_;
                                        v___y_8946_ = v_snd_8990_;
                                        v___y_8947_ = v___y_8984_;
                                        v___y_8948_ = v___x_9027_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_tail_8991_);
                                lean_dec(v_head_8989_);
                                lean_dec(v___x_8986_);
                                lean_dec(v___y_8985_);
                                lean_dec(v___y_8983_);
                                lean_dec(v___y_8981_);
                                lean_dec(v___y_8980_);
                                v_a_9028_ = lean_ctor_get(v___x_8987_, 1);
                                lean_inc(v_a_9028_);
                                lean_dec_ref_known(v___x_8987_, 2);
                                v___y_8801_ = v___y_8984_;
                                v___y_8802_ = v_a_9028_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_snd_8990_);
                            lean_dec_ref_known(v_a_8988_, 2);
                            lean_dec(v_head_8989_);
                            lean_dec(v___x_8986_);
                            lean_dec(v___y_8985_);
                            lean_dec(v___y_8983_);
                            lean_dec(v___y_8981_);
                            lean_dec(v___y_8980_);
                            v_a_9029_ = lean_ctor_get(v___x_8987_, 1);
                            lean_inc(v_a_9029_);
                            lean_dec_ref_known(v___x_8987_, 2);
                            v___y_8801_ = v___y_8984_;
                            v___y_8802_ = v_a_9029_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_8988_);
                        lean_dec(v___x_8986_);
                        lean_dec(v___y_8985_);
                        lean_dec(v___y_8983_);
                        lean_dec(v___y_8981_);
                        lean_dec(v___y_8980_);
                        v_a_9030_ = lean_ctor_get(v___x_8987_, 1);
                        lean_inc(v_a_9030_);
                        lean_dec_ref_known(v___x_8987_, 2);
                        v___y_8801_ = v___y_8984_;
                        v___y_8802_ = v_a_9030_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_8986_);
                    lean_dec(v___y_8985_);
                    lean_dec(v___y_8983_);
                    lean_dec(v___y_8981_);
                    lean_dec(v___y_8980_);
                    v_a_9031_ = lean_ctor_get(v___x_8987_, 0);
                    v_a_9032_ = lean_ctor_get(v___x_8987_, 1);
                    v_isSharedCheck_9039_ = (!lean_is_exclusive(v___x_8987_)) as u8;
                    if v_isSharedCheck_9039_ == 0 {
                        v___x_9034_ = v___x_8987_;
                        v_isShared_9035_ = v_isSharedCheck_9039_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_9032_);
                        lean_inc(v_a_9031_);
                        lean_dec(v___x_8987_);
                        v___x_9034_ = lean_box(0);
                        v_isShared_9035_ = v_isSharedCheck_9039_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_9035_ == 0 {
                    v___x_9037_ = v___x_9034_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_9038_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9038_, 0, v_a_9031_);
                    lean_ctor_set(v_reuseFailAlloc_9038_, 1, v_a_9032_);
                    v___x_9037_ = v_reuseFailAlloc_9038_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_9037_;
            }
            8 => {
                v___x_9047_ = l_Lean_Syntax_getOptional_x3f(v___y_9041_);
                lean_dec(v___y_9041_);
                if lean_obj_tag(v___x_9047_) == 0 {
                    v___x_9048_ = lean_box(0);
                    v___y_8980_ = v___y_9043_;
                    v___y_8981_ = v___y_9042_;
                    v___y_8982_ = v___y_9044_;
                    v___y_8983_ = v___y_9046_;
                    v___y_8984_ = v___y_9045_;
                    v___y_8985_ = v___x_9048_;
                    state = 5;
                    continue;
                } else {
                    v_val_9049_ = lean_ctor_get(v___x_9047_, 0);
                    v_isSharedCheck_9056_ = (!lean_is_exclusive(v___x_9047_)) as u8;
                    if v_isSharedCheck_9056_ == 0 {
                        v___x_9051_ = v___x_9047_;
                        v_isShared_9052_ = v_isSharedCheck_9056_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_val_9049_);
                        lean_dec(v___x_9047_);
                        v___x_9051_ = lean_box(0);
                        v_isShared_9052_ = v_isSharedCheck_9056_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_9052_ == 0 {
                    v___x_9054_ = v___x_9051_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_9055_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9055_, 0, v_val_9049_);
                    v___x_9054_ = v_reuseFailAlloc_9055_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_8980_ = v___y_9043_;
                v___y_8981_ = v___y_9042_;
                v___y_8982_ = v___y_9044_;
                v___y_8983_ = v___y_9046_;
                v___y_8984_ = v___y_9045_;
                v___y_8985_ = v___x_9054_;
                state = 5;
                continue;
            }
            11 => {
                v___x_9061_ = lean_unsigned_to_nat(2);
                v___x_9062_ = l_Lean_Syntax_getArg(v_x_8797_, v___x_9061_);
                v___x_9063_ = lean_unsigned_to_nat(3);
                v_declName_9064_ = l_Lean_Syntax_getArg(v_x_8797_, v___x_9063_);
                v___x_9065_ = lean_unsigned_to_nat(4);
                v___x_9066_ = l_Lean_Syntax_getArg(v_x_8797_, v___x_9065_);
                lean_dec(v_x_8797_);
                v___x_9067_ = l_Lean_Syntax_getOptional_x3f(v___x_9066_);
                lean_dec(v___x_9066_);
                if lean_obj_tag(v___x_9067_) == 0 {
                    v___x_9068_ = lean_box(0);
                    v___y_9041_ = v___x_9062_;
                    v___y_9042_ = v_declName_9064_;
                    v___y_9043_ = v_kind_x3f_9058_;
                    v___y_9044_ = v___y_9060_;
                    v___y_9045_ = v___y_9059_;
                    v___y_9046_ = v___x_9068_;
                    state = 8;
                    continue;
                } else {
                    v_val_9069_ = lean_ctor_get(v___x_9067_, 0);
                    v_isSharedCheck_9076_ = (!lean_is_exclusive(v___x_9067_)) as u8;
                    if v_isSharedCheck_9076_ == 0 {
                        v___x_9071_ = v___x_9067_;
                        v_isShared_9072_ = v_isSharedCheck_9076_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_val_9069_);
                        lean_dec(v___x_9067_);
                        v___x_9071_ = lean_box(0);
                        v_isShared_9072_ = v_isSharedCheck_9076_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_9072_ == 0 {
                    v___x_9074_ = v___x_9071_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_9075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9075_, 0, v_val_9069_);
                    v___x_9074_ = v_reuseFailAlloc_9075_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_9041_ = v___x_9062_;
                v___y_9042_ = v_declName_9064_;
                v___y_9043_ = v_kind_x3f_9058_;
                v___y_9044_ = v___y_9060_;
                v___y_9045_ = v___y_9059_;
                v___y_9046_ = v___x_9074_;
                state = 8;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___boxed(
    mut v_x_9097_: *mut LeanObject,
    mut v_a_9098_: *mut LeanObject,
    mut v_a_9099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9100_: *mut LeanObject = core::ptr::null_mut();
    v_res_9100_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1(v_x_9097_, v_a_9098_, v_a_9099_);
    lean_dec_ref(v_a_9098_);
    return v_res_9100_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(
    mut v___y_9101_: *mut LeanObject,
    mut v___y_9102_: *mut LeanObject,
    mut v___y_9103_: *mut LeanObject,
    mut v___y_9104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9106_: *mut LeanObject = core::ptr::null_mut();
    v___x_9106_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
    return v___x_9106_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(
    mut v___y_9107_: *mut LeanObject,
    mut v___y_9108_: *mut LeanObject,
    mut v___y_9109_: *mut LeanObject,
    mut v___y_9110_: *mut LeanObject,
    mut v___y_9111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9112_: *mut LeanObject = core::ptr::null_mut();
    v_res_9112_ = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(v___y_9107_, v___y_9108_, v___y_9109_, v___y_9110_);
    lean_dec(v___y_9110_);
    lean_dec_ref(v___y_9109_);
    lean_dec(v___y_9108_);
    lean_dec_ref(v___y_9107_);
    return v_res_9112_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(
    mut v___y_9113_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_9113_);
    return v___y_9113_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(
    mut v___y_9114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9115_: *mut LeanObject = core::ptr::null_mut();
    v_res_9115_ = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(v___y_9114_);
    lean_dec_ref(v___y_9114_);
    return v_res_9115_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(
    mut v___y_9116_: *mut LeanObject,
    mut v___y_9117_: *mut LeanObject,
    mut v___y_9118_: *mut LeanObject,
    mut v___y_9119_: *mut LeanObject,
    mut v___y_9120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9122_: *mut LeanObject = core::ptr::null_mut();
    v___x_9122_ = lean_apply_5(
        v___y_9116_,
        v___y_9117_,
        v___y_9118_,
        v___y_9119_,
        v___y_9120_,
        lean_box(0),
    );
    return v___x_9122_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(
    mut v___y_9123_: *mut LeanObject,
    mut v___y_9124_: *mut LeanObject,
    mut v___y_9125_: *mut LeanObject,
    mut v___y_9126_: *mut LeanObject,
    mut v___y_9127_: *mut LeanObject,
    mut v___y_9128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9129_: *mut LeanObject = core::ptr::null_mut();
    v_res_9129_ = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(v___y_9123_, v___y_9124_, v___y_9125_, v___y_9126_, v___y_9127_);
    return v_res_9129_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(
    mut v___y_9130_: *mut LeanObject,
    mut v___y_9131_: *mut LeanObject,
    mut v___y_9132_: *mut LeanObject,
    mut v___y_9133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9135_: *mut LeanObject = core::ptr::null_mut();
    v___x_9135_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_9131_);
    return v___x_9135_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(
    mut v___y_9136_: *mut LeanObject,
    mut v___y_9137_: *mut LeanObject,
    mut v___y_9138_: *mut LeanObject,
    mut v___y_9139_: *mut LeanObject,
    mut v___y_9140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9141_: *mut LeanObject = core::ptr::null_mut();
    v_res_9141_ = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(v___y_9136_, v___y_9137_, v___y_9138_, v___y_9139_);
    lean_dec(v___y_9139_);
    lean_dec_ref(v___y_9138_);
    lean_dec(v___y_9137_);
    lean_dec_ref(v___y_9136_);
    return v_res_9141_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_initFn___lam__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(
    mut v___x_9142_: *mut LeanObject,
    mut v___y_9143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9144_: *mut LeanObject = core::ptr::null_mut();
    v___x_9144_ = l_Lean_Parser_node(v___x_9142_, v___y_9143_);
    return v___x_9144_;
}
pub unsafe fn _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9158_: *mut LeanObject = core::ptr::null_mut();
    v___x_9157_ = lean_alloc_closure(
        l_Lean_ppHardLineUnlessUngrouped_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_9158_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9158_, 0, v___x_9157_);
    return v___x_9158_;
}
pub unsafe fn _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9166_: *mut LeanObject = core::ptr::null_mut();
    v___x_9165_ = lean_alloc_closure(
        l_Lean_ppAllowUngrouped_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_9166_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9166_, 0, v___x_9165_);
    return v___x_9166_;
}
pub unsafe fn _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9224_: *mut LeanObject = core::ptr::null_mut();
    v___x_9223_ = lean_alloc_closure(
        l_Lean_ppLine_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_9224_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9224_, 0, v___x_9223_);
    return v___x_9224_;
}
pub unsafe fn _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9232_: *mut LeanObject = core::ptr::null_mut();
    v___x_9231_ = l_Lean_Parser_skip;
    v___x_9232_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9232_, 0, v___x_9231_);
    return v___x_9232_;
}
pub unsafe fn _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9242_: *mut LeanObject = core::ptr::null_mut();
    v___x_9241_ = lean_alloc_closure(
        l_Lean_ppHardSpace_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_9242_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9242_, 0, v___x_9241_);
    return v___x_9242_;
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_9268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9432_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9268_ = l_Lean_Parser_patternIgnore_formatter___closed__1;
                v___x_9363_ = l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0;
                v___x_9364_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                v___x_9365_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                v___x_9416_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                v___x_9428_ = l_Lean_Parser_registerAlias(
                    v___x_9268_,
                    v___x_9363_,
                    v___x_9364_,
                    v___x_9365_,
                    v___x_9416_,
                );
                if lean_obj_tag(v___x_9428_) == 0 {
                    lean_dec_ref_known(v___x_9428_, 1);
                    v___x_9429_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9430_ =
                        l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9268_, v___x_9429_);
                    if lean_obj_tag(v___x_9430_) == 0 {
                        lean_dec_ref_known(v___x_9430_, 1);
                        v___x_9431_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                        v___x_9432_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                            v___x_9268_,
                            v___x_9431_,
                        );
                        v___y_9418_ = v___x_9432_;
                        state = 12;
                        continue;
                    } else {
                        v___y_9418_ = v___x_9430_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___y_9418_ = v___x_9428_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v___y_9272_) == 0 {
                    lean_dec_ref_known(v___y_9272_, 1);
                    v___x_9273_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9274_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1;
                    v___x_9275_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9276_ = l_Lean_Parser_registerAlias(
                        v___x_9273_,
                        v___x_9274_,
                        v___y_9270_,
                        v___x_9275_,
                        v___y_9271_,
                    );
                    if lean_obj_tag(v___x_9276_) == 0 {
                        lean_dec_ref_known(v___x_9276_, 1);
                        v___x_9277_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
                        v___x_9278_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9273_, v___x_9277_);
                        if lean_obj_tag(v___x_9278_) == 0 {
                            lean_dec_ref_known(v___x_9278_, 1);
                            v___x_9279_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9280_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9273_,
                                v___x_9279_,
                            );
                            return v___x_9280_;
                        } else {
                            return v___x_9278_;
                        }
                    } else {
                        return v___x_9276_;
                    }
                } else {
                    lean_dec_ref(v___y_9271_);
                    lean_dec_ref(v___y_9270_);
                    return v___y_9272_;
                }
            }
            2 => {
                if lean_obj_tag(v___y_9284_) == 0 {
                    lean_dec_ref_known(v___y_9284_, 1);
                    v___x_9285_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9286_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1;
                    v___x_9287_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_9283_);
                    lean_inc_ref(v___y_9282_);
                    v___x_9288_ = l_Lean_Parser_registerAlias(
                        v___x_9285_,
                        v___x_9286_,
                        v___y_9282_,
                        v___x_9287_,
                        v___y_9283_,
                    );
                    if lean_obj_tag(v___x_9288_) == 0 {
                        lean_dec_ref_known(v___x_9288_, 1);
                        v___x_9289_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
                        v___x_9290_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9285_, v___x_9289_);
                        if lean_obj_tag(v___x_9290_) == 0 {
                            lean_dec_ref_known(v___x_9290_, 1);
                            v___x_9291_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9292_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9285_,
                                v___x_9291_,
                            );
                            v___y_9270_ = v___y_9282_;
                            v___y_9271_ = v___y_9283_;
                            v___y_9272_ = v___x_9292_;
                            state = 1;
                            continue;
                        } else {
                            v___y_9270_ = v___y_9282_;
                            v___y_9271_ = v___y_9283_;
                            v___y_9272_ = v___x_9290_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_9270_ = v___y_9282_;
                        v___y_9271_ = v___y_9283_;
                        v___y_9272_ = v___x_9288_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_9283_);
                    lean_dec_ref(v___y_9282_);
                    return v___y_9284_;
                }
            }
            3 => {
                if lean_obj_tag(v___y_9297_) == 0 {
                    lean_dec_ref_known(v___y_9297_, 1);
                    v___x_9298_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9299_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1;
                    v___x_9300_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9301_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9302_ = l_Lean_Parser_registerAlias(
                        v___x_9298_,
                        v___x_9299_,
                        v___x_9300_,
                        v___x_9301_,
                        v___y_9296_,
                    );
                    if lean_obj_tag(v___x_9302_) == 0 {
                        lean_dec_ref_known(v___x_9302_, 1);
                        v___x_9303_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                        v___x_9304_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9298_, v___x_9303_);
                        if lean_obj_tag(v___x_9304_) == 0 {
                            lean_dec_ref_known(v___x_9304_, 1);
                            v___x_9305_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9306_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9298_,
                                v___x_9305_,
                            );
                            v___y_9282_ = v___y_9294_;
                            v___y_9283_ = v___y_9295_;
                            v___y_9284_ = v___x_9306_;
                            state = 2;
                            continue;
                        } else {
                            v___y_9282_ = v___y_9294_;
                            v___y_9283_ = v___y_9295_;
                            v___y_9284_ = v___x_9304_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_9282_ = v___y_9294_;
                        v___y_9283_ = v___y_9295_;
                        v___y_9284_ = v___x_9302_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_9296_);
                    lean_dec_ref(v___y_9295_);
                    lean_dec_ref(v___y_9294_);
                    return v___y_9297_;
                }
            }
            4 => {
                if lean_obj_tag(v___y_9311_) == 0 {
                    lean_dec_ref_known(v___y_9311_, 1);
                    v___x_9312_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9313_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1;
                    v___x_9314_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9315_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_9310_);
                    v___x_9316_ = l_Lean_Parser_registerAlias(
                        v___x_9312_,
                        v___x_9313_,
                        v___x_9314_,
                        v___x_9315_,
                        v___y_9310_,
                    );
                    if lean_obj_tag(v___x_9316_) == 0 {
                        lean_dec_ref_known(v___x_9316_, 1);
                        v___x_9317_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                        v___x_9318_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9312_, v___x_9317_);
                        if lean_obj_tag(v___x_9318_) == 0 {
                            lean_dec_ref_known(v___x_9318_, 1);
                            v___x_9319_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9320_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9312_,
                                v___x_9319_,
                            );
                            v___y_9294_ = v___y_9308_;
                            v___y_9295_ = v___y_9309_;
                            v___y_9296_ = v___y_9310_;
                            v___y_9297_ = v___x_9320_;
                            state = 3;
                            continue;
                        } else {
                            v___y_9294_ = v___y_9308_;
                            v___y_9295_ = v___y_9309_;
                            v___y_9296_ = v___y_9310_;
                            v___y_9297_ = v___x_9318_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___y_9294_ = v___y_9308_;
                        v___y_9295_ = v___y_9309_;
                        v___y_9296_ = v___y_9310_;
                        v___y_9297_ = v___x_9316_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_9310_);
                    lean_dec_ref(v___y_9309_);
                    lean_dec_ref(v___y_9308_);
                    return v___y_9311_;
                }
            }
            5 => {
                if lean_obj_tag(v___y_9325_) == 0 {
                    lean_dec_ref_known(v___y_9325_, 1);
                    v___x_9326_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9327_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1;
                    v___x_9328_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9329_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_9324_);
                    v___x_9330_ = l_Lean_Parser_registerAlias(
                        v___x_9326_,
                        v___x_9327_,
                        v___x_9328_,
                        v___x_9329_,
                        v___y_9324_,
                    );
                    if lean_obj_tag(v___x_9330_) == 0 {
                        lean_dec_ref_known(v___x_9330_, 1);
                        v___x_9331_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                        v___x_9332_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9326_, v___x_9331_);
                        if lean_obj_tag(v___x_9332_) == 0 {
                            lean_dec_ref_known(v___x_9332_, 1);
                            v___x_9333_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9334_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9326_,
                                v___x_9333_,
                            );
                            v___y_9308_ = v___y_9322_;
                            v___y_9309_ = v___y_9323_;
                            v___y_9310_ = v___y_9324_;
                            v___y_9311_ = v___x_9334_;
                            state = 4;
                            continue;
                        } else {
                            v___y_9308_ = v___y_9322_;
                            v___y_9309_ = v___y_9323_;
                            v___y_9310_ = v___y_9324_;
                            v___y_9311_ = v___x_9332_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___y_9308_ = v___y_9322_;
                        v___y_9309_ = v___y_9323_;
                        v___y_9310_ = v___y_9324_;
                        v___y_9311_ = v___x_9330_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_9324_);
                    lean_dec_ref(v___y_9323_);
                    lean_dec_ref(v___y_9322_);
                    return v___y_9325_;
                }
            }
            6 => {
                if lean_obj_tag(v___y_9339_) == 0 {
                    lean_dec_ref_known(v___y_9339_, 1);
                    v___x_9340_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9341_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1;
                    v___x_9342_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9343_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_9338_);
                    v___x_9344_ = l_Lean_Parser_registerAlias(
                        v___x_9340_,
                        v___x_9341_,
                        v___x_9342_,
                        v___x_9343_,
                        v___y_9338_,
                    );
                    if lean_obj_tag(v___x_9344_) == 0 {
                        lean_dec_ref_known(v___x_9344_, 1);
                        v___x_9345_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                        v___x_9346_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9340_, v___x_9345_);
                        if lean_obj_tag(v___x_9346_) == 0 {
                            lean_dec_ref_known(v___x_9346_, 1);
                            v___x_9347_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9348_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9340_,
                                v___x_9347_,
                            );
                            v___y_9322_ = v___y_9336_;
                            v___y_9323_ = v___y_9337_;
                            v___y_9324_ = v___y_9338_;
                            v___y_9325_ = v___x_9348_;
                            state = 5;
                            continue;
                        } else {
                            v___y_9322_ = v___y_9336_;
                            v___y_9323_ = v___y_9337_;
                            v___y_9324_ = v___y_9338_;
                            v___y_9325_ = v___x_9346_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___y_9322_ = v___y_9336_;
                        v___y_9323_ = v___y_9337_;
                        v___y_9324_ = v___y_9338_;
                        v___y_9325_ = v___x_9344_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_9338_);
                    lean_dec_ref(v___y_9337_);
                    lean_dec_ref(v___y_9336_);
                    return v___y_9339_;
                }
            }
            7 => {
                if lean_obj_tag(v___y_9353_) == 0 {
                    lean_dec_ref_known(v___y_9353_, 1);
                    v___x_9354_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9355_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1;
                    v___x_9356_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9357_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_9352_);
                    v___x_9358_ = l_Lean_Parser_registerAlias(
                        v___x_9354_,
                        v___x_9355_,
                        v___x_9356_,
                        v___x_9357_,
                        v___y_9352_,
                    );
                    if lean_obj_tag(v___x_9358_) == 0 {
                        lean_dec_ref_known(v___x_9358_, 1);
                        v___x_9359_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                        v___x_9360_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9354_, v___x_9359_);
                        if lean_obj_tag(v___x_9360_) == 0 {
                            lean_dec_ref_known(v___x_9360_, 1);
                            v___x_9361_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9362_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9354_,
                                v___x_9361_,
                            );
                            v___y_9336_ = v___y_9350_;
                            v___y_9337_ = v___y_9351_;
                            v___y_9338_ = v___y_9352_;
                            v___y_9339_ = v___x_9362_;
                            state = 6;
                            continue;
                        } else {
                            v___y_9336_ = v___y_9350_;
                            v___y_9337_ = v___y_9351_;
                            v___y_9338_ = v___y_9352_;
                            v___y_9339_ = v___x_9360_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___y_9336_ = v___y_9350_;
                        v___y_9337_ = v___y_9351_;
                        v___y_9338_ = v___y_9352_;
                        v___y_9339_ = v___x_9358_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_9352_);
                    lean_dec_ref(v___y_9351_);
                    lean_dec_ref(v___y_9350_);
                    return v___y_9353_;
                }
            }
            8 => {
                if lean_obj_tag(v___y_9369_) == 0 {
                    lean_dec_ref_known(v___y_9369_, 1);
                    v___x_9370_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9371_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1;
                    v___x_9372_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9373_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9374_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9375_ = l_Lean_Parser_registerAlias(
                        v___x_9370_,
                        v___x_9371_,
                        v___x_9372_,
                        v___x_9373_,
                        v___x_9374_,
                    );
                    if lean_obj_tag(v___x_9375_) == 0 {
                        lean_dec_ref_known(v___x_9375_, 1);
                        v___x_9376_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                        v___x_9377_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9370_, v___x_9376_);
                        if lean_obj_tag(v___x_9377_) == 0 {
                            lean_dec_ref_known(v___x_9377_, 1);
                            v___x_9378_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9379_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9370_,
                                v___x_9378_,
                            );
                            v___y_9350_ = v___y_9367_;
                            v___y_9351_ = v___y_9368_;
                            v___y_9352_ = v___x_9374_;
                            v___y_9353_ = v___x_9379_;
                            state = 7;
                            continue;
                        } else {
                            v___y_9350_ = v___y_9367_;
                            v___y_9351_ = v___y_9368_;
                            v___y_9352_ = v___x_9374_;
                            v___y_9353_ = v___x_9377_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___y_9350_ = v___y_9367_;
                        v___y_9351_ = v___y_9368_;
                        v___y_9352_ = v___x_9374_;
                        v___y_9353_ = v___x_9375_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_9368_);
                    lean_dec_ref(v___y_9367_);
                    return v___y_9369_;
                }
            }
            9 => {
                if lean_obj_tag(v___y_9383_) == 0 {
                    lean_dec_ref_known(v___y_9383_, 1);
                    v___x_9384_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9385_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1;
                    v___x_9386_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_9382_);
                    lean_inc_ref(v___y_9381_);
                    v___x_9387_ = l_Lean_Parser_registerAlias(
                        v___x_9384_,
                        v___x_9385_,
                        v___y_9381_,
                        v___x_9386_,
                        v___y_9382_,
                    );
                    if lean_obj_tag(v___x_9387_) == 0 {
                        lean_dec_ref_known(v___x_9387_, 1);
                        v___x_9388_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
                        v___x_9389_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9384_, v___x_9388_);
                        if lean_obj_tag(v___x_9389_) == 0 {
                            lean_dec_ref_known(v___x_9389_, 1);
                            v___x_9390_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9391_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9384_,
                                v___x_9390_,
                            );
                            v___y_9367_ = v___y_9381_;
                            v___y_9368_ = v___y_9382_;
                            v___y_9369_ = v___x_9391_;
                            state = 8;
                            continue;
                        } else {
                            v___y_9367_ = v___y_9381_;
                            v___y_9368_ = v___y_9382_;
                            v___y_9369_ = v___x_9389_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___y_9367_ = v___y_9381_;
                        v___y_9368_ = v___y_9382_;
                        v___y_9369_ = v___x_9387_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_9382_);
                    lean_dec_ref(v___y_9381_);
                    return v___y_9383_;
                }
            }
            10 => {
                if lean_obj_tag(v___y_9395_) == 0 {
                    lean_dec_ref_known(v___y_9395_, 1);
                    v___x_9396_ = l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22;
                    v___x_9397_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1;
                    v___x_9398_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_9394_);
                    lean_inc_ref(v___y_9393_);
                    v___x_9399_ = l_Lean_Parser_registerAlias(
                        v___x_9396_,
                        v___x_9397_,
                        v___y_9393_,
                        v___x_9398_,
                        v___y_9394_,
                    );
                    if lean_obj_tag(v___x_9399_) == 0 {
                        lean_dec_ref_known(v___x_9399_, 1);
                        v___x_9400_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                        v___x_9401_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9396_, v___x_9400_);
                        if lean_obj_tag(v___x_9401_) == 0 {
                            lean_dec_ref_known(v___x_9401_, 1);
                            v___x_9402_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9403_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9396_,
                                v___x_9402_,
                            );
                            v___y_9381_ = v___y_9393_;
                            v___y_9382_ = v___y_9394_;
                            v___y_9383_ = v___x_9403_;
                            state = 9;
                            continue;
                        } else {
                            v___y_9381_ = v___y_9393_;
                            v___y_9382_ = v___y_9394_;
                            v___y_9383_ = v___x_9401_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___y_9381_ = v___y_9393_;
                        v___y_9382_ = v___y_9394_;
                        v___y_9383_ = v___x_9399_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_9394_);
                    lean_dec_ref(v___y_9393_);
                    return v___y_9395_;
                }
            }
            11 => {
                if lean_obj_tag(v___y_9405_) == 0 {
                    lean_dec_ref_known(v___y_9405_, 1);
                    v___x_9406_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9407_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1;
                    v___x_9408_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
                    v___x_9409_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9410_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9411_ = l_Lean_Parser_registerAlias(
                        v___x_9406_,
                        v___x_9407_,
                        v___x_9408_,
                        v___x_9409_,
                        v___x_9410_,
                    );
                    if lean_obj_tag(v___x_9411_) == 0 {
                        lean_dec_ref_known(v___x_9411_, 1);
                        v___x_9412_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
                        v___x_9413_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9406_, v___x_9412_);
                        if lean_obj_tag(v___x_9413_) == 0 {
                            lean_dec_ref_known(v___x_9413_, 1);
                            v___x_9414_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9415_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9406_,
                                v___x_9414_,
                            );
                            v___y_9393_ = v___x_9408_;
                            v___y_9394_ = v___x_9410_;
                            v___y_9395_ = v___x_9415_;
                            state = 10;
                            continue;
                        } else {
                            v___y_9393_ = v___x_9408_;
                            v___y_9394_ = v___x_9410_;
                            v___y_9395_ = v___x_9413_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___y_9393_ = v___x_9408_;
                        v___y_9394_ = v___x_9410_;
                        v___y_9395_ = v___x_9411_;
                        state = 10;
                        continue;
                    }
                } else {
                    return v___y_9405_;
                }
            }
            12 => {
                if lean_obj_tag(v___y_9418_) == 0 {
                    lean_dec_ref_known(v___y_9418_, 1);
                    v___x_9419_ = l_Lean_Parser_group_formatter___closed__1;
                    v___x_9420_ = l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0;
                    v___x_9421_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9422_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                    v___x_9423_ = l_Lean_Parser_registerAlias(
                        v___x_9419_,
                        v___x_9420_,
                        v___x_9421_,
                        v___x_9422_,
                        v___x_9416_,
                    );
                    if lean_obj_tag(v___x_9423_) == 0 {
                        lean_dec_ref_known(v___x_9423_, 1);
                        v___x_9424_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                        v___x_9425_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_9419_, v___x_9424_);
                        if lean_obj_tag(v___x_9425_) == 0 {
                            lean_dec_ref_known(v___x_9425_, 1);
                            v___x_9426_ = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
                            v___x_9427_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_9419_,
                                v___x_9426_,
                            );
                            v___y_9405_ = v___x_9427_;
                            state = 11;
                            continue;
                        } else {
                            v___y_9405_ = v___x_9425_;
                            state = 11;
                            continue;
                        }
                    } else {
                        v___y_9405_ = v___x_9423_;
                        state = 11;
                        continue;
                    }
                } else {
                    return v___y_9418_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(
    mut v_a_9433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9434_: *mut LeanObject = core::ptr::null_mut();
    v_res_9434_ = l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
    return v_res_9434_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_ident = _init_l_Lean_Parser_ident();
    lean_mark_persistent(l_Lean_Parser_ident);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_identWithPartialTrailingDot = _init_l_Lean_Parser_identWithPartialTrailingDot();
    lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot);
    l_Lean_Parser_rawIdent = _init_l_Lean_Parser_rawIdent();
    lean_mark_persistent(l_Lean_Parser_rawIdent);
    l_Lean_Parser_hygieneInfo = _init_l_Lean_Parser_hygieneInfo();
    lean_mark_persistent(l_Lean_Parser_hygieneInfo);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_numLit = _init_l_Lean_Parser_numLit();
    lean_mark_persistent(l_Lean_Parser_numLit);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_hexnum = _init_l_Lean_Parser_hexnum();
    lean_mark_persistent(l_Lean_Parser_hexnum);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_scientificLit = _init_l_Lean_Parser_scientificLit();
    lean_mark_persistent(l_Lean_Parser_scientificLit);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_strLit = _init_l_Lean_Parser_strLit();
    lean_mark_persistent(l_Lean_Parser_strLit);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_charLit = _init_l_Lean_Parser_charLit();
    lean_mark_persistent(l_Lean_Parser_charLit);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_nameLit = _init_l_Lean_Parser_nameLit();
    lean_mark_persistent(l_Lean_Parser_nameLit);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_ppHardSpace = _init_l_Lean_Parser_ppHardSpace();
    lean_mark_persistent(l_Lean_Parser_ppHardSpace);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_ppSpace = _init_l_Lean_Parser_ppSpace();
    lean_mark_persistent(l_Lean_Parser_ppSpace);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_ppLine = _init_l_Lean_Parser_ppLine();
    lean_mark_persistent(l_Lean_Parser_ppLine);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_ppAllowUngrouped = _init_l_Lean_Parser_ppAllowUngrouped();
    lean_mark_persistent(l_Lean_Parser_ppAllowUngrouped);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_ppHardLineUnlessUngrouped = _init_l_Lean_Parser_ppHardLineUnlessUngrouped();
    lean_mark_persistent(l_Lean_Parser_ppHardLineUnlessUngrouped);
    res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Hygiene(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Parser_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_PrettyPrinter_Formatter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Hygiene(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Parser_Extra(builtin);
}
