// Lean compiler output
// Module: Lake.Util.Binder
// Imports: Lean.Parser.Term Lean.Parser.Term
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_to_int, lean_string_length,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_instRepr_repr, l_Lean_Syntax_instReprTSyntax_repr___redArg, l_Lean_Syntax_isNone,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Macro_throwErrorAt___redArg,
    l_Lean_Macro_throwUnsupported___redArg, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind, l_Lean_Syntax_getNumArgs,
    l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isIdent, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node5, l_Lean_addMacroScope, l_Lean_firstFrontendMacroScope, l_Lean_mkAtomFrom,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Expr::l_Lean_instReprBinderInfo_repr;
use crate::r#gen::Lean::Parser::Basic::l_Lean_Parser_orelse;
use crate::r#gen::Lean::Parser::Term::Basic::{
    l_Lean_Parser_Term_binderIdent, l_Lean_Parser_Term_binderIdent_formatter___boxed,
    l_Lean_Parser_Term_binderIdent_parenthesizer___boxed, l_Lean_Parser_Term_bracketedBinder,
    l_Lean_Parser_Term_bracketedBinder_formatter___boxed,
    l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed,
};
use crate::r#gen::Lean::Parser::Term::{
    initialize_Lean_Parser_Term, runtime_initialize_Lean_Parser_Term,
};
use crate::r#gen::Lean::PrettyPrinter::Formatter::l_Lean_PrettyPrinter_Formatter_orelse_formatter;
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer;
pub static l_Lake_instCoeTermArgument___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoeTermArgument___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeTermArgument___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTermArgument___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeTermArgument: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTermArgument___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeEllipsisArgument: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTermArgument___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeNamedArgumentArgument: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTermArgument___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_mkHoleFrom___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lake_mkHoleFrom___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_mkHoleFrom___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Lake_mkHoleFrom___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_mkHoleFrom___closed__2_value: leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lake_mkHoleFrom___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_mkHoleFrom___closed__3_value: leanh::LeanStringObject<5> =
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
        m_data: [104, 111, 108, 101, 0],
    };
static mut l_Lake_mkHoleFrom___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__3_value) as *mut leanh::LeanObject;
static l_Lake_mkHoleFrom___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_mkHoleFrom___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_mkHoleFrom___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_mkHoleFrom___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__3_value)
                as *mut leanh::LeanObject,
            3984140175429830279 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_mkHoleFrom___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_mkHoleFrom___closed__5_value: leanh::LeanStringObject<2> =
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
        m_data: [95, 0],
    };
static mut l_Lake_mkHoleFrom___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__5_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeHoleTerm: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTermArgument___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeHoleBinderIdent: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTermArgument___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeIdentBinderIdent: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTermArgument___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeBinderIdentFunBinder: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTermArgument___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_binder_formatter___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_binderIdent_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_binder_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_binder_formatter___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_binder_formatter___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_Term_bracketedBinder_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_binder_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_binder_formatter___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_binder_parenthesizer___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_binderIdent_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_binder_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_binder_parenthesizer___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_binder_parenthesizer___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_binder_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_binder_parenthesizer___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_binder___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_binder___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_binder___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_binder___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_binder: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instCoeBinderIdentBinder___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoeBinderIdentBinder___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeBinderIdentBinder___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeBinderIdentBinder___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeBinderIdentBinder: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeBinderIdentBinder___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeBracketedBinderBinder: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeBinderIdentBinder___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeBinderDeclBinder: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeBinderIdentBinder___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeDepArrowTerm: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeBinderIdentBinder___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedBinderSyntaxView_default___closed__0_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 8) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedBinderSyntaxView_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedBinderSyntaxView_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedBinderSyntaxView_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedBinderSyntaxView_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedBinderSyntaxView: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedBinderSyntaxView_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__2_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 111, 109, 101, 32, 0],
};
static mut l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [123, 32, 0],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__1_value:
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
    m_data: [114, 101, 102, 0],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__8_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__10_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [105, 100, 0],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__13_value:
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
    m_data: [116, 121, 112, 101, 0],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__14_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__16_value:
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
    m_data: [105, 110, 102, 111, 0],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__17_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__16_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__18_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [109, 111, 100, 105, 102, 105, 101, 114, 63, 0],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__19_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__19_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__21_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 125, 0],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__24_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView_repr___redArg___closed__25_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__21_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBinderSyntaxView_repr___redArg___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBinderSyntaxView___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprBinderSyntaxView_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprBinderSyntaxView___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instReprBinderSyntaxView: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBinderSyntaxView___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 111, 114, 32, 96, 95, 96, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_expandBinderIdent___closed__0_value: leanh::LeanStringObject<2> =
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
        m_data: [120, 0],
    };
static mut l_Lake_expandBinderIdent___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_expandBinderIdent___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_expandBinderIdent___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_expandBinderIdent___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_expandBinderIdent___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderIdent___closed__0_value)
                as *mut leanh::LeanObject,
            13655884332201764339 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_expandBinderIdent___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_expandBinderIdent___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_expandBinderCore___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            101, 120, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0,
        ],
    };
static mut l_Lake_expandBinderCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_expandBinderCore___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_expandBinderCore___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_expandBinderCore___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_expandBinderCore___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_expandBinderCore___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__0_value)
                as *mut leanh::LeanObject,
            17201320286889277233 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_expandBinderCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_expandBinderCore___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_expandBinderCore___closed__2_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            105, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0,
        ],
    };
static mut l_Lake_expandBinderCore___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_expandBinderCore___closed__2_value) as *mut leanh::LeanObject;
static l_Lake_expandBinderCore___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_expandBinderCore___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_expandBinderCore___closed__3_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_expandBinderCore___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__3_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__2_value)
                as *mut leanh::LeanObject,
            6962862263136859431 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_expandBinderCore___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_expandBinderCore___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_expandBinderCore___closed__4_value: leanh::LeanStringObject<21> =
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
            115, 116, 114, 105, 99, 116, 73, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100,
            101, 114, 0,
        ],
    };
static mut l_Lake_expandBinderCore___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_expandBinderCore___closed__4_value) as *mut leanh::LeanObject;
static l_Lake_expandBinderCore___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_expandBinderCore___closed__5_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_expandBinderCore___closed__5_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__5_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_expandBinderCore___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__5_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__4_value)
                as *mut leanh::LeanObject,
            13687021865847480189 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_expandBinderCore___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_expandBinderCore___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_expandBinderCore___closed__6_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 110, 115, 116, 66, 105, 110, 100, 101, 114, 0],
    };
static mut l_Lake_expandBinderCore___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_expandBinderCore___closed__6_value) as *mut leanh::LeanObject;
static l_Lake_expandBinderCore___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_expandBinderCore___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_expandBinderCore___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_expandBinderCore___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_expandBinderCore___closed__6_value)
                as *mut leanh::LeanObject,
            16363371701764479942 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_expandBinderCore___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_expandBinderCore___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_expandBinder___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_expandBinder___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_expandBinder___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkBinder___closed__0_value: leanh::LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lake_BinderSyntaxView_mkBinder___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkBinder___closed__1_value: leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lake_BinderSyntaxView_mkBinder___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkBinder___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__1_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkBinder___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkBinder___closed__3_value: leanh::LeanStringObject<2> =
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
static mut l_Lake_BinderSyntaxView_mkBinder___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lake_BinderSyntaxView_mkBinder___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_BinderSyntaxView_mkBinder___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_BinderSyntaxView_mkBinder___closed__5_value: leanh::LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Lake_BinderSyntaxView_mkBinder___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkBinder___closed__6_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_BinderSyntaxView_mkBinder___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkBinder___closed__7_value: leanh::LeanStringObject<2> =
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
        m_data: [123, 0],
    };
static mut l_Lake_BinderSyntaxView_mkBinder___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkBinder___closed__8_value: leanh::LeanStringObject<2> =
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
        m_data: [125, 0],
    };
static mut l_Lake_BinderSyntaxView_mkBinder___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkBinder___closed__9_value: leanh::LeanStringObject<4> =
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
        m_data: [226, 166, 131, 0],
    };
static mut l_Lake_BinderSyntaxView_mkBinder___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkBinder___closed__10_value: leanh::LeanStringObject<4> =
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
        m_data: [226, 166, 132, 0],
    };
static mut l_Lake_BinderSyntaxView_mkBinder___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkBinder___closed__11_value: leanh::LeanStringObject<2> =
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
        m_data: [91, 0],
    };
static mut l_Lake_BinderSyntaxView_mkBinder___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkBinder___closed__12_value: leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lake_BinderSyntaxView_mkBinder___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkBinder___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkDepArrow___closed__0_value: leanh::LeanStringObject<9> =
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
        m_data: [100, 101, 112, 65, 114, 114, 111, 119, 0],
    };
static mut l_Lake_BinderSyntaxView_mkDepArrow___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkDepArrow___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkDepArrow___closed__0_value)
                as *mut leanh::LeanObject,
            12159670197228439923 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkDepArrow___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkDepArrow___closed__2_value: leanh::LeanStringObject<4> =
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
        m_data: [226, 134, 146, 0],
    };
static mut l_Lake_BinderSyntaxView_mkDepArrow___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkDepArrow___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__0_value: leanh::LeanStringObject<
    15,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        85, 110, 104, 121, 103, 105, 101, 110, 105, 99, 77, 97, 105, 110, 0,
    ],
};
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__0_value)
                as *mut leanh::LeanObject,
            5644479884357183868 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__2_value: leanh::LeanStringObject<
    15,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__1_value) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__2_value) as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__2_value)
                as *mut leanh::LeanObject,
            5346268661279150583 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__4_value: leanh::LeanStringObject<
    15,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__1_value) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__2_value) as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__4_value)
                as *mut leanh::LeanObject,
            7306243862518720553 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__6_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__6_value)
                as *mut leanh::LeanObject,
            9871775667037945883 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__8_value: leanh::LeanStringObject<
    1,
> = leanh::LeanStringObject {
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
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__11_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 97, 107, 101, 0],
};
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__12_value: leanh::LeanStringObject<
    17,
> = leanh::LeanStringObject {
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
        66, 105, 110, 100, 101, 114, 83, 121, 110, 116, 97, 120, 86, 105, 101, 119, 0,
    ],
};
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__12_value)
        as *mut leanh::LeanObject;
static l_Lake_BinderSyntaxView_mkFunBinder___closed__13_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__11_value)
            as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__13_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__13_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__12_value)
                as *mut leanh::LeanObject,
            18129502515766026163 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__14_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lake_BinderSyntaxView_mkFunBinder___closed__15_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__15_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__15_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__16_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__18_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__19_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__18_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__20_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__16_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__19_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkFunBinder___closed__21_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__14_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkFunBinder___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkFunBinder___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkArgument___closed__0_value: leanh::LeanStringObject<
    14,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        110, 97, 109, 101, 100, 65, 114, 103, 117, 109, 101, 110, 116, 0,
    ],
};
static mut l_Lake_BinderSyntaxView_mkArgument___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkArgument___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mkHoleFrom___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_BinderSyntaxView_mkArgument___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkArgument___closed__0_value)
                as *mut leanh::LeanObject,
            13594530736035158498 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BinderSyntaxView_mkArgument___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkArgument___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BinderSyntaxView_mkArgument___closed__2_value: leanh::LeanStringObject<3> =
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
        m_data: [58, 61, 0],
    };
static mut l_Lake_BinderSyntaxView_mkArgument___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BinderSyntaxView_mkArgument___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_instCoeTermArgument___lam__0(
    mut v_s_1003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_s_1003_);
    return v_s_1003_;
}
pub unsafe fn l_Lake_instCoeTermArgument___lam__0___boxed(
    mut v_s_1004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1005_ = l_Lake_instCoeTermArgument___lam__0(v_s_1004_);
    leanh::lean_dec(v_s_1004_);
    return v_res_1005_;
}
pub unsafe fn l_Lake_mkHoleFrom(
    mut v_ref_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: u8 = 0;
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1021_ = l_Lake_mkHoleFrom___closed__4;
    v___x_1022_ = l_Lake_mkHoleFrom___closed__5;
    v___x_1023_ = 0;
    v___x_1024_ = l_Lean_mkAtomFrom(v_ref_1020_, v___x_1022_, v___x_1023_);
    v___x_1025_ = leanh::lean_unsigned_to_nat(1);
    v___x_1026_ = lean_mk_empty_array_with_capacity(v___x_1025_);
    v___x_1027_ = lean_array_push(v___x_1026_, v___x_1024_);
    v___x_1028_ = leanh::lean_box(2);
    v___x_1029_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1029_, 0, v___x_1028_);
    leanh::lean_ctor_set(v___x_1029_, 1, v___x_1021_);
    leanh::lean_ctor_set(v___x_1029_, 2, v___x_1027_);
    return v___x_1029_;
}
pub unsafe fn l_Lake_mkHoleFrom___boxed(
    mut v_ref_1030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1031_ = l_Lake_mkHoleFrom(v_ref_1030_);
    leanh::lean_dec(v_ref_1030_);
    return v_res_1031_;
}
pub unsafe fn l_Lake_binder_formatter(
    mut v_a_1040_: *mut leanh::LeanObject,
    mut v_a_1041_: *mut leanh::LeanObject,
    mut v_a_1042_: *mut leanh::LeanObject,
    mut v_a_1043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = l_Lake_binder_formatter___closed__0;
    v___x_1046_ = l_Lake_binder_formatter___closed__1;
    v___x_1047_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1045_,
        v___x_1046_,
        v_a_1040_,
        v_a_1041_,
        v_a_1042_,
        v_a_1043_,
    );
    return v___x_1047_;
}
pub unsafe fn l_Lake_binder_formatter___boxed(
    mut v_a_1048_: *mut leanh::LeanObject,
    mut v_a_1049_: *mut leanh::LeanObject,
    mut v_a_1050_: *mut leanh::LeanObject,
    mut v_a_1051_: *mut leanh::LeanObject,
    mut v_a_1052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1053_ = l_Lake_binder_formatter(v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
    leanh::lean_dec(v_a_1051_);
    leanh::lean_dec_ref(v_a_1050_);
    leanh::lean_dec(v_a_1049_);
    leanh::lean_dec_ref(v_a_1048_);
    return v_res_1053_;
}
pub unsafe fn l_Lake_binder_parenthesizer(
    mut v_a_1058_: *mut leanh::LeanObject,
    mut v_a_1059_: *mut leanh::LeanObject,
    mut v_a_1060_: *mut leanh::LeanObject,
    mut v_a_1061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1063_ = l_Lake_binder_parenthesizer___closed__0;
    v___x_1064_ = l_Lake_binder_parenthesizer___closed__1;
    v___x_1065_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(
        v___x_1063_,
        v___x_1064_,
        v_a_1058_,
        v_a_1059_,
        v_a_1060_,
        v_a_1061_,
    );
    return v___x_1065_;
}
pub unsafe fn l_Lake_binder_parenthesizer___boxed(
    mut v_a_1066_: *mut leanh::LeanObject,
    mut v_a_1067_: *mut leanh::LeanObject,
    mut v_a_1068_: *mut leanh::LeanObject,
    mut v_a_1069_: *mut leanh::LeanObject,
    mut v_a_1070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1071_ = l_Lake_binder_parenthesizer(v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
    leanh::lean_dec(v_a_1069_);
    leanh::lean_dec_ref(v_a_1068_);
    leanh::lean_dec(v_a_1067_);
    leanh::lean_dec_ref(v_a_1066_);
    return v_res_1071_;
}
pub unsafe fn _init_l_Lake_binder___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1072_: u8 = 0;
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = 0;
    v___x_1073_ = l_Lean_Parser_Term_bracketedBinder(v___x_1072_);
    return v___x_1073_;
}
pub unsafe fn _init_l_Lake_binder___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_binder___closed__0),
        core::ptr::addr_of_mut!(l_Lake_binder___closed__0_once),
        _init_l_Lake_binder___closed__0,
    );
    v___x_1075_ = l_Lean_Parser_Term_binderIdent;
    v___x_1076_ = l_Lean_Parser_orelse(v___x_1075_, v___x_1074_);
    return v___x_1076_;
}
pub unsafe fn _init_l_Lake_binder() -> *mut leanh::LeanObject {
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1077_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_binder___closed__1),
        core::ptr::addr_of_mut!(l_Lake_binder___closed__1_once),
        _init_l_Lake_binder___closed__1,
    );
    return v___x_1077_;
}
pub unsafe fn l_Lake_instCoeBinderIdentBinder___lam__0(
    mut v_stx_1078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_stx_1078_);
    return v_stx_1078_;
}
pub unsafe fn l_Lake_instCoeBinderIdentBinder___lam__0___boxed(
    mut v_stx_1079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1080_ = l_Lake_instCoeBinderIdentBinder___lam__0(v_stx_1079_);
    leanh::lean_dec(v_stx_1079_);
    return v_res_1080_;
}
pub unsafe fn l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0(
    mut v_x_1098_: *mut leanh::LeanObject,
    mut v_x_1099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1098_) == 0 {
        let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1100_ = l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__1;
        return v___x_1100_;
    } else {
        let mut v_val_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1101_ = leanh::lean_ctor_get(v_x_1098_, 0);
        leanh::lean_inc(v_val_1101_);
        leanh::lean_dec_ref_known(v_x_1098_, 1);
        v___x_1102_ = l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__3;
        v___x_1103_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_1101_);
        v___x_1104_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1104_, 0, v___x_1102_);
        leanh::lean_ctor_set(v___x_1104_, 1, v___x_1103_);
        v___x_1105_ = l_Repr_addAppParen(v___x_1104_, v_x_1099_);
        return v___x_1105_;
    }
}
pub unsafe fn l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___boxed(
    mut v_x_1106_: *mut leanh::LeanObject,
    mut v_x_1107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1108_ =
        l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0(v_x_1106_, v_x_1107_);
    leanh::lean_dec(v_x_1107_);
    return v_res_1108_;
}
pub unsafe fn l_Nat_cast___at___00Lake_instReprBinderSyntaxView_repr_spec__1(
    mut v_a_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = lean_nat_to_int(v_a_1109_);
    return v___x_1110_;
}
pub unsafe fn _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1124_ = leanh::lean_unsigned_to_nat(7);
    v___x_1125_ = lean_nat_to_int(v___x_1124_);
    return v___x_1125_;
}
pub unsafe fn _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1132_ = leanh::lean_unsigned_to_nat(6);
    v___x_1133_ = lean_nat_to_int(v___x_1132_);
    return v___x_1133_;
}
pub unsafe fn _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1137_ = leanh::lean_unsigned_to_nat(8);
    v___x_1138_ = lean_nat_to_int(v___x_1137_);
    return v___x_1138_;
}
pub unsafe fn _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ = leanh::lean_unsigned_to_nat(13);
    v___x_1146_ = lean_nat_to_int(v___x_1145_);
    return v___x_1146_;
}
pub unsafe fn _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1148_ = l_Lake_instReprBinderSyntaxView_repr___redArg___closed__0;
    v___x_1149_ = lean_string_length(v___x_1148_);
    return v___x_1149_;
}
pub unsafe fn _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22),
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22_once),
        _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22,
    );
    v___x_1151_ = lean_nat_to_int(v___x_1150_);
    return v___x_1151_;
}
pub unsafe fn l_Lake_instReprBinderSyntaxView_repr___redArg(
    mut v_x_1156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1160_: u8 = 0;
    let mut v_modifier_x3f_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: u8 = 0;
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1157_ = leanh::lean_ctor_get(v_x_1156_, 0);
    leanh::lean_inc(v_ref_1157_);
    v_id_1158_ = leanh::lean_ctor_get(v_x_1156_, 1);
    leanh::lean_inc(v_id_1158_);
    v_type_1159_ = leanh::lean_ctor_get(v_x_1156_, 2);
    leanh::lean_inc(v_type_1159_);
    v_info_1160_ = leanh::lean_ctor_get_uint8(
        v_x_1156_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
    );
    v_modifier_x3f_1161_ = leanh::lean_ctor_get(v_x_1156_, 3);
    leanh::lean_inc(v_modifier_x3f_1161_);
    leanh::lean_dec_ref(v_x_1156_);
    v___x_1162_ = l_Lake_instReprBinderSyntaxView_repr___redArg___closed__5;
    v___x_1163_ = l_Lake_instReprBinderSyntaxView_repr___redArg___closed__6;
    v___x_1164_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7_once),
        _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7,
    );
    v___x_1165_ = leanh::lean_unsigned_to_nat(0);
    v___x_1166_ = l_Lean_Syntax_instRepr_repr(v_ref_1157_, v___x_1165_);
    v___x_1167_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1167_, 0, v___x_1164_);
    leanh::lean_ctor_set(v___x_1167_, 1, v___x_1166_);
    v___x_1168_ = 0;
    v___x_1169_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1169_, 0, v___x_1167_);
    leanh::lean_ctor_set_uint8(
        v___x_1169_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1168_,
    );
    v___x_1170_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1170_, 0, v___x_1163_);
    leanh::lean_ctor_set(v___x_1170_, 1, v___x_1169_);
    v___x_1171_ = l_Lake_instReprBinderSyntaxView_repr___redArg___closed__9;
    v___x_1172_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1172_, 0, v___x_1170_);
    leanh::lean_ctor_set(v___x_1172_, 1, v___x_1171_);
    v___x_1173_ = leanh::lean_box(1);
    v___x_1174_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1174_, 0, v___x_1172_);
    leanh::lean_ctor_set(v___x_1174_, 1, v___x_1173_);
    v___x_1175_ = l_Lake_instReprBinderSyntaxView_repr___redArg___closed__11;
    v___x_1176_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1176_, 0, v___x_1174_);
    leanh::lean_ctor_set(v___x_1176_, 1, v___x_1175_);
    v___x_1177_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1177_, 0, v___x_1176_);
    leanh::lean_ctor_set(v___x_1177_, 1, v___x_1162_);
    v___x_1178_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12_once),
        _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12,
    );
    v___x_1179_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_id_1158_);
    v___x_1180_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1180_, 0, v___x_1178_);
    leanh::lean_ctor_set(v___x_1180_, 1, v___x_1179_);
    v___x_1181_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1181_, 0, v___x_1180_);
    leanh::lean_ctor_set_uint8(
        v___x_1181_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1168_,
    );
    v___x_1182_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1182_, 0, v___x_1177_);
    leanh::lean_ctor_set(v___x_1182_, 1, v___x_1181_);
    v___x_1183_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1183_, 0, v___x_1182_);
    leanh::lean_ctor_set(v___x_1183_, 1, v___x_1171_);
    v___x_1184_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1184_, 0, v___x_1183_);
    leanh::lean_ctor_set(v___x_1184_, 1, v___x_1173_);
    v___x_1185_ = l_Lake_instReprBinderSyntaxView_repr___redArg___closed__14;
    v___x_1186_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1186_, 0, v___x_1184_);
    leanh::lean_ctor_set(v___x_1186_, 1, v___x_1185_);
    v___x_1187_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1187_, 0, v___x_1186_);
    leanh::lean_ctor_set(v___x_1187_, 1, v___x_1162_);
    v___x_1188_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15_once),
        _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15,
    );
    v___x_1189_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_type_1159_);
    v___x_1190_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1190_, 0, v___x_1188_);
    leanh::lean_ctor_set(v___x_1190_, 1, v___x_1189_);
    v___x_1191_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1191_, 0, v___x_1190_);
    leanh::lean_ctor_set_uint8(
        v___x_1191_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1168_,
    );
    v___x_1192_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1192_, 0, v___x_1187_);
    leanh::lean_ctor_set(v___x_1192_, 1, v___x_1191_);
    v___x_1193_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1193_, 0, v___x_1192_);
    leanh::lean_ctor_set(v___x_1193_, 1, v___x_1171_);
    v___x_1194_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1194_, 0, v___x_1193_);
    leanh::lean_ctor_set(v___x_1194_, 1, v___x_1173_);
    v___x_1195_ = l_Lake_instReprBinderSyntaxView_repr___redArg___closed__17;
    v___x_1196_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1196_, 0, v___x_1194_);
    leanh::lean_ctor_set(v___x_1196_, 1, v___x_1195_);
    v___x_1197_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1197_, 0, v___x_1196_);
    leanh::lean_ctor_set(v___x_1197_, 1, v___x_1162_);
    v___x_1198_ = l_Lean_instReprBinderInfo_repr(v_info_1160_, v___x_1165_);
    v___x_1199_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1199_, 0, v___x_1188_);
    leanh::lean_ctor_set(v___x_1199_, 1, v___x_1198_);
    v___x_1200_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1200_, 0, v___x_1199_);
    leanh::lean_ctor_set_uint8(
        v___x_1200_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1168_,
    );
    v___x_1201_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1201_, 0, v___x_1197_);
    leanh::lean_ctor_set(v___x_1201_, 1, v___x_1200_);
    v___x_1202_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1202_, 0, v___x_1201_);
    leanh::lean_ctor_set(v___x_1202_, 1, v___x_1171_);
    v___x_1203_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1203_, 0, v___x_1202_);
    leanh::lean_ctor_set(v___x_1203_, 1, v___x_1173_);
    v___x_1204_ = l_Lake_instReprBinderSyntaxView_repr___redArg___closed__19;
    v___x_1205_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1205_, 0, v___x_1203_);
    leanh::lean_ctor_set(v___x_1205_, 1, v___x_1204_);
    v___x_1206_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1206_, 0, v___x_1205_);
    leanh::lean_ctor_set(v___x_1206_, 1, v___x_1162_);
    v___x_1207_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20_once),
        _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20,
    );
    v___x_1208_ = l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0(
        v_modifier_x3f_1161_,
        v___x_1165_,
    );
    v___x_1209_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1209_, 0, v___x_1207_);
    leanh::lean_ctor_set(v___x_1209_, 1, v___x_1208_);
    v___x_1210_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1210_, 0, v___x_1209_);
    leanh::lean_ctor_set_uint8(
        v___x_1210_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1168_,
    );
    v___x_1211_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1211_, 0, v___x_1206_);
    leanh::lean_ctor_set(v___x_1211_, 1, v___x_1210_);
    v___x_1212_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23_once),
        _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23,
    );
    v___x_1213_ = l_Lake_instReprBinderSyntaxView_repr___redArg___closed__24;
    v___x_1214_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1214_, 0, v___x_1213_);
    leanh::lean_ctor_set(v___x_1214_, 1, v___x_1211_);
    v___x_1215_ = l_Lake_instReprBinderSyntaxView_repr___redArg___closed__25;
    v___x_1216_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1216_, 0, v___x_1214_);
    leanh::lean_ctor_set(v___x_1216_, 1, v___x_1215_);
    v___x_1217_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1217_, 0, v___x_1212_);
    leanh::lean_ctor_set(v___x_1217_, 1, v___x_1216_);
    v___x_1218_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1218_, 0, v___x_1217_);
    leanh::lean_ctor_set_uint8(
        v___x_1218_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1168_,
    );
    return v___x_1218_;
}
pub unsafe fn l_Lake_instReprBinderSyntaxView_repr(
    mut v_x_1219_: *mut leanh::LeanObject,
    mut v_prec_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = l_Lake_instReprBinderSyntaxView_repr___redArg(v_x_1219_);
    return v___x_1221_;
}
pub unsafe fn l_Lake_instReprBinderSyntaxView_repr___boxed(
    mut v_x_1222_: *mut leanh::LeanObject,
    mut v_prec_1223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Lake_instReprBinderSyntaxView_repr(v_x_1222_, v_prec_1223_);
    leanh::lean_dec(v_prec_1223_);
    return v_res_1224_;
}
pub unsafe fn l_Lake_expandOptType(
    mut v_ref_1227_: *mut leanh::LeanObject,
    mut v_optType_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1229_: u8 = 0;
    v___x_1229_ = l_Lean_Syntax_isNone(v_optType_1228_);
    if v___x_1229_ == 0 {
        let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1230_ = leanh::lean_unsigned_to_nat(0);
        v___x_1231_ = l_Lean_Syntax_getArg(v_optType_1228_, v___x_1230_);
        v___x_1232_ = leanh::lean_unsigned_to_nat(1);
        v___x_1233_ = l_Lean_Syntax_getArg(v___x_1231_, v___x_1232_);
        leanh::lean_dec(v___x_1231_);
        return v___x_1233_;
    } else {
        let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1234_ = l_Lake_mkHoleFrom(v_ref_1227_);
        return v___x_1234_;
    }
}
pub unsafe fn l_Lake_expandOptType___boxed(
    mut v_ref_1235_: *mut leanh::LeanObject,
    mut v_optType_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l_Lake_expandOptType(v_ref_1235_, v_optType_1236_);
    leanh::lean_dec(v_optType_1236_);
    leanh::lean_dec(v_ref_1235_);
    return v_res_1237_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(
    mut v_sz_1242_: usize,
    mut v_i_1243_: usize,
    mut v_bs_1244_: *mut leanh::LeanObject,
    mut v___y_1245_: *mut leanh::LeanObject,
    mut v___y_1246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1247_: u8 = 0;
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: usize = 0;
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1260_: u8 = 0;
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1273_: u8 = 0;
    let mut v_k_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1247_ = lean_usize_dec_lt(v_i_1243_, v_sz_1242_);
                if v___x_1247_ == 0 {
                    v___x_1248_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1248_, 0, v_bs_1244_);
                    leanh::lean_ctor_set(v___x_1248_, 1, v___y_1246_);
                    return v___x_1248_;
                } else {
                    v_v_1249_ = lean_array_uget(v_bs_1244_, v_i_1243_);
                    v___x_1250_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1251_ = lean_array_uset(v_bs_1244_, v_i_1243_, v___x_1250_);
                    leanh::lean_inc(v_v_1249_);
                    v_k_1274_ = l_Lean_Syntax_getKind(v_v_1249_);
                    v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__2;
                    v___x_1276_ = lean_name_eq(v_k_1274_, v___x_1275_);
                    if v___x_1276_ == 0 {
                        v___x_1277_ = l_Lake_mkHoleFrom___closed__4;
                        v___x_1278_ = lean_name_eq(v_k_1274_, v___x_1277_);
                        leanh::lean_dec(v_k_1274_);
                        v___y_1260_ = v___x_1278_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_k_1274_);
                        v___y_1260_ = v___x_1276_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1255_ = 1usize;
                v___x_1256_ = lean_usize_add(v_i_1243_, v___x_1255_);
                v___x_1257_ = lean_array_uset(v_bs_x27_1251_, v_i_1243_, v_a_1253_);
                v_i_1243_ = v___x_1256_;
                v_bs_1244_ = v___x_1257_;
                v___y_1246_ = v_a_1254_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_1260_ == 0 {
                    v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0;
                    v___x_1262_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_v_1249_,
                        v___x_1261_,
                        v___y_1245_,
                        v___y_1246_,
                    );
                    leanh::lean_dec(v_v_1249_);
                    if leanh::lean_obj_tag(v___x_1262_) == 0 {
                        v_a_1263_ = leanh::lean_ctor_get(v___x_1262_, 0);
                        leanh::lean_inc(v_a_1263_);
                        v_a_1264_ = leanh::lean_ctor_get(v___x_1262_, 1);
                        leanh::lean_inc(v_a_1264_);
                        leanh::lean_dec_ref_known(v___x_1262_, 2);
                        v_a_1253_ = v_a_1263_;
                        v_a_1254_ = v_a_1264_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_x27_1251_);
                        v_a_1265_ = leanh::lean_ctor_get(v___x_1262_, 0);
                        v_a_1266_ = leanh::lean_ctor_get(v___x_1262_, 1);
                        v_isSharedCheck_1273_ =
                            (!leanh::lean_is_exclusive(v___x_1262_)) as u8;
                        if v_isSharedCheck_1273_ == 0 {
                            v___x_1268_ = v___x_1262_;
                            v_isShared_1269_ = v_isSharedCheck_1273_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1266_);
                            leanh::lean_inc(v_a_1265_);
                            leanh::lean_dec(v___x_1262_);
                            v___x_1268_ = leanh::lean_box(0);
                            v_isShared_1269_ = v_isSharedCheck_1273_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1253_ = v_v_1249_;
                    v_a_1254_ = v___y_1246_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_1269_ == 0 {
                    v___x_1271_ = v___x_1268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1272_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1265_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_a_1266_);
                    v___x_1271_ = v_reuseFailAlloc_1272_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___boxed(
    mut v_sz_1279_: *mut leanh::LeanObject,
    mut v_i_1280_: *mut leanh::LeanObject,
    mut v_bs_1281_: *mut leanh::LeanObject,
    mut v___y_1282_: *mut leanh::LeanObject,
    mut v___y_1283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1284_: usize = 0;
    let mut v_i_boxed_1285_: usize = 0;
    let mut v_res_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1284_ = leanh::lean_unbox_usize(v_sz_1279_);
    leanh::lean_dec(v_sz_1279_);
    v_i_boxed_1285_ = leanh::lean_unbox_usize(v_i_1280_);
    leanh::lean_dec(v_i_1280_);
    v_res_1286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(v_sz_boxed_1284_, v_i_boxed_1285_, v_bs_1281_, v___y_1282_, v___y_1283_);
    leanh::lean_dec_ref(v___y_1282_);
    return v_res_1286_;
}
pub unsafe fn l_Lake_getBinderIds(
    mut v_ids_1287_: *mut leanh::LeanObject,
    mut v_a_1288_: *mut leanh::LeanObject,
    mut v_a_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1291_: usize = 0;
    let mut v___x_1292_: usize = 0;
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1290_ = l_Lean_Syntax_getArgs(v_ids_1287_);
    v_sz_1291_ = lean_array_size(v___x_1290_);
    v___x_1292_ = 0usize;
    v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(v_sz_1291_, v___x_1292_, v___x_1290_, v_a_1288_, v_a_1289_);
    return v___x_1293_;
}
pub unsafe fn l_Lake_getBinderIds___boxed(
    mut v_ids_1294_: *mut leanh::LeanObject,
    mut v_a_1295_: *mut leanh::LeanObject,
    mut v_a_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1297_ = l_Lake_getBinderIds(v_ids_1294_, v_a_1295_, v_a_1296_);
    leanh::lean_dec_ref(v_a_1295_);
    leanh::lean_dec(v_ids_1294_);
    return v_res_1297_;
}
pub unsafe fn _init_l_Lake_expandBinderIdent___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1299_ = l_Lake_expandBinderIdent___closed__0;
    v___x_1300_ = l_String_toRawSubstring_x27(v___x_1299_);
    return v___x_1300_;
}
pub unsafe fn l_Lake_expandBinderIdent(
    mut v_stx_1303_: *mut leanh::LeanObject,
    mut v_a_1304_: *mut leanh::LeanObject,
    mut v_a_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: u8 = 0;
    v___x_1306_ = l_Lake_mkHoleFrom___closed__4;
    leanh::lean_inc(v_stx_1303_);
    v___x_1307_ = l_Lean_Syntax_isOfKind(v_stx_1303_, v___x_1306_);
    if v___x_1307_ == 0 {
        let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1308_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1308_, 0, v_stx_1303_);
        leanh::lean_ctor_set(v___x_1308_, 1, v_a_1305_);
        return v___x_1308_;
    } else {
        let mut v_quotContext_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1312_: u8 = 0;
        let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_1303_);
        v_quotContext_1309_ = leanh::lean_ctor_get(v_a_1304_, 1);
        v_currMacroScope_1310_ = leanh::lean_ctor_get(v_a_1304_, 2);
        v_ref_1311_ = leanh::lean_ctor_get(v_a_1304_, 5);
        v___x_1312_ = 0;
        v___x_1313_ = l_Lean_SourceInfo_fromRef(v_ref_1311_, v___x_1312_);
        v___x_1314_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_expandBinderIdent___closed__1),
            core::ptr::addr_of_mut!(l_Lake_expandBinderIdent___closed__1_once),
            _init_l_Lake_expandBinderIdent___closed__1,
        );
        v___x_1315_ = l_Lake_expandBinderIdent___closed__2;
        leanh::lean_inc(v_currMacroScope_1310_);
        leanh::lean_inc(v_quotContext_1309_);
        v___x_1316_ =
            l_Lean_addMacroScope(v_quotContext_1309_, v___x_1315_, v_currMacroScope_1310_);
        v___x_1317_ = leanh::lean_box(0);
        v___x_1318_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1318_, 0, v___x_1313_);
        leanh::lean_ctor_set(v___x_1318_, 1, v___x_1314_);
        leanh::lean_ctor_set(v___x_1318_, 2, v___x_1316_);
        leanh::lean_ctor_set(v___x_1318_, 3, v___x_1317_);
        v___x_1319_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1319_, 0, v___x_1318_);
        leanh::lean_ctor_set(v___x_1319_, 1, v_a_1305_);
        return v___x_1319_;
    }
}
pub unsafe fn l_Lake_expandBinderIdent___boxed(
    mut v_stx_1320_: *mut leanh::LeanObject,
    mut v_a_1321_: *mut leanh::LeanObject,
    mut v_a_1322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1323_ = l_Lake_expandBinderIdent(v_stx_1320_, v_a_1321_, v_a_1322_);
    leanh::lean_dec_ref(v_a_1321_);
    return v_res_1323_;
}
pub unsafe fn l_Lake_expandOptIdent(
    mut v_stx_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1325_: u8 = 0;
    v___x_1325_ = l_Lean_Syntax_isNone(v_stx_1324_);
    if v___x_1325_ == 0 {
        let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1326_ = leanh::lean_unsigned_to_nat(0);
        v___x_1327_ = l_Lean_Syntax_getArg(v_stx_1324_, v___x_1326_);
        return v___x_1327_;
    } else {
        let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1328_ = l_Lake_mkHoleFrom(v_stx_1324_);
        return v___x_1328_;
    }
}
pub unsafe fn l_Lake_expandOptIdent___boxed(
    mut v_stx_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Lake_expandOptIdent(v_stx_1329_);
    leanh::lean_dec(v_stx_1329_);
    return v_res_1330_;
}
pub unsafe fn l_Lake_expandBinderType(
    mut v_ref_1331_: *mut leanh::LeanObject,
    mut v_stx_1332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: u8 = 0;
    v___x_1333_ = l_Lean_Syntax_getNumArgs(v_stx_1332_);
    v___x_1334_ = leanh::lean_unsigned_to_nat(0);
    v___x_1335_ = lean_nat_dec_eq(v___x_1333_, v___x_1334_);
    leanh::lean_dec(v___x_1333_);
    if v___x_1335_ == 0 {
        let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1336_ = leanh::lean_unsigned_to_nat(1);
        v___x_1337_ = l_Lean_Syntax_getArg(v_stx_1332_, v___x_1336_);
        return v___x_1337_;
    } else {
        let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1338_ = l_Lake_mkHoleFrom(v_ref_1331_);
        return v___x_1338_;
    }
}
pub unsafe fn l_Lake_expandBinderType___boxed(
    mut v_ref_1339_: *mut leanh::LeanObject,
    mut v_stx_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1341_ = l_Lake_expandBinderType(v_ref_1339_, v_stx_1340_);
    leanh::lean_dec(v_stx_1340_);
    leanh::lean_dec(v_ref_1339_);
    return v_res_1341_;
}
pub unsafe fn l_Lake_expandBinderModifier(
    mut v_optBinderModifier_1342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1348_: u8 = 0;
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1343_ = l_Lean_Syntax_getOptional_x3f(v_optBinderModifier_1342_);
                if leanh::lean_obj_tag(v___x_1343_) == 0 {
                    v___x_1344_ = leanh::lean_box(0);
                    return v___x_1344_;
                } else {
                    v_val_1345_ = leanh::lean_ctor_get(v___x_1343_, 0);
                    v_isSharedCheck_1352_ = (!leanh::lean_is_exclusive(v___x_1343_)) as u8;
                    if v_isSharedCheck_1352_ == 0 {
                        v___x_1347_ = v___x_1343_;
                        v_isShared_1348_ = v_isSharedCheck_1352_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1345_);
                        leanh::lean_dec(v___x_1343_);
                        v___x_1347_ = leanh::lean_box(0);
                        v_isShared_1348_ = v_isSharedCheck_1352_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1348_ == 0 {
                    v___x_1350_ = v___x_1347_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_val_1345_);
                    v___x_1350_ = v_reuseFailAlloc_1351_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_expandBinderModifier___boxed(
    mut v_optBinderModifier_1353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ = l_Lake_expandBinderModifier(v_optBinderModifier_1353_);
    leanh::lean_dec(v_optBinderModifier_1353_);
    return v_res_1354_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(
    mut v___x_1355_: *mut leanh::LeanObject,
    mut v_stx_1356_: *mut leanh::LeanObject,
    mut v_as_1357_: *mut leanh::LeanObject,
    mut v_i_1358_: usize,
    mut v_stop_1359_: usize,
    mut v_b_1360_: *mut leanh::LeanObject,
    mut v___y_1361_: *mut leanh::LeanObject,
    mut v___y_1362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: u8 = 0;
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: usize = 0;
    let mut v___x_1374_: usize = 0;
    let mut v_a_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1380_: u8 = 0;
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1384_: u8 = 0;
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1363_ = lean_usize_dec_eq(v_i_1358_, v_stop_1359_);
                if v___x_1363_ == 0 {
                    v___x_1364_ = lean_array_uget_borrowed(v_as_1357_, v_i_1358_);
                    leanh::lean_inc(v___x_1364_);
                    v___x_1365_ = l_Lake_expandBinderIdent(v___x_1364_, v___y_1361_, v___y_1362_);
                    if leanh::lean_obj_tag(v___x_1365_) == 0 {
                        v_a_1366_ = leanh::lean_ctor_get(v___x_1365_, 0);
                        leanh::lean_inc(v_a_1366_);
                        v_a_1367_ = leanh::lean_ctor_get(v___x_1365_, 1);
                        leanh::lean_inc(v_a_1367_);
                        leanh::lean_dec_ref_known(v___x_1365_, 2);
                        v___x_1368_ = l_Lake_expandBinderType(v___x_1364_, v___x_1355_);
                        v___x_1369_ = 1;
                        v___x_1370_ = leanh::lean_box(0);
                        leanh::lean_inc(v_stx_1356_);
                        v___x_1371_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                        leanh::lean_ctor_set(v___x_1371_, 0, v_stx_1356_);
                        leanh::lean_ctor_set(v___x_1371_, 1, v_a_1366_);
                        leanh::lean_ctor_set(v___x_1371_, 2, v___x_1368_);
                        leanh::lean_ctor_set(v___x_1371_, 3, v___x_1370_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1371_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                            v___x_1369_,
                        );
                        v___x_1372_ = lean_array_push(v_b_1360_, v___x_1371_);
                        v___x_1373_ = 1usize;
                        v___x_1374_ = lean_usize_add(v_i_1358_, v___x_1373_);
                        v_i_1358_ = v___x_1374_;
                        v_b_1360_ = v___x_1372_;
                        v___y_1362_ = v_a_1367_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_b_1360_);
                        leanh::lean_dec(v_stx_1356_);
                        v_a_1376_ = leanh::lean_ctor_get(v___x_1365_, 0);
                        v_a_1377_ = leanh::lean_ctor_get(v___x_1365_, 1);
                        v_isSharedCheck_1384_ =
                            (!leanh::lean_is_exclusive(v___x_1365_)) as u8;
                        if v_isSharedCheck_1384_ == 0 {
                            v___x_1379_ = v___x_1365_;
                            v_isShared_1380_ = v_isSharedCheck_1384_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1377_);
                            leanh::lean_inc(v_a_1376_);
                            leanh::lean_dec(v___x_1365_);
                            v___x_1379_ = leanh::lean_box(0);
                            v_isShared_1380_ = v_isSharedCheck_1384_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_stx_1356_);
                    v___x_1385_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1385_, 0, v_b_1360_);
                    leanh::lean_ctor_set(v___x_1385_, 1, v___y_1362_);
                    return v___x_1385_;
                }
            }
            1 => {
                if v_isShared_1380_ == 0 {
                    v___x_1382_ = v___x_1379_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1383_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1376_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_a_1377_);
                    v___x_1382_ = v_reuseFailAlloc_1383_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1___boxed(
    mut v___x_1386_: *mut leanh::LeanObject,
    mut v_stx_1387_: *mut leanh::LeanObject,
    mut v_as_1388_: *mut leanh::LeanObject,
    mut v_i_1389_: *mut leanh::LeanObject,
    mut v_stop_1390_: *mut leanh::LeanObject,
    mut v_b_1391_: *mut leanh::LeanObject,
    mut v___y_1392_: *mut leanh::LeanObject,
    mut v___y_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1394_: usize = 0;
    let mut v_stop_boxed_1395_: usize = 0;
    let mut v_res_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1394_ = leanh::lean_unbox_usize(v_i_1389_);
    leanh::lean_dec(v_i_1389_);
    v_stop_boxed_1395_ = leanh::lean_unbox_usize(v_stop_1390_);
    leanh::lean_dec(v_stop_1390_);
    v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_1386_, v_stx_1387_, v_as_1388_, v_i_boxed_1394_, v_stop_boxed_1395_, v_b_1391_, v___y_1392_, v___y_1393_);
    leanh::lean_dec_ref(v___y_1392_);
    leanh::lean_dec_ref(v_as_1388_);
    leanh::lean_dec(v___x_1386_);
    return v_res_1396_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(
    mut v___x_1397_: *mut leanh::LeanObject,
    mut v_stx_1398_: *mut leanh::LeanObject,
    mut v___x_1399_: *mut leanh::LeanObject,
    mut v_as_1400_: *mut leanh::LeanObject,
    mut v_i_1401_: usize,
    mut v_stop_1402_: usize,
    mut v_b_1403_: *mut leanh::LeanObject,
    mut v___y_1404_: *mut leanh::LeanObject,
    mut v___y_1405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1406_: u8 = 0;
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: u8 = 0;
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: usize = 0;
    let mut v___x_1416_: usize = 0;
    let mut v_a_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1422_: u8 = 0;
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1426_: u8 = 0;
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1406_ = lean_usize_dec_eq(v_i_1401_, v_stop_1402_);
                if v___x_1406_ == 0 {
                    v___x_1407_ = lean_array_uget_borrowed(v_as_1400_, v_i_1401_);
                    leanh::lean_inc(v___x_1407_);
                    v___x_1408_ = l_Lake_expandBinderIdent(v___x_1407_, v___y_1404_, v___y_1405_);
                    if leanh::lean_obj_tag(v___x_1408_) == 0 {
                        v_a_1409_ = leanh::lean_ctor_get(v___x_1408_, 0);
                        leanh::lean_inc(v_a_1409_);
                        v_a_1410_ = leanh::lean_ctor_get(v___x_1408_, 1);
                        leanh::lean_inc(v_a_1410_);
                        leanh::lean_dec_ref_known(v___x_1408_, 2);
                        v___x_1411_ = l_Lake_expandBinderType(v___x_1407_, v___x_1397_);
                        v___x_1412_ = 0;
                        leanh::lean_inc(v___x_1399_);
                        leanh::lean_inc(v_stx_1398_);
                        v___x_1413_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                        leanh::lean_ctor_set(v___x_1413_, 0, v_stx_1398_);
                        leanh::lean_ctor_set(v___x_1413_, 1, v_a_1409_);
                        leanh::lean_ctor_set(v___x_1413_, 2, v___x_1411_);
                        leanh::lean_ctor_set(v___x_1413_, 3, v___x_1399_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1413_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                            v___x_1412_,
                        );
                        v___x_1414_ = lean_array_push(v_b_1403_, v___x_1413_);
                        v___x_1415_ = 1usize;
                        v___x_1416_ = lean_usize_add(v_i_1401_, v___x_1415_);
                        v_i_1401_ = v___x_1416_;
                        v_b_1403_ = v___x_1414_;
                        v___y_1405_ = v_a_1410_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_b_1403_);
                        leanh::lean_dec(v___x_1399_);
                        leanh::lean_dec(v_stx_1398_);
                        v_a_1418_ = leanh::lean_ctor_get(v___x_1408_, 0);
                        v_a_1419_ = leanh::lean_ctor_get(v___x_1408_, 1);
                        v_isSharedCheck_1426_ =
                            (!leanh::lean_is_exclusive(v___x_1408_)) as u8;
                        if v_isSharedCheck_1426_ == 0 {
                            v___x_1421_ = v___x_1408_;
                            v_isShared_1422_ = v_isSharedCheck_1426_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1419_);
                            leanh::lean_inc(v_a_1418_);
                            leanh::lean_dec(v___x_1408_);
                            v___x_1421_ = leanh::lean_box(0);
                            v_isShared_1422_ = v_isSharedCheck_1426_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1399_);
                    leanh::lean_dec(v_stx_1398_);
                    v___x_1427_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1427_, 0, v_b_1403_);
                    leanh::lean_ctor_set(v___x_1427_, 1, v___y_1405_);
                    return v___x_1427_;
                }
            }
            1 => {
                if v_isShared_1422_ == 0 {
                    v___x_1424_ = v___x_1421_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1425_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1418_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_a_1419_);
                    v___x_1424_ = v_reuseFailAlloc_1425_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2___boxed(
    mut v___x_1428_: *mut leanh::LeanObject,
    mut v_stx_1429_: *mut leanh::LeanObject,
    mut v___x_1430_: *mut leanh::LeanObject,
    mut v_as_1431_: *mut leanh::LeanObject,
    mut v_i_1432_: *mut leanh::LeanObject,
    mut v_stop_1433_: *mut leanh::LeanObject,
    mut v_b_1434_: *mut leanh::LeanObject,
    mut v___y_1435_: *mut leanh::LeanObject,
    mut v___y_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1437_: usize = 0;
    let mut v_stop_boxed_1438_: usize = 0;
    let mut v_res_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1437_ = leanh::lean_unbox_usize(v_i_1432_);
    leanh::lean_dec(v_i_1432_);
    v_stop_boxed_1438_ = leanh::lean_unbox_usize(v_stop_1433_);
    leanh::lean_dec(v_stop_1433_);
    v_res_1439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_1428_, v_stx_1429_, v___x_1430_, v_as_1431_, v_i_boxed_1437_, v_stop_boxed_1438_, v_b_1434_, v___y_1435_, v___y_1436_);
    leanh::lean_dec_ref(v___y_1435_);
    leanh::lean_dec_ref(v_as_1431_);
    leanh::lean_dec(v___x_1428_);
    return v_res_1439_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(
    mut v___x_1440_: *mut leanh::LeanObject,
    mut v_stx_1441_: *mut leanh::LeanObject,
    mut v_as_1442_: *mut leanh::LeanObject,
    mut v_i_1443_: usize,
    mut v_stop_1444_: usize,
    mut v_b_1445_: *mut leanh::LeanObject,
    mut v___y_1446_: *mut leanh::LeanObject,
    mut v___y_1447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1448_: u8 = 0;
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: usize = 0;
    let mut v___x_1459_: usize = 0;
    let mut v_a_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1469_: u8 = 0;
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1448_ = lean_usize_dec_eq(v_i_1443_, v_stop_1444_);
                if v___x_1448_ == 0 {
                    v___x_1449_ = lean_array_uget_borrowed(v_as_1442_, v_i_1443_);
                    leanh::lean_inc(v___x_1449_);
                    v___x_1450_ = l_Lake_expandBinderIdent(v___x_1449_, v___y_1446_, v___y_1447_);
                    if leanh::lean_obj_tag(v___x_1450_) == 0 {
                        v_a_1451_ = leanh::lean_ctor_get(v___x_1450_, 0);
                        leanh::lean_inc(v_a_1451_);
                        v_a_1452_ = leanh::lean_ctor_get(v___x_1450_, 1);
                        leanh::lean_inc(v_a_1452_);
                        leanh::lean_dec_ref_known(v___x_1450_, 2);
                        v___x_1453_ = l_Lake_expandBinderType(v___x_1449_, v___x_1440_);
                        v___x_1454_ = 2;
                        v___x_1455_ = leanh::lean_box(0);
                        leanh::lean_inc(v_stx_1441_);
                        v___x_1456_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                        leanh::lean_ctor_set(v___x_1456_, 0, v_stx_1441_);
                        leanh::lean_ctor_set(v___x_1456_, 1, v_a_1451_);
                        leanh::lean_ctor_set(v___x_1456_, 2, v___x_1453_);
                        leanh::lean_ctor_set(v___x_1456_, 3, v___x_1455_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1456_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                            v___x_1454_,
                        );
                        v___x_1457_ = lean_array_push(v_b_1445_, v___x_1456_);
                        v___x_1458_ = 1usize;
                        v___x_1459_ = lean_usize_add(v_i_1443_, v___x_1458_);
                        v_i_1443_ = v___x_1459_;
                        v_b_1445_ = v___x_1457_;
                        v___y_1447_ = v_a_1452_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_b_1445_);
                        leanh::lean_dec(v_stx_1441_);
                        v_a_1461_ = leanh::lean_ctor_get(v___x_1450_, 0);
                        v_a_1462_ = leanh::lean_ctor_get(v___x_1450_, 1);
                        v_isSharedCheck_1469_ =
                            (!leanh::lean_is_exclusive(v___x_1450_)) as u8;
                        if v_isSharedCheck_1469_ == 0 {
                            v___x_1464_ = v___x_1450_;
                            v_isShared_1465_ = v_isSharedCheck_1469_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1462_);
                            leanh::lean_inc(v_a_1461_);
                            leanh::lean_dec(v___x_1450_);
                            v___x_1464_ = leanh::lean_box(0);
                            v_isShared_1465_ = v_isSharedCheck_1469_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_stx_1441_);
                    v___x_1470_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1470_, 0, v_b_1445_);
                    leanh::lean_ctor_set(v___x_1470_, 1, v___y_1447_);
                    return v___x_1470_;
                }
            }
            1 => {
                if v_isShared_1465_ == 0 {
                    v___x_1467_ = v___x_1464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1468_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1461_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_a_1462_);
                    v___x_1467_ = v_reuseFailAlloc_1468_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0___boxed(
    mut v___x_1471_: *mut leanh::LeanObject,
    mut v_stx_1472_: *mut leanh::LeanObject,
    mut v_as_1473_: *mut leanh::LeanObject,
    mut v_i_1474_: *mut leanh::LeanObject,
    mut v_stop_1475_: *mut leanh::LeanObject,
    mut v_b_1476_: *mut leanh::LeanObject,
    mut v___y_1477_: *mut leanh::LeanObject,
    mut v___y_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1479_: usize = 0;
    let mut v_stop_boxed_1480_: usize = 0;
    let mut v_res_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1479_ = leanh::lean_unbox_usize(v_i_1474_);
    leanh::lean_dec(v_i_1474_);
    v_stop_boxed_1480_ = leanh::lean_unbox_usize(v_stop_1475_);
    leanh::lean_dec(v_stop_1475_);
    v_res_1481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_1471_, v_stx_1472_, v_as_1473_, v_i_boxed_1479_, v_stop_boxed_1480_, v_b_1476_, v___y_1477_, v___y_1478_);
    leanh::lean_dec_ref(v___y_1477_);
    leanh::lean_dec_ref(v_as_1473_);
    leanh::lean_dec(v___x_1471_);
    return v_res_1481_;
}
pub unsafe fn l_Lake_expandBinderCore(
    mut v_binders_1506_: *mut leanh::LeanObject,
    mut v_stx_1507_: *mut leanh::LeanObject,
    mut v_a_1508_: *mut leanh::LeanObject,
    mut v_a_1509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1512_: u8 = 0;
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1540_: u8 = 0;
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1548_: u8 = 0;
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: u8 = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: u8 = 0;
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: usize = 0;
    let mut v___x_1562_: usize = 0;
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: usize = 0;
    let mut v___x_1565_: usize = 0;
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut v_a_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1572_: u8 = 0;
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1584_: u8 = 0;
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u8 = 0;
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: usize = 0;
    let mut v___x_1598_: usize = 0;
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: usize = 0;
    let mut v___x_1601_: usize = 0;
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_a_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1608_: u8 = 0;
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1620_: u8 = 0;
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: usize = 0;
    let mut v___x_1637_: usize = 0;
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: usize = 0;
    let mut v___x_1640_: usize = 0;
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1642_: u8 = 0;
    let mut v_a_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1657_: u8 = 0;
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1666_: u8 = 0;
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_stx_1507_);
                v_k_1510_ = l_Lean_Syntax_getKind(v_stx_1507_);
                v___x_1667_ = l_Lean_Syntax_isIdent(v_stx_1507_);
                if v___x_1667_ == 0 {
                    v___x_1668_ = l_Lake_mkHoleFrom___closed__4;
                    v___x_1669_ = lean_name_eq(v_k_1510_, v___x_1668_);
                    v___y_1512_ = v___x_1669_;
                    state = 1;
                    continue;
                } else {
                    v___y_1512_ = v___x_1667_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1512_ == 0 {
                    v___x_1513_ = l_Lake_expandBinderCore___closed__1;
                    v___x_1514_ = lean_name_eq(v_k_1510_, v___x_1513_);
                    if v___x_1514_ == 0 {
                        v___x_1515_ = l_Lake_expandBinderCore___closed__3;
                        v___x_1516_ = lean_name_eq(v_k_1510_, v___x_1515_);
                        if v___x_1516_ == 0 {
                            v___x_1517_ = l_Lake_expandBinderCore___closed__5;
                            v___x_1518_ = lean_name_eq(v_k_1510_, v___x_1517_);
                            if v___x_1518_ == 0 {
                                v___x_1519_ = l_Lake_expandBinderCore___closed__7;
                                v___x_1520_ = lean_name_eq(v_k_1510_, v___x_1519_);
                                leanh::lean_dec(v_k_1510_);
                                if v___x_1520_ == 0 {
                                    leanh::lean_dec(v_stx_1507_);
                                    leanh::lean_dec_ref(v_binders_1506_);
                                    v___x_1521_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1509_);
                                    return v___x_1521_;
                                } else {
                                    v___x_1522_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_1523_ = l_Lean_Syntax_getArg(v_stx_1507_, v___x_1522_);
                                    v_id_1524_ = l_Lake_expandOptIdent(v___x_1523_);
                                    leanh::lean_dec(v___x_1523_);
                                    v___x_1525_ =
                                        l_Lake_expandBinderIdent(v_id_1524_, v_a_1508_, v_a_1509_);
                                    v_a_1526_ = leanh::lean_ctor_get(v___x_1525_, 0);
                                    v_a_1527_ = leanh::lean_ctor_get(v___x_1525_, 1);
                                    v_isSharedCheck_1540_ =
                                        (!leanh::lean_is_exclusive(v___x_1525_)) as u8;
                                    if v_isSharedCheck_1540_ == 0 {
                                        v___x_1529_ = v___x_1525_;
                                        v_isShared_1530_ = v_isSharedCheck_1540_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1527_);
                                        leanh::lean_inc(v_a_1526_);
                                        leanh::lean_dec(v___x_1525_);
                                        v___x_1529_ = leanh::lean_box(0);
                                        v_isShared_1530_ = v_isSharedCheck_1540_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_k_1510_);
                                v___x_1541_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1542_ = l_Lean_Syntax_getArg(v_stx_1507_, v___x_1541_);
                                v___x_1543_ =
                                    l_Lake_getBinderIds(v___x_1542_, v_a_1508_, v_a_1509_);
                                leanh::lean_dec(v___x_1542_);
                                if leanh::lean_obj_tag(v___x_1543_) == 0 {
                                    v_a_1544_ = leanh::lean_ctor_get(v___x_1543_, 0);
                                    v_a_1545_ = leanh::lean_ctor_get(v___x_1543_, 1);
                                    v_isSharedCheck_1567_ =
                                        (!leanh::lean_is_exclusive(v___x_1543_)) as u8;
                                    if v_isSharedCheck_1567_ == 0 {
                                        v___x_1547_ = v___x_1543_;
                                        v_isShared_1548_ = v_isSharedCheck_1567_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1545_);
                                        leanh::lean_inc(v_a_1544_);
                                        leanh::lean_dec(v___x_1543_);
                                        v___x_1547_ = leanh::lean_box(0);
                                        v_isShared_1548_ = v_isSharedCheck_1567_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_stx_1507_);
                                    leanh::lean_dec_ref(v_binders_1506_);
                                    v_a_1568_ = leanh::lean_ctor_get(v___x_1543_, 0);
                                    v_a_1569_ = leanh::lean_ctor_get(v___x_1543_, 1);
                                    v_isSharedCheck_1576_ =
                                        (!leanh::lean_is_exclusive(v___x_1543_)) as u8;
                                    if v_isSharedCheck_1576_ == 0 {
                                        v___x_1571_ = v___x_1543_;
                                        v_isShared_1572_ = v_isSharedCheck_1576_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1569_);
                                        leanh::lean_inc(v_a_1568_);
                                        leanh::lean_dec(v___x_1543_);
                                        v___x_1571_ = leanh::lean_box(0);
                                        v_isShared_1572_ = v_isSharedCheck_1576_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_k_1510_);
                            v___x_1577_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1578_ = l_Lean_Syntax_getArg(v_stx_1507_, v___x_1577_);
                            v___x_1579_ = l_Lake_getBinderIds(v___x_1578_, v_a_1508_, v_a_1509_);
                            leanh::lean_dec(v___x_1578_);
                            if leanh::lean_obj_tag(v___x_1579_) == 0 {
                                v_a_1580_ = leanh::lean_ctor_get(v___x_1579_, 0);
                                v_a_1581_ = leanh::lean_ctor_get(v___x_1579_, 1);
                                v_isSharedCheck_1603_ =
                                    (!leanh::lean_is_exclusive(v___x_1579_)) as u8;
                                if v_isSharedCheck_1603_ == 0 {
                                    v___x_1583_ = v___x_1579_;
                                    v_isShared_1584_ = v_isSharedCheck_1603_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1581_);
                                    leanh::lean_inc(v_a_1580_);
                                    leanh::lean_dec(v___x_1579_);
                                    v___x_1583_ = leanh::lean_box(0);
                                    v_isShared_1584_ = v_isSharedCheck_1603_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_stx_1507_);
                                leanh::lean_dec_ref(v_binders_1506_);
                                v_a_1604_ = leanh::lean_ctor_get(v___x_1579_, 0);
                                v_a_1605_ = leanh::lean_ctor_get(v___x_1579_, 1);
                                v_isSharedCheck_1612_ =
                                    (!leanh::lean_is_exclusive(v___x_1579_)) as u8;
                                if v_isSharedCheck_1612_ == 0 {
                                    v___x_1607_ = v___x_1579_;
                                    v_isShared_1608_ = v_isSharedCheck_1612_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1605_);
                                    leanh::lean_inc(v_a_1604_);
                                    leanh::lean_dec(v___x_1579_);
                                    v___x_1607_ = leanh::lean_box(0);
                                    v_isShared_1608_ = v_isSharedCheck_1612_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_k_1510_);
                        v___x_1613_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1614_ = l_Lean_Syntax_getArg(v_stx_1507_, v___x_1613_);
                        v___x_1615_ = l_Lake_getBinderIds(v___x_1614_, v_a_1508_, v_a_1509_);
                        leanh::lean_dec(v___x_1614_);
                        if leanh::lean_obj_tag(v___x_1615_) == 0 {
                            v_a_1616_ = leanh::lean_ctor_get(v___x_1615_, 0);
                            v_a_1617_ = leanh::lean_ctor_get(v___x_1615_, 1);
                            v_isSharedCheck_1642_ =
                                (!leanh::lean_is_exclusive(v___x_1615_)) as u8;
                            if v_isSharedCheck_1642_ == 0 {
                                v___x_1619_ = v___x_1615_;
                                v_isShared_1620_ = v_isSharedCheck_1642_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1617_);
                                leanh::lean_inc(v_a_1616_);
                                leanh::lean_dec(v___x_1615_);
                                v___x_1619_ = leanh::lean_box(0);
                                v_isShared_1620_ = v_isSharedCheck_1642_;
                                state = 14;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_stx_1507_);
                            leanh::lean_dec_ref(v_binders_1506_);
                            v_a_1643_ = leanh::lean_ctor_get(v___x_1615_, 0);
                            v_a_1644_ = leanh::lean_ctor_get(v___x_1615_, 1);
                            v_isSharedCheck_1651_ =
                                (!leanh::lean_is_exclusive(v___x_1615_)) as u8;
                            if v_isSharedCheck_1651_ == 0 {
                                v___x_1646_ = v___x_1615_;
                                v_isShared_1647_ = v_isSharedCheck_1651_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1644_);
                                leanh::lean_inc(v_a_1643_);
                                leanh::lean_dec(v___x_1615_);
                                v___x_1646_ = leanh::lean_box(0);
                                v_isShared_1647_ = v_isSharedCheck_1651_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_k_1510_);
                    leanh::lean_inc(v_stx_1507_);
                    v___x_1652_ = l_Lake_expandBinderIdent(v_stx_1507_, v_a_1508_, v_a_1509_);
                    v_a_1653_ = leanh::lean_ctor_get(v___x_1652_, 0);
                    v_a_1654_ = leanh::lean_ctor_get(v___x_1652_, 1);
                    v_isSharedCheck_1666_ = (!leanh::lean_is_exclusive(v___x_1652_)) as u8;
                    if v_isSharedCheck_1666_ == 0 {
                        v___x_1656_ = v___x_1652_;
                        v_isShared_1657_ = v_isSharedCheck_1666_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1654_);
                        leanh::lean_inc(v_a_1653_);
                        leanh::lean_dec(v___x_1652_);
                        v___x_1656_ = leanh::lean_box(0);
                        v_isShared_1657_ = v_isSharedCheck_1666_;
                        state = 19;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1531_ = leanh::lean_unsigned_to_nat(2);
                v_type_1532_ = l_Lean_Syntax_getArg(v_stx_1507_, v___x_1531_);
                v___x_1533_ = 3;
                v___x_1534_ = leanh::lean_box(0);
                v___x_1535_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_1535_, 0, v_stx_1507_);
                leanh::lean_ctor_set(v___x_1535_, 1, v_a_1526_);
                leanh::lean_ctor_set(v___x_1535_, 2, v_type_1532_);
                leanh::lean_ctor_set(v___x_1535_, 3, v___x_1534_);
                leanh::lean_ctor_set_uint8(
                    v___x_1535_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_1533_,
                );
                v___x_1536_ = lean_array_push(v_binders_1506_, v___x_1535_);
                if v_isShared_1530_ == 0 {
                    leanh::lean_ctor_set(v___x_1529_, 0, v___x_1536_);
                    v___x_1538_ = v___x_1529_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1539_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_a_1527_);
                    v___x_1538_ = v_reuseFailAlloc_1539_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1538_;
            }
            4 => {
                v___x_1549_ = leanh::lean_unsigned_to_nat(0);
                v___x_1550_ = lean_array_get_size(v_a_1544_);
                v___x_1551_ = lean_nat_dec_lt(v___x_1549_, v___x_1550_);
                if v___x_1551_ == 0 {
                    leanh::lean_dec(v_a_1544_);
                    leanh::lean_dec(v_stx_1507_);
                    if v_isShared_1548_ == 0 {
                        leanh::lean_ctor_set(v___x_1547_, 0, v_binders_1506_);
                        v___x_1553_ = v___x_1547_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1554_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_binders_1506_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_a_1545_);
                        v___x_1553_ = v_reuseFailAlloc_1554_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_1555_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1556_ = l_Lean_Syntax_getArg(v_stx_1507_, v___x_1555_);
                    v___x_1557_ = lean_nat_dec_le(v___x_1550_, v___x_1550_);
                    if v___x_1557_ == 0 {
                        if v___x_1551_ == 0 {
                            leanh::lean_dec(v___x_1556_);
                            leanh::lean_dec(v_a_1544_);
                            leanh::lean_dec(v_stx_1507_);
                            if v_isShared_1548_ == 0 {
                                leanh::lean_ctor_set(v___x_1547_, 0, v_binders_1506_);
                                v___x_1559_ = v___x_1547_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_1560_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1560_,
                                    0,
                                    v_binders_1506_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_a_1545_);
                                v___x_1559_ = v_reuseFailAlloc_1560_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1547_);
                            v___x_1561_ = 0usize;
                            v___x_1562_ = lean_usize_of_nat(v___x_1550_);
                            v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_1556_, v_stx_1507_, v_a_1544_, v___x_1561_, v___x_1562_, v_binders_1506_, v_a_1508_, v_a_1545_);
                            leanh::lean_dec(v_a_1544_);
                            leanh::lean_dec(v___x_1556_);
                            return v___x_1563_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1547_);
                        v___x_1564_ = 0usize;
                        v___x_1565_ = lean_usize_of_nat(v___x_1550_);
                        v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_1556_, v_stx_1507_, v_a_1544_, v___x_1564_, v___x_1565_, v_binders_1506_, v_a_1508_, v_a_1545_);
                        leanh::lean_dec(v_a_1544_);
                        leanh::lean_dec(v___x_1556_);
                        return v___x_1566_;
                    }
                }
            }
            5 => {
                return v___x_1553_;
            }
            6 => {
                return v___x_1559_;
            }
            7 => {
                if v_isShared_1572_ == 0 {
                    v___x_1574_ = v___x_1571_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1575_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1568_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_a_1569_);
                    v___x_1574_ = v_reuseFailAlloc_1575_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1574_;
            }
            9 => {
                v___x_1585_ = leanh::lean_unsigned_to_nat(0);
                v___x_1586_ = lean_array_get_size(v_a_1580_);
                v___x_1587_ = lean_nat_dec_lt(v___x_1585_, v___x_1586_);
                if v___x_1587_ == 0 {
                    leanh::lean_dec(v_a_1580_);
                    leanh::lean_dec(v_stx_1507_);
                    if v_isShared_1584_ == 0 {
                        leanh::lean_ctor_set(v___x_1583_, 0, v_binders_1506_);
                        v___x_1589_ = v___x_1583_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1590_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_binders_1506_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_a_1581_);
                        v___x_1589_ = v_reuseFailAlloc_1590_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___x_1591_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1592_ = l_Lean_Syntax_getArg(v_stx_1507_, v___x_1591_);
                    v___x_1593_ = lean_nat_dec_le(v___x_1586_, v___x_1586_);
                    if v___x_1593_ == 0 {
                        if v___x_1587_ == 0 {
                            leanh::lean_dec(v___x_1592_);
                            leanh::lean_dec(v_a_1580_);
                            leanh::lean_dec(v_stx_1507_);
                            if v_isShared_1584_ == 0 {
                                leanh::lean_ctor_set(v___x_1583_, 0, v_binders_1506_);
                                v___x_1595_ = v___x_1583_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_1596_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1596_,
                                    0,
                                    v_binders_1506_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_a_1581_);
                                v___x_1595_ = v_reuseFailAlloc_1596_;
                                state = 11;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1583_);
                            v___x_1597_ = 0usize;
                            v___x_1598_ = lean_usize_of_nat(v___x_1586_);
                            v___x_1599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_1592_, v_stx_1507_, v_a_1580_, v___x_1597_, v___x_1598_, v_binders_1506_, v_a_1508_, v_a_1581_);
                            leanh::lean_dec(v_a_1580_);
                            leanh::lean_dec(v___x_1592_);
                            return v___x_1599_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1583_);
                        v___x_1600_ = 0usize;
                        v___x_1601_ = lean_usize_of_nat(v___x_1586_);
                        v___x_1602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_1592_, v_stx_1507_, v_a_1580_, v___x_1600_, v___x_1601_, v_binders_1506_, v_a_1508_, v_a_1581_);
                        leanh::lean_dec(v_a_1580_);
                        leanh::lean_dec(v___x_1592_);
                        return v___x_1602_;
                    }
                }
            }
            10 => {
                return v___x_1589_;
            }
            11 => {
                return v___x_1595_;
            }
            12 => {
                if v_isShared_1608_ == 0 {
                    v___x_1610_ = v___x_1607_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1604_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_a_1605_);
                    v___x_1610_ = v_reuseFailAlloc_1611_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1610_;
            }
            14 => {
                v___x_1621_ = leanh::lean_unsigned_to_nat(0);
                v___x_1622_ = lean_array_get_size(v_a_1616_);
                v___x_1623_ = lean_nat_dec_lt(v___x_1621_, v___x_1622_);
                if v___x_1623_ == 0 {
                    leanh::lean_dec(v_a_1616_);
                    leanh::lean_dec(v_stx_1507_);
                    if v_isShared_1620_ == 0 {
                        leanh::lean_ctor_set(v___x_1619_, 0, v_binders_1506_);
                        v___x_1625_ = v___x_1619_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1626_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_binders_1506_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_a_1617_);
                        v___x_1625_ = v_reuseFailAlloc_1626_;
                        state = 15;
                        continue;
                    }
                } else {
                    v___x_1627_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1628_ = l_Lean_Syntax_getArg(v_stx_1507_, v___x_1627_);
                    v___x_1629_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1630_ = l_Lean_Syntax_getArg(v_stx_1507_, v___x_1629_);
                    v___x_1631_ = l_Lake_expandBinderModifier(v___x_1630_);
                    leanh::lean_dec(v___x_1630_);
                    v___x_1632_ = lean_nat_dec_le(v___x_1622_, v___x_1622_);
                    if v___x_1632_ == 0 {
                        if v___x_1623_ == 0 {
                            leanh::lean_dec(v___x_1631_);
                            leanh::lean_dec(v___x_1628_);
                            leanh::lean_dec(v_a_1616_);
                            leanh::lean_dec(v_stx_1507_);
                            if v_isShared_1620_ == 0 {
                                leanh::lean_ctor_set(v___x_1619_, 0, v_binders_1506_);
                                v___x_1634_ = v___x_1619_;
                                state = 16;
                                continue;
                            } else {
                                v_reuseFailAlloc_1635_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1635_,
                                    0,
                                    v_binders_1506_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_a_1617_);
                                v___x_1634_ = v_reuseFailAlloc_1635_;
                                state = 16;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1619_);
                            v___x_1636_ = 0usize;
                            v___x_1637_ = lean_usize_of_nat(v___x_1622_);
                            v___x_1638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_1628_, v_stx_1507_, v___x_1631_, v_a_1616_, v___x_1636_, v___x_1637_, v_binders_1506_, v_a_1508_, v_a_1617_);
                            leanh::lean_dec(v_a_1616_);
                            leanh::lean_dec(v___x_1628_);
                            return v___x_1638_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1619_);
                        v___x_1639_ = 0usize;
                        v___x_1640_ = lean_usize_of_nat(v___x_1622_);
                        v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_1628_, v_stx_1507_, v___x_1631_, v_a_1616_, v___x_1639_, v___x_1640_, v_binders_1506_, v_a_1508_, v_a_1617_);
                        leanh::lean_dec(v_a_1616_);
                        leanh::lean_dec(v___x_1628_);
                        return v___x_1641_;
                    }
                }
            }
            15 => {
                return v___x_1625_;
            }
            16 => {
                return v___x_1634_;
            }
            17 => {
                if v_isShared_1647_ == 0 {
                    v___x_1649_ = v___x_1646_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1650_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1643_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_a_1644_);
                    v___x_1649_ = v_reuseFailAlloc_1650_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1649_;
            }
            19 => {
                v___x_1658_ = l_Lake_mkHoleFrom(v_stx_1507_);
                v___x_1659_ = 0;
                v___x_1660_ = leanh::lean_box(0);
                v___x_1661_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_1661_, 0, v_stx_1507_);
                leanh::lean_ctor_set(v___x_1661_, 1, v_a_1653_);
                leanh::lean_ctor_set(v___x_1661_, 2, v___x_1658_);
                leanh::lean_ctor_set(v___x_1661_, 3, v___x_1660_);
                leanh::lean_ctor_set_uint8(
                    v___x_1661_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_1659_,
                );
                v___x_1662_ = lean_array_push(v_binders_1506_, v___x_1661_);
                if v_isShared_1657_ == 0 {
                    leanh::lean_ctor_set(v___x_1656_, 0, v___x_1662_);
                    v___x_1664_ = v___x_1656_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1665_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_a_1654_);
                    v___x_1664_ = v_reuseFailAlloc_1665_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1664_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_expandBinderCore___boxed(
    mut v_binders_1670_: *mut leanh::LeanObject,
    mut v_stx_1671_: *mut leanh::LeanObject,
    mut v_a_1672_: *mut leanh::LeanObject,
    mut v_a_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1674_ = l_Lake_expandBinderCore(v_binders_1670_, v_stx_1671_, v_a_1672_, v_a_1673_);
    leanh::lean_dec_ref(v_a_1672_);
    return v_res_1674_;
}
pub unsafe fn l_Lake_expandBinder(
    mut v_stx_1677_: *mut leanh::LeanObject,
    mut v_a_1678_: *mut leanh::LeanObject,
    mut v_a_1679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = l_Lake_expandBinder___closed__0;
    v___x_1681_ = l_Lake_expandBinderCore(v___x_1680_, v_stx_1677_, v_a_1678_, v_a_1679_);
    return v___x_1681_;
}
pub unsafe fn l_Lake_expandBinder___boxed(
    mut v_stx_1682_: *mut leanh::LeanObject,
    mut v_a_1683_: *mut leanh::LeanObject,
    mut v_a_1684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1685_ = l_Lake_expandBinder(v_stx_1682_, v_a_1683_, v_a_1684_);
    leanh::lean_dec_ref(v_a_1683_);
    return v_res_1685_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(
    mut v_as_1686_: *mut leanh::LeanObject,
    mut v_i_1687_: usize,
    mut v_stop_1688_: usize,
    mut v_b_1689_: *mut leanh::LeanObject,
    mut v___y_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: usize = 0;
    let mut v___x_1698_: usize = 0;
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1692_ = lean_usize_dec_eq(v_i_1687_, v_stop_1688_);
                if v___x_1692_ == 0 {
                    v___x_1693_ = lean_array_uget_borrowed(v_as_1686_, v_i_1687_);
                    leanh::lean_inc(v___x_1693_);
                    v___x_1694_ =
                        l_Lake_expandBinderCore(v_b_1689_, v___x_1693_, v___y_1690_, v___y_1691_);
                    if leanh::lean_obj_tag(v___x_1694_) == 0 {
                        v_a_1695_ = leanh::lean_ctor_get(v___x_1694_, 0);
                        leanh::lean_inc(v_a_1695_);
                        v_a_1696_ = leanh::lean_ctor_get(v___x_1694_, 1);
                        leanh::lean_inc(v_a_1696_);
                        leanh::lean_dec_ref_known(v___x_1694_, 2);
                        v___x_1697_ = 1usize;
                        v___x_1698_ = lean_usize_add(v_i_1687_, v___x_1697_);
                        v_i_1687_ = v___x_1698_;
                        v_b_1689_ = v_a_1695_;
                        v___y_1691_ = v_a_1696_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1694_;
                    }
                } else {
                    v___x_1700_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1700_, 0, v_b_1689_);
                    leanh::lean_ctor_set(v___x_1700_, 1, v___y_1691_);
                    return v___x_1700_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0___boxed(
    mut v_as_1701_: *mut leanh::LeanObject,
    mut v_i_1702_: *mut leanh::LeanObject,
    mut v_stop_1703_: *mut leanh::LeanObject,
    mut v_b_1704_: *mut leanh::LeanObject,
    mut v___y_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1707_: usize = 0;
    let mut v_stop_boxed_1708_: usize = 0;
    let mut v_res_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1707_ = leanh::lean_unbox_usize(v_i_1702_);
    leanh::lean_dec(v_i_1702_);
    v_stop_boxed_1708_ = leanh::lean_unbox_usize(v_stop_1703_);
    leanh::lean_dec(v_stop_1703_);
    v_res_1709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_as_1701_, v_i_boxed_1707_, v_stop_boxed_1708_, v_b_1704_, v___y_1705_, v___y_1706_);
    leanh::lean_dec_ref(v___y_1705_);
    leanh::lean_dec_ref(v_as_1701_);
    return v_res_1709_;
}
pub unsafe fn l_Lake_expandBinders(
    mut v_stxs_1710_: *mut leanh::LeanObject,
    mut v_a_1711_: *mut leanh::LeanObject,
    mut v_a_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    v___x_1713_ = leanh::lean_unsigned_to_nat(0);
    v___x_1714_ = l_Lake_expandBinder___closed__0;
    v___x_1715_ = lean_array_get_size(v_stxs_1710_);
    v___x_1716_ = lean_nat_dec_lt(v___x_1713_, v___x_1715_);
    if v___x_1716_ == 0 {
        let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1717_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1717_, 0, v___x_1714_);
        leanh::lean_ctor_set(v___x_1717_, 1, v_a_1712_);
        return v___x_1717_;
    } else {
        let mut v___x_1718_: u8 = 0;
        v___x_1718_ = lean_nat_dec_le(v___x_1715_, v___x_1715_);
        if v___x_1718_ == 0 {
            if v___x_1716_ == 0 {
                let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1719_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1719_, 0, v___x_1714_);
                leanh::lean_ctor_set(v___x_1719_, 1, v_a_1712_);
                return v___x_1719_;
            } else {
                let mut v___x_1720_: usize = 0;
                let mut v___x_1721_: usize = 0;
                let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1720_ = 0usize;
                v___x_1721_ = lean_usize_of_nat(v___x_1715_);
                v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_stxs_1710_, v___x_1720_, v___x_1721_, v___x_1714_, v_a_1711_, v_a_1712_);
                return v___x_1722_;
            }
        } else {
            let mut v___x_1723_: usize = 0;
            let mut v___x_1724_: usize = 0;
            let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1723_ = 0usize;
            v___x_1724_ = lean_usize_of_nat(v___x_1715_);
            v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_stxs_1710_, v___x_1723_, v___x_1724_, v___x_1714_, v_a_1711_, v_a_1712_);
            return v___x_1725_;
        }
    }
}
pub unsafe fn l_Lake_expandBinders___boxed(
    mut v_stxs_1726_: *mut leanh::LeanObject,
    mut v_a_1727_: *mut leanh::LeanObject,
    mut v_a_1728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1729_ = l_Lake_expandBinders(v_stxs_1726_, v_a_1727_, v_a_1728_);
    leanh::lean_dec_ref(v_a_1727_);
    leanh::lean_dec_ref(v_stxs_1726_);
    return v_res_1729_;
}
pub unsafe fn _init_l_Lake_BinderSyntaxView_mkBinder___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1735_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_1735_;
}
pub unsafe fn l_Lake_BinderSyntaxView_mkBinder(
    mut v_x_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_1746_: u8 = 0;
    let mut v_ref_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifier_x3f_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: u8 = 0;
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: u8 = 0;
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: u8 = 0;
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_1746_ = leanh::lean_ctor_get_uint8(
                    v_x_1745_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                );
                match v_info_1746_ {
                    0 => {
                        v_ref_1747_ = leanh::lean_ctor_get(v_x_1745_, 0);
                        leanh::lean_inc(v_ref_1747_);
                        v_id_1748_ = leanh::lean_ctor_get(v_x_1745_, 1);
                        leanh::lean_inc(v_id_1748_);
                        v_type_1749_ = leanh::lean_ctor_get(v_x_1745_, 2);
                        leanh::lean_inc(v_type_1749_);
                        v_modifier_x3f_1750_ = leanh::lean_ctor_get(v_x_1745_, 3);
                        leanh::lean_inc(v_modifier_x3f_1750_);
                        leanh::lean_dec_ref(v_x_1745_);
                        v___x_1751_ = 0;
                        v___x_1752_ = l_Lean_SourceInfo_fromRef(v_ref_1747_, v___x_1751_);
                        leanh::lean_dec(v_ref_1747_);
                        v___x_1753_ = l_Lake_expandBinderCore___closed__1;
                        v___x_1754_ = l_Lake_BinderSyntaxView_mkBinder___closed__0;
                        leanh::lean_inc_n(v___x_1752_, 4);
                        v___x_1755_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1755_, 0, v___x_1752_);
                        leanh::lean_ctor_set(v___x_1755_, 1, v___x_1754_);
                        v___x_1756_ = l_Lake_BinderSyntaxView_mkBinder___closed__2;
                        v___x_1757_ = l_Lean_Syntax_node1(v___x_1752_, v___x_1756_, v_id_1748_);
                        v___x_1758_ = l_Lake_BinderSyntaxView_mkBinder___closed__3;
                        v___x_1759_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1759_, 0, v___x_1752_);
                        leanh::lean_ctor_set(v___x_1759_, 1, v___x_1758_);
                        v___x_1760_ = l_Lean_Syntax_node2(
                            v___x_1752_,
                            v___x_1756_,
                            v___x_1759_,
                            v_type_1749_,
                        );
                        v___x_1761_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_BinderSyntaxView_mkBinder___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lake_BinderSyntaxView_mkBinder___closed__4_once
                            ),
                            _init_l_Lake_BinderSyntaxView_mkBinder___closed__4,
                        );
                        if leanh::lean_obj_tag(v_modifier_x3f_1750_) == 1 {
                            v_val_1769_ = leanh::lean_ctor_get(v_modifier_x3f_1750_, 0);
                            leanh::lean_inc(v_val_1769_);
                            leanh::lean_dec_ref_known(v_modifier_x3f_1750_, 1);
                            v___x_1770_ = l_Array_mkArray1___redArg(v_val_1769_);
                            v___y_1763_ = v___x_1770_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_modifier_x3f_1750_);
                            v___x_1771_ = l_Lake_BinderSyntaxView_mkBinder___closed__6;
                            v___y_1763_ = v___x_1771_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_ref_1772_ = leanh::lean_ctor_get(v_x_1745_, 0);
                        leanh::lean_inc(v_ref_1772_);
                        v_id_1773_ = leanh::lean_ctor_get(v_x_1745_, 1);
                        leanh::lean_inc(v_id_1773_);
                        v_type_1774_ = leanh::lean_ctor_get(v_x_1745_, 2);
                        leanh::lean_inc(v_type_1774_);
                        leanh::lean_dec_ref(v_x_1745_);
                        v___x_1775_ = 0;
                        v___x_1776_ = l_Lean_SourceInfo_fromRef(v_ref_1772_, v___x_1775_);
                        leanh::lean_dec(v_ref_1772_);
                        v___x_1777_ = l_Lake_expandBinderCore___closed__3;
                        v___x_1778_ = l_Lake_BinderSyntaxView_mkBinder___closed__7;
                        leanh::lean_inc_n(v___x_1776_, 5);
                        v___x_1779_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1779_, 0, v___x_1776_);
                        leanh::lean_ctor_set(v___x_1779_, 1, v___x_1778_);
                        v___x_1780_ = l_Lake_BinderSyntaxView_mkBinder___closed__2;
                        v___x_1781_ = l_Lean_Syntax_node1(v___x_1776_, v___x_1780_, v_id_1773_);
                        v___x_1782_ = l_Lake_BinderSyntaxView_mkBinder___closed__3;
                        v___x_1783_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1783_, 0, v___x_1776_);
                        leanh::lean_ctor_set(v___x_1783_, 1, v___x_1782_);
                        v___x_1784_ = l_Lean_Syntax_node2(
                            v___x_1776_,
                            v___x_1780_,
                            v___x_1783_,
                            v_type_1774_,
                        );
                        v___x_1785_ = l_Lake_BinderSyntaxView_mkBinder___closed__8;
                        v___x_1786_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1786_, 0, v___x_1776_);
                        leanh::lean_ctor_set(v___x_1786_, 1, v___x_1785_);
                        v___x_1787_ = l_Lean_Syntax_node4(
                            v___x_1776_,
                            v___x_1777_,
                            v___x_1779_,
                            v___x_1781_,
                            v___x_1784_,
                            v___x_1786_,
                        );
                        return v___x_1787_;
                    }
                    2 => {
                        v_ref_1788_ = leanh::lean_ctor_get(v_x_1745_, 0);
                        leanh::lean_inc(v_ref_1788_);
                        v_id_1789_ = leanh::lean_ctor_get(v_x_1745_, 1);
                        leanh::lean_inc(v_id_1789_);
                        v_type_1790_ = leanh::lean_ctor_get(v_x_1745_, 2);
                        leanh::lean_inc(v_type_1790_);
                        leanh::lean_dec_ref(v_x_1745_);
                        v___x_1791_ = 0;
                        v___x_1792_ = l_Lean_SourceInfo_fromRef(v_ref_1788_, v___x_1791_);
                        leanh::lean_dec(v_ref_1788_);
                        v___x_1793_ = l_Lake_expandBinderCore___closed__5;
                        v___x_1794_ = l_Lake_BinderSyntaxView_mkBinder___closed__9;
                        leanh::lean_inc_n(v___x_1792_, 5);
                        v___x_1795_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1795_, 0, v___x_1792_);
                        leanh::lean_ctor_set(v___x_1795_, 1, v___x_1794_);
                        v___x_1796_ = l_Lake_BinderSyntaxView_mkBinder___closed__2;
                        v___x_1797_ = l_Lean_Syntax_node1(v___x_1792_, v___x_1796_, v_id_1789_);
                        v___x_1798_ = l_Lake_BinderSyntaxView_mkBinder___closed__3;
                        v___x_1799_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1799_, 0, v___x_1792_);
                        leanh::lean_ctor_set(v___x_1799_, 1, v___x_1798_);
                        v___x_1800_ = l_Lean_Syntax_node2(
                            v___x_1792_,
                            v___x_1796_,
                            v___x_1799_,
                            v_type_1790_,
                        );
                        v___x_1801_ = l_Lake_BinderSyntaxView_mkBinder___closed__10;
                        v___x_1802_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1802_, 0, v___x_1792_);
                        leanh::lean_ctor_set(v___x_1802_, 1, v___x_1801_);
                        v___x_1803_ = l_Lean_Syntax_node4(
                            v___x_1792_,
                            v___x_1793_,
                            v___x_1795_,
                            v___x_1797_,
                            v___x_1800_,
                            v___x_1802_,
                        );
                        return v___x_1803_;
                    }
                    _ => {
                        v_ref_1804_ = leanh::lean_ctor_get(v_x_1745_, 0);
                        leanh::lean_inc(v_ref_1804_);
                        v_id_1805_ = leanh::lean_ctor_get(v_x_1745_, 1);
                        leanh::lean_inc(v_id_1805_);
                        v_type_1806_ = leanh::lean_ctor_get(v_x_1745_, 2);
                        leanh::lean_inc(v_type_1806_);
                        leanh::lean_dec_ref(v_x_1745_);
                        v___x_1807_ = 0;
                        v___x_1808_ = l_Lean_SourceInfo_fromRef(v_ref_1804_, v___x_1807_);
                        leanh::lean_dec(v_ref_1804_);
                        v___x_1809_ = l_Lake_expandBinderCore___closed__7;
                        v___x_1810_ = l_Lake_BinderSyntaxView_mkBinder___closed__11;
                        leanh::lean_inc_n(v___x_1808_, 4);
                        v___x_1811_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1811_, 0, v___x_1808_);
                        leanh::lean_ctor_set(v___x_1811_, 1, v___x_1810_);
                        v___x_1812_ = l_Lake_BinderSyntaxView_mkBinder___closed__2;
                        v___x_1813_ = l_Lake_BinderSyntaxView_mkBinder___closed__3;
                        v___x_1814_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1814_, 0, v___x_1808_);
                        leanh::lean_ctor_set(v___x_1814_, 1, v___x_1813_);
                        v___x_1815_ =
                            l_Lean_Syntax_node2(v___x_1808_, v___x_1812_, v_id_1805_, v___x_1814_);
                        v___x_1816_ = l_Lake_BinderSyntaxView_mkBinder___closed__12;
                        v___x_1817_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1817_, 0, v___x_1808_);
                        leanh::lean_ctor_set(v___x_1817_, 1, v___x_1816_);
                        v___x_1818_ = l_Lean_Syntax_node4(
                            v___x_1808_,
                            v___x_1809_,
                            v___x_1811_,
                            v___x_1815_,
                            v_type_1806_,
                            v___x_1817_,
                        );
                        return v___x_1818_;
                    }
                }
            }
            1 => {
                v___x_1764_ = l_Array_append___redArg(v___x_1761_, v___y_1763_);
                leanh::lean_dec_ref(v___y_1763_);
                leanh::lean_inc_n(v___x_1752_, 2);
                v___x_1765_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1765_, 0, v___x_1752_);
                leanh::lean_ctor_set(v___x_1765_, 1, v___x_1756_);
                leanh::lean_ctor_set(v___x_1765_, 2, v___x_1764_);
                v___x_1766_ = l_Lake_BinderSyntaxView_mkBinder___closed__5;
                v___x_1767_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1767_, 0, v___x_1752_);
                leanh::lean_ctor_set(v___x_1767_, 1, v___x_1766_);
                v___x_1768_ = l_Lean_Syntax_node5(
                    v___x_1752_,
                    v___x_1753_,
                    v___x_1755_,
                    v___x_1757_,
                    v___x_1760_,
                    v___x_1765_,
                    v___x_1767_,
                );
                return v___x_1768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BinderSyntaxView_mkDepArrow(
    mut v_res_1826_: *mut leanh::LeanObject,
    mut v_self_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1828_ = leanh::lean_ctor_get(v_self_1827_, 0);
    v___x_1829_ = 0;
    v___x_1830_ = l_Lean_SourceInfo_fromRef(v_ref_1828_, v___x_1829_);
    v___x_1831_ = l_Lake_BinderSyntaxView_mkDepArrow___closed__1;
    v___x_1832_ = l_Lake_BinderSyntaxView_mkBinder(v_self_1827_);
    v___x_1833_ = l_Lake_BinderSyntaxView_mkDepArrow___closed__2;
    leanh::lean_inc(v___x_1830_);
    v___x_1834_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1834_, 0, v___x_1830_);
    leanh::lean_ctor_set(v___x_1834_, 1, v___x_1833_);
    v___x_1835_ = l_Lean_Syntax_node3(
        v___x_1830_,
        v___x_1831_,
        v___x_1832_,
        v___x_1834_,
        v_res_1826_,
    );
    return v___x_1835_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(
    mut v_as_1836_: *mut leanh::LeanObject,
    mut v_i_1837_: usize,
    mut v_stop_1838_: usize,
    mut v_b_1839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1840_: u8 = 0;
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: usize = 0;
    let mut v___x_1844_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1840_ = lean_usize_dec_eq(v_i_1837_, v_stop_1838_);
                if v___x_1840_ == 0 {
                    v___x_1841_ = lean_array_uget_borrowed(v_as_1836_, v_i_1837_);
                    leanh::lean_inc(v___x_1841_);
                    v___x_1842_ = l_Lake_BinderSyntaxView_mkDepArrow(v_b_1839_, v___x_1841_);
                    v___x_1843_ = 1usize;
                    v___x_1844_ = lean_usize_add(v_i_1837_, v___x_1843_);
                    v_i_1837_ = v___x_1844_;
                    v_b_1839_ = v___x_1842_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1839_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0___boxed(
    mut v_as_1846_: *mut leanh::LeanObject,
    mut v_i_1847_: *mut leanh::LeanObject,
    mut v_stop_1848_: *mut leanh::LeanObject,
    mut v_b_1849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1850_: usize = 0;
    let mut v_stop_boxed_1851_: usize = 0;
    let mut v_res_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1850_ = leanh::lean_unbox_usize(v_i_1847_);
    leanh::lean_dec(v_i_1847_);
    v_stop_boxed_1851_ = leanh::lean_unbox_usize(v_stop_1848_);
    leanh::lean_dec(v_stop_1848_);
    v_res_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_as_1846_, v_i_boxed_1850_, v_stop_boxed_1851_, v_b_1849_);
    leanh::lean_dec_ref(v_as_1846_);
    return v_res_1852_;
}
pub unsafe fn l_Lake_mkDepArrow(
    mut v_binders_1853_: *mut leanh::LeanObject,
    mut v_res_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: u8 = 0;
    v___x_1855_ = leanh::lean_unsigned_to_nat(0);
    v___x_1856_ = lean_array_get_size(v_binders_1853_);
    v___x_1857_ = lean_nat_dec_lt(v___x_1855_, v___x_1856_);
    if v___x_1857_ == 0 {
        return v_res_1854_;
    } else {
        let mut v___x_1858_: u8 = 0;
        v___x_1858_ = lean_nat_dec_le(v___x_1856_, v___x_1856_);
        if v___x_1858_ == 0 {
            if v___x_1857_ == 0 {
                return v_res_1854_;
            } else {
                let mut v___x_1859_: usize = 0;
                let mut v___x_1860_: usize = 0;
                let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1859_ = 0usize;
                v___x_1860_ = lean_usize_of_nat(v___x_1856_);
                v___x_1861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_binders_1853_, v___x_1859_, v___x_1860_, v_res_1854_);
                return v___x_1861_;
            }
        } else {
            let mut v___x_1862_: usize = 0;
            let mut v___x_1863_: usize = 0;
            let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1862_ = 0usize;
            v___x_1863_ = lean_usize_of_nat(v___x_1856_);
            v___x_1864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_binders_1853_, v___x_1862_, v___x_1863_, v_res_1854_);
            return v___x_1864_;
        }
    }
}
pub unsafe fn l_Lake_mkDepArrow___boxed(
    mut v_binders_1865_: *mut leanh::LeanObject,
    mut v_res_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_Lake_mkDepArrow(v_binders_1865_, v_res_1866_);
    leanh::lean_dec_ref(v_binders_1865_);
    return v_res_1867_;
}
pub unsafe fn _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1887_ = l_Lake_BinderSyntaxView_mkFunBinder___closed__8;
    v___x_1888_ = l_String_toRawSubstring_x27(v___x_1887_);
    return v___x_1888_;
}
pub unsafe fn _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1889_ = l_Lean_firstFrontendMacroScope;
    v___x_1890_ = leanh::lean_box(0);
    v___x_1891_ = l_Lake_BinderSyntaxView_mkFunBinder___closed__1;
    v___x_1892_ = l_Lean_addMacroScope(v___x_1891_, v___x_1890_, v___x_1889_);
    return v___x_1892_;
}
pub unsafe fn l_Lake_BinderSyntaxView_mkFunBinder(
    mut v_x_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1922_: u8 = 0;
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1919_ = leanh::lean_ctor_get(v_x_1918_, 0);
    leanh::lean_inc(v_ref_1919_);
    v_id_1920_ = leanh::lean_ctor_get(v_x_1918_, 1);
    leanh::lean_inc(v_id_1920_);
    v_type_1921_ = leanh::lean_ctor_get(v_x_1918_, 2);
    leanh::lean_inc(v_type_1921_);
    v_info_1922_ = leanh::lean_ctor_get_uint8(
        v_x_1918_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
    );
    leanh::lean_dec_ref(v_x_1918_);
    v___x_1923_ = leanh::lean_box(0);
    v_ref_1924_ = l_Lean_replaceRef(v_ref_1919_, v___x_1923_);
    leanh::lean_dec(v_ref_1919_);
    match v_info_1922_ {
        0 => {
            let mut v___x_1925_: u8 = 0;
            let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1925_ = 0;
            v___x_1926_ = l_Lean_SourceInfo_fromRef(v_ref_1924_, v___x_1925_);
            leanh::lean_dec(v_ref_1924_);
            v___x_1927_ = l_Lake_BinderSyntaxView_mkFunBinder___closed__3;
            v___x_1928_ = l_Lake_BinderSyntaxView_mkFunBinder___closed__5;
            v___x_1929_ = l_Lake_BinderSyntaxView_mkBinder___closed__0;
            leanh::lean_inc_n(v___x_1926_, 7);
            v___x_1930_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1930_, 0, v___x_1926_);
            leanh::lean_ctor_set(v___x_1930_, 1, v___x_1929_);
            v___x_1931_ = l_Lake_BinderSyntaxView_mkFunBinder___closed__7;
            v___x_1932_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lake_BinderSyntaxView_mkFunBinder___closed__9),
                core::ptr::addr_of_mut!(l_Lake_BinderSyntaxView_mkFunBinder___closed__9_once),
                _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__9,
            );
            v___x_1933_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lake_BinderSyntaxView_mkFunBinder___closed__10),
                core::ptr::addr_of_mut!(l_Lake_BinderSyntaxView_mkFunBinder___closed__10_once),
                _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__10,
            );
            v___x_1934_ = l_Lake_BinderSyntaxView_mkFunBinder___closed__21;
            v___x_1935_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_1935_, 0, v___x_1926_);
            leanh::lean_ctor_set(v___x_1935_, 1, v___x_1932_);
            leanh::lean_ctor_set(v___x_1935_, 2, v___x_1933_);
            leanh::lean_ctor_set(v___x_1935_, 3, v___x_1934_);
            v___x_1936_ = l_Lean_Syntax_node1(v___x_1926_, v___x_1931_, v___x_1935_);
            v___x_1937_ = l_Lean_Syntax_node2(v___x_1926_, v___x_1928_, v___x_1930_, v___x_1936_);
            v___x_1938_ = l_Lake_BinderSyntaxView_mkBinder___closed__3;
            v___x_1939_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1939_, 0, v___x_1926_);
            leanh::lean_ctor_set(v___x_1939_, 1, v___x_1938_);
            v___x_1940_ = l_Lake_BinderSyntaxView_mkBinder___closed__2;
            v___x_1941_ = l_Lean_Syntax_node1(v___x_1926_, v___x_1940_, v_type_1921_);
            v___x_1942_ = l_Lake_BinderSyntaxView_mkBinder___closed__5;
            v___x_1943_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1943_, 0, v___x_1926_);
            leanh::lean_ctor_set(v___x_1943_, 1, v___x_1942_);
            v___x_1944_ = l_Lean_Syntax_node5(
                v___x_1926_,
                v___x_1927_,
                v___x_1937_,
                v_id_1920_,
                v___x_1939_,
                v___x_1941_,
                v___x_1943_,
            );
            return v___x_1944_;
        }
        1 => {
            let mut v___x_1945_: u8 = 0;
            let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1945_ = 0;
            v___x_1946_ = l_Lean_SourceInfo_fromRef(v_ref_1924_, v___x_1945_);
            leanh::lean_dec(v_ref_1924_);
            v___x_1947_ = l_Lake_expandBinderCore___closed__3;
            v___x_1948_ = l_Lake_BinderSyntaxView_mkBinder___closed__7;
            leanh::lean_inc_n(v___x_1946_, 5);
            v___x_1949_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1949_, 0, v___x_1946_);
            leanh::lean_ctor_set(v___x_1949_, 1, v___x_1948_);
            v___x_1950_ = l_Lake_BinderSyntaxView_mkBinder___closed__2;
            v___x_1951_ = l_Lean_Syntax_node1(v___x_1946_, v___x_1950_, v_id_1920_);
            v___x_1952_ = l_Lake_BinderSyntaxView_mkBinder___closed__3;
            v___x_1953_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1953_, 0, v___x_1946_);
            leanh::lean_ctor_set(v___x_1953_, 1, v___x_1952_);
            v___x_1954_ = l_Lean_Syntax_node2(v___x_1946_, v___x_1950_, v___x_1953_, v_type_1921_);
            v___x_1955_ = l_Lake_BinderSyntaxView_mkBinder___closed__8;
            v___x_1956_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1956_, 0, v___x_1946_);
            leanh::lean_ctor_set(v___x_1956_, 1, v___x_1955_);
            v___x_1957_ = l_Lean_Syntax_node4(
                v___x_1946_,
                v___x_1947_,
                v___x_1949_,
                v___x_1951_,
                v___x_1954_,
                v___x_1956_,
            );
            return v___x_1957_;
        }
        2 => {
            let mut v___x_1958_: u8 = 0;
            let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1958_ = 0;
            v___x_1959_ = l_Lean_SourceInfo_fromRef(v_ref_1924_, v___x_1958_);
            leanh::lean_dec(v_ref_1924_);
            v___x_1960_ = l_Lake_expandBinderCore___closed__5;
            v___x_1961_ = l_Lake_BinderSyntaxView_mkBinder___closed__9;
            leanh::lean_inc_n(v___x_1959_, 5);
            v___x_1962_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1962_, 0, v___x_1959_);
            leanh::lean_ctor_set(v___x_1962_, 1, v___x_1961_);
            v___x_1963_ = l_Lake_BinderSyntaxView_mkBinder___closed__2;
            v___x_1964_ = l_Lean_Syntax_node1(v___x_1959_, v___x_1963_, v_id_1920_);
            v___x_1965_ = l_Lake_BinderSyntaxView_mkBinder___closed__3;
            v___x_1966_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1966_, 0, v___x_1959_);
            leanh::lean_ctor_set(v___x_1966_, 1, v___x_1965_);
            v___x_1967_ = l_Lean_Syntax_node2(v___x_1959_, v___x_1963_, v___x_1966_, v_type_1921_);
            v___x_1968_ = l_Lake_BinderSyntaxView_mkBinder___closed__10;
            v___x_1969_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1969_, 0, v___x_1959_);
            leanh::lean_ctor_set(v___x_1969_, 1, v___x_1968_);
            v___x_1970_ = l_Lean_Syntax_node4(
                v___x_1959_,
                v___x_1960_,
                v___x_1962_,
                v___x_1964_,
                v___x_1967_,
                v___x_1969_,
            );
            return v___x_1970_;
        }
        _ => {
            let mut v___x_1971_: u8 = 0;
            let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1971_ = 0;
            v___x_1972_ = l_Lean_SourceInfo_fromRef(v_ref_1924_, v___x_1971_);
            leanh::lean_dec(v_ref_1924_);
            v___x_1973_ = l_Lake_expandBinderCore___closed__7;
            v___x_1974_ = l_Lake_BinderSyntaxView_mkBinder___closed__11;
            leanh::lean_inc_n(v___x_1972_, 4);
            v___x_1975_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1975_, 0, v___x_1972_);
            leanh::lean_ctor_set(v___x_1975_, 1, v___x_1974_);
            v___x_1976_ = l_Lake_BinderSyntaxView_mkBinder___closed__2;
            v___x_1977_ = l_Lake_BinderSyntaxView_mkBinder___closed__3;
            v___x_1978_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1978_, 0, v___x_1972_);
            leanh::lean_ctor_set(v___x_1978_, 1, v___x_1977_);
            v___x_1979_ = l_Lean_Syntax_node2(v___x_1972_, v___x_1976_, v_id_1920_, v___x_1978_);
            v___x_1980_ = l_Lake_BinderSyntaxView_mkBinder___closed__12;
            v___x_1981_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1981_, 0, v___x_1972_);
            leanh::lean_ctor_set(v___x_1981_, 1, v___x_1980_);
            v___x_1982_ = l_Lean_Syntax_node4(
                v___x_1972_,
                v___x_1973_,
                v___x_1975_,
                v___x_1979_,
                v_type_1921_,
                v___x_1981_,
            );
            return v___x_1982_;
        }
    }
}
pub unsafe fn l_Lake_BinderSyntaxView_mkArgument(
    mut v_x_1990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: u8 = 0;
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1991_ = leanh::lean_ctor_get(v_x_1990_, 0);
    leanh::lean_inc(v_ref_1991_);
    v_id_1992_ = leanh::lean_ctor_get(v_x_1990_, 1);
    leanh::lean_inc_n(v_id_1992_, 2);
    leanh::lean_dec_ref(v_x_1990_);
    v___x_1993_ = leanh::lean_box(0);
    v_ref_1994_ = l_Lean_replaceRef(v_ref_1991_, v___x_1993_);
    leanh::lean_dec(v_ref_1991_);
    v___x_1995_ = 0;
    v___x_1996_ = l_Lean_SourceInfo_fromRef(v_ref_1994_, v___x_1995_);
    leanh::lean_dec(v_ref_1994_);
    v___x_1997_ = l_Lake_BinderSyntaxView_mkArgument___closed__1;
    v___x_1998_ = l_Lake_BinderSyntaxView_mkBinder___closed__0;
    leanh::lean_inc_n(v___x_1996_, 3);
    v___x_1999_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1999_, 0, v___x_1996_);
    leanh::lean_ctor_set(v___x_1999_, 1, v___x_1998_);
    v___x_2000_ = l_Lake_BinderSyntaxView_mkArgument___closed__2;
    v___x_2001_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2001_, 0, v___x_1996_);
    leanh::lean_ctor_set(v___x_2001_, 1, v___x_2000_);
    v___x_2002_ = l_Lake_BinderSyntaxView_mkBinder___closed__5;
    v___x_2003_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2003_, 0, v___x_1996_);
    leanh::lean_ctor_set(v___x_2003_, 1, v___x_2002_);
    v___x_2004_ = l_Lean_Syntax_node5(
        v___x_1996_,
        v___x_1997_,
        v___x_1999_,
        v_id_1992_,
        v___x_2001_,
        v_id_1992_,
        v___x_2003_,
    );
    return v___x_2004_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Binder(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_binder = _init_l_Lake_binder();
    leanh::lean_mark_persistent(l_Lake_binder);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Binder(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Binder(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Binder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Binder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Binder(builtin);
}