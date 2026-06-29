// Lean compiler output
// Module: Lean.Elab.DocString.Builtin.Parsing
// Imports: Lean.Parser.Extension Init.While Init.Data.Array.Attach Init.Data.Array.Mem
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_uget, lean_array_uset, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
    lean_string_utf8_get, lean_string_utf8_next, lean_string_utf8_prev, lean_uint32_dec_eq,
    lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Attach::{
    initialize_Init_Data_Array_Attach, runtime_initialize_Init_Data_Array_Attach,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Array::Mem::{
    initialize_Init_Data_Array_Mem, runtime_initialize_Init_Data_Array_Mem,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getString;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::While::{
    initialize_Init_While, l___private_Init_While_0__whileM_erased___redArg,
    runtime_initialize_Init_While,
};
use crate::r#gen::Lean::Exception::{l_Lean_throwError___redArg, l_Lean_throwErrorAt___redArg};
use crate::r#gen::Lean::Log::l_Lean_logError___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Parser::Extension::{
    initialize_Lean_Parser_Extension, l_Lean_Parser_getTokenTable,
    l_Lean_Parser_mkInputContext___redArg, l_Lean_Parser_mkParserState,
    runtime_initialize_Lean_Parser_Extension,
};
use crate::r#gen::Lean::Parser::Types::{
    l_Lean_Parser_InputContext_atEnd, l_Lean_Parser_ParserFn_run,
    l_Lean_Parser_ParserState_allErrors, l_Lean_Parser_ParserState_mkError,
    l_Lean_Parser_ParserState_setPos, l_Lean_Parser_ParserState_toErrorMsg,
    l_Lean_Parser_SyntaxStack_back,
};
pub static l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [101, 110, 100, 32, 111, 102, 32, 105, 110, 112, 117, 116, 0],
};
static mut l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        78, 111, 116, 32, 97, 32, 113, 117, 111, 116, 101, 100, 32, 115, 116, 114, 105, 110, 103,
        32, 108, 105, 116, 101, 114, 97, 108, 0,
    ],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_951_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2;
    v___x_952_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_953_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_954_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1;
    v___x_955_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0;
    v___x_956_ =
        l_mkPanicMessageWithDecl(v___x_955_, v___x_954_, v___x_953_, v___x_952_, v___x_951_);
    return v___x_956_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
    mut v_inst_957_: *mut crate::leanh::LeanObject,
    mut v_s_958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_965_: u8 = 0;
    let mut v_toPure_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_971_: u8 = 0;
    let mut v_unused_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___y_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_973_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_974_ = 1;
                v___x_981_ = l_Lean_Syntax_getPos_x3f(v_s_958_, v___x_974_);
                if crate::leanh::lean_obj_tag(v___x_981_) == 0 {
                    v___x_982_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_983_ = l_panic___redArg(v___x_973_, v___x_982_);
                    v___y_976_ = v___x_983_;
                    state = 4;
                    continue;
                } else {
                    v_val_984_ = crate::leanh::lean_ctor_get(v___x_981_, 0);
                    crate::leanh::lean_inc(v_val_984_);
                    crate::leanh::lean_dec_ref_known(v___x_981_, 1);
                    v___y_976_ = v_val_984_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v_toApplicative_962_ = crate::leanh::lean_ctor_get(v_inst_957_, 0);
                v_isSharedCheck_971_ = (!crate::leanh::lean_is_exclusive(v_inst_957_)) as u8;
                if v_isSharedCheck_971_ == 0 {
                    v_unused_972_ = crate::leanh::lean_ctor_get(v_inst_957_, 1);
                    crate::leanh::lean_dec(v_unused_972_);
                    v___x_964_ = v_inst_957_;
                    v_isShared_965_ = v_isSharedCheck_971_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_962_);
                    crate::leanh::lean_dec(v_inst_957_);
                    v___x_964_ = crate::leanh::lean_box(0);
                    v_isShared_965_ = v_isSharedCheck_971_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toPure_966_ = crate::leanh::lean_ctor_get(v_toApplicative_962_, 1);
                crate::leanh::lean_inc(v_toPure_966_);
                crate::leanh::lean_dec_ref(v_toApplicative_962_);
                if v_isShared_965_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_964_, 1, v___y_961_);
                    crate::leanh::lean_ctor_set(v___x_964_, 0, v___y_960_);
                    v___x_968_ = v___x_964_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_970_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_970_, 0, v___y_960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_970_, 1, v___y_961_);
                    v___x_968_ = v_reuseFailAlloc_970_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_969_ = crate::leanh::lean_apply_2(
                    v_toPure_966_,
                    crate::leanh::lean_box(0),
                    v___x_968_,
                );
                return v___x_969_;
            }
            4 => {
                v___x_977_ = l_Lean_Syntax_getTailPos_x3f(v_s_958_, v___x_974_);
                if crate::leanh::lean_obj_tag(v___x_977_) == 0 {
                    v___x_978_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_979_ = l_panic___redArg(v___x_973_, v___x_978_);
                    v___y_960_ = v___y_976_;
                    v___y_961_ = v___x_979_;
                    state = 1;
                    continue;
                } else {
                    v_val_980_ = crate::leanh::lean_ctor_get(v___x_977_, 0);
                    crate::leanh::lean_inc(v_val_980_);
                    crate::leanh::lean_dec_ref_known(v___x_977_, 1);
                    v___y_960_ = v___y_976_;
                    v___y_961_ = v_val_980_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___boxed(
    mut v_inst_985_: *mut crate::leanh::LeanObject,
    mut v_s_986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_987_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_985_,
        v_s_986_,
    );
    crate::leanh::lean_dec(v_s_986_);
    return v_res_987_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(
    mut v_m_988_: *mut crate::leanh::LeanObject,
    mut v_inst_989_: *mut crate::leanh::LeanObject,
    mut v_inst_990_: *mut crate::leanh::LeanObject,
    mut v_s_991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_989_,
        v_s_991_,
    );
    return v___x_992_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___boxed(
    mut v_m_993_: *mut crate::leanh::LeanObject,
    mut v_inst_994_: *mut crate::leanh::LeanObject,
    mut v_inst_995_: *mut crate::leanh::LeanObject,
    mut v_s_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_997_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(
        v_m_993_,
        v_inst_994_,
        v_inst_995_,
        v_s_996_,
    );
    crate::leanh::lean_dec(v_s_996_);
    crate::leanh::lean_dec(v_inst_995_);
    return v_res_997_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__0(
    mut v_env_999_: *mut crate::leanh::LeanObject,
    mut v_p_1000_: *mut crate::leanh::LeanObject,
    mut v_ictx_1001_: *mut crate::leanh::LeanObject,
    mut v_s_1002_: *mut crate::leanh::LeanObject,
    mut v_inst_1003_: *mut crate::leanh::LeanObject,
    mut v_inst_1004_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1005_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: u8 = 0;
    v___x_1007_ = crate::leanh::lean_box(0);
    v___x_1008_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_env_999_);
    v___x_1009_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1009_, 0, v_env_999_);
    crate::leanh::lean_ctor_set(v___x_1009_, 1, v_____do__lift_1006_);
    crate::leanh::lean_ctor_set(v___x_1009_, 2, v___x_1007_);
    crate::leanh::lean_ctor_set(v___x_1009_, 3, v___x_1008_);
    v___x_1010_ = l_Lean_Parser_getTokenTable(v_env_999_);
    crate::leanh::lean_inc_ref(v_ictx_1001_);
    v_s_1011_ =
        l_Lean_Parser_ParserFn_run(v_p_1000_, v_ictx_1001_, v___x_1009_, v___x_1010_, v_s_1002_);
    crate::leanh::lean_inc_ref(v_s_1011_);
    v___x_1012_ = l_Lean_Parser_ParserState_allErrors(v_s_1011_);
    v___x_1013_ = lean_array_get_size(v___x_1012_);
    crate::leanh::lean_dec_ref(v___x_1012_);
    v___x_1014_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1015_ = lean_nat_dec_eq(v___x_1013_, v___x_1014_);
    if v___x_1015_ == 0 {
        let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toApplicative_1005_);
        v___x_1016_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1001_, v_s_1011_);
        v___x_1017_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1017_, 0, v___x_1016_);
        v___x_1018_ = l_Lean_MessageData_ofFormat(v___x_1017_);
        v___x_1019_ = l_Lean_throwError___redArg(v_inst_1003_, v_inst_1004_, v___x_1018_);
        return v___x_1019_;
    } else {
        let mut v_stxStack_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1022_: u8 = 0;
        v_stxStack_1020_ = crate::leanh::lean_ctor_get(v_s_1011_, 0);
        crate::leanh::lean_inc_ref(v_stxStack_1020_);
        v_pos_1021_ = crate::leanh::lean_ctor_get(v_s_1011_, 2);
        crate::leanh::lean_inc(v_pos_1021_);
        v___x_1022_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1001_, v_pos_1021_);
        crate::leanh::lean_dec(v_pos_1021_);
        if v___x_1022_ == 0 {
            let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_stxStack_1020_);
            crate::leanh::lean_dec_ref(v_toApplicative_1005_);
            v___x_1023_ = l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0;
            v___x_1024_ = l_Lean_Parser_ParserState_mkError(v_s_1011_, v___x_1023_);
            v___x_1025_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1001_, v___x_1024_);
            v___x_1026_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1026_, 0, v___x_1025_);
            v___x_1027_ = l_Lean_MessageData_ofFormat(v___x_1026_);
            v___x_1028_ = l_Lean_throwError___redArg(v_inst_1003_, v_inst_1004_, v___x_1027_);
            return v___x_1028_;
        } else {
            let mut v_toPure_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_s_1011_);
            crate::leanh::lean_dec_ref(v_inst_1004_);
            crate::leanh::lean_dec_ref(v_inst_1003_);
            crate::leanh::lean_dec_ref(v_ictx_1001_);
            v_toPure_1029_ = crate::leanh::lean_ctor_get(v_toApplicative_1005_, 1);
            crate::leanh::lean_inc(v_toPure_1029_);
            crate::leanh::lean_dec_ref(v_toApplicative_1005_);
            v___x_1030_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1020_);
            crate::leanh::lean_dec_ref(v_stxStack_1020_);
            v___x_1031_ =
                crate::leanh::lean_apply_2(v_toPure_1029_, crate::leanh::lean_box(0), v___x_1030_);
            return v___x_1031_;
        }
    }
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__1(
    mut v_source_1032_: *mut crate::leanh::LeanObject,
    mut v___y_1033_: *mut crate::leanh::LeanObject,
    mut v_start_1034_: *mut crate::leanh::LeanObject,
    mut v_env_1035_: *mut crate::leanh::LeanObject,
    mut v_p_1036_: *mut crate::leanh::LeanObject,
    mut v_inst_1037_: *mut crate::leanh::LeanObject,
    mut v_inst_1038_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1039_: *mut crate::leanh::LeanObject,
    mut v_toBind_1040_: *mut crate::leanh::LeanObject,
    mut v_inst_1041_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1043_: u8 = 0;
    let mut v_ictx_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1043_ = 1;
    crate::leanh::lean_inc_ref(v_source_1032_);
    v_ictx_1044_ = l_Lean_Parser_mkInputContext___redArg(
        v_source_1032_,
        v_____do__lift_1042_,
        v___x_1043_,
        v___y_1033_,
    );
    v___x_1045_ = l_Lean_Parser_mkParserState(v_source_1032_);
    crate::leanh::lean_dec_ref(v_source_1032_);
    v_s_1046_ = l_Lean_Parser_ParserState_setPos(v___x_1045_, v_start_1034_);
    v___f_1047_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__0 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1047_, 0, v_env_1035_);
    crate::leanh::lean_closure_set(v___f_1047_, 1, v_p_1036_);
    crate::leanh::lean_closure_set(v___f_1047_, 2, v_ictx_1044_);
    crate::leanh::lean_closure_set(v___f_1047_, 3, v_s_1046_);
    crate::leanh::lean_closure_set(v___f_1047_, 4, v_inst_1037_);
    crate::leanh::lean_closure_set(v___f_1047_, 5, v_inst_1038_);
    crate::leanh::lean_closure_set(v___f_1047_, 6, v_toApplicative_1039_);
    v___x_1048_ = crate::leanh::lean_apply_4(
        v_toBind_1040_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1041_,
        v___f_1047_,
    );
    return v___x_1048_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__2(
    mut v_text_1049_: *mut crate::leanh::LeanObject,
    mut v_inst_1050_: *mut crate::leanh::LeanObject,
    mut v_env_1051_: *mut crate::leanh::LeanObject,
    mut v_p_1052_: *mut crate::leanh::LeanObject,
    mut v_inst_1053_: *mut crate::leanh::LeanObject,
    mut v_inst_1054_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1055_: *mut crate::leanh::LeanObject,
    mut v_toBind_1056_: *mut crate::leanh::LeanObject,
    mut v_inst_1057_: *mut crate::leanh::LeanObject,
    mut v_____x_1058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getFileName_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_1059_ = crate::leanh::lean_ctor_get(v_____x_1058_, 0);
                crate::leanh::lean_inc(v_start_1059_);
                v_stop_1060_ = crate::leanh::lean_ctor_get(v_____x_1058_, 1);
                crate::leanh::lean_inc(v_stop_1060_);
                crate::leanh::lean_dec_ref(v_____x_1058_);
                v_source_1061_ = crate::leanh::lean_ctor_get(v_text_1049_, 0);
                crate::leanh::lean_inc_ref(v_source_1061_);
                crate::leanh::lean_dec_ref(v_text_1049_);
                v___x_1067_ = lean_string_utf8_byte_size(v_source_1061_);
                v___x_1068_ = lean_nat_dec_le(v_stop_1060_, v___x_1067_);
                if v___x_1068_ == 0 {
                    crate::leanh::lean_dec(v_stop_1060_);
                    v___y_1063_ = v___x_1067_;
                    state = 1;
                    continue;
                } else {
                    v___y_1063_ = v_stop_1060_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_getFileName_1064_ = crate::leanh::lean_ctor_get(v_inst_1050_, 2);
                crate::leanh::lean_inc(v_getFileName_1064_);
                crate::leanh::lean_dec_ref(v_inst_1050_);
                crate::leanh::lean_inc(v_toBind_1056_);
                v___f_1065_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_parseStrLit___redArg___lam__1 as *mut core::ffi::c_void,
                    11,
                    10,
                );
                crate::leanh::lean_closure_set(v___f_1065_, 0, v_source_1061_);
                crate::leanh::lean_closure_set(v___f_1065_, 1, v___y_1063_);
                crate::leanh::lean_closure_set(v___f_1065_, 2, v_start_1059_);
                crate::leanh::lean_closure_set(v___f_1065_, 3, v_env_1051_);
                crate::leanh::lean_closure_set(v___f_1065_, 4, v_p_1052_);
                crate::leanh::lean_closure_set(v___f_1065_, 5, v_inst_1053_);
                crate::leanh::lean_closure_set(v___f_1065_, 6, v_inst_1054_);
                crate::leanh::lean_closure_set(v___f_1065_, 7, v_toApplicative_1055_);
                crate::leanh::lean_closure_set(v___f_1065_, 8, v_toBind_1056_);
                crate::leanh::lean_closure_set(v___f_1065_, 9, v_inst_1057_);
                v___x_1066_ = crate::leanh::lean_apply_4(
                    v_toBind_1056_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_getFileName_1064_,
                    v___f_1065_,
                );
                return v___x_1066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__3(
    mut v_text_1069_: *mut crate::leanh::LeanObject,
    mut v_inst_1070_: *mut crate::leanh::LeanObject,
    mut v_p_1071_: *mut crate::leanh::LeanObject,
    mut v_inst_1072_: *mut crate::leanh::LeanObject,
    mut v_inst_1073_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1074_: *mut crate::leanh::LeanObject,
    mut v_toBind_1075_: *mut crate::leanh::LeanObject,
    mut v_inst_1076_: *mut crate::leanh::LeanObject,
    mut v_s_1077_: *mut crate::leanh::LeanObject,
    mut v_env_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_1075_);
    crate::leanh::lean_inc_ref(v_inst_1072_);
    v___f_1079_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_1079_, 0, v_text_1069_);
    crate::leanh::lean_closure_set(v___f_1079_, 1, v_inst_1070_);
    crate::leanh::lean_closure_set(v___f_1079_, 2, v_env_1078_);
    crate::leanh::lean_closure_set(v___f_1079_, 3, v_p_1071_);
    crate::leanh::lean_closure_set(v___f_1079_, 4, v_inst_1072_);
    crate::leanh::lean_closure_set(v___f_1079_, 5, v_inst_1073_);
    crate::leanh::lean_closure_set(v___f_1079_, 6, v_toApplicative_1074_);
    crate::leanh::lean_closure_set(v___f_1079_, 7, v_toBind_1075_);
    crate::leanh::lean_closure_set(v___f_1079_, 8, v_inst_1076_);
    v___x_1080_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_1072_,
        v_s_1077_,
    );
    v___x_1081_ = crate::leanh::lean_apply_4(
        v_toBind_1075_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1080_,
        v___f_1079_,
    );
    return v___x_1081_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__3___boxed(
    mut v_text_1082_: *mut crate::leanh::LeanObject,
    mut v_inst_1083_: *mut crate::leanh::LeanObject,
    mut v_p_1084_: *mut crate::leanh::LeanObject,
    mut v_inst_1085_: *mut crate::leanh::LeanObject,
    mut v_inst_1086_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1087_: *mut crate::leanh::LeanObject,
    mut v_toBind_1088_: *mut crate::leanh::LeanObject,
    mut v_inst_1089_: *mut crate::leanh::LeanObject,
    mut v_s_1090_: *mut crate::leanh::LeanObject,
    mut v_env_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Lean_Doc_parseStrLit___redArg___lam__3(
        v_text_1082_,
        v_inst_1083_,
        v_p_1084_,
        v_inst_1085_,
        v_inst_1086_,
        v_toApplicative_1087_,
        v_toBind_1088_,
        v_inst_1089_,
        v_s_1090_,
        v_env_1091_,
    );
    crate::leanh::lean_dec(v_s_1090_);
    return v_res_1092_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__4(
    mut v_inst_1093_: *mut crate::leanh::LeanObject,
    mut v_inst_1094_: *mut crate::leanh::LeanObject,
    mut v_p_1095_: *mut crate::leanh::LeanObject,
    mut v_inst_1096_: *mut crate::leanh::LeanObject,
    mut v_inst_1097_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1098_: *mut crate::leanh::LeanObject,
    mut v_toBind_1099_: *mut crate::leanh::LeanObject,
    mut v_inst_1100_: *mut crate::leanh::LeanObject,
    mut v_s_1101_: *mut crate::leanh::LeanObject,
    mut v_text_1102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getEnv_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getEnv_1103_ = crate::leanh::lean_ctor_get(v_inst_1093_, 0);
    crate::leanh::lean_inc(v_getEnv_1103_);
    crate::leanh::lean_dec_ref(v_inst_1093_);
    crate::leanh::lean_inc(v_toBind_1099_);
    v___f_1104_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__3___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_1104_, 0, v_text_1102_);
    crate::leanh::lean_closure_set(v___f_1104_, 1, v_inst_1094_);
    crate::leanh::lean_closure_set(v___f_1104_, 2, v_p_1095_);
    crate::leanh::lean_closure_set(v___f_1104_, 3, v_inst_1096_);
    crate::leanh::lean_closure_set(v___f_1104_, 4, v_inst_1097_);
    crate::leanh::lean_closure_set(v___f_1104_, 5, v_toApplicative_1098_);
    crate::leanh::lean_closure_set(v___f_1104_, 6, v_toBind_1099_);
    crate::leanh::lean_closure_set(v___f_1104_, 7, v_inst_1100_);
    crate::leanh::lean_closure_set(v___f_1104_, 8, v_s_1101_);
    v___x_1105_ = crate::leanh::lean_apply_4(
        v_toBind_1099_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1103_,
        v___f_1104_,
    );
    return v___x_1105_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg(
    mut v_inst_1106_: *mut crate::leanh::LeanObject,
    mut v_inst_1107_: *mut crate::leanh::LeanObject,
    mut v_inst_1108_: *mut crate::leanh::LeanObject,
    mut v_inst_1109_: *mut crate::leanh::LeanObject,
    mut v_inst_1110_: *mut crate::leanh::LeanObject,
    mut v_inst_1111_: *mut crate::leanh::LeanObject,
    mut v_p_1112_: *mut crate::leanh::LeanObject,
    mut v_s_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1114_ = crate::leanh::lean_ctor_get(v_inst_1106_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1114_);
    v_toBind_1115_ = crate::leanh::lean_ctor_get(v_inst_1106_, 1);
    crate::leanh::lean_inc_n(v_toBind_1115_, 2);
    v___f_1116_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__4 as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_1116_, 0, v_inst_1108_);
    crate::leanh::lean_closure_set(v___f_1116_, 1, v_inst_1110_);
    crate::leanh::lean_closure_set(v___f_1116_, 2, v_p_1112_);
    crate::leanh::lean_closure_set(v___f_1116_, 3, v_inst_1106_);
    crate::leanh::lean_closure_set(v___f_1116_, 4, v_inst_1109_);
    crate::leanh::lean_closure_set(v___f_1116_, 5, v_toApplicative_1114_);
    crate::leanh::lean_closure_set(v___f_1116_, 6, v_toBind_1115_);
    crate::leanh::lean_closure_set(v___f_1116_, 7, v_inst_1111_);
    crate::leanh::lean_closure_set(v___f_1116_, 8, v_s_1113_);
    v___x_1117_ = crate::leanh::lean_apply_4(
        v_toBind_1115_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1107_,
        v___f_1116_,
    );
    return v___x_1117_;
}
pub unsafe fn l_Lean_Doc_parseStrLit(
    mut v_m_1118_: *mut crate::leanh::LeanObject,
    mut v_inst_1119_: *mut crate::leanh::LeanObject,
    mut v_inst_1120_: *mut crate::leanh::LeanObject,
    mut v_inst_1121_: *mut crate::leanh::LeanObject,
    mut v_inst_1122_: *mut crate::leanh::LeanObject,
    mut v_inst_1123_: *mut crate::leanh::LeanObject,
    mut v_inst_1124_: *mut crate::leanh::LeanObject,
    mut v_p_1125_: *mut crate::leanh::LeanObject,
    mut v_s_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = l_Lean_Doc_parseStrLit___redArg(
        v_inst_1119_,
        v_inst_1120_,
        v_inst_1121_,
        v_inst_1122_,
        v_inst_1123_,
        v_inst_1124_,
        v_p_1125_,
        v_s_1126_,
    );
    return v___x_1127_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(
    mut v_str_1128_: *mut crate::leanh::LeanObject,
    mut v_a_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1130_ = crate::leanh::lean_ctor_get(v_a_1129_, 0);
                v_snd_1131_ = crate::leanh::lean_ctor_get(v_a_1129_, 1);
                v_isSharedCheck_1147_ = (!crate::leanh::lean_is_exclusive(v_a_1129_)) as u8;
                if v_isSharedCheck_1147_ == 0 {
                    v___x_1133_ = v_a_1129_;
                    v_isShared_1134_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1131_);
                    crate::leanh::lean_inc(v_fst_1130_);
                    crate::leanh::lean_dec(v_a_1129_);
                    v___x_1133_ = crate::leanh::lean_box(0);
                    v_isShared_1134_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1135_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1136_ = lean_nat_dec_lt(v___x_1135_, v_fst_1130_);
                if v___x_1136_ == 0 {
                    if v_isShared_1134_ == 0 {
                        v___x_1138_ = v___x_1133_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1139_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_fst_1130_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_snd_1131_);
                        v___x_1138_ = v_reuseFailAlloc_1139_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1140_ = lean_string_utf8_prev(v_str_1128_, v_fst_1130_);
                    crate::leanh::lean_dec(v_fst_1130_);
                    v___x_1141_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1142_ = lean_nat_add(v_snd_1131_, v___x_1141_);
                    crate::leanh::lean_dec(v_snd_1131_);
                    if v_isShared_1134_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1133_, 1, v___x_1142_);
                        crate::leanh::lean_ctor_set(v___x_1133_, 0, v___x_1140_);
                        v___x_1144_ = v___x_1133_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1146_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1140_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1142_);
                        v___x_1144_ = v_reuseFailAlloc_1146_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1138_;
            }
            3 => {
                v_a_1129_ = v___x_1144_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg___boxed(
    mut v_str_1148_: *mut crate::leanh::LeanObject,
    mut v_a_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1150_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_1148_, v_a_1149_);
    crate::leanh::lean_dec_ref(v_str_1148_);
    return v_res_1150_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(
    mut v_str_1151_: *mut crate::leanh::LeanObject,
    mut v_p_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_1153_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1154_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1154_, 0, v_p_1152_);
    crate::leanh::lean_ctor_set(v___x_1154_, 1, v_n_1153_);
    v___x_1155_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_1151_, v___x_1154_);
    v_snd_1156_ = crate::leanh::lean_ctor_get(v___x_1155_, 1);
    crate::leanh::lean_inc(v_snd_1156_);
    crate::leanh::lean_dec_ref(v___x_1155_);
    return v_snd_1156_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(
    mut v_str_1157_: *mut crate::leanh::LeanObject,
    mut v_p_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1159_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(
            v_str_1157_,
            v_p_1158_,
        );
    crate::leanh::lean_dec_ref(v_str_1157_);
    return v_res_1159_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(
    mut v_str_1160_: *mut crate::leanh::LeanObject,
    mut v_inst_1161_: *mut crate::leanh::LeanObject,
    mut v_a_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1163_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_1160_, v_a_1162_);
    return v___x_1163_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(
    mut v_str_1164_: *mut crate::leanh::LeanObject,
    mut v_inst_1165_: *mut crate::leanh::LeanObject,
    mut v_a_1166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1167_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(v_str_1164_, v_inst_1165_, v_a_1166_);
    crate::leanh::lean_dec_ref(v_str_1164_);
    return v_res_1167_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(
    mut v_str_1168_: *mut crate::leanh::LeanObject,
    mut v_p_1169_: *mut crate::leanh::LeanObject,
    mut v_j_1170_: *mut crate::leanh::LeanObject,
    mut v_a_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1173_: u8 = 0;
    let mut v_one_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1172_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1173_ = lean_nat_dec_eq(v_j_1170_, v_zero_1172_);
                if v_isZero_1173_ == 1 {
                    crate::leanh::lean_dec(v_j_1170_);
                    return v_a_1171_;
                } else {
                    crate::leanh::lean_dec(v_a_1171_);
                    v_one_1174_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1175_ = lean_nat_sub(v_j_1170_, v_one_1174_);
                    crate::leanh::lean_dec(v_j_1170_);
                    v___x_1176_ = lean_string_utf8_next(v_str_1168_, v_p_1169_);
                    v_j_1170_ = v_n_1175_;
                    v_a_1171_ = v___x_1176_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg___boxed(
    mut v_str_1178_: *mut crate::leanh::LeanObject,
    mut v_p_1179_: *mut crate::leanh::LeanObject,
    mut v_j_1180_: *mut crate::leanh::LeanObject,
    mut v_a_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1182_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_1178_, v_p_1179_, v_j_1180_, v_a_1181_);
    crate::leanh::lean_dec(v_p_1179_);
    crate::leanh::lean_dec_ref(v_str_1178_);
    return v_res_1182_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(
    mut v_str_1183_: *mut crate::leanh::LeanObject,
    mut v_n_1184_: *mut crate::leanh::LeanObject,
    mut v_p_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_p_1185_);
    v___x_1186_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_1183_, v_p_1185_, v_n_1184_, v_p_1185_);
    crate::leanh::lean_dec(v_p_1185_);
    return v___x_1186_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(
    mut v_str_1187_: *mut crate::leanh::LeanObject,
    mut v_n_1188_: *mut crate::leanh::LeanObject,
    mut v_p_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1190_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(
            v_str_1187_,
            v_n_1188_,
            v_p_1189_,
        );
    crate::leanh::lean_dec_ref(v_str_1187_);
    return v_res_1190_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(
    mut v_str_1191_: *mut crate::leanh::LeanObject,
    mut v_p_1192_: *mut crate::leanh::LeanObject,
    mut v_n_1193_: *mut crate::leanh::LeanObject,
    mut v_j_1194_: *mut crate::leanh::LeanObject,
    mut v_a_1195_: *mut crate::leanh::LeanObject,
    mut v_a_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_1191_, v_p_1192_, v_j_1194_, v_a_1196_);
    return v___x_1197_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(
    mut v_str_1198_: *mut crate::leanh::LeanObject,
    mut v_p_1199_: *mut crate::leanh::LeanObject,
    mut v_n_1200_: *mut crate::leanh::LeanObject,
    mut v_j_1201_: *mut crate::leanh::LeanObject,
    mut v_a_1202_: *mut crate::leanh::LeanObject,
    mut v_a_1203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1204_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(v_str_1198_, v_p_1199_, v_n_1200_, v_j_1201_, v_a_1202_, v_a_1203_);
    crate::leanh::lean_dec(v_n_1200_);
    crate::leanh::lean_dec(v_p_1199_);
    crate::leanh::lean_dec_ref(v_str_1198_);
    return v_res_1204_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(
    mut v_text_1205_: *mut crate::leanh::LeanObject,
    mut v_posOfStr_1206_: *mut crate::leanh::LeanObject,
    mut v_str_1207_: *mut crate::leanh::LeanObject,
    mut v_posInStr_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_source_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_source_1209_ = crate::leanh::lean_ctor_get(v_text_1205_, 0);
    v___x_1210_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(
            v_str_1207_,
            v_posInStr_1208_,
        );
    crate::leanh::lean_inc(v_posOfStr_1206_);
    v___x_1211_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_source_1209_, v_posOfStr_1206_, v___x_1210_, v_posOfStr_1206_);
    crate::leanh::lean_dec(v_posOfStr_1206_);
    return v___x_1211_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(
    mut v_text_1212_: *mut crate::leanh::LeanObject,
    mut v_posOfStr_1213_: *mut crate::leanh::LeanObject,
    mut v_str_1214_: *mut crate::leanh::LeanObject,
    mut v_posInStr_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1216_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(
            v_text_1212_,
            v_posOfStr_1213_,
            v_str_1214_,
            v_posInStr_1215_,
        );
    crate::leanh::lean_dec_ref(v_str_1214_);
    crate::leanh::lean_dec_ref(v_text_1212_);
    return v_res_1216_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(
    mut v_text_1217_: *mut crate::leanh::LeanObject,
    mut v_posOfStr_1218_: *mut crate::leanh::LeanObject,
    mut v_str_1219_: *mut crate::leanh::LeanObject,
    mut v_a_1220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: u8 = 0;
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canonical_1229_: u8 = 0;
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1238_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_1220_) {
                0 => {
                    v_pos_1221_ = crate::leanh::lean_ctor_get(v_a_1220_, 1);
                    crate::leanh::lean_inc(v_pos_1221_);
                    v_endPos_1222_ = crate::leanh::lean_ctor_get(v_a_1220_, 3);
                    crate::leanh::lean_inc(v_endPos_1222_);
                    crate::leanh::lean_dec_ref_known(v_a_1220_, 4);
                    crate::leanh::lean_inc(v_posOfStr_1218_);
                    v___x_1223_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_pos_1221_);
                    v___x_1224_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_endPos_1222_);
                    v___x_1225_ = 1;
                    v___x_1226_ = crate::leanh::lean_alloc_ctor(1, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1226_, 0, v___x_1223_);
                    crate::leanh::lean_ctor_set(v___x_1226_, 1, v___x_1224_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1226_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_1225_,
                    );
                    return v___x_1226_;
                }
                1 => {
                    v_pos_1227_ = crate::leanh::lean_ctor_get(v_a_1220_, 0);
                    v_endPos_1228_ = crate::leanh::lean_ctor_get(v_a_1220_, 1);
                    v_canonical_1229_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_1220_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_isSharedCheck_1238_ = (!crate::leanh::lean_is_exclusive(v_a_1220_)) as u8;
                    if v_isSharedCheck_1238_ == 0 {
                        v___x_1231_ = v_a_1220_;
                        v_isShared_1232_ = v_isSharedCheck_1238_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endPos_1228_);
                        crate::leanh::lean_inc(v_pos_1227_);
                        crate::leanh::lean_dec(v_a_1220_);
                        v___x_1231_ = crate::leanh::lean_box(0);
                        v_isShared_1232_ = v_isSharedCheck_1238_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_posOfStr_1218_);
                    return v_a_1220_;
                }
            },
            1 => {
                crate::leanh::lean_inc(v_posOfStr_1218_);
                v___x_1233_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_pos_1227_);
                v___x_1234_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_endPos_1228_);
                if v_isShared_1232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1231_, 1, v___x_1234_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1233_);
                    v___x_1236_ = v___x_1231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1237_ = crate::leanh::lean_alloc_ctor(1, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1233_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1234_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1237_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_canonical_1229_,
                    );
                    v___x_1236_ = v_reuseFailAlloc_1237_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo___boxed(
    mut v_text_1239_: *mut crate::leanh::LeanObject,
    mut v_posOfStr_1240_: *mut crate::leanh::LeanObject,
    mut v_str_1241_: *mut crate::leanh::LeanObject,
    mut v_a_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_1239_, v_posOfStr_1240_, v_str_1241_, v_a_1242_);
    crate::leanh::lean_dec_ref(v_str_1241_);
    crate::leanh::lean_dec_ref(v_text_1239_);
    return v_res_1243_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(
    mut v_text_1244_: *mut crate::leanh::LeanObject,
    mut v_posOfStr_1245_: *mut crate::leanh::LeanObject,
    mut v_str_1246_: *mut crate::leanh::LeanObject,
    mut v_a_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1253_: u8 = 0;
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1255_: usize = 0;
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1261_: u8 = 0;
    let mut v_info_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1266_: u8 = 0;
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_info_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1278_: u8 = 0;
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_1247_) {
                0 => {
                    crate::leanh::lean_dec(v_posOfStr_1245_);
                    return v_a_1247_;
                }
                1 => {
                    v_info_1248_ = crate::leanh::lean_ctor_get(v_a_1247_, 0);
                    v_kind_1249_ = crate::leanh::lean_ctor_get(v_a_1247_, 1);
                    v_args_1250_ = crate::leanh::lean_ctor_get(v_a_1247_, 2);
                    v_isSharedCheck_1261_ = (!crate::leanh::lean_is_exclusive(v_a_1247_)) as u8;
                    if v_isSharedCheck_1261_ == 0 {
                        v___x_1252_ = v_a_1247_;
                        v_isShared_1253_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_1250_);
                        crate::leanh::lean_inc(v_kind_1249_);
                        crate::leanh::lean_inc(v_info_1248_);
                        crate::leanh::lean_dec(v_a_1247_);
                        v___x_1252_ = crate::leanh::lean_box(0);
                        v_isShared_1253_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_info_1262_ = crate::leanh::lean_ctor_get(v_a_1247_, 0);
                    v_val_1263_ = crate::leanh::lean_ctor_get(v_a_1247_, 1);
                    v_isSharedCheck_1271_ = (!crate::leanh::lean_is_exclusive(v_a_1247_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v___x_1265_ = v_a_1247_;
                        v_isShared_1266_ = v_isSharedCheck_1271_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1263_);
                        crate::leanh::lean_inc(v_info_1262_);
                        crate::leanh::lean_dec(v_a_1247_);
                        v___x_1265_ = crate::leanh::lean_box(0);
                        v_isShared_1266_ = v_isSharedCheck_1271_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_info_1272_ = crate::leanh::lean_ctor_get(v_a_1247_, 0);
                    v_rawVal_1273_ = crate::leanh::lean_ctor_get(v_a_1247_, 1);
                    v_val_1274_ = crate::leanh::lean_ctor_get(v_a_1247_, 2);
                    v_preresolved_1275_ = crate::leanh::lean_ctor_get(v_a_1247_, 3);
                    v_isSharedCheck_1283_ = (!crate::leanh::lean_is_exclusive(v_a_1247_)) as u8;
                    if v_isSharedCheck_1283_ == 0 {
                        v___x_1277_ = v_a_1247_;
                        v_isShared_1278_ = v_isSharedCheck_1283_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_preresolved_1275_);
                        crate::leanh::lean_inc(v_val_1274_);
                        crate::leanh::lean_inc(v_rawVal_1273_);
                        crate::leanh::lean_inc(v_info_1272_);
                        crate::leanh::lean_dec(v_a_1247_);
                        v___x_1277_ = crate::leanh::lean_box(0);
                        v_isShared_1278_ = v_isSharedCheck_1283_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                crate::leanh::lean_inc(v_posOfStr_1245_);
                v___x_1254_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_1244_, v_posOfStr_1245_, v_str_1246_, v_info_1248_);
                v_sz_1255_ = lean_array_size(v_args_1250_);
                v___x_1256_ = 0usize;
                v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_1244_, v_posOfStr_1245_, v_str_1246_, v_sz_1255_, v___x_1256_, v_args_1250_);
                if v_isShared_1253_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1252_, 2, v___x_1257_);
                    crate::leanh::lean_ctor_set(v___x_1252_, 0, v___x_1254_);
                    v___x_1259_ = v___x_1252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1260_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_kind_1249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 2, v___x_1257_);
                    v___x_1259_ = v_reuseFailAlloc_1260_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1259_;
            }
            3 => {
                v___x_1267_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_1244_, v_posOfStr_1245_, v_str_1246_, v_info_1262_);
                if v_isShared_1266_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1265_, 0, v___x_1267_);
                    v___x_1269_ = v___x_1265_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_val_1263_);
                    v___x_1269_ = v_reuseFailAlloc_1270_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1269_;
            }
            5 => {
                v___x_1279_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_1244_, v_posOfStr_1245_, v_str_1246_, v_info_1272_);
                if v_isShared_1278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1277_, 0, v___x_1279_);
                    v___x_1281_ = v___x_1277_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1282_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_rawVal_1273_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_val_1274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_preresolved_1275_);
                    v___x_1281_ = v_reuseFailAlloc_1282_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(
    mut v_text_1284_: *mut crate::leanh::LeanObject,
    mut v_posOfStr_1285_: *mut crate::leanh::LeanObject,
    mut v_str_1286_: *mut crate::leanh::LeanObject,
    mut v_sz_1287_: usize,
    mut v_i_1288_: usize,
    mut v_bs_1289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1290_: u8 = 0;
    let mut v_v_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: usize = 0;
    let mut v___x_1296_: usize = 0;
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1290_ = lean_usize_dec_lt(v_i_1288_, v_sz_1287_);
                if v___x_1290_ == 0 {
                    crate::leanh::lean_dec(v_posOfStr_1285_);
                    return v_bs_1289_;
                } else {
                    v_v_1291_ = lean_array_uget(v_bs_1289_, v_i_1288_);
                    v___x_1292_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1293_ = lean_array_uset(v_bs_1289_, v_i_1288_, v___x_1292_);
                    crate::leanh::lean_inc(v_posOfStr_1285_);
                    v___x_1294_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_1284_, v_posOfStr_1285_, v_str_1286_, v_v_1291_);
                    v___x_1295_ = 1usize;
                    v___x_1296_ = lean_usize_add(v_i_1288_, v___x_1295_);
                    v___x_1297_ = lean_array_uset(v_bs_x27_1293_, v_i_1288_, v___x_1294_);
                    v_i_1288_ = v___x_1296_;
                    v_bs_1289_ = v___x_1297_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0___boxed(
    mut v_text_1299_: *mut crate::leanh::LeanObject,
    mut v_posOfStr_1300_: *mut crate::leanh::LeanObject,
    mut v_str_1301_: *mut crate::leanh::LeanObject,
    mut v_sz_1302_: *mut crate::leanh::LeanObject,
    mut v_i_1303_: *mut crate::leanh::LeanObject,
    mut v_bs_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1305_: usize = 0;
    let mut v_i_boxed_1306_: usize = 0;
    let mut v_res_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1305_ = crate::leanh::lean_unbox_usize(v_sz_1302_);
    crate::leanh::lean_dec(v_sz_1302_);
    v_i_boxed_1306_ = crate::leanh::lean_unbox_usize(v_i_1303_);
    crate::leanh::lean_dec(v_i_1303_);
    v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_1299_, v_posOfStr_1300_, v_str_1301_, v_sz_boxed_1305_, v_i_boxed_1306_, v_bs_1304_);
    crate::leanh::lean_dec_ref(v_str_1301_);
    crate::leanh::lean_dec_ref(v_text_1299_);
    return v_res_1307_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(
    mut v_text_1308_: *mut crate::leanh::LeanObject,
    mut v_posOfStr_1309_: *mut crate::leanh::LeanObject,
    mut v_str_1310_: *mut crate::leanh::LeanObject,
    mut v_a_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1312_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_1308_, v_posOfStr_1309_, v_str_1310_, v_a_1311_);
    crate::leanh::lean_dec_ref(v_str_1310_);
    crate::leanh::lean_dec_ref(v_text_1308_);
    return v_res_1312_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(
    mut v_x_1313_: *mut crate::leanh::LeanObject,
    mut v_h__1_1314_: *mut crate::leanh::LeanObject,
    mut v_h__2_1315_: *mut crate::leanh::LeanObject,
    mut v_h__3_1316_: *mut crate::leanh::LeanObject,
    mut v_h__4_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1313_) {
        0 => {
            let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1316_);
            crate::leanh::lean_dec(v_h__2_1315_);
            crate::leanh::lean_dec(v_h__1_1314_);
            v___x_1318_ = crate::leanh::lean_box(0);
            v___x_1319_ = crate::leanh::lean_apply_1(v_h__4_1317_, v___x_1318_);
            return v___x_1319_;
        }
        1 => {
            let mut v_info_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_kind_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_args_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1317_);
            crate::leanh::lean_dec(v_h__3_1316_);
            crate::leanh::lean_dec(v_h__2_1315_);
            v_info_1320_ = crate::leanh::lean_ctor_get(v_x_1313_, 0);
            crate::leanh::lean_inc(v_info_1320_);
            v_kind_1321_ = crate::leanh::lean_ctor_get(v_x_1313_, 1);
            crate::leanh::lean_inc(v_kind_1321_);
            v_args_1322_ = crate::leanh::lean_ctor_get(v_x_1313_, 2);
            crate::leanh::lean_inc_ref(v_args_1322_);
            crate::leanh::lean_dec_ref_known(v_x_1313_, 3);
            v___x_1323_ =
                crate::leanh::lean_apply_3(v_h__1_1314_, v_info_1320_, v_kind_1321_, v_args_1322_);
            return v___x_1323_;
        }
        2 => {
            let mut v_info_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1317_);
            crate::leanh::lean_dec(v_h__2_1315_);
            crate::leanh::lean_dec(v_h__1_1314_);
            v_info_1324_ = crate::leanh::lean_ctor_get(v_x_1313_, 0);
            crate::leanh::lean_inc(v_info_1324_);
            v_val_1325_ = crate::leanh::lean_ctor_get(v_x_1313_, 1);
            crate::leanh::lean_inc_ref(v_val_1325_);
            crate::leanh::lean_dec_ref_known(v_x_1313_, 2);
            v___x_1326_ = crate::leanh::lean_apply_2(v_h__3_1316_, v_info_1324_, v_val_1325_);
            return v___x_1326_;
        }
        _ => {
            let mut v_info_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rawVal_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_preresolved_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1317_);
            crate::leanh::lean_dec(v_h__3_1316_);
            crate::leanh::lean_dec(v_h__1_1314_);
            v_info_1327_ = crate::leanh::lean_ctor_get(v_x_1313_, 0);
            crate::leanh::lean_inc(v_info_1327_);
            v_rawVal_1328_ = crate::leanh::lean_ctor_get(v_x_1313_, 1);
            crate::leanh::lean_inc_ref(v_rawVal_1328_);
            v_val_1329_ = crate::leanh::lean_ctor_get(v_x_1313_, 2);
            crate::leanh::lean_inc(v_val_1329_);
            v_preresolved_1330_ = crate::leanh::lean_ctor_get(v_x_1313_, 3);
            crate::leanh::lean_inc(v_preresolved_1330_);
            crate::leanh::lean_dec_ref_known(v_x_1313_, 4);
            v___x_1331_ = crate::leanh::lean_apply_4(
                v_h__2_1315_,
                v_info_1327_,
                v_rawVal_1328_,
                v_val_1329_,
                v_preresolved_1330_,
            );
            return v___x_1331_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter(
    mut v_motive_1332_: *mut crate::leanh::LeanObject,
    mut v_x_1333_: *mut crate::leanh::LeanObject,
    mut v_h__1_1334_: *mut crate::leanh::LeanObject,
    mut v_h__2_1335_: *mut crate::leanh::LeanObject,
    mut v_h__3_1336_: *mut crate::leanh::LeanObject,
    mut v_h__4_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1333_) {
        0 => {
            let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1336_);
            crate::leanh::lean_dec(v_h__2_1335_);
            crate::leanh::lean_dec(v_h__1_1334_);
            v___x_1338_ = crate::leanh::lean_box(0);
            v___x_1339_ = crate::leanh::lean_apply_1(v_h__4_1337_, v___x_1338_);
            return v___x_1339_;
        }
        1 => {
            let mut v_info_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_kind_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_args_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1337_);
            crate::leanh::lean_dec(v_h__3_1336_);
            crate::leanh::lean_dec(v_h__2_1335_);
            v_info_1340_ = crate::leanh::lean_ctor_get(v_x_1333_, 0);
            crate::leanh::lean_inc(v_info_1340_);
            v_kind_1341_ = crate::leanh::lean_ctor_get(v_x_1333_, 1);
            crate::leanh::lean_inc(v_kind_1341_);
            v_args_1342_ = crate::leanh::lean_ctor_get(v_x_1333_, 2);
            crate::leanh::lean_inc_ref(v_args_1342_);
            crate::leanh::lean_dec_ref_known(v_x_1333_, 3);
            v___x_1343_ =
                crate::leanh::lean_apply_3(v_h__1_1334_, v_info_1340_, v_kind_1341_, v_args_1342_);
            return v___x_1343_;
        }
        2 => {
            let mut v_info_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1337_);
            crate::leanh::lean_dec(v_h__2_1335_);
            crate::leanh::lean_dec(v_h__1_1334_);
            v_info_1344_ = crate::leanh::lean_ctor_get(v_x_1333_, 0);
            crate::leanh::lean_inc(v_info_1344_);
            v_val_1345_ = crate::leanh::lean_ctor_get(v_x_1333_, 1);
            crate::leanh::lean_inc_ref(v_val_1345_);
            crate::leanh::lean_dec_ref_known(v_x_1333_, 2);
            v___x_1346_ = crate::leanh::lean_apply_2(v_h__3_1336_, v_info_1344_, v_val_1345_);
            return v___x_1346_;
        }
        _ => {
            let mut v_info_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_rawVal_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_preresolved_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1337_);
            crate::leanh::lean_dec(v_h__3_1336_);
            crate::leanh::lean_dec(v_h__1_1334_);
            v_info_1347_ = crate::leanh::lean_ctor_get(v_x_1333_, 0);
            crate::leanh::lean_inc(v_info_1347_);
            v_rawVal_1348_ = crate::leanh::lean_ctor_get(v_x_1333_, 1);
            crate::leanh::lean_inc_ref(v_rawVal_1348_);
            v_val_1349_ = crate::leanh::lean_ctor_get(v_x_1333_, 2);
            crate::leanh::lean_inc(v_val_1349_);
            v_preresolved_1350_ = crate::leanh::lean_ctor_get(v_x_1333_, 3);
            crate::leanh::lean_inc(v_preresolved_1350_);
            crate::leanh::lean_dec_ref_known(v_x_1333_, 4);
            v___x_1351_ = crate::leanh::lean_apply_4(
                v_h__2_1335_,
                v_info_1347_,
                v_rawVal_1348_,
                v_val_1349_,
                v_preresolved_1350_,
            );
            return v___x_1351_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter___redArg(
    mut v_x_1352_: *mut crate::leanh::LeanObject,
    mut v_h__1_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1354_ = crate::leanh::lean_apply_2(v_h__1_1353_, v_x_1352_, crate::leanh::lean_box(0));
    return v___x_1354_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(
    mut v_00_u03b1_1355_: *mut crate::leanh::LeanObject,
    mut v_P_1356_: *mut crate::leanh::LeanObject,
    mut v_motive_1357_: *mut crate::leanh::LeanObject,
    mut v_x_1358_: *mut crate::leanh::LeanObject,
    mut v_h__1_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = crate::leanh::lean_apply_2(v_h__1_1359_, v_x_1358_, crate::leanh::lean_box(0));
    return v___x_1360_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(
    mut v_text_1361_: *mut crate::leanh::LeanObject,
    mut v_pos_1362_: *mut crate::leanh::LeanObject,
    mut v_str_1363_: *mut crate::leanh::LeanObject,
    mut v_x_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1365_ = crate::leanh::lean_ctor_get(v_x_1364_, 0);
                v_snd_1366_ = crate::leanh::lean_ctor_get(v_x_1364_, 1);
                v_isSharedCheck_1374_ = (!crate::leanh::lean_is_exclusive(v_x_1364_)) as u8;
                if v_isSharedCheck_1374_ == 0 {
                    v___x_1368_ = v_x_1364_;
                    v_isShared_1369_ = v_isSharedCheck_1374_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1366_);
                    crate::leanh::lean_inc(v_fst_1365_);
                    crate::leanh::lean_dec(v_x_1364_);
                    v___x_1368_ = crate::leanh::lean_box(0);
                    v_isShared_1369_ = v_isSharedCheck_1374_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1370_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1361_, v_pos_1362_, v_str_1363_, v_fst_1365_);
                if v_isShared_1369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1368_, 0, v___x_1370_);
                    v___x_1372_ = v___x_1368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1373_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_snd_1366_);
                    v___x_1372_ = v_reuseFailAlloc_1373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed(
    mut v_text_1375_: *mut crate::leanh::LeanObject,
    mut v_pos_1376_: *mut crate::leanh::LeanObject,
    mut v_str_1377_: *mut crate::leanh::LeanObject,
    mut v_x_1378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(
        v_text_1375_,
        v_pos_1376_,
        v_str_1377_,
        v_x_1378_,
    );
    crate::leanh::lean_dec_ref(v_str_1377_);
    crate::leanh::lean_dec_ref(v_text_1375_);
    return v_res_1379_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(
    mut v_env_1399_: *mut crate::leanh::LeanObject,
    mut v_p_1400_: *mut crate::leanh::LeanObject,
    mut v_ictx_1401_: *mut crate::leanh::LeanObject,
    mut v_s_1402_: *mut crate::leanh::LeanObject,
    mut v_text_1403_: *mut crate::leanh::LeanObject,
    mut v_pos_1404_: *mut crate::leanh::LeanObject,
    mut v_str_1405_: *mut crate::leanh::LeanObject,
    mut v___f_1406_: *mut crate::leanh::LeanObject,
    mut v_inst_1407_: *mut crate::leanh::LeanObject,
    mut v_inst_1408_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1409_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: u8 = 0;
    let mut v_stxStack_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1428_: u8 = 0;
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1433_: usize = 0;
    let mut v___x_1434_: usize = 0;
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1446_: u8 = 0;
    let mut v_unexpectedTk_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unexpected_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1460_: u8 = 0;
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut v_stxStack_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1411_ = crate::leanh::lean_box(0);
                v___x_1412_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_env_1399_);
                v___x_1413_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1413_, 0, v_env_1399_);
                crate::leanh::lean_ctor_set(v___x_1413_, 1, v_____do__lift_1410_);
                crate::leanh::lean_ctor_set(v___x_1413_, 2, v___x_1411_);
                crate::leanh::lean_ctor_set(v___x_1413_, 3, v___x_1412_);
                v___x_1414_ = l_Lean_Parser_getTokenTable(v_env_1399_);
                crate::leanh::lean_inc_ref(v_ictx_1401_);
                v_s_1415_ = l_Lean_Parser_ParserFn_run(
                    v_p_1400_,
                    v_ictx_1401_,
                    v___x_1413_,
                    v___x_1414_,
                    v_s_1402_,
                );
                crate::leanh::lean_inc_ref(v_s_1415_);
                v___x_1416_ = l_Lean_Parser_ParserState_allErrors(v_s_1415_);
                v___x_1417_ = lean_array_get_size(v___x_1416_);
                crate::leanh::lean_dec_ref(v___x_1416_);
                v___x_1418_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1419_ = lean_nat_dec_eq(v___x_1417_, v___x_1418_);
                if v___x_1419_ == 0 {
                    crate::leanh::lean_dec_ref(v_toApplicative_1409_);
                    v_stxStack_1420_ = crate::leanh::lean_ctor_get(v_s_1415_, 0);
                    v_lhsPrec_1421_ = crate::leanh::lean_ctor_get(v_s_1415_, 1);
                    v_pos_1422_ = crate::leanh::lean_ctor_get(v_s_1415_, 2);
                    v_cache_1423_ = crate::leanh::lean_ctor_get(v_s_1415_, 3);
                    v_errorMsg_1424_ = crate::leanh::lean_ctor_get(v_s_1415_, 4);
                    v_recoveredErrors_1425_ = crate::leanh::lean_ctor_get(v_s_1415_, 5);
                    v_isSharedCheck_1462_ = (!crate::leanh::lean_is_exclusive(v_s_1415_)) as u8;
                    if v_isSharedCheck_1462_ == 0 {
                        v___x_1427_ = v_s_1415_;
                        v_isShared_1428_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_recoveredErrors_1425_);
                        crate::leanh::lean_inc(v_errorMsg_1424_);
                        crate::leanh::lean_inc(v_cache_1423_);
                        crate::leanh::lean_inc(v_pos_1422_);
                        crate::leanh::lean_inc(v_lhsPrec_1421_);
                        crate::leanh::lean_inc(v_stxStack_1420_);
                        crate::leanh::lean_dec(v_s_1415_);
                        v___x_1427_ = crate::leanh::lean_box(0);
                        v_isShared_1428_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_1406_);
                    v_stxStack_1463_ = crate::leanh::lean_ctor_get(v_s_1415_, 0);
                    crate::leanh::lean_inc_ref(v_stxStack_1463_);
                    v_pos_1464_ = crate::leanh::lean_ctor_get(v_s_1415_, 2);
                    crate::leanh::lean_inc(v_pos_1464_);
                    v___x_1465_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1401_, v_pos_1464_);
                    crate::leanh::lean_dec(v_pos_1464_);
                    if v___x_1465_ == 0 {
                        crate::leanh::lean_dec_ref(v_stxStack_1463_);
                        crate::leanh::lean_dec_ref(v_toApplicative_1409_);
                        crate::leanh::lean_dec(v_pos_1404_);
                        v___x_1466_ = l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0;
                        v___x_1467_ = l_Lean_Parser_ParserState_mkError(v_s_1415_, v___x_1466_);
                        v___x_1468_ =
                            l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1401_, v___x_1467_);
                        v___x_1469_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1469_, 0, v___x_1468_);
                        v___x_1470_ = l_Lean_MessageData_ofFormat(v___x_1469_);
                        v___x_1471_ =
                            l_Lean_throwError___redArg(v_inst_1407_, v_inst_1408_, v___x_1470_);
                        return v___x_1471_;
                    } else {
                        crate::leanh::lean_dec_ref(v_s_1415_);
                        crate::leanh::lean_dec_ref(v_inst_1408_);
                        crate::leanh::lean_dec_ref(v_inst_1407_);
                        crate::leanh::lean_dec_ref(v_ictx_1401_);
                        v_toPure_1472_ = crate::leanh::lean_ctor_get(v_toApplicative_1409_, 1);
                        crate::leanh::lean_inc(v_toPure_1472_);
                        crate::leanh::lean_dec_ref(v_toApplicative_1409_);
                        v___x_1473_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1463_);
                        crate::leanh::lean_dec_ref(v_stxStack_1463_);
                        v___x_1474_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_1403_, v_pos_1404_, v_str_1405_, v___x_1473_);
                        v___x_1475_ = crate::leanh::lean_apply_2(
                            v_toPure_1472_,
                            crate::leanh::lean_box(0),
                            v___x_1474_,
                        );
                        return v___x_1475_;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_pos_1404_);
                v___x_1429_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1403_, v_pos_1404_, v_str_1405_, v_pos_1422_);
                if crate::leanh::lean_obj_tag(v_errorMsg_1424_) == 0 {
                    crate::leanh::lean_dec(v_pos_1404_);
                    v___y_1431_ = v_errorMsg_1424_;
                    state = 2;
                    continue;
                } else {
                    v_val_1443_ = crate::leanh::lean_ctor_get(v_errorMsg_1424_, 0);
                    v_isSharedCheck_1461_ =
                        (!crate::leanh::lean_is_exclusive(v_errorMsg_1424_)) as u8;
                    if v_isSharedCheck_1461_ == 0 {
                        v___x_1445_ = v_errorMsg_1424_;
                        v_isShared_1446_ = v_isSharedCheck_1461_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1443_);
                        crate::leanh::lean_dec(v_errorMsg_1424_);
                        v___x_1445_ = crate::leanh::lean_box(0);
                        v_isShared_1446_ = v_isSharedCheck_1461_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1432_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9;
                v_sz_1433_ = lean_array_size(v_recoveredErrors_1425_);
                v___x_1434_ = 0usize;
                v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1432_,
                    v___f_1406_,
                    v_sz_1433_,
                    v___x_1434_,
                    v_recoveredErrors_1425_,
                );
                if v_isShared_1428_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1427_, 5, v___x_1435_);
                    crate::leanh::lean_ctor_set(v___x_1427_, 4, v___y_1431_);
                    crate::leanh::lean_ctor_set(v___x_1427_, 2, v___x_1429_);
                    v_s_1437_ = v___x_1427_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_stxStack_1420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_lhsPrec_1421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 2, v___x_1429_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_cache_1423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 4, v___y_1431_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 5, v___x_1435_);
                    v_s_1437_ = v_reuseFailAlloc_1442_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1438_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1401_, v_s_1437_);
                v___x_1439_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1439_, 0, v___x_1438_);
                v___x_1440_ = l_Lean_MessageData_ofFormat(v___x_1439_);
                v___x_1441_ = l_Lean_throwError___redArg(v_inst_1407_, v_inst_1408_, v___x_1440_);
                return v___x_1441_;
            }
            4 => {
                v_unexpectedTk_1447_ = crate::leanh::lean_ctor_get(v_val_1443_, 0);
                v_unexpected_1448_ = crate::leanh::lean_ctor_get(v_val_1443_, 1);
                v_expected_1449_ = crate::leanh::lean_ctor_get(v_val_1443_, 2);
                v_isSharedCheck_1460_ = (!crate::leanh::lean_is_exclusive(v_val_1443_)) as u8;
                if v_isSharedCheck_1460_ == 0 {
                    v___x_1451_ = v_val_1443_;
                    v_isShared_1452_ = v_isSharedCheck_1460_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_expected_1449_);
                    crate::leanh::lean_inc(v_unexpected_1448_);
                    crate::leanh::lean_inc(v_unexpectedTk_1447_);
                    crate::leanh::lean_dec(v_val_1443_);
                    v___x_1451_ = crate::leanh::lean_box(0);
                    v_isShared_1452_ = v_isSharedCheck_1460_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1453_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_1403_, v_pos_1404_, v_str_1405_, v_unexpectedTk_1447_);
                if v_isShared_1452_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1451_, 0, v___x_1453_);
                    v___x_1455_ = v___x_1451_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1459_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_unexpected_1448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_expected_1449_);
                    v___x_1455_ = v_reuseFailAlloc_1459_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1446_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1445_, 0, v___x_1455_);
                    v___x_1457_ = v___x_1445_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
                    v___x_1457_ = v_reuseFailAlloc_1458_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1431_ = v___x_1457_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(
    mut v_env_1476_: *mut crate::leanh::LeanObject,
    mut v_p_1477_: *mut crate::leanh::LeanObject,
    mut v_ictx_1478_: *mut crate::leanh::LeanObject,
    mut v_s_1479_: *mut crate::leanh::LeanObject,
    mut v_text_1480_: *mut crate::leanh::LeanObject,
    mut v_pos_1481_: *mut crate::leanh::LeanObject,
    mut v_str_1482_: *mut crate::leanh::LeanObject,
    mut v___f_1483_: *mut crate::leanh::LeanObject,
    mut v_inst_1484_: *mut crate::leanh::LeanObject,
    mut v_inst_1485_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1486_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1488_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(
        v_env_1476_,
        v_p_1477_,
        v_ictx_1478_,
        v_s_1479_,
        v_text_1480_,
        v_pos_1481_,
        v_str_1482_,
        v___f_1483_,
        v_inst_1484_,
        v_inst_1485_,
        v_toApplicative_1486_,
        v_____do__lift_1487_,
    );
    crate::leanh::lean_dec_ref(v_str_1482_);
    crate::leanh::lean_dec_ref(v_text_1480_);
    return v_res_1488_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(
    mut v_str_1489_: *mut crate::leanh::LeanObject,
    mut v_env_1490_: *mut crate::leanh::LeanObject,
    mut v_p_1491_: *mut crate::leanh::LeanObject,
    mut v_text_1492_: *mut crate::leanh::LeanObject,
    mut v_pos_1493_: *mut crate::leanh::LeanObject,
    mut v___f_1494_: *mut crate::leanh::LeanObject,
    mut v_inst_1495_: *mut crate::leanh::LeanObject,
    mut v_inst_1496_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1497_: *mut crate::leanh::LeanObject,
    mut v_toBind_1498_: *mut crate::leanh::LeanObject,
    mut v_inst_1499_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1501_: u8 = 0;
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ictx_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1501_ = 1;
    v___x_1502_ = lean_string_utf8_byte_size(v_str_1489_);
    crate::leanh::lean_inc_ref(v_str_1489_);
    v_ictx_1503_ = l_Lean_Parser_mkInputContext___redArg(
        v_str_1489_,
        v_____do__lift_1500_,
        v___x_1501_,
        v___x_1502_,
    );
    v_s_1504_ = l_Lean_Parser_mkParserState(v_str_1489_);
    v___f_1505_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_1505_, 0, v_env_1490_);
    crate::leanh::lean_closure_set(v___f_1505_, 1, v_p_1491_);
    crate::leanh::lean_closure_set(v___f_1505_, 2, v_ictx_1503_);
    crate::leanh::lean_closure_set(v___f_1505_, 3, v_s_1504_);
    crate::leanh::lean_closure_set(v___f_1505_, 4, v_text_1492_);
    crate::leanh::lean_closure_set(v___f_1505_, 5, v_pos_1493_);
    crate::leanh::lean_closure_set(v___f_1505_, 6, v_str_1489_);
    crate::leanh::lean_closure_set(v___f_1505_, 7, v___f_1494_);
    crate::leanh::lean_closure_set(v___f_1505_, 8, v_inst_1495_);
    crate::leanh::lean_closure_set(v___f_1505_, 9, v_inst_1496_);
    crate::leanh::lean_closure_set(v___f_1505_, 10, v_toApplicative_1497_);
    v___x_1506_ = crate::leanh::lean_apply_4(
        v_toBind_1498_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1499_,
        v___f_1505_,
    );
    return v___x_1506_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(
    mut v_inst_1507_: *mut crate::leanh::LeanObject,
    mut v_strLit_1508_: *mut crate::leanh::LeanObject,
    mut v_text_1509_: *mut crate::leanh::LeanObject,
    mut v_env_1510_: *mut crate::leanh::LeanObject,
    mut v_p_1511_: *mut crate::leanh::LeanObject,
    mut v_inst_1512_: *mut crate::leanh::LeanObject,
    mut v_inst_1513_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1514_: *mut crate::leanh::LeanObject,
    mut v_toBind_1515_: *mut crate::leanh::LeanObject,
    mut v_inst_1516_: *mut crate::leanh::LeanObject,
    mut v_pos_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getFileName_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getFileName_1518_ = crate::leanh::lean_ctor_get(v_inst_1507_, 2);
    crate::leanh::lean_inc(v_getFileName_1518_);
    crate::leanh::lean_dec_ref(v_inst_1507_);
    v_str_1519_ = l_Lean_TSyntax_getString(v_strLit_1508_);
    crate::leanh::lean_inc_ref(v_str_1519_);
    crate::leanh::lean_inc(v_pos_1517_);
    crate::leanh::lean_inc_ref(v_text_1509_);
    v___f_1520_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1520_, 0, v_text_1509_);
    crate::leanh::lean_closure_set(v___f_1520_, 1, v_pos_1517_);
    crate::leanh::lean_closure_set(v___f_1520_, 2, v_str_1519_);
    crate::leanh::lean_inc(v_toBind_1515_);
    v___f_1521_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__2 as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_1521_, 0, v_str_1519_);
    crate::leanh::lean_closure_set(v___f_1521_, 1, v_env_1510_);
    crate::leanh::lean_closure_set(v___f_1521_, 2, v_p_1511_);
    crate::leanh::lean_closure_set(v___f_1521_, 3, v_text_1509_);
    crate::leanh::lean_closure_set(v___f_1521_, 4, v_pos_1517_);
    crate::leanh::lean_closure_set(v___f_1521_, 5, v___f_1520_);
    crate::leanh::lean_closure_set(v___f_1521_, 6, v_inst_1512_);
    crate::leanh::lean_closure_set(v___f_1521_, 7, v_inst_1513_);
    crate::leanh::lean_closure_set(v___f_1521_, 8, v_toApplicative_1514_);
    crate::leanh::lean_closure_set(v___f_1521_, 9, v_toBind_1515_);
    crate::leanh::lean_closure_set(v___f_1521_, 10, v_inst_1516_);
    v___x_1522_ = crate::leanh::lean_apply_4(
        v_toBind_1515_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getFileName_1518_,
        v___f_1521_,
    );
    return v___x_1522_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(
    mut v_inst_1523_: *mut crate::leanh::LeanObject,
    mut v_strLit_1524_: *mut crate::leanh::LeanObject,
    mut v_text_1525_: *mut crate::leanh::LeanObject,
    mut v_env_1526_: *mut crate::leanh::LeanObject,
    mut v_p_1527_: *mut crate::leanh::LeanObject,
    mut v_inst_1528_: *mut crate::leanh::LeanObject,
    mut v_inst_1529_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1530_: *mut crate::leanh::LeanObject,
    mut v_toBind_1531_: *mut crate::leanh::LeanObject,
    mut v_inst_1532_: *mut crate::leanh::LeanObject,
    mut v_pos_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(
        v_inst_1523_,
        v_strLit_1524_,
        v_text_1525_,
        v_env_1526_,
        v_p_1527_,
        v_inst_1528_,
        v_inst_1529_,
        v_toApplicative_1530_,
        v_toBind_1531_,
        v_inst_1532_,
        v_pos_1533_,
    );
    crate::leanh::lean_dec(v_strLit_1524_);
    return v_res_1534_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(
    mut v___f_1535_: *mut crate::leanh::LeanObject,
    mut v_pos_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1537_ = crate::leanh::lean_apply_1(v___f_1535_, v_pos_1536_);
    return v___x_1537_;
}
pub unsafe fn _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0;
    v___x_1540_ = l_Lean_stringToMessageData(v___x_1539_);
    return v___x_1540_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(
    mut v_text_1541_: *mut crate::leanh::LeanObject,
    mut v_inst_1542_: *mut crate::leanh::LeanObject,
    mut v_inst_1543_: *mut crate::leanh::LeanObject,
    mut v_strLit_1544_: *mut crate::leanh::LeanObject,
    mut v_toBind_1545_: *mut crate::leanh::LeanObject,
    mut v___f_1546_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1547_: *mut crate::leanh::LeanObject,
    mut v___f_1548_: *mut crate::leanh::LeanObject,
    mut v_____r_1549_: *mut crate::leanh::LeanObject,
    mut v_pos_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_source_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u32 = 0;
    let mut v___x_1553_: u32 = 0;
    let mut v___x_1554_: u8 = 0;
    v_source_1551_ = crate::leanh::lean_ctor_get(v_text_1541_, 0);
    v___x_1552_ = lean_string_utf8_get(v_source_1551_, v_pos_1550_);
    v___x_1553_ = 34;
    v___x_1554_ = lean_uint32_dec_eq(v___x_1552_, v___x_1553_);
    if v___x_1554_ == 0 {
        let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_1548_);
        crate::leanh::lean_dec_ref(v_toApplicative_1547_);
        v___x_1555_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once
            ),
            _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1,
        );
        v___x_1556_ =
            l_Lean_throwErrorAt___redArg(v_inst_1542_, v_inst_1543_, v_strLit_1544_, v___x_1555_);
        v___x_1557_ = crate::leanh::lean_apply_4(
            v_toBind_1545_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1556_,
            v___f_1546_,
        );
        return v___x_1557_;
    } else {
        let mut v_toPure_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_1546_);
        crate::leanh::lean_dec(v_strLit_1544_);
        crate::leanh::lean_dec_ref(v_inst_1543_);
        crate::leanh::lean_dec_ref(v_inst_1542_);
        v_toPure_1558_ = crate::leanh::lean_ctor_get(v_toApplicative_1547_, 1);
        crate::leanh::lean_inc(v_toPure_1558_);
        crate::leanh::lean_dec_ref(v_toApplicative_1547_);
        v___x_1559_ = lean_string_utf8_next(v_source_1551_, v_pos_1550_);
        v___x_1560_ =
            crate::leanh::lean_apply_2(v_toPure_1558_, crate::leanh::lean_box(0), v___x_1559_);
        v___x_1561_ = crate::leanh::lean_apply_4(
            v_toBind_1545_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1560_,
            v___f_1548_,
        );
        return v___x_1561_;
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed(
    mut v_text_1562_: *mut crate::leanh::LeanObject,
    mut v_inst_1563_: *mut crate::leanh::LeanObject,
    mut v_inst_1564_: *mut crate::leanh::LeanObject,
    mut v_strLit_1565_: *mut crate::leanh::LeanObject,
    mut v_toBind_1566_: *mut crate::leanh::LeanObject,
    mut v___f_1567_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1568_: *mut crate::leanh::LeanObject,
    mut v___f_1569_: *mut crate::leanh::LeanObject,
    mut v_____r_1570_: *mut crate::leanh::LeanObject,
    mut v_pos_1571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1572_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(
        v_text_1562_,
        v_inst_1563_,
        v_inst_1564_,
        v_strLit_1565_,
        v_toBind_1566_,
        v___f_1567_,
        v_toApplicative_1568_,
        v___f_1569_,
        v_____r_1570_,
        v_pos_1571_,
    );
    crate::leanh::lean_dec(v_pos_1571_);
    crate::leanh::lean_dec_ref(v_text_1562_);
    return v_res_1572_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(
    mut v___f_1573_: *mut crate::leanh::LeanObject,
    mut v_____s_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = crate::leanh::lean_box(0);
    v___x_1576_ = crate::leanh::lean_apply_2(v___f_1573_, v___x_1575_, v_____s_1574_);
    return v___x_1576_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(
    mut v_toPure_1577_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_a_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1596_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_1578_) == 0 {
                    v_a_1579_ = crate::leanh::lean_ctor_get(v_____do__lift_1578_, 0);
                    v_isSharedCheck_1587_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_1578_)) as u8;
                    if v_isSharedCheck_1587_ == 0 {
                        v___x_1581_ = v_____do__lift_1578_;
                        v_isShared_1582_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1579_);
                        crate::leanh::lean_dec(v_____do__lift_1578_);
                        v___x_1581_ = crate::leanh::lean_box(0);
                        v_isShared_1582_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1588_ = crate::leanh::lean_ctor_get(v_____do__lift_1578_, 0);
                    v_isSharedCheck_1596_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_1578_)) as u8;
                    if v_isSharedCheck_1596_ == 0 {
                        v___x_1590_ = v_____do__lift_1578_;
                        v_isShared_1591_ = v_isSharedCheck_1596_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1588_);
                        crate::leanh::lean_dec(v_____do__lift_1578_);
                        v___x_1590_ = crate::leanh::lean_box(0);
                        v_isShared_1591_ = v_isSharedCheck_1596_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1582_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1581_, 1);
                    v___x_1584_ = v___x_1581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1579_);
                    v___x_1584_ = v_reuseFailAlloc_1586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1585_ = crate::leanh::lean_apply_2(
                    v_toPure_1577_,
                    crate::leanh::lean_box(0),
                    v___x_1584_,
                );
                return v___x_1585_;
            }
            3 => {
                if v_isShared_1591_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1590_, 0);
                    v___x_1593_ = v___x_1590_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1588_);
                    v___x_1593_ = v_reuseFailAlloc_1595_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1594_ = crate::leanh::lean_apply_2(
                    v_toPure_1577_,
                    crate::leanh::lean_box(0),
                    v___x_1593_,
                );
                return v___x_1594_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(
    mut v_source_1597_: *mut crate::leanh::LeanObject,
    mut v_toPure_1598_: *mut crate::leanh::LeanObject,
    mut v_toBind_1599_: *mut crate::leanh::LeanObject,
    mut v___f_1600_: *mut crate::leanh::LeanObject,
    mut v_b_1601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1602_: u32 = 0;
    let mut v___x_1603_: u32 = 0;
    let mut v___x_1604_: u8 = 0;
    v___x_1602_ = lean_string_utf8_get(v_source_1597_, v_b_1601_);
    v___x_1603_ = 35;
    v___x_1604_ = lean_uint32_dec_eq(v___x_1602_, v___x_1603_);
    if v___x_1604_ == 0 {
        let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1605_, 0, v_b_1601_);
        v___x_1606_ =
            crate::leanh::lean_apply_2(v_toPure_1598_, crate::leanh::lean_box(0), v___x_1605_);
        v___x_1607_ = crate::leanh::lean_apply_4(
            v_toBind_1599_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1606_,
            v___f_1600_,
        );
        return v___x_1607_;
    } else {
        let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1608_ = lean_string_utf8_next(v_source_1597_, v_b_1601_);
        crate::leanh::lean_dec(v_b_1601_);
        v___x_1609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1609_, 0, v___x_1608_);
        v___x_1610_ =
            crate::leanh::lean_apply_2(v_toPure_1598_, crate::leanh::lean_box(0), v___x_1609_);
        v___x_1611_ = crate::leanh::lean_apply_4(
            v_toBind_1599_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1610_,
            v___f_1600_,
        );
        return v___x_1611_;
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(
    mut v_source_1612_: *mut crate::leanh::LeanObject,
    mut v_toPure_1613_: *mut crate::leanh::LeanObject,
    mut v_toBind_1614_: *mut crate::leanh::LeanObject,
    mut v___f_1615_: *mut crate::leanh::LeanObject,
    mut v_b_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1617_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(
        v_source_1612_,
        v_toPure_1613_,
        v_toBind_1614_,
        v___f_1615_,
        v_b_1616_,
    );
    crate::leanh::lean_dec_ref(v_source_1612_);
    return v_res_1617_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(
    mut v_text_1618_: *mut crate::leanh::LeanObject,
    mut v___f_1619_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1620_: *mut crate::leanh::LeanObject,
    mut v_toBind_1621_: *mut crate::leanh::LeanObject,
    mut v_inst_1622_: *mut crate::leanh::LeanObject,
    mut v___f_1623_: *mut crate::leanh::LeanObject,
    mut v_____x_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u32 = 0;
    let mut v___x_1628_: u32 = 0;
    let mut v___x_1629_: u8 = 0;
    v_start_1625_ = crate::leanh::lean_ctor_get(v_____x_1624_, 0);
    crate::leanh::lean_inc(v_start_1625_);
    crate::leanh::lean_dec_ref(v_____x_1624_);
    v_source_1626_ = crate::leanh::lean_ctor_get(v_text_1618_, 0);
    crate::leanh::lean_inc_ref(v_source_1626_);
    crate::leanh::lean_dec_ref(v_text_1618_);
    v___x_1627_ = lean_string_utf8_get(v_source_1626_, v_start_1625_);
    v___x_1628_ = 114;
    v___x_1629_ = lean_uint32_dec_eq(v___x_1627_, v___x_1628_);
    if v___x_1629_ == 0 {
        let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_source_1626_);
        crate::leanh::lean_dec(v___f_1623_);
        crate::leanh::lean_dec_ref(v_inst_1622_);
        crate::leanh::lean_dec(v_toBind_1621_);
        crate::leanh::lean_dec_ref(v_toApplicative_1620_);
        v___x_1630_ = crate::leanh::lean_box(0);
        v___x_1631_ = crate::leanh::lean_apply_2(v___f_1619_, v___x_1630_, v_start_1625_);
        return v___x_1631_;
    } else {
        let mut v_toPure_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_1619_);
        v_toPure_1632_ = crate::leanh::lean_ctor_get(v_toApplicative_1620_, 1);
        crate::leanh::lean_inc_n(v_toPure_1632_, 2);
        crate::leanh::lean_dec_ref(v_toApplicative_1620_);
        v_pos_1633_ = lean_string_utf8_next(v_source_1626_, v_start_1625_);
        crate::leanh::lean_dec(v_start_1625_);
        v___f_1634_ = crate::leanh::lean_alloc_closure(
            l_Lean_Doc_parseQuotedStrLit___redArg___lam__7 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1634_, 0, v_toPure_1632_);
        crate::leanh::lean_inc(v_toBind_1621_);
        v___f_1635_ = crate::leanh::lean_alloc_closure(
            l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1635_, 0, v_source_1626_);
        crate::leanh::lean_closure_set(v___f_1635_, 1, v_toPure_1632_);
        crate::leanh::lean_closure_set(v___f_1635_, 2, v_toBind_1621_);
        crate::leanh::lean_closure_set(v___f_1635_, 3, v___f_1634_);
        v___x_1636_ = l___private_Init_While_0__whileM_erased___redArg(
            v_inst_1622_,
            v___f_1635_,
            v_pos_1633_,
        );
        v___x_1637_ = crate::leanh::lean_apply_4(
            v_toBind_1621_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1636_,
            v___f_1623_,
        );
        return v___x_1637_;
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(
    mut v_inst_1638_: *mut crate::leanh::LeanObject,
    mut v_strLit_1639_: *mut crate::leanh::LeanObject,
    mut v_text_1640_: *mut crate::leanh::LeanObject,
    mut v_p_1641_: *mut crate::leanh::LeanObject,
    mut v_inst_1642_: *mut crate::leanh::LeanObject,
    mut v_inst_1643_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1644_: *mut crate::leanh::LeanObject,
    mut v_toBind_1645_: *mut crate::leanh::LeanObject,
    mut v_inst_1646_: *mut crate::leanh::LeanObject,
    mut v_env_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_toBind_1645_, 3);
    crate::leanh::lean_inc_ref_n(v_toApplicative_1644_, 2);
    crate::leanh::lean_inc_ref(v_inst_1643_);
    crate::leanh::lean_inc_ref_n(v_inst_1642_, 3);
    crate::leanh::lean_inc_ref_n(v_text_1640_, 2);
    crate::leanh::lean_inc_n(v_strLit_1639_, 2);
    v___f_1648_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed as *mut core::ffi::c_void,
        11,
        10,
    );
    crate::leanh::lean_closure_set(v___f_1648_, 0, v_inst_1638_);
    crate::leanh::lean_closure_set(v___f_1648_, 1, v_strLit_1639_);
    crate::leanh::lean_closure_set(v___f_1648_, 2, v_text_1640_);
    crate::leanh::lean_closure_set(v___f_1648_, 3, v_env_1647_);
    crate::leanh::lean_closure_set(v___f_1648_, 4, v_p_1641_);
    crate::leanh::lean_closure_set(v___f_1648_, 5, v_inst_1642_);
    crate::leanh::lean_closure_set(v___f_1648_, 6, v_inst_1643_);
    crate::leanh::lean_closure_set(v___f_1648_, 7, v_toApplicative_1644_);
    crate::leanh::lean_closure_set(v___f_1648_, 8, v_toBind_1645_);
    crate::leanh::lean_closure_set(v___f_1648_, 9, v_inst_1646_);
    v___f_1649_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__4 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1649_, 0, v___f_1648_);
    crate::leanh::lean_inc_ref(v___f_1649_);
    v___f_1650_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    crate::leanh::lean_closure_set(v___f_1650_, 0, v_text_1640_);
    crate::leanh::lean_closure_set(v___f_1650_, 1, v_inst_1642_);
    crate::leanh::lean_closure_set(v___f_1650_, 2, v_inst_1643_);
    crate::leanh::lean_closure_set(v___f_1650_, 3, v_strLit_1639_);
    crate::leanh::lean_closure_set(v___f_1650_, 4, v_toBind_1645_);
    crate::leanh::lean_closure_set(v___f_1650_, 5, v___f_1649_);
    crate::leanh::lean_closure_set(v___f_1650_, 6, v_toApplicative_1644_);
    crate::leanh::lean_closure_set(v___f_1650_, 7, v___f_1649_);
    crate::leanh::lean_inc_ref(v___f_1650_);
    v___f_1651_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1651_, 0, v___f_1650_);
    v___f_1652_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__9 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1652_, 0, v_text_1640_);
    crate::leanh::lean_closure_set(v___f_1652_, 1, v___f_1650_);
    crate::leanh::lean_closure_set(v___f_1652_, 2, v_toApplicative_1644_);
    crate::leanh::lean_closure_set(v___f_1652_, 3, v_toBind_1645_);
    crate::leanh::lean_closure_set(v___f_1652_, 4, v_inst_1642_);
    crate::leanh::lean_closure_set(v___f_1652_, 5, v___f_1651_);
    v___x_1653_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_1642_,
        v_strLit_1639_,
    );
    crate::leanh::lean_dec(v_strLit_1639_);
    v___x_1654_ = crate::leanh::lean_apply_4(
        v_toBind_1645_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1653_,
        v___f_1652_,
    );
    return v___x_1654_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(
    mut v_inst_1655_: *mut crate::leanh::LeanObject,
    mut v_inst_1656_: *mut crate::leanh::LeanObject,
    mut v_strLit_1657_: *mut crate::leanh::LeanObject,
    mut v_p_1658_: *mut crate::leanh::LeanObject,
    mut v_inst_1659_: *mut crate::leanh::LeanObject,
    mut v_inst_1660_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1661_: *mut crate::leanh::LeanObject,
    mut v_toBind_1662_: *mut crate::leanh::LeanObject,
    mut v_inst_1663_: *mut crate::leanh::LeanObject,
    mut v_text_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getEnv_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getEnv_1665_ = crate::leanh::lean_ctor_get(v_inst_1655_, 0);
    crate::leanh::lean_inc(v_getEnv_1665_);
    crate::leanh::lean_dec_ref(v_inst_1655_);
    crate::leanh::lean_inc(v_toBind_1662_);
    v___f_1666_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__10 as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_1666_, 0, v_inst_1656_);
    crate::leanh::lean_closure_set(v___f_1666_, 1, v_strLit_1657_);
    crate::leanh::lean_closure_set(v___f_1666_, 2, v_text_1664_);
    crate::leanh::lean_closure_set(v___f_1666_, 3, v_p_1658_);
    crate::leanh::lean_closure_set(v___f_1666_, 4, v_inst_1659_);
    crate::leanh::lean_closure_set(v___f_1666_, 5, v_inst_1660_);
    crate::leanh::lean_closure_set(v___f_1666_, 6, v_toApplicative_1661_);
    crate::leanh::lean_closure_set(v___f_1666_, 7, v_toBind_1662_);
    crate::leanh::lean_closure_set(v___f_1666_, 8, v_inst_1663_);
    v___x_1667_ = crate::leanh::lean_apply_4(
        v_toBind_1662_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1665_,
        v___f_1666_,
    );
    return v___x_1667_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg(
    mut v_inst_1668_: *mut crate::leanh::LeanObject,
    mut v_inst_1669_: *mut crate::leanh::LeanObject,
    mut v_inst_1670_: *mut crate::leanh::LeanObject,
    mut v_inst_1671_: *mut crate::leanh::LeanObject,
    mut v_inst_1672_: *mut crate::leanh::LeanObject,
    mut v_inst_1673_: *mut crate::leanh::LeanObject,
    mut v_p_1674_: *mut crate::leanh::LeanObject,
    mut v_strLit_1675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1676_ = crate::leanh::lean_ctor_get(v_inst_1668_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1676_);
    v_toBind_1677_ = crate::leanh::lean_ctor_get(v_inst_1668_, 1);
    crate::leanh::lean_inc_n(v_toBind_1677_, 2);
    v___f_1678_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__11 as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_1678_, 0, v_inst_1670_);
    crate::leanh::lean_closure_set(v___f_1678_, 1, v_inst_1672_);
    crate::leanh::lean_closure_set(v___f_1678_, 2, v_strLit_1675_);
    crate::leanh::lean_closure_set(v___f_1678_, 3, v_p_1674_);
    crate::leanh::lean_closure_set(v___f_1678_, 4, v_inst_1668_);
    crate::leanh::lean_closure_set(v___f_1678_, 5, v_inst_1671_);
    crate::leanh::lean_closure_set(v___f_1678_, 6, v_toApplicative_1676_);
    crate::leanh::lean_closure_set(v___f_1678_, 7, v_toBind_1677_);
    crate::leanh::lean_closure_set(v___f_1678_, 8, v_inst_1673_);
    v___x_1679_ = crate::leanh::lean_apply_4(
        v_toBind_1677_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1669_,
        v___f_1678_,
    );
    return v___x_1679_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit(
    mut v_m_1680_: *mut crate::leanh::LeanObject,
    mut v_inst_1681_: *mut crate::leanh::LeanObject,
    mut v_inst_1682_: *mut crate::leanh::LeanObject,
    mut v_inst_1683_: *mut crate::leanh::LeanObject,
    mut v_inst_1684_: *mut crate::leanh::LeanObject,
    mut v_inst_1685_: *mut crate::leanh::LeanObject,
    mut v_inst_1686_: *mut crate::leanh::LeanObject,
    mut v_p_1687_: *mut crate::leanh::LeanObject,
    mut v_strLit_1688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1689_ = l_Lean_Doc_parseQuotedStrLit___redArg(
        v_inst_1681_,
        v_inst_1682_,
        v_inst_1683_,
        v_inst_1684_,
        v_inst_1685_,
        v_inst_1686_,
        v_p_1687_,
        v_strLit_1688_,
    );
    return v___x_1689_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__0(
    mut v_s_1690_: *mut crate::leanh::LeanObject,
    mut v_toPure_1691_: *mut crate::leanh::LeanObject,
    mut v_err_1692_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_stxStack_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stxStack_1693_ = crate::leanh::lean_ctor_get(v_s_1690_, 0);
    v___x_1694_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1693_);
    v___x_1695_ = crate::leanh::lean_box((v_err_1692_) as usize);
    v___x_1696_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1696_, 0, v___x_1694_);
    crate::leanh::lean_ctor_set(v___x_1696_, 1, v___x_1695_);
    v___x_1697_ =
        crate::leanh::lean_apply_2(v_toPure_1691_, crate::leanh::lean_box(0), v___x_1696_);
    return v___x_1697_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed(
    mut v_s_1698_: *mut crate::leanh::LeanObject,
    mut v_toPure_1699_: *mut crate::leanh::LeanObject,
    mut v_err_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_err_boxed_1701_: u8 = 0;
    let mut v_res_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_err_boxed_1701_ = (crate::leanh::lean_unbox(v_err_1700_) as u8);
    v_res_1702_ =
        l_Lean_Doc_parseStrLit_x27___redArg___lam__0(v_s_1698_, v_toPure_1699_, v_err_boxed_1701_);
    crate::leanh::lean_dec_ref(v_s_1698_);
    return v_res_1702_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__1(
    mut v___f_1703_: *mut crate::leanh::LeanObject,
    mut v_err_1704_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = crate::leanh::lean_box((v_err_1704_) as usize);
    v___x_1706_ = crate::leanh::lean_apply_1(v___f_1703_, v___x_1705_);
    return v___x_1706_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed(
    mut v___f_1707_: *mut crate::leanh::LeanObject,
    mut v_err_1708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_err_boxed_1709_: u8 = 0;
    let mut v_res_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_err_boxed_1709_ = (crate::leanh::lean_unbox(v_err_1708_) as u8);
    v_res_1710_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__1(v___f_1707_, v_err_boxed_1709_);
    return v_res_1710_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__2(
    mut v_toPure_1711_: *mut crate::leanh::LeanObject,
    mut v___x_1712_: u8,
    mut v_toBind_1713_: *mut crate::leanh::LeanObject,
    mut v___f_1714_: *mut crate::leanh::LeanObject,
    mut v_____r_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = crate::leanh::lean_box((v___x_1712_) as usize);
    v___x_1717_ =
        crate::leanh::lean_apply_2(v_toPure_1711_, crate::leanh::lean_box(0), v___x_1716_);
    v___x_1718_ = crate::leanh::lean_apply_4(
        v_toBind_1713_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1717_,
        v___f_1714_,
    );
    return v___x_1718_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(
    mut v_toPure_1719_: *mut crate::leanh::LeanObject,
    mut v___x_1720_: *mut crate::leanh::LeanObject,
    mut v_toBind_1721_: *mut crate::leanh::LeanObject,
    mut v___f_1722_: *mut crate::leanh::LeanObject,
    mut v_____r_1723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_559__boxed_1724_: u8 = 0;
    let mut v_res_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_559__boxed_1724_ = (crate::leanh::lean_unbox(v___x_1720_) as u8);
    v_res_1725_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__2(
        v_toPure_1719_,
        v___x_559__boxed_1724_,
        v_toBind_1721_,
        v___f_1722_,
        v_____r_1723_,
    );
    return v_res_1725_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__6(
    mut v_env_1726_: *mut crate::leanh::LeanObject,
    mut v_p_1727_: *mut crate::leanh::LeanObject,
    mut v_ictx_1728_: *mut crate::leanh::LeanObject,
    mut v_s_1729_: *mut crate::leanh::LeanObject,
    mut v_toPure_1730_: *mut crate::leanh::LeanObject,
    mut v___x_1731_: u8,
    mut v_toBind_1732_: *mut crate::leanh::LeanObject,
    mut v_inst_1733_: *mut crate::leanh::LeanObject,
    mut v_inst_1734_: *mut crate::leanh::LeanObject,
    mut v_inst_1735_: *mut crate::leanh::LeanObject,
    mut v_inst_1736_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: u8 = 0;
    v___x_1738_ = crate::leanh::lean_box(0);
    v___x_1739_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_env_1726_);
    v___x_1740_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1740_, 0, v_env_1726_);
    crate::leanh::lean_ctor_set(v___x_1740_, 1, v_____do__lift_1737_);
    crate::leanh::lean_ctor_set(v___x_1740_, 2, v___x_1738_);
    crate::leanh::lean_ctor_set(v___x_1740_, 3, v___x_1739_);
    v___x_1741_ = l_Lean_Parser_getTokenTable(v_env_1726_);
    crate::leanh::lean_inc_ref(v_ictx_1728_);
    v_s_1742_ =
        l_Lean_Parser_ParserFn_run(v_p_1727_, v_ictx_1728_, v___x_1740_, v___x_1741_, v_s_1729_);
    crate::leanh::lean_inc(v_toPure_1730_);
    crate::leanh::lean_inc_ref_n(v_s_1742_, 2);
    v___f_1743_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1743_, 0, v_s_1742_);
    crate::leanh::lean_closure_set(v___f_1743_, 1, v_toPure_1730_);
    v___x_1744_ = l_Lean_Parser_ParserState_allErrors(v_s_1742_);
    v___x_1745_ = lean_array_get_size(v___x_1744_);
    crate::leanh::lean_dec_ref(v___x_1744_);
    v___x_1746_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1747_ = lean_nat_dec_eq(v___x_1745_, v___x_1746_);
    if v___x_1747_ == 0 {
        let mut v___f_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_1748_ = crate::leanh::lean_alloc_closure(
            l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1748_, 0, v___f_1743_);
        v___x_1749_ = crate::leanh::lean_box((v___x_1731_) as usize);
        crate::leanh::lean_inc(v_toBind_1732_);
        v___f_1750_ = crate::leanh::lean_alloc_closure(
            l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1750_, 0, v_toPure_1730_);
        crate::leanh::lean_closure_set(v___f_1750_, 1, v___x_1749_);
        crate::leanh::lean_closure_set(v___f_1750_, 2, v_toBind_1732_);
        crate::leanh::lean_closure_set(v___f_1750_, 3, v___f_1748_);
        v___x_1751_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1728_, v_s_1742_);
        v___x_1752_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1752_, 0, v___x_1751_);
        v___x_1753_ = l_Lean_MessageData_ofFormat(v___x_1752_);
        v___x_1754_ = l_Lean_logError___redArg(
            v_inst_1733_,
            v_inst_1734_,
            v_inst_1735_,
            v_inst_1736_,
            v___x_1753_,
        );
        v___x_1755_ = crate::leanh::lean_apply_4(
            v_toBind_1732_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1754_,
            v___f_1750_,
        );
        return v___x_1755_;
    } else {
        let mut v_pos_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: u8 = 0;
        v_pos_1756_ = crate::leanh::lean_ctor_get(v_s_1742_, 2);
        crate::leanh::lean_inc(v_pos_1756_);
        v___x_1757_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1728_, v_pos_1756_);
        crate::leanh::lean_dec(v_pos_1756_);
        if v___x_1757_ == 0 {
            let mut v___f_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___f_1758_ = crate::leanh::lean_alloc_closure(
                l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_1758_, 0, v___f_1743_);
            v___x_1759_ = crate::leanh::lean_box((v___x_1731_) as usize);
            crate::leanh::lean_inc(v_toBind_1732_);
            v___f_1760_ = crate::leanh::lean_alloc_closure(
                l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed as *mut core::ffi::c_void,
                5,
                4,
            );
            crate::leanh::lean_closure_set(v___f_1760_, 0, v_toPure_1730_);
            crate::leanh::lean_closure_set(v___f_1760_, 1, v___x_1759_);
            crate::leanh::lean_closure_set(v___f_1760_, 2, v_toBind_1732_);
            crate::leanh::lean_closure_set(v___f_1760_, 3, v___f_1758_);
            v___x_1761_ = l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0;
            v___x_1762_ = l_Lean_Parser_ParserState_mkError(v_s_1742_, v___x_1761_);
            v___x_1763_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1728_, v___x_1762_);
            v___x_1764_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1764_, 0, v___x_1763_);
            v___x_1765_ = l_Lean_MessageData_ofFormat(v___x_1764_);
            v___x_1766_ = l_Lean_logError___redArg(
                v_inst_1733_,
                v_inst_1734_,
                v_inst_1735_,
                v_inst_1736_,
                v___x_1765_,
            );
            v___x_1767_ = crate::leanh::lean_apply_4(
                v_toBind_1732_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1766_,
                v___f_1760_,
            );
            return v___x_1767_;
        } else {
            let mut v___f_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1769_: u8 = 0;
            let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_s_1742_);
            crate::leanh::lean_dec(v_inst_1736_);
            crate::leanh::lean_dec(v_inst_1735_);
            crate::leanh::lean_dec_ref(v_inst_1734_);
            crate::leanh::lean_dec_ref(v_inst_1733_);
            crate::leanh::lean_dec_ref(v_ictx_1728_);
            v___f_1768_ = crate::leanh::lean_alloc_closure(
                l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_1768_, 0, v___f_1743_);
            v___x_1769_ = 0;
            v___x_1770_ = crate::leanh::lean_box((v___x_1769_) as usize);
            v___x_1771_ =
                crate::leanh::lean_apply_2(v_toPure_1730_, crate::leanh::lean_box(0), v___x_1770_);
            v___x_1772_ = crate::leanh::lean_apply_4(
                v_toBind_1732_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1771_,
                v___f_1768_,
            );
            return v___x_1772_;
        }
    }
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(
    mut v_env_1773_: *mut crate::leanh::LeanObject,
    mut v_p_1774_: *mut crate::leanh::LeanObject,
    mut v_ictx_1775_: *mut crate::leanh::LeanObject,
    mut v_s_1776_: *mut crate::leanh::LeanObject,
    mut v_toPure_1777_: *mut crate::leanh::LeanObject,
    mut v___x_1778_: *mut crate::leanh::LeanObject,
    mut v_toBind_1779_: *mut crate::leanh::LeanObject,
    mut v_inst_1780_: *mut crate::leanh::LeanObject,
    mut v_inst_1781_: *mut crate::leanh::LeanObject,
    mut v_inst_1782_: *mut crate::leanh::LeanObject,
    mut v_inst_1783_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_575__boxed_1785_: u8 = 0;
    let mut v_res_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_575__boxed_1785_ = (crate::leanh::lean_unbox(v___x_1778_) as u8);
    v_res_1786_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__6(
        v_env_1773_,
        v_p_1774_,
        v_ictx_1775_,
        v_s_1776_,
        v_toPure_1777_,
        v___x_575__boxed_1785_,
        v_toBind_1779_,
        v_inst_1780_,
        v_inst_1781_,
        v_inst_1782_,
        v_inst_1783_,
        v_____do__lift_1784_,
    );
    return v_res_1786_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__3(
    mut v_source_1787_: *mut crate::leanh::LeanObject,
    mut v___x_1788_: u8,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
    mut v_env_1790_: *mut crate::leanh::LeanObject,
    mut v_p_1791_: *mut crate::leanh::LeanObject,
    mut v_toPure_1792_: *mut crate::leanh::LeanObject,
    mut v_toBind_1793_: *mut crate::leanh::LeanObject,
    mut v_inst_1794_: *mut crate::leanh::LeanObject,
    mut v_inst_1795_: *mut crate::leanh::LeanObject,
    mut v_inst_1796_: *mut crate::leanh::LeanObject,
    mut v_inst_1797_: *mut crate::leanh::LeanObject,
    mut v_s_1798_: *mut crate::leanh::LeanObject,
    mut v___x_1799_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ictx_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_source_1787_);
                v_ictx_1801_ = l_Lean_Parser_mkInputContext___redArg(
                    v_source_1787_,
                    v_____do__lift_1800_,
                    v___x_1788_,
                    v___y_1789_,
                );
                v___x_1802_ = l_Lean_Parser_mkParserState(v_source_1787_);
                crate::leanh::lean_dec_ref(v_source_1787_);
                v___x_1809_ = l_Lean_Syntax_getPos_x3f(v_s_1798_, v___x_1788_);
                if crate::leanh::lean_obj_tag(v___x_1809_) == 0 {
                    v___x_1810_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_1811_ = l_panic___redArg(v___x_1799_, v___x_1810_);
                    v___y_1804_ = v___x_1811_;
                    state = 1;
                    continue;
                } else {
                    v_val_1812_ = crate::leanh::lean_ctor_get(v___x_1809_, 0);
                    crate::leanh::lean_inc(v_val_1812_);
                    crate::leanh::lean_dec_ref_known(v___x_1809_, 1);
                    v___y_1804_ = v_val_1812_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_s_1805_ = l_Lean_Parser_ParserState_setPos(v___x_1802_, v___y_1804_);
                v___x_1806_ = crate::leanh::lean_box((v___x_1788_) as usize);
                crate::leanh::lean_inc(v_inst_1797_);
                crate::leanh::lean_inc(v_toBind_1793_);
                v___f_1807_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed as *mut core::ffi::c_void,
                    12,
                    11,
                );
                crate::leanh::lean_closure_set(v___f_1807_, 0, v_env_1790_);
                crate::leanh::lean_closure_set(v___f_1807_, 1, v_p_1791_);
                crate::leanh::lean_closure_set(v___f_1807_, 2, v_ictx_1801_);
                crate::leanh::lean_closure_set(v___f_1807_, 3, v_s_1805_);
                crate::leanh::lean_closure_set(v___f_1807_, 4, v_toPure_1792_);
                crate::leanh::lean_closure_set(v___f_1807_, 5, v___x_1806_);
                crate::leanh::lean_closure_set(v___f_1807_, 6, v_toBind_1793_);
                crate::leanh::lean_closure_set(v___f_1807_, 7, v_inst_1794_);
                crate::leanh::lean_closure_set(v___f_1807_, 8, v_inst_1795_);
                crate::leanh::lean_closure_set(v___f_1807_, 9, v_inst_1796_);
                crate::leanh::lean_closure_set(v___f_1807_, 10, v_inst_1797_);
                v___x_1808_ = crate::leanh::lean_apply_4(
                    v_toBind_1793_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_1797_,
                    v___f_1807_,
                );
                return v___x_1808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed(
    mut v_source_1813_: *mut crate::leanh::LeanObject,
    mut v___x_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v_env_1816_: *mut crate::leanh::LeanObject,
    mut v_p_1817_: *mut crate::leanh::LeanObject,
    mut v_toPure_1818_: *mut crate::leanh::LeanObject,
    mut v_toBind_1819_: *mut crate::leanh::LeanObject,
    mut v_inst_1820_: *mut crate::leanh::LeanObject,
    mut v_inst_1821_: *mut crate::leanh::LeanObject,
    mut v_inst_1822_: *mut crate::leanh::LeanObject,
    mut v_inst_1823_: *mut crate::leanh::LeanObject,
    mut v_s_1824_: *mut crate::leanh::LeanObject,
    mut v___x_1825_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_668__boxed_1827_: u8 = 0;
    let mut v_res_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_668__boxed_1827_ = (crate::leanh::lean_unbox(v___x_1814_) as u8);
    v_res_1828_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__3(
        v_source_1813_,
        v___x_668__boxed_1827_,
        v___y_1815_,
        v_env_1816_,
        v_p_1817_,
        v_toPure_1818_,
        v_toBind_1819_,
        v_inst_1820_,
        v_inst_1821_,
        v_inst_1822_,
        v_inst_1823_,
        v_s_1824_,
        v___x_1825_,
        v_____do__lift_1826_,
    );
    crate::leanh::lean_dec(v___x_1825_);
    crate::leanh::lean_dec(v_s_1824_);
    return v_res_1828_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__4(
    mut v_text_1829_: *mut crate::leanh::LeanObject,
    mut v_inst_1830_: *mut crate::leanh::LeanObject,
    mut v_p_1831_: *mut crate::leanh::LeanObject,
    mut v_toPure_1832_: *mut crate::leanh::LeanObject,
    mut v_toBind_1833_: *mut crate::leanh::LeanObject,
    mut v_inst_1834_: *mut crate::leanh::LeanObject,
    mut v_inst_1835_: *mut crate::leanh::LeanObject,
    mut v_inst_1836_: *mut crate::leanh::LeanObject,
    mut v_s_1837_: *mut crate::leanh::LeanObject,
    mut v___x_1838_: *mut crate::leanh::LeanObject,
    mut v_env_1839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1840_: u8 = 0;
    let mut v___y_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getFileName_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: u8 = 0;
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1840_ = 1;
                v___x_1853_ = l_Lean_Syntax_getTailPos_x3f(v_s_1837_, v___x_1840_);
                if crate::leanh::lean_obj_tag(v___x_1853_) == 0 {
                    v___x_1854_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_1855_ = l_panic___redArg(v___x_1838_, v___x_1854_);
                    v___y_1849_ = v___x_1855_;
                    state = 2;
                    continue;
                } else {
                    v_val_1856_ = crate::leanh::lean_ctor_get(v___x_1853_, 0);
                    crate::leanh::lean_inc(v_val_1856_);
                    crate::leanh::lean_dec_ref_known(v___x_1853_, 1);
                    v___y_1849_ = v_val_1856_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v_getFileName_1844_ = crate::leanh::lean_ctor_get(v_inst_1830_, 2);
                crate::leanh::lean_inc(v_getFileName_1844_);
                v___x_1845_ = crate::leanh::lean_box((v___x_1840_) as usize);
                crate::leanh::lean_inc(v_toBind_1833_);
                v___f_1846_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed as *mut core::ffi::c_void,
                    14,
                    13,
                );
                crate::leanh::lean_closure_set(v___f_1846_, 0, v___y_1842_);
                crate::leanh::lean_closure_set(v___f_1846_, 1, v___x_1845_);
                crate::leanh::lean_closure_set(v___f_1846_, 2, v___y_1843_);
                crate::leanh::lean_closure_set(v___f_1846_, 3, v_env_1839_);
                crate::leanh::lean_closure_set(v___f_1846_, 4, v_p_1831_);
                crate::leanh::lean_closure_set(v___f_1846_, 5, v_toPure_1832_);
                crate::leanh::lean_closure_set(v___f_1846_, 6, v_toBind_1833_);
                crate::leanh::lean_closure_set(v___f_1846_, 7, v_inst_1834_);
                crate::leanh::lean_closure_set(v___f_1846_, 8, v_inst_1830_);
                crate::leanh::lean_closure_set(v___f_1846_, 9, v_inst_1835_);
                crate::leanh::lean_closure_set(v___f_1846_, 10, v_inst_1836_);
                crate::leanh::lean_closure_set(v___f_1846_, 11, v_s_1837_);
                crate::leanh::lean_closure_set(v___f_1846_, 12, v___x_1838_);
                v___x_1847_ = crate::leanh::lean_apply_4(
                    v_toBind_1833_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_getFileName_1844_,
                    v___f_1846_,
                );
                return v___x_1847_;
            }
            2 => {
                v_source_1850_ = crate::leanh::lean_ctor_get(v_text_1829_, 0);
                crate::leanh::lean_inc_ref(v_source_1850_);
                crate::leanh::lean_dec_ref(v_text_1829_);
                v___x_1851_ = lean_string_utf8_byte_size(v_source_1850_);
                v___x_1852_ = lean_nat_dec_le(v___y_1849_, v___x_1851_);
                if v___x_1852_ == 0 {
                    crate::leanh::lean_dec(v___y_1849_);
                    v___y_1842_ = v_source_1850_;
                    v___y_1843_ = v___x_1851_;
                    state = 1;
                    continue;
                } else {
                    v___y_1842_ = v_source_1850_;
                    v___y_1843_ = v___y_1849_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__5(
    mut v_inst_1857_: *mut crate::leanh::LeanObject,
    mut v_inst_1858_: *mut crate::leanh::LeanObject,
    mut v_p_1859_: *mut crate::leanh::LeanObject,
    mut v_toPure_1860_: *mut crate::leanh::LeanObject,
    mut v_toBind_1861_: *mut crate::leanh::LeanObject,
    mut v_inst_1862_: *mut crate::leanh::LeanObject,
    mut v_inst_1863_: *mut crate::leanh::LeanObject,
    mut v_inst_1864_: *mut crate::leanh::LeanObject,
    mut v_s_1865_: *mut crate::leanh::LeanObject,
    mut v___x_1866_: *mut crate::leanh::LeanObject,
    mut v_text_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getEnv_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getEnv_1868_ = crate::leanh::lean_ctor_get(v_inst_1857_, 0);
    crate::leanh::lean_inc(v_getEnv_1868_);
    crate::leanh::lean_dec_ref(v_inst_1857_);
    crate::leanh::lean_inc(v_toBind_1861_);
    v___f_1869_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit_x27___redArg___lam__4 as *mut core::ffi::c_void,
        11,
        10,
    );
    crate::leanh::lean_closure_set(v___f_1869_, 0, v_text_1867_);
    crate::leanh::lean_closure_set(v___f_1869_, 1, v_inst_1858_);
    crate::leanh::lean_closure_set(v___f_1869_, 2, v_p_1859_);
    crate::leanh::lean_closure_set(v___f_1869_, 3, v_toPure_1860_);
    crate::leanh::lean_closure_set(v___f_1869_, 4, v_toBind_1861_);
    crate::leanh::lean_closure_set(v___f_1869_, 5, v_inst_1862_);
    crate::leanh::lean_closure_set(v___f_1869_, 6, v_inst_1863_);
    crate::leanh::lean_closure_set(v___f_1869_, 7, v_inst_1864_);
    crate::leanh::lean_closure_set(v___f_1869_, 8, v_s_1865_);
    crate::leanh::lean_closure_set(v___f_1869_, 9, v___x_1866_);
    v___x_1870_ = crate::leanh::lean_apply_4(
        v_toBind_1861_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1868_,
        v___f_1869_,
    );
    return v___x_1870_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg(
    mut v_inst_1871_: *mut crate::leanh::LeanObject,
    mut v_inst_1872_: *mut crate::leanh::LeanObject,
    mut v_inst_1873_: *mut crate::leanh::LeanObject,
    mut v_inst_1874_: *mut crate::leanh::LeanObject,
    mut v_inst_1875_: *mut crate::leanh::LeanObject,
    mut v_inst_1876_: *mut crate::leanh::LeanObject,
    mut v_p_1877_: *mut crate::leanh::LeanObject,
    mut v_s_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1879_ = crate::leanh::lean_ctor_get(v_inst_1871_, 0);
    v_toBind_1880_ = crate::leanh::lean_ctor_get(v_inst_1871_, 1);
    crate::leanh::lean_inc_n(v_toBind_1880_, 2);
    v_toPure_1881_ = crate::leanh::lean_ctor_get(v_toApplicative_1879_, 1);
    crate::leanh::lean_inc(v_toPure_1881_);
    v___x_1882_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_1883_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit_x27___redArg___lam__5 as *mut core::ffi::c_void,
        11,
        10,
    );
    crate::leanh::lean_closure_set(v___f_1883_, 0, v_inst_1873_);
    crate::leanh::lean_closure_set(v___f_1883_, 1, v_inst_1875_);
    crate::leanh::lean_closure_set(v___f_1883_, 2, v_p_1877_);
    crate::leanh::lean_closure_set(v___f_1883_, 3, v_toPure_1881_);
    crate::leanh::lean_closure_set(v___f_1883_, 4, v_toBind_1880_);
    crate::leanh::lean_closure_set(v___f_1883_, 5, v_inst_1871_);
    crate::leanh::lean_closure_set(v___f_1883_, 6, v_inst_1874_);
    crate::leanh::lean_closure_set(v___f_1883_, 7, v_inst_1876_);
    crate::leanh::lean_closure_set(v___f_1883_, 8, v_s_1878_);
    crate::leanh::lean_closure_set(v___f_1883_, 9, v___x_1882_);
    v___x_1884_ = crate::leanh::lean_apply_4(
        v_toBind_1880_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1872_,
        v___f_1883_,
    );
    return v___x_1884_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27(
    mut v_m_1885_: *mut crate::leanh::LeanObject,
    mut v_inst_1886_: *mut crate::leanh::LeanObject,
    mut v_inst_1887_: *mut crate::leanh::LeanObject,
    mut v_inst_1888_: *mut crate::leanh::LeanObject,
    mut v_inst_1889_: *mut crate::leanh::LeanObject,
    mut v_inst_1890_: *mut crate::leanh::LeanObject,
    mut v_inst_1891_: *mut crate::leanh::LeanObject,
    mut v_p_1892_: *mut crate::leanh::LeanObject,
    mut v_s_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = l_Lean_Doc_parseStrLit_x27___redArg(
        v_inst_1886_,
        v_inst_1887_,
        v_inst_1888_,
        v_inst_1889_,
        v_inst_1890_,
        v_inst_1891_,
        v_p_1892_,
        v_s_1893_,
    );
    return v___x_1894_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Extension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Mem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DocString_Builtin_Parsing(
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
pub unsafe fn initialize_Lean_Elab_DocString_Builtin_Parsing(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Extension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Mem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
}
