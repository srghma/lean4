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
pub static l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
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
        78, 111, 116, 32, 97, 32, 113, 117, 111, 116, 101, 100, 32, 115, 116, 114, 105, 110, 103,
        32, 108, 105, 116, 101, 114, 97, 108, 0,
    ],
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_951_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2;
    v___x_952_ = leanh::lean_unsigned_to_nat(14);
    v___x_953_ = leanh::lean_unsigned_to_nat(22);
    v___x_954_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1;
    v___x_955_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0;
    v___x_956_ =
        l_mkPanicMessageWithDecl(v___x_955_, v___x_954_, v___x_953_, v___x_952_, v___x_951_);
    return v___x_956_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
    mut v_inst_957_: *mut leanh::LeanObject,
    mut v_s_958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_965_: u8 = 0;
    let mut v_toPure_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_971_: u8 = 0;
    let mut v_unused_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___y_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_973_ = leanh::lean_unsigned_to_nat(0);
                v___x_974_ = 1;
                v___x_981_ = l_Lean_Syntax_getPos_x3f(v_s_958_, v___x_974_);
                if leanh::lean_obj_tag(v___x_981_) == 0 {
                    v___x_982_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_983_ = l_panic___redArg(v___x_973_, v___x_982_);
                    v___y_976_ = v___x_983_;
                    state = 4;
                    continue;
                } else {
                    v_val_984_ = leanh::lean_ctor_get(v___x_981_, 0);
                    leanh::lean_inc(v_val_984_);
                    leanh::lean_dec_ref_known(v___x_981_, 1);
                    v___y_976_ = v_val_984_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v_toApplicative_962_ = leanh::lean_ctor_get(v_inst_957_, 0);
                v_isSharedCheck_971_ = (!leanh::lean_is_exclusive(v_inst_957_)) as u8;
                if v_isSharedCheck_971_ == 0 {
                    v_unused_972_ = leanh::lean_ctor_get(v_inst_957_, 1);
                    leanh::lean_dec(v_unused_972_);
                    v___x_964_ = v_inst_957_;
                    v_isShared_965_ = v_isSharedCheck_971_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_962_);
                    leanh::lean_dec(v_inst_957_);
                    v___x_964_ = leanh::lean_box(0);
                    v_isShared_965_ = v_isSharedCheck_971_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toPure_966_ = leanh::lean_ctor_get(v_toApplicative_962_, 1);
                leanh::lean_inc(v_toPure_966_);
                leanh::lean_dec_ref(v_toApplicative_962_);
                if v_isShared_965_ == 0 {
                    leanh::lean_ctor_set(v___x_964_, 1, v___y_961_);
                    leanh::lean_ctor_set(v___x_964_, 0, v___y_960_);
                    v___x_968_ = v___x_964_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_970_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_970_, 0, v___y_960_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_970_, 1, v___y_961_);
                    v___x_968_ = v_reuseFailAlloc_970_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_969_ = leanh::lean_apply_2(
                    v_toPure_966_,
                    leanh::lean_box(0),
                    v___x_968_,
                );
                return v___x_969_;
            }
            4 => {
                v___x_977_ = l_Lean_Syntax_getTailPos_x3f(v_s_958_, v___x_974_);
                if leanh::lean_obj_tag(v___x_977_) == 0 {
                    v___x_978_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_979_ = l_panic___redArg(v___x_973_, v___x_978_);
                    v___y_960_ = v___y_976_;
                    v___y_961_ = v___x_979_;
                    state = 1;
                    continue;
                } else {
                    v_val_980_ = leanh::lean_ctor_get(v___x_977_, 0);
                    leanh::lean_inc(v_val_980_);
                    leanh::lean_dec_ref_known(v___x_977_, 1);
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
    mut v_inst_985_: *mut leanh::LeanObject,
    mut v_s_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_987_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_985_,
        v_s_986_,
    );
    leanh::lean_dec(v_s_986_);
    return v_res_987_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(
    mut v_m_988_: *mut leanh::LeanObject,
    mut v_inst_989_: *mut leanh::LeanObject,
    mut v_inst_990_: *mut leanh::LeanObject,
    mut v_s_991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_989_,
        v_s_991_,
    );
    return v___x_992_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___boxed(
    mut v_m_993_: *mut leanh::LeanObject,
    mut v_inst_994_: *mut leanh::LeanObject,
    mut v_inst_995_: *mut leanh::LeanObject,
    mut v_s_996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_997_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(
        v_m_993_,
        v_inst_994_,
        v_inst_995_,
        v_s_996_,
    );
    leanh::lean_dec(v_s_996_);
    leanh::lean_dec(v_inst_995_);
    return v_res_997_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__0(
    mut v_env_999_: *mut leanh::LeanObject,
    mut v_p_1000_: *mut leanh::LeanObject,
    mut v_ictx_1001_: *mut leanh::LeanObject,
    mut v_s_1002_: *mut leanh::LeanObject,
    mut v_inst_1003_: *mut leanh::LeanObject,
    mut v_inst_1004_: *mut leanh::LeanObject,
    mut v_toApplicative_1005_: *mut leanh::LeanObject,
    mut v_____do__lift_1006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: u8 = 0;
    v___x_1007_ = leanh::lean_box(0);
    v___x_1008_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_env_999_);
    v___x_1009_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1009_, 0, v_env_999_);
    leanh::lean_ctor_set(v___x_1009_, 1, v_____do__lift_1006_);
    leanh::lean_ctor_set(v___x_1009_, 2, v___x_1007_);
    leanh::lean_ctor_set(v___x_1009_, 3, v___x_1008_);
    v___x_1010_ = l_Lean_Parser_getTokenTable(v_env_999_);
    leanh::lean_inc_ref(v_ictx_1001_);
    v_s_1011_ =
        l_Lean_Parser_ParserFn_run(v_p_1000_, v_ictx_1001_, v___x_1009_, v___x_1010_, v_s_1002_);
    leanh::lean_inc_ref(v_s_1011_);
    v___x_1012_ = l_Lean_Parser_ParserState_allErrors(v_s_1011_);
    v___x_1013_ = lean_array_get_size(v___x_1012_);
    leanh::lean_dec_ref(v___x_1012_);
    v___x_1014_ = leanh::lean_unsigned_to_nat(0);
    v___x_1015_ = lean_nat_dec_eq(v___x_1013_, v___x_1014_);
    if v___x_1015_ == 0 {
        let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toApplicative_1005_);
        v___x_1016_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1001_, v_s_1011_);
        v___x_1017_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1017_, 0, v___x_1016_);
        v___x_1018_ = l_Lean_MessageData_ofFormat(v___x_1017_);
        v___x_1019_ = l_Lean_throwError___redArg(v_inst_1003_, v_inst_1004_, v___x_1018_);
        return v___x_1019_;
    } else {
        let mut v_stxStack_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1022_: u8 = 0;
        v_stxStack_1020_ = leanh::lean_ctor_get(v_s_1011_, 0);
        leanh::lean_inc_ref(v_stxStack_1020_);
        v_pos_1021_ = leanh::lean_ctor_get(v_s_1011_, 2);
        leanh::lean_inc(v_pos_1021_);
        v___x_1022_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1001_, v_pos_1021_);
        leanh::lean_dec(v_pos_1021_);
        if v___x_1022_ == 0 {
            let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_stxStack_1020_);
            leanh::lean_dec_ref(v_toApplicative_1005_);
            v___x_1023_ = l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0;
            v___x_1024_ = l_Lean_Parser_ParserState_mkError(v_s_1011_, v___x_1023_);
            v___x_1025_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1001_, v___x_1024_);
            v___x_1026_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1026_, 0, v___x_1025_);
            v___x_1027_ = l_Lean_MessageData_ofFormat(v___x_1026_);
            v___x_1028_ = l_Lean_throwError___redArg(v_inst_1003_, v_inst_1004_, v___x_1027_);
            return v___x_1028_;
        } else {
            let mut v_toPure_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_s_1011_);
            leanh::lean_dec_ref(v_inst_1004_);
            leanh::lean_dec_ref(v_inst_1003_);
            leanh::lean_dec_ref(v_ictx_1001_);
            v_toPure_1029_ = leanh::lean_ctor_get(v_toApplicative_1005_, 1);
            leanh::lean_inc(v_toPure_1029_);
            leanh::lean_dec_ref(v_toApplicative_1005_);
            v___x_1030_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1020_);
            leanh::lean_dec_ref(v_stxStack_1020_);
            v___x_1031_ =
                leanh::lean_apply_2(v_toPure_1029_, leanh::lean_box(0), v___x_1030_);
            return v___x_1031_;
        }
    }
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__1(
    mut v_source_1032_: *mut leanh::LeanObject,
    mut v___y_1033_: *mut leanh::LeanObject,
    mut v_start_1034_: *mut leanh::LeanObject,
    mut v_env_1035_: *mut leanh::LeanObject,
    mut v_p_1036_: *mut leanh::LeanObject,
    mut v_inst_1037_: *mut leanh::LeanObject,
    mut v_inst_1038_: *mut leanh::LeanObject,
    mut v_toApplicative_1039_: *mut leanh::LeanObject,
    mut v_toBind_1040_: *mut leanh::LeanObject,
    mut v_inst_1041_: *mut leanh::LeanObject,
    mut v_____do__lift_1042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1043_: u8 = 0;
    let mut v_ictx_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1043_ = 1;
    leanh::lean_inc_ref(v_source_1032_);
    v_ictx_1044_ = l_Lean_Parser_mkInputContext___redArg(
        v_source_1032_,
        v_____do__lift_1042_,
        v___x_1043_,
        v___y_1033_,
    );
    v___x_1045_ = l_Lean_Parser_mkParserState(v_source_1032_);
    leanh::lean_dec_ref(v_source_1032_);
    v_s_1046_ = l_Lean_Parser_ParserState_setPos(v___x_1045_, v_start_1034_);
    v___f_1047_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__0 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1047_, 0, v_env_1035_);
    leanh::lean_closure_set(v___f_1047_, 1, v_p_1036_);
    leanh::lean_closure_set(v___f_1047_, 2, v_ictx_1044_);
    leanh::lean_closure_set(v___f_1047_, 3, v_s_1046_);
    leanh::lean_closure_set(v___f_1047_, 4, v_inst_1037_);
    leanh::lean_closure_set(v___f_1047_, 5, v_inst_1038_);
    leanh::lean_closure_set(v___f_1047_, 6, v_toApplicative_1039_);
    v___x_1048_ = leanh::lean_apply_4(
        v_toBind_1040_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1041_,
        v___f_1047_,
    );
    return v___x_1048_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__2(
    mut v_text_1049_: *mut leanh::LeanObject,
    mut v_inst_1050_: *mut leanh::LeanObject,
    mut v_env_1051_: *mut leanh::LeanObject,
    mut v_p_1052_: *mut leanh::LeanObject,
    mut v_inst_1053_: *mut leanh::LeanObject,
    mut v_inst_1054_: *mut leanh::LeanObject,
    mut v_toApplicative_1055_: *mut leanh::LeanObject,
    mut v_toBind_1056_: *mut leanh::LeanObject,
    mut v_inst_1057_: *mut leanh::LeanObject,
    mut v_____x_1058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getFileName_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_1059_ = leanh::lean_ctor_get(v_____x_1058_, 0);
                leanh::lean_inc(v_start_1059_);
                v_stop_1060_ = leanh::lean_ctor_get(v_____x_1058_, 1);
                leanh::lean_inc(v_stop_1060_);
                leanh::lean_dec_ref(v_____x_1058_);
                v_source_1061_ = leanh::lean_ctor_get(v_text_1049_, 0);
                leanh::lean_inc_ref(v_source_1061_);
                leanh::lean_dec_ref(v_text_1049_);
                v___x_1067_ = lean_string_utf8_byte_size(v_source_1061_);
                v___x_1068_ = lean_nat_dec_le(v_stop_1060_, v___x_1067_);
                if v___x_1068_ == 0 {
                    leanh::lean_dec(v_stop_1060_);
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
                v_getFileName_1064_ = leanh::lean_ctor_get(v_inst_1050_, 2);
                leanh::lean_inc(v_getFileName_1064_);
                leanh::lean_dec_ref(v_inst_1050_);
                leanh::lean_inc(v_toBind_1056_);
                v___f_1065_ = leanh::lean_alloc_closure(
                    l_Lean_Doc_parseStrLit___redArg___lam__1 as *mut core::ffi::c_void,
                    11,
                    10,
                );
                leanh::lean_closure_set(v___f_1065_, 0, v_source_1061_);
                leanh::lean_closure_set(v___f_1065_, 1, v___y_1063_);
                leanh::lean_closure_set(v___f_1065_, 2, v_start_1059_);
                leanh::lean_closure_set(v___f_1065_, 3, v_env_1051_);
                leanh::lean_closure_set(v___f_1065_, 4, v_p_1052_);
                leanh::lean_closure_set(v___f_1065_, 5, v_inst_1053_);
                leanh::lean_closure_set(v___f_1065_, 6, v_inst_1054_);
                leanh::lean_closure_set(v___f_1065_, 7, v_toApplicative_1055_);
                leanh::lean_closure_set(v___f_1065_, 8, v_toBind_1056_);
                leanh::lean_closure_set(v___f_1065_, 9, v_inst_1057_);
                v___x_1066_ = leanh::lean_apply_4(
                    v_toBind_1056_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_text_1069_: *mut leanh::LeanObject,
    mut v_inst_1070_: *mut leanh::LeanObject,
    mut v_p_1071_: *mut leanh::LeanObject,
    mut v_inst_1072_: *mut leanh::LeanObject,
    mut v_inst_1073_: *mut leanh::LeanObject,
    mut v_toApplicative_1074_: *mut leanh::LeanObject,
    mut v_toBind_1075_: *mut leanh::LeanObject,
    mut v_inst_1076_: *mut leanh::LeanObject,
    mut v_s_1077_: *mut leanh::LeanObject,
    mut v_env_1078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_1075_);
    leanh::lean_inc_ref(v_inst_1072_);
    v___f_1079_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_1079_, 0, v_text_1069_);
    leanh::lean_closure_set(v___f_1079_, 1, v_inst_1070_);
    leanh::lean_closure_set(v___f_1079_, 2, v_env_1078_);
    leanh::lean_closure_set(v___f_1079_, 3, v_p_1071_);
    leanh::lean_closure_set(v___f_1079_, 4, v_inst_1072_);
    leanh::lean_closure_set(v___f_1079_, 5, v_inst_1073_);
    leanh::lean_closure_set(v___f_1079_, 6, v_toApplicative_1074_);
    leanh::lean_closure_set(v___f_1079_, 7, v_toBind_1075_);
    leanh::lean_closure_set(v___f_1079_, 8, v_inst_1076_);
    v___x_1080_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_1072_,
        v_s_1077_,
    );
    v___x_1081_ = leanh::lean_apply_4(
        v_toBind_1075_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1080_,
        v___f_1079_,
    );
    return v___x_1081_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__3___boxed(
    mut v_text_1082_: *mut leanh::LeanObject,
    mut v_inst_1083_: *mut leanh::LeanObject,
    mut v_p_1084_: *mut leanh::LeanObject,
    mut v_inst_1085_: *mut leanh::LeanObject,
    mut v_inst_1086_: *mut leanh::LeanObject,
    mut v_toApplicative_1087_: *mut leanh::LeanObject,
    mut v_toBind_1088_: *mut leanh::LeanObject,
    mut v_inst_1089_: *mut leanh::LeanObject,
    mut v_s_1090_: *mut leanh::LeanObject,
    mut v_env_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_s_1090_);
    return v_res_1092_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__4(
    mut v_inst_1093_: *mut leanh::LeanObject,
    mut v_inst_1094_: *mut leanh::LeanObject,
    mut v_p_1095_: *mut leanh::LeanObject,
    mut v_inst_1096_: *mut leanh::LeanObject,
    mut v_inst_1097_: *mut leanh::LeanObject,
    mut v_toApplicative_1098_: *mut leanh::LeanObject,
    mut v_toBind_1099_: *mut leanh::LeanObject,
    mut v_inst_1100_: *mut leanh::LeanObject,
    mut v_s_1101_: *mut leanh::LeanObject,
    mut v_text_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getEnv_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getEnv_1103_ = leanh::lean_ctor_get(v_inst_1093_, 0);
    leanh::lean_inc(v_getEnv_1103_);
    leanh::lean_dec_ref(v_inst_1093_);
    leanh::lean_inc(v_toBind_1099_);
    v___f_1104_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__3___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_1104_, 0, v_text_1102_);
    leanh::lean_closure_set(v___f_1104_, 1, v_inst_1094_);
    leanh::lean_closure_set(v___f_1104_, 2, v_p_1095_);
    leanh::lean_closure_set(v___f_1104_, 3, v_inst_1096_);
    leanh::lean_closure_set(v___f_1104_, 4, v_inst_1097_);
    leanh::lean_closure_set(v___f_1104_, 5, v_toApplicative_1098_);
    leanh::lean_closure_set(v___f_1104_, 6, v_toBind_1099_);
    leanh::lean_closure_set(v___f_1104_, 7, v_inst_1100_);
    leanh::lean_closure_set(v___f_1104_, 8, v_s_1101_);
    v___x_1105_ = leanh::lean_apply_4(
        v_toBind_1099_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1103_,
        v___f_1104_,
    );
    return v___x_1105_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg(
    mut v_inst_1106_: *mut leanh::LeanObject,
    mut v_inst_1107_: *mut leanh::LeanObject,
    mut v_inst_1108_: *mut leanh::LeanObject,
    mut v_inst_1109_: *mut leanh::LeanObject,
    mut v_inst_1110_: *mut leanh::LeanObject,
    mut v_inst_1111_: *mut leanh::LeanObject,
    mut v_p_1112_: *mut leanh::LeanObject,
    mut v_s_1113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1114_ = leanh::lean_ctor_get(v_inst_1106_, 0);
    leanh::lean_inc_ref(v_toApplicative_1114_);
    v_toBind_1115_ = leanh::lean_ctor_get(v_inst_1106_, 1);
    leanh::lean_inc_n(v_toBind_1115_, 2);
    v___f_1116_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__4 as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_1116_, 0, v_inst_1108_);
    leanh::lean_closure_set(v___f_1116_, 1, v_inst_1110_);
    leanh::lean_closure_set(v___f_1116_, 2, v_p_1112_);
    leanh::lean_closure_set(v___f_1116_, 3, v_inst_1106_);
    leanh::lean_closure_set(v___f_1116_, 4, v_inst_1109_);
    leanh::lean_closure_set(v___f_1116_, 5, v_toApplicative_1114_);
    leanh::lean_closure_set(v___f_1116_, 6, v_toBind_1115_);
    leanh::lean_closure_set(v___f_1116_, 7, v_inst_1111_);
    leanh::lean_closure_set(v___f_1116_, 8, v_s_1113_);
    v___x_1117_ = leanh::lean_apply_4(
        v_toBind_1115_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1107_,
        v___f_1116_,
    );
    return v___x_1117_;
}
pub unsafe fn l_Lean_Doc_parseStrLit(
    mut v_m_1118_: *mut leanh::LeanObject,
    mut v_inst_1119_: *mut leanh::LeanObject,
    mut v_inst_1120_: *mut leanh::LeanObject,
    mut v_inst_1121_: *mut leanh::LeanObject,
    mut v_inst_1122_: *mut leanh::LeanObject,
    mut v_inst_1123_: *mut leanh::LeanObject,
    mut v_inst_1124_: *mut leanh::LeanObject,
    mut v_p_1125_: *mut leanh::LeanObject,
    mut v_s_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_str_1128_: *mut leanh::LeanObject,
    mut v_a_1129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1130_ = leanh::lean_ctor_get(v_a_1129_, 0);
                v_snd_1131_ = leanh::lean_ctor_get(v_a_1129_, 1);
                v_isSharedCheck_1147_ = (!leanh::lean_is_exclusive(v_a_1129_)) as u8;
                if v_isSharedCheck_1147_ == 0 {
                    v___x_1133_ = v_a_1129_;
                    v_isShared_1134_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1131_);
                    leanh::lean_inc(v_fst_1130_);
                    leanh::lean_dec(v_a_1129_);
                    v___x_1133_ = leanh::lean_box(0);
                    v_isShared_1134_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1135_ = leanh::lean_unsigned_to_nat(0);
                v___x_1136_ = lean_nat_dec_lt(v___x_1135_, v_fst_1130_);
                if v___x_1136_ == 0 {
                    if v_isShared_1134_ == 0 {
                        v___x_1138_ = v___x_1133_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1139_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_fst_1130_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_snd_1131_);
                        v___x_1138_ = v_reuseFailAlloc_1139_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1140_ = lean_string_utf8_prev(v_str_1128_, v_fst_1130_);
                    leanh::lean_dec(v_fst_1130_);
                    v___x_1141_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1142_ = lean_nat_add(v_snd_1131_, v___x_1141_);
                    leanh::lean_dec(v_snd_1131_);
                    if v_isShared_1134_ == 0 {
                        leanh::lean_ctor_set(v___x_1133_, 1, v___x_1142_);
                        leanh::lean_ctor_set(v___x_1133_, 0, v___x_1140_);
                        v___x_1144_ = v___x_1133_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1140_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1142_);
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
    mut v_str_1148_: *mut leanh::LeanObject,
    mut v_a_1149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1150_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_1148_, v_a_1149_);
    leanh::lean_dec_ref(v_str_1148_);
    return v_res_1150_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(
    mut v_str_1151_: *mut leanh::LeanObject,
    mut v_p_1152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_1153_ = leanh::lean_unsigned_to_nat(0);
    v___x_1154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1154_, 0, v_p_1152_);
    leanh::lean_ctor_set(v___x_1154_, 1, v_n_1153_);
    v___x_1155_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_1151_, v___x_1154_);
    v_snd_1156_ = leanh::lean_ctor_get(v___x_1155_, 1);
    leanh::lean_inc(v_snd_1156_);
    leanh::lean_dec_ref(v___x_1155_);
    return v_snd_1156_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(
    mut v_str_1157_: *mut leanh::LeanObject,
    mut v_p_1158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1159_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(
            v_str_1157_,
            v_p_1158_,
        );
    leanh::lean_dec_ref(v_str_1157_);
    return v_res_1159_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(
    mut v_str_1160_: *mut leanh::LeanObject,
    mut v_inst_1161_: *mut leanh::LeanObject,
    mut v_a_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1163_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_1160_, v_a_1162_);
    return v___x_1163_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(
    mut v_str_1164_: *mut leanh::LeanObject,
    mut v_inst_1165_: *mut leanh::LeanObject,
    mut v_a_1166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1167_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(v_str_1164_, v_inst_1165_, v_a_1166_);
    leanh::lean_dec_ref(v_str_1164_);
    return v_res_1167_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(
    mut v_str_1168_: *mut leanh::LeanObject,
    mut v_p_1169_: *mut leanh::LeanObject,
    mut v_j_1170_: *mut leanh::LeanObject,
    mut v_a_1171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1173_: u8 = 0;
    let mut v_one_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1172_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1173_ = lean_nat_dec_eq(v_j_1170_, v_zero_1172_);
                if v_isZero_1173_ == 1 {
                    leanh::lean_dec(v_j_1170_);
                    return v_a_1171_;
                } else {
                    leanh::lean_dec(v_a_1171_);
                    v_one_1174_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1175_ = lean_nat_sub(v_j_1170_, v_one_1174_);
                    leanh::lean_dec(v_j_1170_);
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
    mut v_str_1178_: *mut leanh::LeanObject,
    mut v_p_1179_: *mut leanh::LeanObject,
    mut v_j_1180_: *mut leanh::LeanObject,
    mut v_a_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1182_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_1178_, v_p_1179_, v_j_1180_, v_a_1181_);
    leanh::lean_dec(v_p_1179_);
    leanh::lean_dec_ref(v_str_1178_);
    return v_res_1182_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(
    mut v_str_1183_: *mut leanh::LeanObject,
    mut v_n_1184_: *mut leanh::LeanObject,
    mut v_p_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_p_1185_);
    v___x_1186_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_1183_, v_p_1185_, v_n_1184_, v_p_1185_);
    leanh::lean_dec(v_p_1185_);
    return v___x_1186_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(
    mut v_str_1187_: *mut leanh::LeanObject,
    mut v_n_1188_: *mut leanh::LeanObject,
    mut v_p_1189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1190_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(
            v_str_1187_,
            v_n_1188_,
            v_p_1189_,
        );
    leanh::lean_dec_ref(v_str_1187_);
    return v_res_1190_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(
    mut v_str_1191_: *mut leanh::LeanObject,
    mut v_p_1192_: *mut leanh::LeanObject,
    mut v_n_1193_: *mut leanh::LeanObject,
    mut v_j_1194_: *mut leanh::LeanObject,
    mut v_a_1195_: *mut leanh::LeanObject,
    mut v_a_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_1191_, v_p_1192_, v_j_1194_, v_a_1196_);
    return v___x_1197_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(
    mut v_str_1198_: *mut leanh::LeanObject,
    mut v_p_1199_: *mut leanh::LeanObject,
    mut v_n_1200_: *mut leanh::LeanObject,
    mut v_j_1201_: *mut leanh::LeanObject,
    mut v_a_1202_: *mut leanh::LeanObject,
    mut v_a_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1204_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(v_str_1198_, v_p_1199_, v_n_1200_, v_j_1201_, v_a_1202_, v_a_1203_);
    leanh::lean_dec(v_n_1200_);
    leanh::lean_dec(v_p_1199_);
    leanh::lean_dec_ref(v_str_1198_);
    return v_res_1204_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(
    mut v_text_1205_: *mut leanh::LeanObject,
    mut v_posOfStr_1206_: *mut leanh::LeanObject,
    mut v_str_1207_: *mut leanh::LeanObject,
    mut v_posInStr_1208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_source_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_source_1209_ = leanh::lean_ctor_get(v_text_1205_, 0);
    v___x_1210_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(
            v_str_1207_,
            v_posInStr_1208_,
        );
    leanh::lean_inc(v_posOfStr_1206_);
    v___x_1211_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_source_1209_, v_posOfStr_1206_, v___x_1210_, v_posOfStr_1206_);
    leanh::lean_dec(v_posOfStr_1206_);
    return v___x_1211_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(
    mut v_text_1212_: *mut leanh::LeanObject,
    mut v_posOfStr_1213_: *mut leanh::LeanObject,
    mut v_str_1214_: *mut leanh::LeanObject,
    mut v_posInStr_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1216_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(
            v_text_1212_,
            v_posOfStr_1213_,
            v_str_1214_,
            v_posInStr_1215_,
        );
    leanh::lean_dec_ref(v_str_1214_);
    leanh::lean_dec_ref(v_text_1212_);
    return v_res_1216_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(
    mut v_text_1217_: *mut leanh::LeanObject,
    mut v_posOfStr_1218_: *mut leanh::LeanObject,
    mut v_str_1219_: *mut leanh::LeanObject,
    mut v_a_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: u8 = 0;
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canonical_1229_: u8 = 0;
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1238_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_1220_) {
                0 => {
                    v_pos_1221_ = leanh::lean_ctor_get(v_a_1220_, 1);
                    leanh::lean_inc(v_pos_1221_);
                    v_endPos_1222_ = leanh::lean_ctor_get(v_a_1220_, 3);
                    leanh::lean_inc(v_endPos_1222_);
                    leanh::lean_dec_ref_known(v_a_1220_, 4);
                    leanh::lean_inc(v_posOfStr_1218_);
                    v___x_1223_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_pos_1221_);
                    v___x_1224_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_endPos_1222_);
                    v___x_1225_ = 1;
                    v___x_1226_ = leanh::lean_alloc_ctor(1, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_1226_, 0, v___x_1223_);
                    leanh::lean_ctor_set(v___x_1226_, 1, v___x_1224_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1226_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_1225_,
                    );
                    return v___x_1226_;
                }
                1 => {
                    v_pos_1227_ = leanh::lean_ctor_get(v_a_1220_, 0);
                    v_endPos_1228_ = leanh::lean_ctor_get(v_a_1220_, 1);
                    v_canonical_1229_ = leanh::lean_ctor_get_uint8(
                        v_a_1220_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v_isSharedCheck_1238_ = (!leanh::lean_is_exclusive(v_a_1220_)) as u8;
                    if v_isSharedCheck_1238_ == 0 {
                        v___x_1231_ = v_a_1220_;
                        v_isShared_1232_ = v_isSharedCheck_1238_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_endPos_1228_);
                        leanh::lean_inc(v_pos_1227_);
                        leanh::lean_dec(v_a_1220_);
                        v___x_1231_ = leanh::lean_box(0);
                        v_isShared_1232_ = v_isSharedCheck_1238_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_posOfStr_1218_);
                    return v_a_1220_;
                }
            },
            1 => {
                leanh::lean_inc(v_posOfStr_1218_);
                v___x_1233_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_pos_1227_);
                v___x_1234_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_endPos_1228_);
                if v_isShared_1232_ == 0 {
                    leanh::lean_ctor_set(v___x_1231_, 1, v___x_1234_);
                    leanh::lean_ctor_set(v___x_1231_, 0, v___x_1233_);
                    v___x_1236_ = v___x_1231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1237_ = leanh::lean_alloc_ctor(1, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1234_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1237_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_text_1239_: *mut leanh::LeanObject,
    mut v_posOfStr_1240_: *mut leanh::LeanObject,
    mut v_str_1241_: *mut leanh::LeanObject,
    mut v_a_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_1239_, v_posOfStr_1240_, v_str_1241_, v_a_1242_);
    leanh::lean_dec_ref(v_str_1241_);
    leanh::lean_dec_ref(v_text_1239_);
    return v_res_1243_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(
    mut v_text_1244_: *mut leanh::LeanObject,
    mut v_posOfStr_1245_: *mut leanh::LeanObject,
    mut v_str_1246_: *mut leanh::LeanObject,
    mut v_a_1247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1253_: u8 = 0;
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1255_: usize = 0;
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1261_: u8 = 0;
    let mut v_info_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1266_: u8 = 0;
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_info_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1278_: u8 = 0;
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_1247_) {
                0 => {
                    leanh::lean_dec(v_posOfStr_1245_);
                    return v_a_1247_;
                }
                1 => {
                    v_info_1248_ = leanh::lean_ctor_get(v_a_1247_, 0);
                    v_kind_1249_ = leanh::lean_ctor_get(v_a_1247_, 1);
                    v_args_1250_ = leanh::lean_ctor_get(v_a_1247_, 2);
                    v_isSharedCheck_1261_ = (!leanh::lean_is_exclusive(v_a_1247_)) as u8;
                    if v_isSharedCheck_1261_ == 0 {
                        v___x_1252_ = v_a_1247_;
                        v_isShared_1253_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_args_1250_);
                        leanh::lean_inc(v_kind_1249_);
                        leanh::lean_inc(v_info_1248_);
                        leanh::lean_dec(v_a_1247_);
                        v___x_1252_ = leanh::lean_box(0);
                        v_isShared_1253_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_info_1262_ = leanh::lean_ctor_get(v_a_1247_, 0);
                    v_val_1263_ = leanh::lean_ctor_get(v_a_1247_, 1);
                    v_isSharedCheck_1271_ = (!leanh::lean_is_exclusive(v_a_1247_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v___x_1265_ = v_a_1247_;
                        v_isShared_1266_ = v_isSharedCheck_1271_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1263_);
                        leanh::lean_inc(v_info_1262_);
                        leanh::lean_dec(v_a_1247_);
                        v___x_1265_ = leanh::lean_box(0);
                        v_isShared_1266_ = v_isSharedCheck_1271_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_info_1272_ = leanh::lean_ctor_get(v_a_1247_, 0);
                    v_rawVal_1273_ = leanh::lean_ctor_get(v_a_1247_, 1);
                    v_val_1274_ = leanh::lean_ctor_get(v_a_1247_, 2);
                    v_preresolved_1275_ = leanh::lean_ctor_get(v_a_1247_, 3);
                    v_isSharedCheck_1283_ = (!leanh::lean_is_exclusive(v_a_1247_)) as u8;
                    if v_isSharedCheck_1283_ == 0 {
                        v___x_1277_ = v_a_1247_;
                        v_isShared_1278_ = v_isSharedCheck_1283_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_preresolved_1275_);
                        leanh::lean_inc(v_val_1274_);
                        leanh::lean_inc(v_rawVal_1273_);
                        leanh::lean_inc(v_info_1272_);
                        leanh::lean_dec(v_a_1247_);
                        v___x_1277_ = leanh::lean_box(0);
                        v_isShared_1278_ = v_isSharedCheck_1283_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                leanh::lean_inc(v_posOfStr_1245_);
                v___x_1254_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_1244_, v_posOfStr_1245_, v_str_1246_, v_info_1248_);
                v_sz_1255_ = lean_array_size(v_args_1250_);
                v___x_1256_ = 0usize;
                v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_1244_, v_posOfStr_1245_, v_str_1246_, v_sz_1255_, v___x_1256_, v_args_1250_);
                if v_isShared_1253_ == 0 {
                    leanh::lean_ctor_set(v___x_1252_, 2, v___x_1257_);
                    leanh::lean_ctor_set(v___x_1252_, 0, v___x_1254_);
                    v___x_1259_ = v___x_1252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1260_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_kind_1249_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 2, v___x_1257_);
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
                    leanh::lean_ctor_set(v___x_1265_, 0, v___x_1267_);
                    v___x_1269_ = v___x_1265_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_val_1263_);
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
                    leanh::lean_ctor_set(v___x_1277_, 0, v___x_1279_);
                    v___x_1281_ = v___x_1277_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1282_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_rawVal_1273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_val_1274_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_preresolved_1275_);
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
    mut v_text_1284_: *mut leanh::LeanObject,
    mut v_posOfStr_1285_: *mut leanh::LeanObject,
    mut v_str_1286_: *mut leanh::LeanObject,
    mut v_sz_1287_: usize,
    mut v_i_1288_: usize,
    mut v_bs_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1290_: u8 = 0;
    let mut v_v_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: usize = 0;
    let mut v___x_1296_: usize = 0;
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1290_ = lean_usize_dec_lt(v_i_1288_, v_sz_1287_);
                if v___x_1290_ == 0 {
                    leanh::lean_dec(v_posOfStr_1285_);
                    return v_bs_1289_;
                } else {
                    v_v_1291_ = lean_array_uget(v_bs_1289_, v_i_1288_);
                    v___x_1292_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1293_ = lean_array_uset(v_bs_1289_, v_i_1288_, v___x_1292_);
                    leanh::lean_inc(v_posOfStr_1285_);
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
    mut v_text_1299_: *mut leanh::LeanObject,
    mut v_posOfStr_1300_: *mut leanh::LeanObject,
    mut v_str_1301_: *mut leanh::LeanObject,
    mut v_sz_1302_: *mut leanh::LeanObject,
    mut v_i_1303_: *mut leanh::LeanObject,
    mut v_bs_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1305_: usize = 0;
    let mut v_i_boxed_1306_: usize = 0;
    let mut v_res_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1305_ = leanh::lean_unbox_usize(v_sz_1302_);
    leanh::lean_dec(v_sz_1302_);
    v_i_boxed_1306_ = leanh::lean_unbox_usize(v_i_1303_);
    leanh::lean_dec(v_i_1303_);
    v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_1299_, v_posOfStr_1300_, v_str_1301_, v_sz_boxed_1305_, v_i_boxed_1306_, v_bs_1304_);
    leanh::lean_dec_ref(v_str_1301_);
    leanh::lean_dec_ref(v_text_1299_);
    return v_res_1307_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(
    mut v_text_1308_: *mut leanh::LeanObject,
    mut v_posOfStr_1309_: *mut leanh::LeanObject,
    mut v_str_1310_: *mut leanh::LeanObject,
    mut v_a_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1312_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_1308_, v_posOfStr_1309_, v_str_1310_, v_a_1311_);
    leanh::lean_dec_ref(v_str_1310_);
    leanh::lean_dec_ref(v_text_1308_);
    return v_res_1312_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(
    mut v_x_1313_: *mut leanh::LeanObject,
    mut v_h__1_1314_: *mut leanh::LeanObject,
    mut v_h__2_1315_: *mut leanh::LeanObject,
    mut v_h__3_1316_: *mut leanh::LeanObject,
    mut v_h__4_1317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1313_) {
        0 => {
            let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1316_);
            leanh::lean_dec(v_h__2_1315_);
            leanh::lean_dec(v_h__1_1314_);
            v___x_1318_ = leanh::lean_box(0);
            v___x_1319_ = leanh::lean_apply_1(v_h__4_1317_, v___x_1318_);
            return v___x_1319_;
        }
        1 => {
            let mut v_info_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_kind_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_args_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1317_);
            leanh::lean_dec(v_h__3_1316_);
            leanh::lean_dec(v_h__2_1315_);
            v_info_1320_ = leanh::lean_ctor_get(v_x_1313_, 0);
            leanh::lean_inc(v_info_1320_);
            v_kind_1321_ = leanh::lean_ctor_get(v_x_1313_, 1);
            leanh::lean_inc(v_kind_1321_);
            v_args_1322_ = leanh::lean_ctor_get(v_x_1313_, 2);
            leanh::lean_inc_ref(v_args_1322_);
            leanh::lean_dec_ref_known(v_x_1313_, 3);
            v___x_1323_ =
                leanh::lean_apply_3(v_h__1_1314_, v_info_1320_, v_kind_1321_, v_args_1322_);
            return v___x_1323_;
        }
        2 => {
            let mut v_info_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1317_);
            leanh::lean_dec(v_h__2_1315_);
            leanh::lean_dec(v_h__1_1314_);
            v_info_1324_ = leanh::lean_ctor_get(v_x_1313_, 0);
            leanh::lean_inc(v_info_1324_);
            v_val_1325_ = leanh::lean_ctor_get(v_x_1313_, 1);
            leanh::lean_inc_ref(v_val_1325_);
            leanh::lean_dec_ref_known(v_x_1313_, 2);
            v___x_1326_ = leanh::lean_apply_2(v_h__3_1316_, v_info_1324_, v_val_1325_);
            return v___x_1326_;
        }
        _ => {
            let mut v_info_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rawVal_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_preresolved_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1317_);
            leanh::lean_dec(v_h__3_1316_);
            leanh::lean_dec(v_h__1_1314_);
            v_info_1327_ = leanh::lean_ctor_get(v_x_1313_, 0);
            leanh::lean_inc(v_info_1327_);
            v_rawVal_1328_ = leanh::lean_ctor_get(v_x_1313_, 1);
            leanh::lean_inc_ref(v_rawVal_1328_);
            v_val_1329_ = leanh::lean_ctor_get(v_x_1313_, 2);
            leanh::lean_inc(v_val_1329_);
            v_preresolved_1330_ = leanh::lean_ctor_get(v_x_1313_, 3);
            leanh::lean_inc(v_preresolved_1330_);
            leanh::lean_dec_ref_known(v_x_1313_, 4);
            v___x_1331_ = leanh::lean_apply_4(
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
    mut v_motive_1332_: *mut leanh::LeanObject,
    mut v_x_1333_: *mut leanh::LeanObject,
    mut v_h__1_1334_: *mut leanh::LeanObject,
    mut v_h__2_1335_: *mut leanh::LeanObject,
    mut v_h__3_1336_: *mut leanh::LeanObject,
    mut v_h__4_1337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1333_) {
        0 => {
            let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1336_);
            leanh::lean_dec(v_h__2_1335_);
            leanh::lean_dec(v_h__1_1334_);
            v___x_1338_ = leanh::lean_box(0);
            v___x_1339_ = leanh::lean_apply_1(v_h__4_1337_, v___x_1338_);
            return v___x_1339_;
        }
        1 => {
            let mut v_info_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_kind_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_args_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1337_);
            leanh::lean_dec(v_h__3_1336_);
            leanh::lean_dec(v_h__2_1335_);
            v_info_1340_ = leanh::lean_ctor_get(v_x_1333_, 0);
            leanh::lean_inc(v_info_1340_);
            v_kind_1341_ = leanh::lean_ctor_get(v_x_1333_, 1);
            leanh::lean_inc(v_kind_1341_);
            v_args_1342_ = leanh::lean_ctor_get(v_x_1333_, 2);
            leanh::lean_inc_ref(v_args_1342_);
            leanh::lean_dec_ref_known(v_x_1333_, 3);
            v___x_1343_ =
                leanh::lean_apply_3(v_h__1_1334_, v_info_1340_, v_kind_1341_, v_args_1342_);
            return v___x_1343_;
        }
        2 => {
            let mut v_info_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1337_);
            leanh::lean_dec(v_h__2_1335_);
            leanh::lean_dec(v_h__1_1334_);
            v_info_1344_ = leanh::lean_ctor_get(v_x_1333_, 0);
            leanh::lean_inc(v_info_1344_);
            v_val_1345_ = leanh::lean_ctor_get(v_x_1333_, 1);
            leanh::lean_inc_ref(v_val_1345_);
            leanh::lean_dec_ref_known(v_x_1333_, 2);
            v___x_1346_ = leanh::lean_apply_2(v_h__3_1336_, v_info_1344_, v_val_1345_);
            return v___x_1346_;
        }
        _ => {
            let mut v_info_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rawVal_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_preresolved_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1337_);
            leanh::lean_dec(v_h__3_1336_);
            leanh::lean_dec(v_h__1_1334_);
            v_info_1347_ = leanh::lean_ctor_get(v_x_1333_, 0);
            leanh::lean_inc(v_info_1347_);
            v_rawVal_1348_ = leanh::lean_ctor_get(v_x_1333_, 1);
            leanh::lean_inc_ref(v_rawVal_1348_);
            v_val_1349_ = leanh::lean_ctor_get(v_x_1333_, 2);
            leanh::lean_inc(v_val_1349_);
            v_preresolved_1350_ = leanh::lean_ctor_get(v_x_1333_, 3);
            leanh::lean_inc(v_preresolved_1350_);
            leanh::lean_dec_ref_known(v_x_1333_, 4);
            v___x_1351_ = leanh::lean_apply_4(
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
    mut v_x_1352_: *mut leanh::LeanObject,
    mut v_h__1_1353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1354_ = leanh::lean_apply_2(v_h__1_1353_, v_x_1352_, leanh::lean_box(0));
    return v___x_1354_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(
    mut v_00_u03b1_1355_: *mut leanh::LeanObject,
    mut v_P_1356_: *mut leanh::LeanObject,
    mut v_motive_1357_: *mut leanh::LeanObject,
    mut v_x_1358_: *mut leanh::LeanObject,
    mut v_h__1_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = leanh::lean_apply_2(v_h__1_1359_, v_x_1358_, leanh::lean_box(0));
    return v___x_1360_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(
    mut v_text_1361_: *mut leanh::LeanObject,
    mut v_pos_1362_: *mut leanh::LeanObject,
    mut v_str_1363_: *mut leanh::LeanObject,
    mut v_x_1364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1365_ = leanh::lean_ctor_get(v_x_1364_, 0);
                v_snd_1366_ = leanh::lean_ctor_get(v_x_1364_, 1);
                v_isSharedCheck_1374_ = (!leanh::lean_is_exclusive(v_x_1364_)) as u8;
                if v_isSharedCheck_1374_ == 0 {
                    v___x_1368_ = v_x_1364_;
                    v_isShared_1369_ = v_isSharedCheck_1374_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1366_);
                    leanh::lean_inc(v_fst_1365_);
                    leanh::lean_dec(v_x_1364_);
                    v___x_1368_ = leanh::lean_box(0);
                    v_isShared_1369_ = v_isSharedCheck_1374_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1370_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1361_, v_pos_1362_, v_str_1363_, v_fst_1365_);
                if v_isShared_1369_ == 0 {
                    leanh::lean_ctor_set(v___x_1368_, 0, v___x_1370_);
                    v___x_1372_ = v___x_1368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1373_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_snd_1366_);
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
    mut v_text_1375_: *mut leanh::LeanObject,
    mut v_pos_1376_: *mut leanh::LeanObject,
    mut v_str_1377_: *mut leanh::LeanObject,
    mut v_x_1378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(
        v_text_1375_,
        v_pos_1376_,
        v_str_1377_,
        v_x_1378_,
    );
    leanh::lean_dec_ref(v_str_1377_);
    leanh::lean_dec_ref(v_text_1375_);
    return v_res_1379_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(
    mut v_env_1399_: *mut leanh::LeanObject,
    mut v_p_1400_: *mut leanh::LeanObject,
    mut v_ictx_1401_: *mut leanh::LeanObject,
    mut v_s_1402_: *mut leanh::LeanObject,
    mut v_text_1403_: *mut leanh::LeanObject,
    mut v_pos_1404_: *mut leanh::LeanObject,
    mut v_str_1405_: *mut leanh::LeanObject,
    mut v___f_1406_: *mut leanh::LeanObject,
    mut v_inst_1407_: *mut leanh::LeanObject,
    mut v_inst_1408_: *mut leanh::LeanObject,
    mut v_toApplicative_1409_: *mut leanh::LeanObject,
    mut v_____do__lift_1410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: u8 = 0;
    let mut v_stxStack_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1428_: u8 = 0;
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1433_: usize = 0;
    let mut v___x_1434_: usize = 0;
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1446_: u8 = 0;
    let mut v_unexpectedTk_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unexpected_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1460_: u8 = 0;
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut v_stxStack_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1411_ = leanh::lean_box(0);
                v___x_1412_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_env_1399_);
                v___x_1413_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1413_, 0, v_env_1399_);
                leanh::lean_ctor_set(v___x_1413_, 1, v_____do__lift_1410_);
                leanh::lean_ctor_set(v___x_1413_, 2, v___x_1411_);
                leanh::lean_ctor_set(v___x_1413_, 3, v___x_1412_);
                v___x_1414_ = l_Lean_Parser_getTokenTable(v_env_1399_);
                leanh::lean_inc_ref(v_ictx_1401_);
                v_s_1415_ = l_Lean_Parser_ParserFn_run(
                    v_p_1400_,
                    v_ictx_1401_,
                    v___x_1413_,
                    v___x_1414_,
                    v_s_1402_,
                );
                leanh::lean_inc_ref(v_s_1415_);
                v___x_1416_ = l_Lean_Parser_ParserState_allErrors(v_s_1415_);
                v___x_1417_ = lean_array_get_size(v___x_1416_);
                leanh::lean_dec_ref(v___x_1416_);
                v___x_1418_ = leanh::lean_unsigned_to_nat(0);
                v___x_1419_ = lean_nat_dec_eq(v___x_1417_, v___x_1418_);
                if v___x_1419_ == 0 {
                    leanh::lean_dec_ref(v_toApplicative_1409_);
                    v_stxStack_1420_ = leanh::lean_ctor_get(v_s_1415_, 0);
                    v_lhsPrec_1421_ = leanh::lean_ctor_get(v_s_1415_, 1);
                    v_pos_1422_ = leanh::lean_ctor_get(v_s_1415_, 2);
                    v_cache_1423_ = leanh::lean_ctor_get(v_s_1415_, 3);
                    v_errorMsg_1424_ = leanh::lean_ctor_get(v_s_1415_, 4);
                    v_recoveredErrors_1425_ = leanh::lean_ctor_get(v_s_1415_, 5);
                    v_isSharedCheck_1462_ = (!leanh::lean_is_exclusive(v_s_1415_)) as u8;
                    if v_isSharedCheck_1462_ == 0 {
                        v___x_1427_ = v_s_1415_;
                        v_isShared_1428_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_recoveredErrors_1425_);
                        leanh::lean_inc(v_errorMsg_1424_);
                        leanh::lean_inc(v_cache_1423_);
                        leanh::lean_inc(v_pos_1422_);
                        leanh::lean_inc(v_lhsPrec_1421_);
                        leanh::lean_inc(v_stxStack_1420_);
                        leanh::lean_dec(v_s_1415_);
                        v___x_1427_ = leanh::lean_box(0);
                        v_isShared_1428_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_1406_);
                    v_stxStack_1463_ = leanh::lean_ctor_get(v_s_1415_, 0);
                    leanh::lean_inc_ref(v_stxStack_1463_);
                    v_pos_1464_ = leanh::lean_ctor_get(v_s_1415_, 2);
                    leanh::lean_inc(v_pos_1464_);
                    v___x_1465_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1401_, v_pos_1464_);
                    leanh::lean_dec(v_pos_1464_);
                    if v___x_1465_ == 0 {
                        leanh::lean_dec_ref(v_stxStack_1463_);
                        leanh::lean_dec_ref(v_toApplicative_1409_);
                        leanh::lean_dec(v_pos_1404_);
                        v___x_1466_ = l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0;
                        v___x_1467_ = l_Lean_Parser_ParserState_mkError(v_s_1415_, v___x_1466_);
                        v___x_1468_ =
                            l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1401_, v___x_1467_);
                        v___x_1469_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1469_, 0, v___x_1468_);
                        v___x_1470_ = l_Lean_MessageData_ofFormat(v___x_1469_);
                        v___x_1471_ =
                            l_Lean_throwError___redArg(v_inst_1407_, v_inst_1408_, v___x_1470_);
                        return v___x_1471_;
                    } else {
                        leanh::lean_dec_ref(v_s_1415_);
                        leanh::lean_dec_ref(v_inst_1408_);
                        leanh::lean_dec_ref(v_inst_1407_);
                        leanh::lean_dec_ref(v_ictx_1401_);
                        v_toPure_1472_ = leanh::lean_ctor_get(v_toApplicative_1409_, 1);
                        leanh::lean_inc(v_toPure_1472_);
                        leanh::lean_dec_ref(v_toApplicative_1409_);
                        v___x_1473_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1463_);
                        leanh::lean_dec_ref(v_stxStack_1463_);
                        v___x_1474_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_1403_, v_pos_1404_, v_str_1405_, v___x_1473_);
                        v___x_1475_ = leanh::lean_apply_2(
                            v_toPure_1472_,
                            leanh::lean_box(0),
                            v___x_1474_,
                        );
                        return v___x_1475_;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_pos_1404_);
                v___x_1429_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1403_, v_pos_1404_, v_str_1405_, v_pos_1422_);
                if leanh::lean_obj_tag(v_errorMsg_1424_) == 0 {
                    leanh::lean_dec(v_pos_1404_);
                    v___y_1431_ = v_errorMsg_1424_;
                    state = 2;
                    continue;
                } else {
                    v_val_1443_ = leanh::lean_ctor_get(v_errorMsg_1424_, 0);
                    v_isSharedCheck_1461_ =
                        (!leanh::lean_is_exclusive(v_errorMsg_1424_)) as u8;
                    if v_isSharedCheck_1461_ == 0 {
                        v___x_1445_ = v_errorMsg_1424_;
                        v_isShared_1446_ = v_isSharedCheck_1461_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1443_);
                        leanh::lean_dec(v_errorMsg_1424_);
                        v___x_1445_ = leanh::lean_box(0);
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
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1432_,
                    v___f_1406_,
                    v_sz_1433_,
                    v___x_1434_,
                    v_recoveredErrors_1425_,
                );
                if v_isShared_1428_ == 0 {
                    leanh::lean_ctor_set(v___x_1427_, 5, v___x_1435_);
                    leanh::lean_ctor_set(v___x_1427_, 4, v___y_1431_);
                    leanh::lean_ctor_set(v___x_1427_, 2, v___x_1429_);
                    v_s_1437_ = v___x_1427_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_stxStack_1420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_lhsPrec_1421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 2, v___x_1429_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_cache_1423_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 4, v___y_1431_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 5, v___x_1435_);
                    v_s_1437_ = v_reuseFailAlloc_1442_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1438_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1401_, v_s_1437_);
                v___x_1439_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1439_, 0, v___x_1438_);
                v___x_1440_ = l_Lean_MessageData_ofFormat(v___x_1439_);
                v___x_1441_ = l_Lean_throwError___redArg(v_inst_1407_, v_inst_1408_, v___x_1440_);
                return v___x_1441_;
            }
            4 => {
                v_unexpectedTk_1447_ = leanh::lean_ctor_get(v_val_1443_, 0);
                v_unexpected_1448_ = leanh::lean_ctor_get(v_val_1443_, 1);
                v_expected_1449_ = leanh::lean_ctor_get(v_val_1443_, 2);
                v_isSharedCheck_1460_ = (!leanh::lean_is_exclusive(v_val_1443_)) as u8;
                if v_isSharedCheck_1460_ == 0 {
                    v___x_1451_ = v_val_1443_;
                    v_isShared_1452_ = v_isSharedCheck_1460_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_expected_1449_);
                    leanh::lean_inc(v_unexpected_1448_);
                    leanh::lean_inc(v_unexpectedTk_1447_);
                    leanh::lean_dec(v_val_1443_);
                    v___x_1451_ = leanh::lean_box(0);
                    v_isShared_1452_ = v_isSharedCheck_1460_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1453_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_1403_, v_pos_1404_, v_str_1405_, v_unexpectedTk_1447_);
                if v_isShared_1452_ == 0 {
                    leanh::lean_ctor_set(v___x_1451_, 0, v___x_1453_);
                    v___x_1455_ = v___x_1451_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1459_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1453_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_unexpected_1448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_expected_1449_);
                    v___x_1455_ = v_reuseFailAlloc_1459_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1446_ == 0 {
                    leanh::lean_ctor_set(v___x_1445_, 0, v___x_1455_);
                    v___x_1457_ = v___x_1445_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1458_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
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
    mut v_env_1476_: *mut leanh::LeanObject,
    mut v_p_1477_: *mut leanh::LeanObject,
    mut v_ictx_1478_: *mut leanh::LeanObject,
    mut v_s_1479_: *mut leanh::LeanObject,
    mut v_text_1480_: *mut leanh::LeanObject,
    mut v_pos_1481_: *mut leanh::LeanObject,
    mut v_str_1482_: *mut leanh::LeanObject,
    mut v___f_1483_: *mut leanh::LeanObject,
    mut v_inst_1484_: *mut leanh::LeanObject,
    mut v_inst_1485_: *mut leanh::LeanObject,
    mut v_toApplicative_1486_: *mut leanh::LeanObject,
    mut v_____do__lift_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_str_1482_);
    leanh::lean_dec_ref(v_text_1480_);
    return v_res_1488_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(
    mut v_str_1489_: *mut leanh::LeanObject,
    mut v_env_1490_: *mut leanh::LeanObject,
    mut v_p_1491_: *mut leanh::LeanObject,
    mut v_text_1492_: *mut leanh::LeanObject,
    mut v_pos_1493_: *mut leanh::LeanObject,
    mut v___f_1494_: *mut leanh::LeanObject,
    mut v_inst_1495_: *mut leanh::LeanObject,
    mut v_inst_1496_: *mut leanh::LeanObject,
    mut v_toApplicative_1497_: *mut leanh::LeanObject,
    mut v_toBind_1498_: *mut leanh::LeanObject,
    mut v_inst_1499_: *mut leanh::LeanObject,
    mut v_____do__lift_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1501_: u8 = 0;
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ictx_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1501_ = 1;
    v___x_1502_ = lean_string_utf8_byte_size(v_str_1489_);
    leanh::lean_inc_ref(v_str_1489_);
    v_ictx_1503_ = l_Lean_Parser_mkInputContext___redArg(
        v_str_1489_,
        v_____do__lift_1500_,
        v___x_1501_,
        v___x_1502_,
    );
    v_s_1504_ = l_Lean_Parser_mkParserState(v_str_1489_);
    v___f_1505_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_1505_, 0, v_env_1490_);
    leanh::lean_closure_set(v___f_1505_, 1, v_p_1491_);
    leanh::lean_closure_set(v___f_1505_, 2, v_ictx_1503_);
    leanh::lean_closure_set(v___f_1505_, 3, v_s_1504_);
    leanh::lean_closure_set(v___f_1505_, 4, v_text_1492_);
    leanh::lean_closure_set(v___f_1505_, 5, v_pos_1493_);
    leanh::lean_closure_set(v___f_1505_, 6, v_str_1489_);
    leanh::lean_closure_set(v___f_1505_, 7, v___f_1494_);
    leanh::lean_closure_set(v___f_1505_, 8, v_inst_1495_);
    leanh::lean_closure_set(v___f_1505_, 9, v_inst_1496_);
    leanh::lean_closure_set(v___f_1505_, 10, v_toApplicative_1497_);
    v___x_1506_ = leanh::lean_apply_4(
        v_toBind_1498_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1499_,
        v___f_1505_,
    );
    return v___x_1506_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(
    mut v_inst_1507_: *mut leanh::LeanObject,
    mut v_strLit_1508_: *mut leanh::LeanObject,
    mut v_text_1509_: *mut leanh::LeanObject,
    mut v_env_1510_: *mut leanh::LeanObject,
    mut v_p_1511_: *mut leanh::LeanObject,
    mut v_inst_1512_: *mut leanh::LeanObject,
    mut v_inst_1513_: *mut leanh::LeanObject,
    mut v_toApplicative_1514_: *mut leanh::LeanObject,
    mut v_toBind_1515_: *mut leanh::LeanObject,
    mut v_inst_1516_: *mut leanh::LeanObject,
    mut v_pos_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getFileName_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getFileName_1518_ = leanh::lean_ctor_get(v_inst_1507_, 2);
    leanh::lean_inc(v_getFileName_1518_);
    leanh::lean_dec_ref(v_inst_1507_);
    v_str_1519_ = l_Lean_TSyntax_getString(v_strLit_1508_);
    leanh::lean_inc_ref(v_str_1519_);
    leanh::lean_inc(v_pos_1517_);
    leanh::lean_inc_ref(v_text_1509_);
    v___f_1520_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1520_, 0, v_text_1509_);
    leanh::lean_closure_set(v___f_1520_, 1, v_pos_1517_);
    leanh::lean_closure_set(v___f_1520_, 2, v_str_1519_);
    leanh::lean_inc(v_toBind_1515_);
    v___f_1521_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__2 as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_1521_, 0, v_str_1519_);
    leanh::lean_closure_set(v___f_1521_, 1, v_env_1510_);
    leanh::lean_closure_set(v___f_1521_, 2, v_p_1511_);
    leanh::lean_closure_set(v___f_1521_, 3, v_text_1509_);
    leanh::lean_closure_set(v___f_1521_, 4, v_pos_1517_);
    leanh::lean_closure_set(v___f_1521_, 5, v___f_1520_);
    leanh::lean_closure_set(v___f_1521_, 6, v_inst_1512_);
    leanh::lean_closure_set(v___f_1521_, 7, v_inst_1513_);
    leanh::lean_closure_set(v___f_1521_, 8, v_toApplicative_1514_);
    leanh::lean_closure_set(v___f_1521_, 9, v_toBind_1515_);
    leanh::lean_closure_set(v___f_1521_, 10, v_inst_1516_);
    v___x_1522_ = leanh::lean_apply_4(
        v_toBind_1515_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getFileName_1518_,
        v___f_1521_,
    );
    return v___x_1522_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(
    mut v_inst_1523_: *mut leanh::LeanObject,
    mut v_strLit_1524_: *mut leanh::LeanObject,
    mut v_text_1525_: *mut leanh::LeanObject,
    mut v_env_1526_: *mut leanh::LeanObject,
    mut v_p_1527_: *mut leanh::LeanObject,
    mut v_inst_1528_: *mut leanh::LeanObject,
    mut v_inst_1529_: *mut leanh::LeanObject,
    mut v_toApplicative_1530_: *mut leanh::LeanObject,
    mut v_toBind_1531_: *mut leanh::LeanObject,
    mut v_inst_1532_: *mut leanh::LeanObject,
    mut v_pos_1533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_strLit_1524_);
    return v_res_1534_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(
    mut v___f_1535_: *mut leanh::LeanObject,
    mut v_pos_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1537_ = leanh::lean_apply_1(v___f_1535_, v_pos_1536_);
    return v___x_1537_;
}
pub unsafe fn _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0;
    v___x_1540_ = l_Lean_stringToMessageData(v___x_1539_);
    return v___x_1540_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(
    mut v_text_1541_: *mut leanh::LeanObject,
    mut v_inst_1542_: *mut leanh::LeanObject,
    mut v_inst_1543_: *mut leanh::LeanObject,
    mut v_strLit_1544_: *mut leanh::LeanObject,
    mut v_toBind_1545_: *mut leanh::LeanObject,
    mut v___f_1546_: *mut leanh::LeanObject,
    mut v_toApplicative_1547_: *mut leanh::LeanObject,
    mut v___f_1548_: *mut leanh::LeanObject,
    mut v_____r_1549_: *mut leanh::LeanObject,
    mut v_pos_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_source_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u32 = 0;
    let mut v___x_1553_: u32 = 0;
    let mut v___x_1554_: u8 = 0;
    v_source_1551_ = leanh::lean_ctor_get(v_text_1541_, 0);
    v___x_1552_ = lean_string_utf8_get(v_source_1551_, v_pos_1550_);
    v___x_1553_ = 34;
    v___x_1554_ = lean_uint32_dec_eq(v___x_1552_, v___x_1553_);
    if v___x_1554_ == 0 {
        let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_1548_);
        leanh::lean_dec_ref(v_toApplicative_1547_);
        v___x_1555_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once
            ),
            _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1,
        );
        v___x_1556_ =
            l_Lean_throwErrorAt___redArg(v_inst_1542_, v_inst_1543_, v_strLit_1544_, v___x_1555_);
        v___x_1557_ = leanh::lean_apply_4(
            v_toBind_1545_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1556_,
            v___f_1546_,
        );
        return v___x_1557_;
    } else {
        let mut v_toPure_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_1546_);
        leanh::lean_dec(v_strLit_1544_);
        leanh::lean_dec_ref(v_inst_1543_);
        leanh::lean_dec_ref(v_inst_1542_);
        v_toPure_1558_ = leanh::lean_ctor_get(v_toApplicative_1547_, 1);
        leanh::lean_inc(v_toPure_1558_);
        leanh::lean_dec_ref(v_toApplicative_1547_);
        v___x_1559_ = lean_string_utf8_next(v_source_1551_, v_pos_1550_);
        v___x_1560_ =
            leanh::lean_apply_2(v_toPure_1558_, leanh::lean_box(0), v___x_1559_);
        v___x_1561_ = leanh::lean_apply_4(
            v_toBind_1545_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1560_,
            v___f_1548_,
        );
        return v___x_1561_;
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed(
    mut v_text_1562_: *mut leanh::LeanObject,
    mut v_inst_1563_: *mut leanh::LeanObject,
    mut v_inst_1564_: *mut leanh::LeanObject,
    mut v_strLit_1565_: *mut leanh::LeanObject,
    mut v_toBind_1566_: *mut leanh::LeanObject,
    mut v___f_1567_: *mut leanh::LeanObject,
    mut v_toApplicative_1568_: *mut leanh::LeanObject,
    mut v___f_1569_: *mut leanh::LeanObject,
    mut v_____r_1570_: *mut leanh::LeanObject,
    mut v_pos_1571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_pos_1571_);
    leanh::lean_dec_ref(v_text_1562_);
    return v_res_1572_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(
    mut v___f_1573_: *mut leanh::LeanObject,
    mut v_____s_1574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = leanh::lean_box(0);
    v___x_1576_ = leanh::lean_apply_2(v___f_1573_, v___x_1575_, v_____s_1574_);
    return v___x_1576_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(
    mut v_toPure_1577_: *mut leanh::LeanObject,
    mut v_____do__lift_1578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_a_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1596_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_1578_) == 0 {
                    v_a_1579_ = leanh::lean_ctor_get(v_____do__lift_1578_, 0);
                    v_isSharedCheck_1587_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_1578_)) as u8;
                    if v_isSharedCheck_1587_ == 0 {
                        v___x_1581_ = v_____do__lift_1578_;
                        v_isShared_1582_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1579_);
                        leanh::lean_dec(v_____do__lift_1578_);
                        v___x_1581_ = leanh::lean_box(0);
                        v_isShared_1582_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1588_ = leanh::lean_ctor_get(v_____do__lift_1578_, 0);
                    v_isSharedCheck_1596_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_1578_)) as u8;
                    if v_isSharedCheck_1596_ == 0 {
                        v___x_1590_ = v_____do__lift_1578_;
                        v_isShared_1591_ = v_isSharedCheck_1596_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1588_);
                        leanh::lean_dec(v_____do__lift_1578_);
                        v___x_1590_ = leanh::lean_box(0);
                        v_isShared_1591_ = v_isSharedCheck_1596_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1582_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1581_, 1);
                    v___x_1584_ = v___x_1581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1579_);
                    v___x_1584_ = v_reuseFailAlloc_1586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1585_ = leanh::lean_apply_2(
                    v_toPure_1577_,
                    leanh::lean_box(0),
                    v___x_1584_,
                );
                return v___x_1585_;
            }
            3 => {
                if v_isShared_1591_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1590_, 0);
                    v___x_1593_ = v___x_1590_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1588_);
                    v___x_1593_ = v_reuseFailAlloc_1595_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1594_ = leanh::lean_apply_2(
                    v_toPure_1577_,
                    leanh::lean_box(0),
                    v___x_1593_,
                );
                return v___x_1594_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(
    mut v_source_1597_: *mut leanh::LeanObject,
    mut v_toPure_1598_: *mut leanh::LeanObject,
    mut v_toBind_1599_: *mut leanh::LeanObject,
    mut v___f_1600_: *mut leanh::LeanObject,
    mut v_b_1601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1602_: u32 = 0;
    let mut v___x_1603_: u32 = 0;
    let mut v___x_1604_: u8 = 0;
    v___x_1602_ = lean_string_utf8_get(v_source_1597_, v_b_1601_);
    v___x_1603_ = 35;
    v___x_1604_ = lean_uint32_dec_eq(v___x_1602_, v___x_1603_);
    if v___x_1604_ == 0 {
        let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1605_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1605_, 0, v_b_1601_);
        v___x_1606_ =
            leanh::lean_apply_2(v_toPure_1598_, leanh::lean_box(0), v___x_1605_);
        v___x_1607_ = leanh::lean_apply_4(
            v_toBind_1599_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1606_,
            v___f_1600_,
        );
        return v___x_1607_;
    } else {
        let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1608_ = lean_string_utf8_next(v_source_1597_, v_b_1601_);
        leanh::lean_dec(v_b_1601_);
        v___x_1609_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1609_, 0, v___x_1608_);
        v___x_1610_ =
            leanh::lean_apply_2(v_toPure_1598_, leanh::lean_box(0), v___x_1609_);
        v___x_1611_ = leanh::lean_apply_4(
            v_toBind_1599_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1610_,
            v___f_1600_,
        );
        return v___x_1611_;
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(
    mut v_source_1612_: *mut leanh::LeanObject,
    mut v_toPure_1613_: *mut leanh::LeanObject,
    mut v_toBind_1614_: *mut leanh::LeanObject,
    mut v___f_1615_: *mut leanh::LeanObject,
    mut v_b_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1617_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(
        v_source_1612_,
        v_toPure_1613_,
        v_toBind_1614_,
        v___f_1615_,
        v_b_1616_,
    );
    leanh::lean_dec_ref(v_source_1612_);
    return v_res_1617_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(
    mut v_text_1618_: *mut leanh::LeanObject,
    mut v___f_1619_: *mut leanh::LeanObject,
    mut v_toApplicative_1620_: *mut leanh::LeanObject,
    mut v_toBind_1621_: *mut leanh::LeanObject,
    mut v_inst_1622_: *mut leanh::LeanObject,
    mut v___f_1623_: *mut leanh::LeanObject,
    mut v_____x_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u32 = 0;
    let mut v___x_1628_: u32 = 0;
    let mut v___x_1629_: u8 = 0;
    v_start_1625_ = leanh::lean_ctor_get(v_____x_1624_, 0);
    leanh::lean_inc(v_start_1625_);
    leanh::lean_dec_ref(v_____x_1624_);
    v_source_1626_ = leanh::lean_ctor_get(v_text_1618_, 0);
    leanh::lean_inc_ref(v_source_1626_);
    leanh::lean_dec_ref(v_text_1618_);
    v___x_1627_ = lean_string_utf8_get(v_source_1626_, v_start_1625_);
    v___x_1628_ = 114;
    v___x_1629_ = lean_uint32_dec_eq(v___x_1627_, v___x_1628_);
    if v___x_1629_ == 0 {
        let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_source_1626_);
        leanh::lean_dec(v___f_1623_);
        leanh::lean_dec_ref(v_inst_1622_);
        leanh::lean_dec(v_toBind_1621_);
        leanh::lean_dec_ref(v_toApplicative_1620_);
        v___x_1630_ = leanh::lean_box(0);
        v___x_1631_ = leanh::lean_apply_2(v___f_1619_, v___x_1630_, v_start_1625_);
        return v___x_1631_;
    } else {
        let mut v_toPure_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_1619_);
        v_toPure_1632_ = leanh::lean_ctor_get(v_toApplicative_1620_, 1);
        leanh::lean_inc_n(v_toPure_1632_, 2);
        leanh::lean_dec_ref(v_toApplicative_1620_);
        v_pos_1633_ = lean_string_utf8_next(v_source_1626_, v_start_1625_);
        leanh::lean_dec(v_start_1625_);
        v___f_1634_ = leanh::lean_alloc_closure(
            l_Lean_Doc_parseQuotedStrLit___redArg___lam__7 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_1634_, 0, v_toPure_1632_);
        leanh::lean_inc(v_toBind_1621_);
        v___f_1635_ = leanh::lean_alloc_closure(
            l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1635_, 0, v_source_1626_);
        leanh::lean_closure_set(v___f_1635_, 1, v_toPure_1632_);
        leanh::lean_closure_set(v___f_1635_, 2, v_toBind_1621_);
        leanh::lean_closure_set(v___f_1635_, 3, v___f_1634_);
        v___x_1636_ = l___private_Init_While_0__whileM_erased___redArg(
            v_inst_1622_,
            v___f_1635_,
            v_pos_1633_,
        );
        v___x_1637_ = leanh::lean_apply_4(
            v_toBind_1621_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1636_,
            v___f_1623_,
        );
        return v___x_1637_;
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(
    mut v_inst_1638_: *mut leanh::LeanObject,
    mut v_strLit_1639_: *mut leanh::LeanObject,
    mut v_text_1640_: *mut leanh::LeanObject,
    mut v_p_1641_: *mut leanh::LeanObject,
    mut v_inst_1642_: *mut leanh::LeanObject,
    mut v_inst_1643_: *mut leanh::LeanObject,
    mut v_toApplicative_1644_: *mut leanh::LeanObject,
    mut v_toBind_1645_: *mut leanh::LeanObject,
    mut v_inst_1646_: *mut leanh::LeanObject,
    mut v_env_1647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_toBind_1645_, 3);
    leanh::lean_inc_ref_n(v_toApplicative_1644_, 2);
    leanh::lean_inc_ref(v_inst_1643_);
    leanh::lean_inc_ref_n(v_inst_1642_, 3);
    leanh::lean_inc_ref_n(v_text_1640_, 2);
    leanh::lean_inc_n(v_strLit_1639_, 2);
    v___f_1648_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_1648_, 0, v_inst_1638_);
    leanh::lean_closure_set(v___f_1648_, 1, v_strLit_1639_);
    leanh::lean_closure_set(v___f_1648_, 2, v_text_1640_);
    leanh::lean_closure_set(v___f_1648_, 3, v_env_1647_);
    leanh::lean_closure_set(v___f_1648_, 4, v_p_1641_);
    leanh::lean_closure_set(v___f_1648_, 5, v_inst_1642_);
    leanh::lean_closure_set(v___f_1648_, 6, v_inst_1643_);
    leanh::lean_closure_set(v___f_1648_, 7, v_toApplicative_1644_);
    leanh::lean_closure_set(v___f_1648_, 8, v_toBind_1645_);
    leanh::lean_closure_set(v___f_1648_, 9, v_inst_1646_);
    v___f_1649_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__4 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1649_, 0, v___f_1648_);
    leanh::lean_inc_ref(v___f_1649_);
    v___f_1650_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    leanh::lean_closure_set(v___f_1650_, 0, v_text_1640_);
    leanh::lean_closure_set(v___f_1650_, 1, v_inst_1642_);
    leanh::lean_closure_set(v___f_1650_, 2, v_inst_1643_);
    leanh::lean_closure_set(v___f_1650_, 3, v_strLit_1639_);
    leanh::lean_closure_set(v___f_1650_, 4, v_toBind_1645_);
    leanh::lean_closure_set(v___f_1650_, 5, v___f_1649_);
    leanh::lean_closure_set(v___f_1650_, 6, v_toApplicative_1644_);
    leanh::lean_closure_set(v___f_1650_, 7, v___f_1649_);
    leanh::lean_inc_ref(v___f_1650_);
    v___f_1651_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1651_, 0, v___f_1650_);
    v___f_1652_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__9 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_1652_, 0, v_text_1640_);
    leanh::lean_closure_set(v___f_1652_, 1, v___f_1650_);
    leanh::lean_closure_set(v___f_1652_, 2, v_toApplicative_1644_);
    leanh::lean_closure_set(v___f_1652_, 3, v_toBind_1645_);
    leanh::lean_closure_set(v___f_1652_, 4, v_inst_1642_);
    leanh::lean_closure_set(v___f_1652_, 5, v___f_1651_);
    v___x_1653_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_1642_,
        v_strLit_1639_,
    );
    leanh::lean_dec(v_strLit_1639_);
    v___x_1654_ = leanh::lean_apply_4(
        v_toBind_1645_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1653_,
        v___f_1652_,
    );
    return v___x_1654_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(
    mut v_inst_1655_: *mut leanh::LeanObject,
    mut v_inst_1656_: *mut leanh::LeanObject,
    mut v_strLit_1657_: *mut leanh::LeanObject,
    mut v_p_1658_: *mut leanh::LeanObject,
    mut v_inst_1659_: *mut leanh::LeanObject,
    mut v_inst_1660_: *mut leanh::LeanObject,
    mut v_toApplicative_1661_: *mut leanh::LeanObject,
    mut v_toBind_1662_: *mut leanh::LeanObject,
    mut v_inst_1663_: *mut leanh::LeanObject,
    mut v_text_1664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getEnv_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getEnv_1665_ = leanh::lean_ctor_get(v_inst_1655_, 0);
    leanh::lean_inc(v_getEnv_1665_);
    leanh::lean_dec_ref(v_inst_1655_);
    leanh::lean_inc(v_toBind_1662_);
    v___f_1666_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__10 as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_1666_, 0, v_inst_1656_);
    leanh::lean_closure_set(v___f_1666_, 1, v_strLit_1657_);
    leanh::lean_closure_set(v___f_1666_, 2, v_text_1664_);
    leanh::lean_closure_set(v___f_1666_, 3, v_p_1658_);
    leanh::lean_closure_set(v___f_1666_, 4, v_inst_1659_);
    leanh::lean_closure_set(v___f_1666_, 5, v_inst_1660_);
    leanh::lean_closure_set(v___f_1666_, 6, v_toApplicative_1661_);
    leanh::lean_closure_set(v___f_1666_, 7, v_toBind_1662_);
    leanh::lean_closure_set(v___f_1666_, 8, v_inst_1663_);
    v___x_1667_ = leanh::lean_apply_4(
        v_toBind_1662_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1665_,
        v___f_1666_,
    );
    return v___x_1667_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg(
    mut v_inst_1668_: *mut leanh::LeanObject,
    mut v_inst_1669_: *mut leanh::LeanObject,
    mut v_inst_1670_: *mut leanh::LeanObject,
    mut v_inst_1671_: *mut leanh::LeanObject,
    mut v_inst_1672_: *mut leanh::LeanObject,
    mut v_inst_1673_: *mut leanh::LeanObject,
    mut v_p_1674_: *mut leanh::LeanObject,
    mut v_strLit_1675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1676_ = leanh::lean_ctor_get(v_inst_1668_, 0);
    leanh::lean_inc_ref(v_toApplicative_1676_);
    v_toBind_1677_ = leanh::lean_ctor_get(v_inst_1668_, 1);
    leanh::lean_inc_n(v_toBind_1677_, 2);
    v___f_1678_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__11 as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_1678_, 0, v_inst_1670_);
    leanh::lean_closure_set(v___f_1678_, 1, v_inst_1672_);
    leanh::lean_closure_set(v___f_1678_, 2, v_strLit_1675_);
    leanh::lean_closure_set(v___f_1678_, 3, v_p_1674_);
    leanh::lean_closure_set(v___f_1678_, 4, v_inst_1668_);
    leanh::lean_closure_set(v___f_1678_, 5, v_inst_1671_);
    leanh::lean_closure_set(v___f_1678_, 6, v_toApplicative_1676_);
    leanh::lean_closure_set(v___f_1678_, 7, v_toBind_1677_);
    leanh::lean_closure_set(v___f_1678_, 8, v_inst_1673_);
    v___x_1679_ = leanh::lean_apply_4(
        v_toBind_1677_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1669_,
        v___f_1678_,
    );
    return v___x_1679_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit(
    mut v_m_1680_: *mut leanh::LeanObject,
    mut v_inst_1681_: *mut leanh::LeanObject,
    mut v_inst_1682_: *mut leanh::LeanObject,
    mut v_inst_1683_: *mut leanh::LeanObject,
    mut v_inst_1684_: *mut leanh::LeanObject,
    mut v_inst_1685_: *mut leanh::LeanObject,
    mut v_inst_1686_: *mut leanh::LeanObject,
    mut v_p_1687_: *mut leanh::LeanObject,
    mut v_strLit_1688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_s_1690_: *mut leanh::LeanObject,
    mut v_toPure_1691_: *mut leanh::LeanObject,
    mut v_err_1692_: u8,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stxStack_1693_ = leanh::lean_ctor_get(v_s_1690_, 0);
    v___x_1694_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1693_);
    v___x_1695_ = leanh::lean_box((v_err_1692_) as usize);
    v___x_1696_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1696_, 0, v___x_1694_);
    leanh::lean_ctor_set(v___x_1696_, 1, v___x_1695_);
    v___x_1697_ =
        leanh::lean_apply_2(v_toPure_1691_, leanh::lean_box(0), v___x_1696_);
    return v___x_1697_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed(
    mut v_s_1698_: *mut leanh::LeanObject,
    mut v_toPure_1699_: *mut leanh::LeanObject,
    mut v_err_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_err_boxed_1701_: u8 = 0;
    let mut v_res_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_err_boxed_1701_ = (leanh::lean_unbox(v_err_1700_) as u8);
    v_res_1702_ =
        l_Lean_Doc_parseStrLit_x27___redArg___lam__0(v_s_1698_, v_toPure_1699_, v_err_boxed_1701_);
    leanh::lean_dec_ref(v_s_1698_);
    return v_res_1702_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__1(
    mut v___f_1703_: *mut leanh::LeanObject,
    mut v_err_1704_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = leanh::lean_box((v_err_1704_) as usize);
    v___x_1706_ = leanh::lean_apply_1(v___f_1703_, v___x_1705_);
    return v___x_1706_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed(
    mut v___f_1707_: *mut leanh::LeanObject,
    mut v_err_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_err_boxed_1709_: u8 = 0;
    let mut v_res_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_err_boxed_1709_ = (leanh::lean_unbox(v_err_1708_) as u8);
    v_res_1710_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__1(v___f_1707_, v_err_boxed_1709_);
    return v_res_1710_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__2(
    mut v_toPure_1711_: *mut leanh::LeanObject,
    mut v___x_1712_: u8,
    mut v_toBind_1713_: *mut leanh::LeanObject,
    mut v___f_1714_: *mut leanh::LeanObject,
    mut v_____r_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = leanh::lean_box((v___x_1712_) as usize);
    v___x_1717_ =
        leanh::lean_apply_2(v_toPure_1711_, leanh::lean_box(0), v___x_1716_);
    v___x_1718_ = leanh::lean_apply_4(
        v_toBind_1713_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1717_,
        v___f_1714_,
    );
    return v___x_1718_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(
    mut v_toPure_1719_: *mut leanh::LeanObject,
    mut v___x_1720_: *mut leanh::LeanObject,
    mut v_toBind_1721_: *mut leanh::LeanObject,
    mut v___f_1722_: *mut leanh::LeanObject,
    mut v_____r_1723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_559__boxed_1724_: u8 = 0;
    let mut v_res_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_559__boxed_1724_ = (leanh::lean_unbox(v___x_1720_) as u8);
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
    mut v_env_1726_: *mut leanh::LeanObject,
    mut v_p_1727_: *mut leanh::LeanObject,
    mut v_ictx_1728_: *mut leanh::LeanObject,
    mut v_s_1729_: *mut leanh::LeanObject,
    mut v_toPure_1730_: *mut leanh::LeanObject,
    mut v___x_1731_: u8,
    mut v_toBind_1732_: *mut leanh::LeanObject,
    mut v_inst_1733_: *mut leanh::LeanObject,
    mut v_inst_1734_: *mut leanh::LeanObject,
    mut v_inst_1735_: *mut leanh::LeanObject,
    mut v_inst_1736_: *mut leanh::LeanObject,
    mut v_____do__lift_1737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: u8 = 0;
    v___x_1738_ = leanh::lean_box(0);
    v___x_1739_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_env_1726_);
    v___x_1740_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1740_, 0, v_env_1726_);
    leanh::lean_ctor_set(v___x_1740_, 1, v_____do__lift_1737_);
    leanh::lean_ctor_set(v___x_1740_, 2, v___x_1738_);
    leanh::lean_ctor_set(v___x_1740_, 3, v___x_1739_);
    v___x_1741_ = l_Lean_Parser_getTokenTable(v_env_1726_);
    leanh::lean_inc_ref(v_ictx_1728_);
    v_s_1742_ =
        l_Lean_Parser_ParserFn_run(v_p_1727_, v_ictx_1728_, v___x_1740_, v___x_1741_, v_s_1729_);
    leanh::lean_inc(v_toPure_1730_);
    leanh::lean_inc_ref_n(v_s_1742_, 2);
    v___f_1743_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1743_, 0, v_s_1742_);
    leanh::lean_closure_set(v___f_1743_, 1, v_toPure_1730_);
    v___x_1744_ = l_Lean_Parser_ParserState_allErrors(v_s_1742_);
    v___x_1745_ = lean_array_get_size(v___x_1744_);
    leanh::lean_dec_ref(v___x_1744_);
    v___x_1746_ = leanh::lean_unsigned_to_nat(0);
    v___x_1747_ = lean_nat_dec_eq(v___x_1745_, v___x_1746_);
    if v___x_1747_ == 0 {
        let mut v___f_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_1748_ = leanh::lean_alloc_closure(
            l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_1748_, 0, v___f_1743_);
        v___x_1749_ = leanh::lean_box((v___x_1731_) as usize);
        leanh::lean_inc(v_toBind_1732_);
        v___f_1750_ = leanh::lean_alloc_closure(
            l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1750_, 0, v_toPure_1730_);
        leanh::lean_closure_set(v___f_1750_, 1, v___x_1749_);
        leanh::lean_closure_set(v___f_1750_, 2, v_toBind_1732_);
        leanh::lean_closure_set(v___f_1750_, 3, v___f_1748_);
        v___x_1751_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1728_, v_s_1742_);
        v___x_1752_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1752_, 0, v___x_1751_);
        v___x_1753_ = l_Lean_MessageData_ofFormat(v___x_1752_);
        v___x_1754_ = l_Lean_logError___redArg(
            v_inst_1733_,
            v_inst_1734_,
            v_inst_1735_,
            v_inst_1736_,
            v___x_1753_,
        );
        v___x_1755_ = leanh::lean_apply_4(
            v_toBind_1732_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1754_,
            v___f_1750_,
        );
        return v___x_1755_;
    } else {
        let mut v_pos_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: u8 = 0;
        v_pos_1756_ = leanh::lean_ctor_get(v_s_1742_, 2);
        leanh::lean_inc(v_pos_1756_);
        v___x_1757_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1728_, v_pos_1756_);
        leanh::lean_dec(v_pos_1756_);
        if v___x_1757_ == 0 {
            let mut v___f_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___f_1758_ = leanh::lean_alloc_closure(
                l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            leanh::lean_closure_set(v___f_1758_, 0, v___f_1743_);
            v___x_1759_ = leanh::lean_box((v___x_1731_) as usize);
            leanh::lean_inc(v_toBind_1732_);
            v___f_1760_ = leanh::lean_alloc_closure(
                l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed as *mut core::ffi::c_void,
                5,
                4,
            );
            leanh::lean_closure_set(v___f_1760_, 0, v_toPure_1730_);
            leanh::lean_closure_set(v___f_1760_, 1, v___x_1759_);
            leanh::lean_closure_set(v___f_1760_, 2, v_toBind_1732_);
            leanh::lean_closure_set(v___f_1760_, 3, v___f_1758_);
            v___x_1761_ = l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0;
            v___x_1762_ = l_Lean_Parser_ParserState_mkError(v_s_1742_, v___x_1761_);
            v___x_1763_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1728_, v___x_1762_);
            v___x_1764_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1764_, 0, v___x_1763_);
            v___x_1765_ = l_Lean_MessageData_ofFormat(v___x_1764_);
            v___x_1766_ = l_Lean_logError___redArg(
                v_inst_1733_,
                v_inst_1734_,
                v_inst_1735_,
                v_inst_1736_,
                v___x_1765_,
            );
            v___x_1767_ = leanh::lean_apply_4(
                v_toBind_1732_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1766_,
                v___f_1760_,
            );
            return v___x_1767_;
        } else {
            let mut v___f_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1769_: u8 = 0;
            let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_s_1742_);
            leanh::lean_dec(v_inst_1736_);
            leanh::lean_dec(v_inst_1735_);
            leanh::lean_dec_ref(v_inst_1734_);
            leanh::lean_dec_ref(v_inst_1733_);
            leanh::lean_dec_ref(v_ictx_1728_);
            v___f_1768_ = leanh::lean_alloc_closure(
                l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            leanh::lean_closure_set(v___f_1768_, 0, v___f_1743_);
            v___x_1769_ = 0;
            v___x_1770_ = leanh::lean_box((v___x_1769_) as usize);
            v___x_1771_ =
                leanh::lean_apply_2(v_toPure_1730_, leanh::lean_box(0), v___x_1770_);
            v___x_1772_ = leanh::lean_apply_4(
                v_toBind_1732_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1771_,
                v___f_1768_,
            );
            return v___x_1772_;
        }
    }
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(
    mut v_env_1773_: *mut leanh::LeanObject,
    mut v_p_1774_: *mut leanh::LeanObject,
    mut v_ictx_1775_: *mut leanh::LeanObject,
    mut v_s_1776_: *mut leanh::LeanObject,
    mut v_toPure_1777_: *mut leanh::LeanObject,
    mut v___x_1778_: *mut leanh::LeanObject,
    mut v_toBind_1779_: *mut leanh::LeanObject,
    mut v_inst_1780_: *mut leanh::LeanObject,
    mut v_inst_1781_: *mut leanh::LeanObject,
    mut v_inst_1782_: *mut leanh::LeanObject,
    mut v_inst_1783_: *mut leanh::LeanObject,
    mut v_____do__lift_1784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_575__boxed_1785_: u8 = 0;
    let mut v_res_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_575__boxed_1785_ = (leanh::lean_unbox(v___x_1778_) as u8);
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
    mut v_source_1787_: *mut leanh::LeanObject,
    mut v___x_1788_: u8,
    mut v___y_1789_: *mut leanh::LeanObject,
    mut v_env_1790_: *mut leanh::LeanObject,
    mut v_p_1791_: *mut leanh::LeanObject,
    mut v_toPure_1792_: *mut leanh::LeanObject,
    mut v_toBind_1793_: *mut leanh::LeanObject,
    mut v_inst_1794_: *mut leanh::LeanObject,
    mut v_inst_1795_: *mut leanh::LeanObject,
    mut v_inst_1796_: *mut leanh::LeanObject,
    mut v_inst_1797_: *mut leanh::LeanObject,
    mut v_s_1798_: *mut leanh::LeanObject,
    mut v___x_1799_: *mut leanh::LeanObject,
    mut v_____do__lift_1800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ictx_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_source_1787_);
                v_ictx_1801_ = l_Lean_Parser_mkInputContext___redArg(
                    v_source_1787_,
                    v_____do__lift_1800_,
                    v___x_1788_,
                    v___y_1789_,
                );
                v___x_1802_ = l_Lean_Parser_mkParserState(v_source_1787_);
                leanh::lean_dec_ref(v_source_1787_);
                v___x_1809_ = l_Lean_Syntax_getPos_x3f(v_s_1798_, v___x_1788_);
                if leanh::lean_obj_tag(v___x_1809_) == 0 {
                    v___x_1810_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_1811_ = l_panic___redArg(v___x_1799_, v___x_1810_);
                    v___y_1804_ = v___x_1811_;
                    state = 1;
                    continue;
                } else {
                    v_val_1812_ = leanh::lean_ctor_get(v___x_1809_, 0);
                    leanh::lean_inc(v_val_1812_);
                    leanh::lean_dec_ref_known(v___x_1809_, 1);
                    v___y_1804_ = v_val_1812_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_s_1805_ = l_Lean_Parser_ParserState_setPos(v___x_1802_, v___y_1804_);
                v___x_1806_ = leanh::lean_box((v___x_1788_) as usize);
                leanh::lean_inc(v_inst_1797_);
                leanh::lean_inc(v_toBind_1793_);
                v___f_1807_ = leanh::lean_alloc_closure(
                    l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed as *mut core::ffi::c_void,
                    12,
                    11,
                );
                leanh::lean_closure_set(v___f_1807_, 0, v_env_1790_);
                leanh::lean_closure_set(v___f_1807_, 1, v_p_1791_);
                leanh::lean_closure_set(v___f_1807_, 2, v_ictx_1801_);
                leanh::lean_closure_set(v___f_1807_, 3, v_s_1805_);
                leanh::lean_closure_set(v___f_1807_, 4, v_toPure_1792_);
                leanh::lean_closure_set(v___f_1807_, 5, v___x_1806_);
                leanh::lean_closure_set(v___f_1807_, 6, v_toBind_1793_);
                leanh::lean_closure_set(v___f_1807_, 7, v_inst_1794_);
                leanh::lean_closure_set(v___f_1807_, 8, v_inst_1795_);
                leanh::lean_closure_set(v___f_1807_, 9, v_inst_1796_);
                leanh::lean_closure_set(v___f_1807_, 10, v_inst_1797_);
                v___x_1808_ = leanh::lean_apply_4(
                    v_toBind_1793_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_source_1813_: *mut leanh::LeanObject,
    mut v___x_1814_: *mut leanh::LeanObject,
    mut v___y_1815_: *mut leanh::LeanObject,
    mut v_env_1816_: *mut leanh::LeanObject,
    mut v_p_1817_: *mut leanh::LeanObject,
    mut v_toPure_1818_: *mut leanh::LeanObject,
    mut v_toBind_1819_: *mut leanh::LeanObject,
    mut v_inst_1820_: *mut leanh::LeanObject,
    mut v_inst_1821_: *mut leanh::LeanObject,
    mut v_inst_1822_: *mut leanh::LeanObject,
    mut v_inst_1823_: *mut leanh::LeanObject,
    mut v_s_1824_: *mut leanh::LeanObject,
    mut v___x_1825_: *mut leanh::LeanObject,
    mut v_____do__lift_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_668__boxed_1827_: u8 = 0;
    let mut v_res_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_668__boxed_1827_ = (leanh::lean_unbox(v___x_1814_) as u8);
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
    leanh::lean_dec(v___x_1825_);
    leanh::lean_dec(v_s_1824_);
    return v_res_1828_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__4(
    mut v_text_1829_: *mut leanh::LeanObject,
    mut v_inst_1830_: *mut leanh::LeanObject,
    mut v_p_1831_: *mut leanh::LeanObject,
    mut v_toPure_1832_: *mut leanh::LeanObject,
    mut v_toBind_1833_: *mut leanh::LeanObject,
    mut v_inst_1834_: *mut leanh::LeanObject,
    mut v_inst_1835_: *mut leanh::LeanObject,
    mut v_inst_1836_: *mut leanh::LeanObject,
    mut v_s_1837_: *mut leanh::LeanObject,
    mut v___x_1838_: *mut leanh::LeanObject,
    mut v_env_1839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1840_: u8 = 0;
    let mut v___y_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getFileName_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: u8 = 0;
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1840_ = 1;
                v___x_1853_ = l_Lean_Syntax_getTailPos_x3f(v_s_1837_, v___x_1840_);
                if leanh::lean_obj_tag(v___x_1853_) == 0 {
                    v___x_1854_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_1855_ = l_panic___redArg(v___x_1838_, v___x_1854_);
                    v___y_1849_ = v___x_1855_;
                    state = 2;
                    continue;
                } else {
                    v_val_1856_ = leanh::lean_ctor_get(v___x_1853_, 0);
                    leanh::lean_inc(v_val_1856_);
                    leanh::lean_dec_ref_known(v___x_1853_, 1);
                    v___y_1849_ = v_val_1856_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v_getFileName_1844_ = leanh::lean_ctor_get(v_inst_1830_, 2);
                leanh::lean_inc(v_getFileName_1844_);
                v___x_1845_ = leanh::lean_box((v___x_1840_) as usize);
                leanh::lean_inc(v_toBind_1833_);
                v___f_1846_ = leanh::lean_alloc_closure(
                    l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed as *mut core::ffi::c_void,
                    14,
                    13,
                );
                leanh::lean_closure_set(v___f_1846_, 0, v___y_1842_);
                leanh::lean_closure_set(v___f_1846_, 1, v___x_1845_);
                leanh::lean_closure_set(v___f_1846_, 2, v___y_1843_);
                leanh::lean_closure_set(v___f_1846_, 3, v_env_1839_);
                leanh::lean_closure_set(v___f_1846_, 4, v_p_1831_);
                leanh::lean_closure_set(v___f_1846_, 5, v_toPure_1832_);
                leanh::lean_closure_set(v___f_1846_, 6, v_toBind_1833_);
                leanh::lean_closure_set(v___f_1846_, 7, v_inst_1834_);
                leanh::lean_closure_set(v___f_1846_, 8, v_inst_1830_);
                leanh::lean_closure_set(v___f_1846_, 9, v_inst_1835_);
                leanh::lean_closure_set(v___f_1846_, 10, v_inst_1836_);
                leanh::lean_closure_set(v___f_1846_, 11, v_s_1837_);
                leanh::lean_closure_set(v___f_1846_, 12, v___x_1838_);
                v___x_1847_ = leanh::lean_apply_4(
                    v_toBind_1833_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_getFileName_1844_,
                    v___f_1846_,
                );
                return v___x_1847_;
            }
            2 => {
                v_source_1850_ = leanh::lean_ctor_get(v_text_1829_, 0);
                leanh::lean_inc_ref(v_source_1850_);
                leanh::lean_dec_ref(v_text_1829_);
                v___x_1851_ = lean_string_utf8_byte_size(v_source_1850_);
                v___x_1852_ = lean_nat_dec_le(v___y_1849_, v___x_1851_);
                if v___x_1852_ == 0 {
                    leanh::lean_dec(v___y_1849_);
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
    mut v_inst_1857_: *mut leanh::LeanObject,
    mut v_inst_1858_: *mut leanh::LeanObject,
    mut v_p_1859_: *mut leanh::LeanObject,
    mut v_toPure_1860_: *mut leanh::LeanObject,
    mut v_toBind_1861_: *mut leanh::LeanObject,
    mut v_inst_1862_: *mut leanh::LeanObject,
    mut v_inst_1863_: *mut leanh::LeanObject,
    mut v_inst_1864_: *mut leanh::LeanObject,
    mut v_s_1865_: *mut leanh::LeanObject,
    mut v___x_1866_: *mut leanh::LeanObject,
    mut v_text_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getEnv_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getEnv_1868_ = leanh::lean_ctor_get(v_inst_1857_, 0);
    leanh::lean_inc(v_getEnv_1868_);
    leanh::lean_dec_ref(v_inst_1857_);
    leanh::lean_inc(v_toBind_1861_);
    v___f_1869_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit_x27___redArg___lam__4 as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_1869_, 0, v_text_1867_);
    leanh::lean_closure_set(v___f_1869_, 1, v_inst_1858_);
    leanh::lean_closure_set(v___f_1869_, 2, v_p_1859_);
    leanh::lean_closure_set(v___f_1869_, 3, v_toPure_1860_);
    leanh::lean_closure_set(v___f_1869_, 4, v_toBind_1861_);
    leanh::lean_closure_set(v___f_1869_, 5, v_inst_1862_);
    leanh::lean_closure_set(v___f_1869_, 6, v_inst_1863_);
    leanh::lean_closure_set(v___f_1869_, 7, v_inst_1864_);
    leanh::lean_closure_set(v___f_1869_, 8, v_s_1865_);
    leanh::lean_closure_set(v___f_1869_, 9, v___x_1866_);
    v___x_1870_ = leanh::lean_apply_4(
        v_toBind_1861_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1868_,
        v___f_1869_,
    );
    return v___x_1870_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg(
    mut v_inst_1871_: *mut leanh::LeanObject,
    mut v_inst_1872_: *mut leanh::LeanObject,
    mut v_inst_1873_: *mut leanh::LeanObject,
    mut v_inst_1874_: *mut leanh::LeanObject,
    mut v_inst_1875_: *mut leanh::LeanObject,
    mut v_inst_1876_: *mut leanh::LeanObject,
    mut v_p_1877_: *mut leanh::LeanObject,
    mut v_s_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1879_ = leanh::lean_ctor_get(v_inst_1871_, 0);
    v_toBind_1880_ = leanh::lean_ctor_get(v_inst_1871_, 1);
    leanh::lean_inc_n(v_toBind_1880_, 2);
    v_toPure_1881_ = leanh::lean_ctor_get(v_toApplicative_1879_, 1);
    leanh::lean_inc(v_toPure_1881_);
    v___x_1882_ = leanh::lean_unsigned_to_nat(0);
    v___f_1883_ = leanh::lean_alloc_closure(
        l_Lean_Doc_parseStrLit_x27___redArg___lam__5 as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_1883_, 0, v_inst_1873_);
    leanh::lean_closure_set(v___f_1883_, 1, v_inst_1875_);
    leanh::lean_closure_set(v___f_1883_, 2, v_p_1877_);
    leanh::lean_closure_set(v___f_1883_, 3, v_toPure_1881_);
    leanh::lean_closure_set(v___f_1883_, 4, v_toBind_1880_);
    leanh::lean_closure_set(v___f_1883_, 5, v_inst_1871_);
    leanh::lean_closure_set(v___f_1883_, 6, v_inst_1874_);
    leanh::lean_closure_set(v___f_1883_, 7, v_inst_1876_);
    leanh::lean_closure_set(v___f_1883_, 8, v_s_1878_);
    leanh::lean_closure_set(v___f_1883_, 9, v___x_1882_);
    v___x_1884_ = leanh::lean_apply_4(
        v_toBind_1880_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1872_,
        v___f_1883_,
    );
    return v___x_1884_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27(
    mut v_m_1885_: *mut leanh::LeanObject,
    mut v_inst_1886_: *mut leanh::LeanObject,
    mut v_inst_1887_: *mut leanh::LeanObject,
    mut v_inst_1888_: *mut leanh::LeanObject,
    mut v_inst_1889_: *mut leanh::LeanObject,
    mut v_inst_1890_: *mut leanh::LeanObject,
    mut v_inst_1891_: *mut leanh::LeanObject,
    mut v_p_1892_: *mut leanh::LeanObject,
    mut v_s_1893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
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
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Mem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DocString_Builtin_Parsing(
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
pub unsafe fn initialize_Lean_Elab_DocString_Builtin_Parsing(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Mem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
}