// Lean compiler output
// Module: Lean.Elab.DocString.Builtin.Parsing
// Imports: Lean.Parser.Extension Init.While Init.Data.Array.Attach Init.Data.Array.Mem
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_get, lean_string_utf8_next, lean_string_utf8_prev,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_sub, lean_string_utf8_byte_size, lean_uint32_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0_value: LeanStringObject<13> =
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
        m_data: [101, 110, 100, 32, 111, 102, 32, 105, 110, 112, 117, 116, 0],
    };
static mut l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            78, 111, 116, 32, 97, 32, 113, 117, 111, 116, 101, 100, 32, 115, 116, 114, 105, 110,
            103, 32, 108, 105, 116, 101, 114, 97, 108, 0,
        ],
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    v___x_951_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2;
    v___x_952_ = lean_unsigned_to_nat(14);
    v___x_953_ = lean_unsigned_to_nat(22);
    v___x_954_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1;
    v___x_955_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0;
    v___x_956_ =
        l_mkPanicMessageWithDecl(v___x_955_, v___x_954_, v___x_953_, v___x_952_, v___x_951_);
    return v___x_956_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
    mut v_inst_957_: *mut LeanObject,
    mut v_s_958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_965_: u8 = 0;
    let mut v_toPure_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_971_: u8 = 0;
    let mut v_unused_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___y_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_984_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_973_ = lean_unsigned_to_nat(0);
                v___x_974_ = 1;
                v___x_981_ = l_Lean_Syntax_getPos_x3f(v_s_958_, v___x_974_);
                if lean_obj_tag(v___x_981_) == 0 {
                    v___x_982_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_983_ = l_panic___redArg(v___x_973_, v___x_982_);
                    v___y_976_ = v___x_983_;
                    state = 4;
                    continue;
                } else {
                    v_val_984_ = lean_ctor_get(v___x_981_, 0);
                    lean_inc(v_val_984_);
                    lean_dec_ref_known(v___x_981_, 1);
                    v___y_976_ = v_val_984_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v_toApplicative_962_ = lean_ctor_get(v_inst_957_, 0);
                v_isSharedCheck_971_ = (!lean_is_exclusive(v_inst_957_)) as u8;
                if v_isSharedCheck_971_ == 0 {
                    v_unused_972_ = lean_ctor_get(v_inst_957_, 1);
                    lean_dec(v_unused_972_);
                    v___x_964_ = v_inst_957_;
                    v_isShared_965_ = v_isSharedCheck_971_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toApplicative_962_);
                    lean_dec(v_inst_957_);
                    v___x_964_ = lean_box(0);
                    v_isShared_965_ = v_isSharedCheck_971_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toPure_966_ = lean_ctor_get(v_toApplicative_962_, 1);
                lean_inc(v_toPure_966_);
                lean_dec_ref(v_toApplicative_962_);
                if v_isShared_965_ == 0 {
                    lean_ctor_set(v___x_964_, 1, v___y_961_);
                    lean_ctor_set(v___x_964_, 0, v___y_960_);
                    v___x_968_ = v___x_964_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_970_, 0, v___y_960_);
                    lean_ctor_set(v_reuseFailAlloc_970_, 1, v___y_961_);
                    v___x_968_ = v_reuseFailAlloc_970_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_969_ = lean_apply_2(v_toPure_966_, lean_box(0), v___x_968_);
                return v___x_969_;
            }
            4 => {
                v___x_977_ = l_Lean_Syntax_getTailPos_x3f(v_s_958_, v___x_974_);
                if lean_obj_tag(v___x_977_) == 0 {
                    v___x_978_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_979_ = l_panic___redArg(v___x_973_, v___x_978_);
                    v___y_960_ = v___y_976_;
                    v___y_961_ = v___x_979_;
                    state = 1;
                    continue;
                } else {
                    v_val_980_ = lean_ctor_get(v___x_977_, 0);
                    lean_inc(v_val_980_);
                    lean_dec_ref_known(v___x_977_, 1);
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
    mut v_inst_985_: *mut LeanObject,
    mut v_s_986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_987_: *mut LeanObject = core::ptr::null_mut();
    v_res_987_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_985_,
        v_s_986_,
    );
    lean_dec(v_s_986_);
    return v_res_987_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(
    mut v_m_988_: *mut LeanObject,
    mut v_inst_989_: *mut LeanObject,
    mut v_inst_990_: *mut LeanObject,
    mut v_s_991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    v___x_992_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_989_,
        v_s_991_,
    );
    return v___x_992_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___boxed(
    mut v_m_993_: *mut LeanObject,
    mut v_inst_994_: *mut LeanObject,
    mut v_inst_995_: *mut LeanObject,
    mut v_s_996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_997_: *mut LeanObject = core::ptr::null_mut();
    v_res_997_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(
        v_m_993_,
        v_inst_994_,
        v_inst_995_,
        v_s_996_,
    );
    lean_dec(v_s_996_);
    lean_dec(v_inst_995_);
    return v_res_997_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__0(
    mut v_env_999_: *mut LeanObject,
    mut v_p_1000_: *mut LeanObject,
    mut v_ictx_1001_: *mut LeanObject,
    mut v_s_1002_: *mut LeanObject,
    mut v_inst_1003_: *mut LeanObject,
    mut v_inst_1004_: *mut LeanObject,
    mut v_toApplicative_1005_: *mut LeanObject,
    mut v_____do__lift_1006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: u8 = 0;
    v___x_1007_ = lean_box(0);
    v___x_1008_ = lean_box(0);
    lean_inc_ref(v_env_999_);
    v___x_1009_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1009_, 0, v_env_999_);
    lean_ctor_set(v___x_1009_, 1, v_____do__lift_1006_);
    lean_ctor_set(v___x_1009_, 2, v___x_1007_);
    lean_ctor_set(v___x_1009_, 3, v___x_1008_);
    v___x_1010_ = l_Lean_Parser_getTokenTable(v_env_999_);
    lean_inc_ref(v_ictx_1001_);
    v_s_1011_ =
        l_Lean_Parser_ParserFn_run(v_p_1000_, v_ictx_1001_, v___x_1009_, v___x_1010_, v_s_1002_);
    lean_inc_ref(v_s_1011_);
    v___x_1012_ = l_Lean_Parser_ParserState_allErrors(v_s_1011_);
    v___x_1013_ = lean_array_get_size(v___x_1012_);
    lean_dec_ref(v___x_1012_);
    v___x_1014_ = lean_unsigned_to_nat(0);
    v___x_1015_ = lean_nat_dec_eq(v___x_1013_, v___x_1014_);
    if v___x_1015_ == 0 {
        let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_1005_);
        v___x_1016_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1001_, v_s_1011_);
        v___x_1017_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_1017_, 0, v___x_1016_);
        v___x_1018_ = l_Lean_MessageData_ofFormat(v___x_1017_);
        v___x_1019_ = l_Lean_throwError___redArg(v_inst_1003_, v_inst_1004_, v___x_1018_);
        return v___x_1019_;
    } else {
        let mut v_stxStack_1020_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pos_1021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1022_: u8 = 0;
        v_stxStack_1020_ = lean_ctor_get(v_s_1011_, 0);
        lean_inc_ref(v_stxStack_1020_);
        v_pos_1021_ = lean_ctor_get(v_s_1011_, 2);
        lean_inc(v_pos_1021_);
        v___x_1022_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1001_, v_pos_1021_);
        lean_dec(v_pos_1021_);
        if v___x_1022_ == 0 {
            let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_stxStack_1020_);
            lean_dec_ref(v_toApplicative_1005_);
            v___x_1023_ = l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0;
            v___x_1024_ = l_Lean_Parser_ParserState_mkError(v_s_1011_, v___x_1023_);
            v___x_1025_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1001_, v___x_1024_);
            v___x_1026_ = lean_alloc_ctor(3, 1, (0) as u32);
            lean_ctor_set(v___x_1026_, 0, v___x_1025_);
            v___x_1027_ = l_Lean_MessageData_ofFormat(v___x_1026_);
            v___x_1028_ = l_Lean_throwError___redArg(v_inst_1003_, v_inst_1004_, v___x_1027_);
            return v___x_1028_;
        } else {
            let mut v_toPure_1029_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_s_1011_);
            lean_dec_ref(v_inst_1004_);
            lean_dec_ref(v_inst_1003_);
            lean_dec_ref(v_ictx_1001_);
            v_toPure_1029_ = lean_ctor_get(v_toApplicative_1005_, 1);
            lean_inc(v_toPure_1029_);
            lean_dec_ref(v_toApplicative_1005_);
            v___x_1030_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1020_);
            lean_dec_ref(v_stxStack_1020_);
            v___x_1031_ = lean_apply_2(v_toPure_1029_, lean_box(0), v___x_1030_);
            return v___x_1031_;
        }
    }
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__1(
    mut v_source_1032_: *mut LeanObject,
    mut v___y_1033_: *mut LeanObject,
    mut v_start_1034_: *mut LeanObject,
    mut v_env_1035_: *mut LeanObject,
    mut v_p_1036_: *mut LeanObject,
    mut v_inst_1037_: *mut LeanObject,
    mut v_inst_1038_: *mut LeanObject,
    mut v_toApplicative_1039_: *mut LeanObject,
    mut v_toBind_1040_: *mut LeanObject,
    mut v_inst_1041_: *mut LeanObject,
    mut v_____do__lift_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1043_: u8 = 0;
    let mut v_ictx_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    v___x_1043_ = 1;
    lean_inc_ref(v_source_1032_);
    v_ictx_1044_ = l_Lean_Parser_mkInputContext___redArg(
        v_source_1032_,
        v_____do__lift_1042_,
        v___x_1043_,
        v___y_1033_,
    );
    v___x_1045_ = l_Lean_Parser_mkParserState(v_source_1032_);
    lean_dec_ref(v_source_1032_);
    v_s_1046_ = l_Lean_Parser_ParserState_setPos(v___x_1045_, v_start_1034_);
    v___f_1047_ = lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__0 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1047_, 0, v_env_1035_);
    lean_closure_set(v___f_1047_, 1, v_p_1036_);
    lean_closure_set(v___f_1047_, 2, v_ictx_1044_);
    lean_closure_set(v___f_1047_, 3, v_s_1046_);
    lean_closure_set(v___f_1047_, 4, v_inst_1037_);
    lean_closure_set(v___f_1047_, 5, v_inst_1038_);
    lean_closure_set(v___f_1047_, 6, v_toApplicative_1039_);
    v___x_1048_ = lean_apply_4(
        v_toBind_1040_,
        lean_box(0),
        lean_box(0),
        v_inst_1041_,
        v___f_1047_,
    );
    return v___x_1048_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__2(
    mut v_text_1049_: *mut LeanObject,
    mut v_inst_1050_: *mut LeanObject,
    mut v_env_1051_: *mut LeanObject,
    mut v_p_1052_: *mut LeanObject,
    mut v_inst_1053_: *mut LeanObject,
    mut v_inst_1054_: *mut LeanObject,
    mut v_toApplicative_1055_: *mut LeanObject,
    mut v_toBind_1056_: *mut LeanObject,
    mut v_inst_1057_: *mut LeanObject,
    mut v_____x_1058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getFileName_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_1059_ = lean_ctor_get(v_____x_1058_, 0);
                lean_inc(v_start_1059_);
                v_stop_1060_ = lean_ctor_get(v_____x_1058_, 1);
                lean_inc(v_stop_1060_);
                lean_dec_ref(v_____x_1058_);
                v_source_1061_ = lean_ctor_get(v_text_1049_, 0);
                lean_inc_ref(v_source_1061_);
                lean_dec_ref(v_text_1049_);
                v___x_1067_ = lean_string_utf8_byte_size(v_source_1061_);
                v___x_1068_ = lean_nat_dec_le(v_stop_1060_, v___x_1067_);
                if v___x_1068_ == 0 {
                    lean_dec(v_stop_1060_);
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
                v_getFileName_1064_ = lean_ctor_get(v_inst_1050_, 2);
                lean_inc(v_getFileName_1064_);
                lean_dec_ref(v_inst_1050_);
                lean_inc(v_toBind_1056_);
                v___f_1065_ = lean_alloc_closure(
                    l_Lean_Doc_parseStrLit___redArg___lam__1 as *mut core::ffi::c_void,
                    11,
                    10,
                );
                lean_closure_set(v___f_1065_, 0, v_source_1061_);
                lean_closure_set(v___f_1065_, 1, v___y_1063_);
                lean_closure_set(v___f_1065_, 2, v_start_1059_);
                lean_closure_set(v___f_1065_, 3, v_env_1051_);
                lean_closure_set(v___f_1065_, 4, v_p_1052_);
                lean_closure_set(v___f_1065_, 5, v_inst_1053_);
                lean_closure_set(v___f_1065_, 6, v_inst_1054_);
                lean_closure_set(v___f_1065_, 7, v_toApplicative_1055_);
                lean_closure_set(v___f_1065_, 8, v_toBind_1056_);
                lean_closure_set(v___f_1065_, 9, v_inst_1057_);
                v___x_1066_ = lean_apply_4(
                    v_toBind_1056_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_text_1069_: *mut LeanObject,
    mut v_inst_1070_: *mut LeanObject,
    mut v_p_1071_: *mut LeanObject,
    mut v_inst_1072_: *mut LeanObject,
    mut v_inst_1073_: *mut LeanObject,
    mut v_toApplicative_1074_: *mut LeanObject,
    mut v_toBind_1075_: *mut LeanObject,
    mut v_inst_1076_: *mut LeanObject,
    mut v_s_1077_: *mut LeanObject,
    mut v_env_1078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_1075_);
    lean_inc_ref(v_inst_1072_);
    v___f_1079_ = lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_1079_, 0, v_text_1069_);
    lean_closure_set(v___f_1079_, 1, v_inst_1070_);
    lean_closure_set(v___f_1079_, 2, v_env_1078_);
    lean_closure_set(v___f_1079_, 3, v_p_1071_);
    lean_closure_set(v___f_1079_, 4, v_inst_1072_);
    lean_closure_set(v___f_1079_, 5, v_inst_1073_);
    lean_closure_set(v___f_1079_, 6, v_toApplicative_1074_);
    lean_closure_set(v___f_1079_, 7, v_toBind_1075_);
    lean_closure_set(v___f_1079_, 8, v_inst_1076_);
    v___x_1080_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_1072_,
        v_s_1077_,
    );
    v___x_1081_ = lean_apply_4(
        v_toBind_1075_,
        lean_box(0),
        lean_box(0),
        v___x_1080_,
        v___f_1079_,
    );
    return v___x_1081_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__3___boxed(
    mut v_text_1082_: *mut LeanObject,
    mut v_inst_1083_: *mut LeanObject,
    mut v_p_1084_: *mut LeanObject,
    mut v_inst_1085_: *mut LeanObject,
    mut v_inst_1086_: *mut LeanObject,
    mut v_toApplicative_1087_: *mut LeanObject,
    mut v_toBind_1088_: *mut LeanObject,
    mut v_inst_1089_: *mut LeanObject,
    mut v_s_1090_: *mut LeanObject,
    mut v_env_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1092_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_s_1090_);
    return v_res_1092_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg___lam__4(
    mut v_inst_1093_: *mut LeanObject,
    mut v_inst_1094_: *mut LeanObject,
    mut v_p_1095_: *mut LeanObject,
    mut v_inst_1096_: *mut LeanObject,
    mut v_inst_1097_: *mut LeanObject,
    mut v_toApplicative_1098_: *mut LeanObject,
    mut v_toBind_1099_: *mut LeanObject,
    mut v_inst_1100_: *mut LeanObject,
    mut v_s_1101_: *mut LeanObject,
    mut v_text_1102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getEnv_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    v_getEnv_1103_ = lean_ctor_get(v_inst_1093_, 0);
    lean_inc(v_getEnv_1103_);
    lean_dec_ref(v_inst_1093_);
    lean_inc(v_toBind_1099_);
    v___f_1104_ = lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__3___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_1104_, 0, v_text_1102_);
    lean_closure_set(v___f_1104_, 1, v_inst_1094_);
    lean_closure_set(v___f_1104_, 2, v_p_1095_);
    lean_closure_set(v___f_1104_, 3, v_inst_1096_);
    lean_closure_set(v___f_1104_, 4, v_inst_1097_);
    lean_closure_set(v___f_1104_, 5, v_toApplicative_1098_);
    lean_closure_set(v___f_1104_, 6, v_toBind_1099_);
    lean_closure_set(v___f_1104_, 7, v_inst_1100_);
    lean_closure_set(v___f_1104_, 8, v_s_1101_);
    v___x_1105_ = lean_apply_4(
        v_toBind_1099_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1103_,
        v___f_1104_,
    );
    return v___x_1105_;
}
pub unsafe fn l_Lean_Doc_parseStrLit___redArg(
    mut v_inst_1106_: *mut LeanObject,
    mut v_inst_1107_: *mut LeanObject,
    mut v_inst_1108_: *mut LeanObject,
    mut v_inst_1109_: *mut LeanObject,
    mut v_inst_1110_: *mut LeanObject,
    mut v_inst_1111_: *mut LeanObject,
    mut v_p_1112_: *mut LeanObject,
    mut v_s_1113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1114_ = lean_ctor_get(v_inst_1106_, 0);
    lean_inc_ref(v_toApplicative_1114_);
    v_toBind_1115_ = lean_ctor_get(v_inst_1106_, 1);
    lean_inc_n(v_toBind_1115_, 2);
    v___f_1116_ = lean_alloc_closure(
        l_Lean_Doc_parseStrLit___redArg___lam__4 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_1116_, 0, v_inst_1108_);
    lean_closure_set(v___f_1116_, 1, v_inst_1110_);
    lean_closure_set(v___f_1116_, 2, v_p_1112_);
    lean_closure_set(v___f_1116_, 3, v_inst_1106_);
    lean_closure_set(v___f_1116_, 4, v_inst_1109_);
    lean_closure_set(v___f_1116_, 5, v_toApplicative_1114_);
    lean_closure_set(v___f_1116_, 6, v_toBind_1115_);
    lean_closure_set(v___f_1116_, 7, v_inst_1111_);
    lean_closure_set(v___f_1116_, 8, v_s_1113_);
    v___x_1117_ = lean_apply_4(
        v_toBind_1115_,
        lean_box(0),
        lean_box(0),
        v_inst_1107_,
        v___f_1116_,
    );
    return v___x_1117_;
}
pub unsafe fn l_Lean_Doc_parseStrLit(
    mut v_m_1118_: *mut LeanObject,
    mut v_inst_1119_: *mut LeanObject,
    mut v_inst_1120_: *mut LeanObject,
    mut v_inst_1121_: *mut LeanObject,
    mut v_inst_1122_: *mut LeanObject,
    mut v_inst_1123_: *mut LeanObject,
    mut v_inst_1124_: *mut LeanObject,
    mut v_p_1125_: *mut LeanObject,
    mut v_s_1126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_str_1128_: *mut LeanObject,
    mut v_a_1129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1130_ = lean_ctor_get(v_a_1129_, 0);
                v_snd_1131_ = lean_ctor_get(v_a_1129_, 1);
                v_isSharedCheck_1147_ = (!lean_is_exclusive(v_a_1129_)) as u8;
                if v_isSharedCheck_1147_ == 0 {
                    v___x_1133_ = v_a_1129_;
                    v_isShared_1134_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1131_);
                    lean_inc(v_fst_1130_);
                    lean_dec(v_a_1129_);
                    v___x_1133_ = lean_box(0);
                    v_isShared_1134_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1135_ = lean_unsigned_to_nat(0);
                v___x_1136_ = lean_nat_dec_lt(v___x_1135_, v_fst_1130_);
                if v___x_1136_ == 0 {
                    if v_isShared_1134_ == 0 {
                        v___x_1138_ = v___x_1133_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_fst_1130_);
                        lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_snd_1131_);
                        v___x_1138_ = v_reuseFailAlloc_1139_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1140_ = lean_string_utf8_prev(v_str_1128_, v_fst_1130_);
                    lean_dec(v_fst_1130_);
                    v___x_1141_ = lean_unsigned_to_nat(1);
                    v___x_1142_ = lean_nat_add(v_snd_1131_, v___x_1141_);
                    lean_dec(v_snd_1131_);
                    if v_isShared_1134_ == 0 {
                        lean_ctor_set(v___x_1133_, 1, v___x_1142_);
                        lean_ctor_set(v___x_1133_, 0, v___x_1140_);
                        v___x_1144_ = v___x_1133_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1140_);
                        lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1142_);
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
    mut v_str_1148_: *mut LeanObject,
    mut v_a_1149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1150_: *mut LeanObject = core::ptr::null_mut();
    v_res_1150_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_1148_, v_a_1149_);
    lean_dec_ref(v_str_1148_);
    return v_res_1150_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(
    mut v_str_1151_: *mut LeanObject,
    mut v_p_1152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1156_: *mut LeanObject = core::ptr::null_mut();
    v_n_1153_ = lean_unsigned_to_nat(0);
    v___x_1154_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1154_, 0, v_p_1152_);
    lean_ctor_set(v___x_1154_, 1, v_n_1153_);
    v___x_1155_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_1151_, v___x_1154_);
    v_snd_1156_ = lean_ctor_get(v___x_1155_, 1);
    lean_inc(v_snd_1156_);
    lean_dec_ref(v___x_1155_);
    return v_snd_1156_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(
    mut v_str_1157_: *mut LeanObject,
    mut v_p_1158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1159_: *mut LeanObject = core::ptr::null_mut();
    v_res_1159_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(
            v_str_1157_,
            v_p_1158_,
        );
    lean_dec_ref(v_str_1157_);
    return v_res_1159_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(
    mut v_str_1160_: *mut LeanObject,
    mut v_inst_1161_: *mut LeanObject,
    mut v_a_1162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    v___x_1163_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_1160_, v_a_1162_);
    return v___x_1163_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(
    mut v_str_1164_: *mut LeanObject,
    mut v_inst_1165_: *mut LeanObject,
    mut v_a_1166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1167_: *mut LeanObject = core::ptr::null_mut();
    v_res_1167_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(v_str_1164_, v_inst_1165_, v_a_1166_);
    lean_dec_ref(v_str_1164_);
    return v_res_1167_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(
    mut v_str_1168_: *mut LeanObject,
    mut v_p_1169_: *mut LeanObject,
    mut v_j_1170_: *mut LeanObject,
    mut v_a_1171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1173_: u8 = 0;
    let mut v_one_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1172_ = lean_unsigned_to_nat(0);
                v_isZero_1173_ = lean_nat_dec_eq(v_j_1170_, v_zero_1172_);
                if v_isZero_1173_ == 1 {
                    lean_dec(v_j_1170_);
                    return v_a_1171_;
                } else {
                    lean_dec(v_a_1171_);
                    v_one_1174_ = lean_unsigned_to_nat(1);
                    v_n_1175_ = lean_nat_sub(v_j_1170_, v_one_1174_);
                    lean_dec(v_j_1170_);
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
    mut v_str_1178_: *mut LeanObject,
    mut v_p_1179_: *mut LeanObject,
    mut v_j_1180_: *mut LeanObject,
    mut v_a_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1182_: *mut LeanObject = core::ptr::null_mut();
    v_res_1182_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_1178_, v_p_1179_, v_j_1180_, v_a_1181_);
    lean_dec(v_p_1179_);
    lean_dec_ref(v_str_1178_);
    return v_res_1182_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(
    mut v_str_1183_: *mut LeanObject,
    mut v_n_1184_: *mut LeanObject,
    mut v_p_1185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_p_1185_);
    v___x_1186_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_1183_, v_p_1185_, v_n_1184_, v_p_1185_);
    lean_dec(v_p_1185_);
    return v___x_1186_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(
    mut v_str_1187_: *mut LeanObject,
    mut v_n_1188_: *mut LeanObject,
    mut v_p_1189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1190_: *mut LeanObject = core::ptr::null_mut();
    v_res_1190_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(
            v_str_1187_,
            v_n_1188_,
            v_p_1189_,
        );
    lean_dec_ref(v_str_1187_);
    return v_res_1190_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(
    mut v_str_1191_: *mut LeanObject,
    mut v_p_1192_: *mut LeanObject,
    mut v_n_1193_: *mut LeanObject,
    mut v_j_1194_: *mut LeanObject,
    mut v_a_1195_: *mut LeanObject,
    mut v_a_1196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    v___x_1197_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_1191_, v_p_1192_, v_j_1194_, v_a_1196_);
    return v___x_1197_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(
    mut v_str_1198_: *mut LeanObject,
    mut v_p_1199_: *mut LeanObject,
    mut v_n_1200_: *mut LeanObject,
    mut v_j_1201_: *mut LeanObject,
    mut v_a_1202_: *mut LeanObject,
    mut v_a_1203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1204_: *mut LeanObject = core::ptr::null_mut();
    v_res_1204_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(v_str_1198_, v_p_1199_, v_n_1200_, v_j_1201_, v_a_1202_, v_a_1203_);
    lean_dec(v_n_1200_);
    lean_dec(v_p_1199_);
    lean_dec_ref(v_str_1198_);
    return v_res_1204_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(
    mut v_text_1205_: *mut LeanObject,
    mut v_posOfStr_1206_: *mut LeanObject,
    mut v_str_1207_: *mut LeanObject,
    mut v_posInStr_1208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_source_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    v_source_1209_ = lean_ctor_get(v_text_1205_, 0);
    v___x_1210_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(
            v_str_1207_,
            v_posInStr_1208_,
        );
    lean_inc(v_posOfStr_1206_);
    v___x_1211_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_source_1209_, v_posOfStr_1206_, v___x_1210_, v_posOfStr_1206_);
    lean_dec(v_posOfStr_1206_);
    return v___x_1211_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(
    mut v_text_1212_: *mut LeanObject,
    mut v_posOfStr_1213_: *mut LeanObject,
    mut v_str_1214_: *mut LeanObject,
    mut v_posInStr_1215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1216_: *mut LeanObject = core::ptr::null_mut();
    v_res_1216_ =
        l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(
            v_text_1212_,
            v_posOfStr_1213_,
            v_str_1214_,
            v_posInStr_1215_,
        );
    lean_dec_ref(v_str_1214_);
    lean_dec_ref(v_text_1212_);
    return v_res_1216_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(
    mut v_text_1217_: *mut LeanObject,
    mut v_posOfStr_1218_: *mut LeanObject,
    mut v_str_1219_: *mut LeanObject,
    mut v_a_1220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: u8 = 0;
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canonical_1229_: u8 = 0;
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1238_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_1220_) {
                0 => {
                    v_pos_1221_ = lean_ctor_get(v_a_1220_, 1);
                    lean_inc(v_pos_1221_);
                    v_endPos_1222_ = lean_ctor_get(v_a_1220_, 3);
                    lean_inc(v_endPos_1222_);
                    lean_dec_ref_known(v_a_1220_, 4);
                    lean_inc(v_posOfStr_1218_);
                    v___x_1223_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_pos_1221_);
                    v___x_1224_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_endPos_1222_);
                    v___x_1225_ = 1;
                    v___x_1226_ = lean_alloc_ctor(1, 2, (1) as u32);
                    lean_ctor_set(v___x_1226_, 0, v___x_1223_);
                    lean_ctor_set(v___x_1226_, 1, v___x_1224_);
                    lean_ctor_set_uint8(
                        v___x_1226_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_1225_,
                    );
                    return v___x_1226_;
                }
                1 => {
                    v_pos_1227_ = lean_ctor_get(v_a_1220_, 0);
                    v_endPos_1228_ = lean_ctor_get(v_a_1220_, 1);
                    v_canonical_1229_ = lean_ctor_get_uint8(
                        v_a_1220_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_isSharedCheck_1238_ = (!lean_is_exclusive(v_a_1220_)) as u8;
                    if v_isSharedCheck_1238_ == 0 {
                        v___x_1231_ = v_a_1220_;
                        v_isShared_1232_ = v_isSharedCheck_1238_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_endPos_1228_);
                        lean_inc(v_pos_1227_);
                        lean_dec(v_a_1220_);
                        v___x_1231_ = lean_box(0);
                        v_isShared_1232_ = v_isSharedCheck_1238_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_posOfStr_1218_);
                    return v_a_1220_;
                }
            },
            1 => {
                lean_inc(v_posOfStr_1218_);
                v___x_1233_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_pos_1227_);
                v___x_1234_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1217_, v_posOfStr_1218_, v_str_1219_, v_endPos_1228_);
                if v_isShared_1232_ == 0 {
                    lean_ctor_set(v___x_1231_, 1, v___x_1234_);
                    lean_ctor_set(v___x_1231_, 0, v___x_1233_);
                    v___x_1236_ = v___x_1231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1233_);
                    lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1234_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1237_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_text_1239_: *mut LeanObject,
    mut v_posOfStr_1240_: *mut LeanObject,
    mut v_str_1241_: *mut LeanObject,
    mut v_a_1242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1243_: *mut LeanObject = core::ptr::null_mut();
    v_res_1243_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_1239_, v_posOfStr_1240_, v_str_1241_, v_a_1242_);
    lean_dec_ref(v_str_1241_);
    lean_dec_ref(v_text_1239_);
    return v_res_1243_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(
    mut v_text_1244_: *mut LeanObject,
    mut v_posOfStr_1245_: *mut LeanObject,
    mut v_str_1246_: *mut LeanObject,
    mut v_a_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1253_: u8 = 0;
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1255_: usize = 0;
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1261_: u8 = 0;
    let mut v_info_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1266_: u8 = 0;
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_info_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rawVal_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preresolved_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1278_: u8 = 0;
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_1247_) {
                0 => {
                    lean_dec(v_posOfStr_1245_);
                    return v_a_1247_;
                }
                1 => {
                    v_info_1248_ = lean_ctor_get(v_a_1247_, 0);
                    v_kind_1249_ = lean_ctor_get(v_a_1247_, 1);
                    v_args_1250_ = lean_ctor_get(v_a_1247_, 2);
                    v_isSharedCheck_1261_ = (!lean_is_exclusive(v_a_1247_)) as u8;
                    if v_isSharedCheck_1261_ == 0 {
                        v___x_1252_ = v_a_1247_;
                        v_isShared_1253_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_args_1250_);
                        lean_inc(v_kind_1249_);
                        lean_inc(v_info_1248_);
                        lean_dec(v_a_1247_);
                        v___x_1252_ = lean_box(0);
                        v_isShared_1253_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_info_1262_ = lean_ctor_get(v_a_1247_, 0);
                    v_val_1263_ = lean_ctor_get(v_a_1247_, 1);
                    v_isSharedCheck_1271_ = (!lean_is_exclusive(v_a_1247_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v___x_1265_ = v_a_1247_;
                        v_isShared_1266_ = v_isSharedCheck_1271_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1263_);
                        lean_inc(v_info_1262_);
                        lean_dec(v_a_1247_);
                        v___x_1265_ = lean_box(0);
                        v_isShared_1266_ = v_isSharedCheck_1271_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_info_1272_ = lean_ctor_get(v_a_1247_, 0);
                    v_rawVal_1273_ = lean_ctor_get(v_a_1247_, 1);
                    v_val_1274_ = lean_ctor_get(v_a_1247_, 2);
                    v_preresolved_1275_ = lean_ctor_get(v_a_1247_, 3);
                    v_isSharedCheck_1283_ = (!lean_is_exclusive(v_a_1247_)) as u8;
                    if v_isSharedCheck_1283_ == 0 {
                        v___x_1277_ = v_a_1247_;
                        v_isShared_1278_ = v_isSharedCheck_1283_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_preresolved_1275_);
                        lean_inc(v_val_1274_);
                        lean_inc(v_rawVal_1273_);
                        lean_inc(v_info_1272_);
                        lean_dec(v_a_1247_);
                        v___x_1277_ = lean_box(0);
                        v_isShared_1278_ = v_isSharedCheck_1283_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                lean_inc(v_posOfStr_1245_);
                v___x_1254_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_1244_, v_posOfStr_1245_, v_str_1246_, v_info_1248_);
                v_sz_1255_ = lean_array_size(v_args_1250_);
                v___x_1256_ = 0usize;
                v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_1244_, v_posOfStr_1245_, v_str_1246_, v_sz_1255_, v___x_1256_, v_args_1250_);
                if v_isShared_1253_ == 0 {
                    lean_ctor_set(v___x_1252_, 2, v___x_1257_);
                    lean_ctor_set(v___x_1252_, 0, v___x_1254_);
                    v___x_1259_ = v___x_1252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1254_);
                    lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_kind_1249_);
                    lean_ctor_set(v_reuseFailAlloc_1260_, 2, v___x_1257_);
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
                    lean_ctor_set(v___x_1265_, 0, v___x_1267_);
                    v___x_1269_ = v___x_1265_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
                    lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_val_1263_);
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
                    lean_ctor_set(v___x_1277_, 0, v___x_1279_);
                    v___x_1281_ = v___x_1277_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1282_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
                    lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_rawVal_1273_);
                    lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_val_1274_);
                    lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_preresolved_1275_);
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
    mut v_text_1284_: *mut LeanObject,
    mut v_posOfStr_1285_: *mut LeanObject,
    mut v_str_1286_: *mut LeanObject,
    mut v_sz_1287_: usize,
    mut v_i_1288_: usize,
    mut v_bs_1289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1290_: u8 = 0;
    let mut v_v_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: usize = 0;
    let mut v___x_1296_: usize = 0;
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1290_ = lean_usize_dec_lt(v_i_1288_, v_sz_1287_);
                if v___x_1290_ == 0 {
                    lean_dec(v_posOfStr_1285_);
                    return v_bs_1289_;
                } else {
                    v_v_1291_ = lean_array_uget(v_bs_1289_, v_i_1288_);
                    v___x_1292_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1293_ = lean_array_uset(v_bs_1289_, v_i_1288_, v___x_1292_);
                    lean_inc(v_posOfStr_1285_);
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
    mut v_text_1299_: *mut LeanObject,
    mut v_posOfStr_1300_: *mut LeanObject,
    mut v_str_1301_: *mut LeanObject,
    mut v_sz_1302_: *mut LeanObject,
    mut v_i_1303_: *mut LeanObject,
    mut v_bs_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1305_: usize = 0;
    let mut v_i_boxed_1306_: usize = 0;
    let mut v_res_1307_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1305_ = lean_unbox_usize(v_sz_1302_);
    lean_dec(v_sz_1302_);
    v_i_boxed_1306_ = lean_unbox_usize(v_i_1303_);
    lean_dec(v_i_1303_);
    v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_1299_, v_posOfStr_1300_, v_str_1301_, v_sz_boxed_1305_, v_i_boxed_1306_, v_bs_1304_);
    lean_dec_ref(v_str_1301_);
    lean_dec_ref(v_text_1299_);
    return v_res_1307_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(
    mut v_text_1308_: *mut LeanObject,
    mut v_posOfStr_1309_: *mut LeanObject,
    mut v_str_1310_: *mut LeanObject,
    mut v_a_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1312_: *mut LeanObject = core::ptr::null_mut();
    v_res_1312_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_1308_, v_posOfStr_1309_, v_str_1310_, v_a_1311_);
    lean_dec_ref(v_str_1310_);
    lean_dec_ref(v_text_1308_);
    return v_res_1312_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(
    mut v_x_1313_: *mut LeanObject,
    mut v_h__1_1314_: *mut LeanObject,
    mut v_h__2_1315_: *mut LeanObject,
    mut v_h__3_1316_: *mut LeanObject,
    mut v_h__4_1317_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1313_) {
        0 => {
            let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1316_);
            lean_dec(v_h__2_1315_);
            lean_dec(v_h__1_1314_);
            v___x_1318_ = lean_box(0);
            v___x_1319_ = lean_apply_1(v_h__4_1317_, v___x_1318_);
            return v___x_1319_;
        }
        1 => {
            let mut v_info_1320_: *mut LeanObject = core::ptr::null_mut();
            let mut v_kind_1321_: *mut LeanObject = core::ptr::null_mut();
            let mut v_args_1322_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1317_);
            lean_dec(v_h__3_1316_);
            lean_dec(v_h__2_1315_);
            v_info_1320_ = lean_ctor_get(v_x_1313_, 0);
            lean_inc(v_info_1320_);
            v_kind_1321_ = lean_ctor_get(v_x_1313_, 1);
            lean_inc(v_kind_1321_);
            v_args_1322_ = lean_ctor_get(v_x_1313_, 2);
            lean_inc_ref(v_args_1322_);
            lean_dec_ref_known(v_x_1313_, 3);
            v___x_1323_ = lean_apply_3(v_h__1_1314_, v_info_1320_, v_kind_1321_, v_args_1322_);
            return v___x_1323_;
        }
        2 => {
            let mut v_info_1324_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1317_);
            lean_dec(v_h__2_1315_);
            lean_dec(v_h__1_1314_);
            v_info_1324_ = lean_ctor_get(v_x_1313_, 0);
            lean_inc(v_info_1324_);
            v_val_1325_ = lean_ctor_get(v_x_1313_, 1);
            lean_inc_ref(v_val_1325_);
            lean_dec_ref_known(v_x_1313_, 2);
            v___x_1326_ = lean_apply_2(v_h__3_1316_, v_info_1324_, v_val_1325_);
            return v___x_1326_;
        }
        _ => {
            let mut v_info_1327_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rawVal_1328_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1329_: *mut LeanObject = core::ptr::null_mut();
            let mut v_preresolved_1330_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1317_);
            lean_dec(v_h__3_1316_);
            lean_dec(v_h__1_1314_);
            v_info_1327_ = lean_ctor_get(v_x_1313_, 0);
            lean_inc(v_info_1327_);
            v_rawVal_1328_ = lean_ctor_get(v_x_1313_, 1);
            lean_inc_ref(v_rawVal_1328_);
            v_val_1329_ = lean_ctor_get(v_x_1313_, 2);
            lean_inc(v_val_1329_);
            v_preresolved_1330_ = lean_ctor_get(v_x_1313_, 3);
            lean_inc(v_preresolved_1330_);
            lean_dec_ref_known(v_x_1313_, 4);
            v___x_1331_ = lean_apply_4(
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
    mut v_motive_1332_: *mut LeanObject,
    mut v_x_1333_: *mut LeanObject,
    mut v_h__1_1334_: *mut LeanObject,
    mut v_h__2_1335_: *mut LeanObject,
    mut v_h__3_1336_: *mut LeanObject,
    mut v_h__4_1337_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1333_) {
        0 => {
            let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1336_);
            lean_dec(v_h__2_1335_);
            lean_dec(v_h__1_1334_);
            v___x_1338_ = lean_box(0);
            v___x_1339_ = lean_apply_1(v_h__4_1337_, v___x_1338_);
            return v___x_1339_;
        }
        1 => {
            let mut v_info_1340_: *mut LeanObject = core::ptr::null_mut();
            let mut v_kind_1341_: *mut LeanObject = core::ptr::null_mut();
            let mut v_args_1342_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1337_);
            lean_dec(v_h__3_1336_);
            lean_dec(v_h__2_1335_);
            v_info_1340_ = lean_ctor_get(v_x_1333_, 0);
            lean_inc(v_info_1340_);
            v_kind_1341_ = lean_ctor_get(v_x_1333_, 1);
            lean_inc(v_kind_1341_);
            v_args_1342_ = lean_ctor_get(v_x_1333_, 2);
            lean_inc_ref(v_args_1342_);
            lean_dec_ref_known(v_x_1333_, 3);
            v___x_1343_ = lean_apply_3(v_h__1_1334_, v_info_1340_, v_kind_1341_, v_args_1342_);
            return v___x_1343_;
        }
        2 => {
            let mut v_info_1344_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1345_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1337_);
            lean_dec(v_h__2_1335_);
            lean_dec(v_h__1_1334_);
            v_info_1344_ = lean_ctor_get(v_x_1333_, 0);
            lean_inc(v_info_1344_);
            v_val_1345_ = lean_ctor_get(v_x_1333_, 1);
            lean_inc_ref(v_val_1345_);
            lean_dec_ref_known(v_x_1333_, 2);
            v___x_1346_ = lean_apply_2(v_h__3_1336_, v_info_1344_, v_val_1345_);
            return v___x_1346_;
        }
        _ => {
            let mut v_info_1347_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rawVal_1348_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1349_: *mut LeanObject = core::ptr::null_mut();
            let mut v_preresolved_1350_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1337_);
            lean_dec(v_h__3_1336_);
            lean_dec(v_h__1_1334_);
            v_info_1347_ = lean_ctor_get(v_x_1333_, 0);
            lean_inc(v_info_1347_);
            v_rawVal_1348_ = lean_ctor_get(v_x_1333_, 1);
            lean_inc_ref(v_rawVal_1348_);
            v_val_1349_ = lean_ctor_get(v_x_1333_, 2);
            lean_inc(v_val_1349_);
            v_preresolved_1350_ = lean_ctor_get(v_x_1333_, 3);
            lean_inc(v_preresolved_1350_);
            lean_dec_ref_known(v_x_1333_, 4);
            v___x_1351_ = lean_apply_4(
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
    mut v_x_1352_: *mut LeanObject,
    mut v_h__1_1353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    v___x_1354_ = lean_apply_2(v_h__1_1353_, v_x_1352_, lean_box(0));
    return v___x_1354_;
}
pub unsafe fn l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(
    mut v_00_u03b1_1355_: *mut LeanObject,
    mut v_P_1356_: *mut LeanObject,
    mut v_motive_1357_: *mut LeanObject,
    mut v_x_1358_: *mut LeanObject,
    mut v_h__1_1359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    v___x_1360_ = lean_apply_2(v_h__1_1359_, v_x_1358_, lean_box(0));
    return v___x_1360_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(
    mut v_text_1361_: *mut LeanObject,
    mut v_pos_1362_: *mut LeanObject,
    mut v_str_1363_: *mut LeanObject,
    mut v_x_1364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1365_ = lean_ctor_get(v_x_1364_, 0);
                v_snd_1366_ = lean_ctor_get(v_x_1364_, 1);
                v_isSharedCheck_1374_ = (!lean_is_exclusive(v_x_1364_)) as u8;
                if v_isSharedCheck_1374_ == 0 {
                    v___x_1368_ = v_x_1364_;
                    v_isShared_1369_ = v_isSharedCheck_1374_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1366_);
                    lean_inc(v_fst_1365_);
                    lean_dec(v_x_1364_);
                    v___x_1368_ = lean_box(0);
                    v_isShared_1369_ = v_isSharedCheck_1374_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1370_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1361_, v_pos_1362_, v_str_1363_, v_fst_1365_);
                if v_isShared_1369_ == 0 {
                    lean_ctor_set(v___x_1368_, 0, v___x_1370_);
                    v___x_1372_ = v___x_1368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
                    lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_snd_1366_);
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
    mut v_text_1375_: *mut LeanObject,
    mut v_pos_1376_: *mut LeanObject,
    mut v_str_1377_: *mut LeanObject,
    mut v_x_1378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1379_: *mut LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(
        v_text_1375_,
        v_pos_1376_,
        v_str_1377_,
        v_x_1378_,
    );
    lean_dec_ref(v_str_1377_);
    lean_dec_ref(v_text_1375_);
    return v_res_1379_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(
    mut v_env_1399_: *mut LeanObject,
    mut v_p_1400_: *mut LeanObject,
    mut v_ictx_1401_: *mut LeanObject,
    mut v_s_1402_: *mut LeanObject,
    mut v_text_1403_: *mut LeanObject,
    mut v_pos_1404_: *mut LeanObject,
    mut v_str_1405_: *mut LeanObject,
    mut v___f_1406_: *mut LeanObject,
    mut v_inst_1407_: *mut LeanObject,
    mut v_inst_1408_: *mut LeanObject,
    mut v_toApplicative_1409_: *mut LeanObject,
    mut v_____do__lift_1410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: u8 = 0;
    let mut v_stxStack_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1428_: u8 = 0;
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1433_: usize = 0;
    let mut v___x_1434_: usize = 0;
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1446_: u8 = 0;
    let mut v_unexpectedTk_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unexpected_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1460_: u8 = 0;
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut v_stxStack_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1411_ = lean_box(0);
                v___x_1412_ = lean_box(0);
                lean_inc_ref(v_env_1399_);
                v___x_1413_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_1413_, 0, v_env_1399_);
                lean_ctor_set(v___x_1413_, 1, v_____do__lift_1410_);
                lean_ctor_set(v___x_1413_, 2, v___x_1411_);
                lean_ctor_set(v___x_1413_, 3, v___x_1412_);
                v___x_1414_ = l_Lean_Parser_getTokenTable(v_env_1399_);
                lean_inc_ref(v_ictx_1401_);
                v_s_1415_ = l_Lean_Parser_ParserFn_run(
                    v_p_1400_,
                    v_ictx_1401_,
                    v___x_1413_,
                    v___x_1414_,
                    v_s_1402_,
                );
                lean_inc_ref(v_s_1415_);
                v___x_1416_ = l_Lean_Parser_ParserState_allErrors(v_s_1415_);
                v___x_1417_ = lean_array_get_size(v___x_1416_);
                lean_dec_ref(v___x_1416_);
                v___x_1418_ = lean_unsigned_to_nat(0);
                v___x_1419_ = lean_nat_dec_eq(v___x_1417_, v___x_1418_);
                if v___x_1419_ == 0 {
                    lean_dec_ref(v_toApplicative_1409_);
                    v_stxStack_1420_ = lean_ctor_get(v_s_1415_, 0);
                    v_lhsPrec_1421_ = lean_ctor_get(v_s_1415_, 1);
                    v_pos_1422_ = lean_ctor_get(v_s_1415_, 2);
                    v_cache_1423_ = lean_ctor_get(v_s_1415_, 3);
                    v_errorMsg_1424_ = lean_ctor_get(v_s_1415_, 4);
                    v_recoveredErrors_1425_ = lean_ctor_get(v_s_1415_, 5);
                    v_isSharedCheck_1462_ = (!lean_is_exclusive(v_s_1415_)) as u8;
                    if v_isSharedCheck_1462_ == 0 {
                        v___x_1427_ = v_s_1415_;
                        v_isShared_1428_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_recoveredErrors_1425_);
                        lean_inc(v_errorMsg_1424_);
                        lean_inc(v_cache_1423_);
                        lean_inc(v_pos_1422_);
                        lean_inc(v_lhsPrec_1421_);
                        lean_inc(v_stxStack_1420_);
                        lean_dec(v_s_1415_);
                        v___x_1427_ = lean_box(0);
                        v_isShared_1428_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_1406_);
                    v_stxStack_1463_ = lean_ctor_get(v_s_1415_, 0);
                    lean_inc_ref(v_stxStack_1463_);
                    v_pos_1464_ = lean_ctor_get(v_s_1415_, 2);
                    lean_inc(v_pos_1464_);
                    v___x_1465_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1401_, v_pos_1464_);
                    lean_dec(v_pos_1464_);
                    if v___x_1465_ == 0 {
                        lean_dec_ref(v_stxStack_1463_);
                        lean_dec_ref(v_toApplicative_1409_);
                        lean_dec(v_pos_1404_);
                        v___x_1466_ = l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0;
                        v___x_1467_ = l_Lean_Parser_ParserState_mkError(v_s_1415_, v___x_1466_);
                        v___x_1468_ =
                            l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1401_, v___x_1467_);
                        v___x_1469_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_1469_, 0, v___x_1468_);
                        v___x_1470_ = l_Lean_MessageData_ofFormat(v___x_1469_);
                        v___x_1471_ =
                            l_Lean_throwError___redArg(v_inst_1407_, v_inst_1408_, v___x_1470_);
                        return v___x_1471_;
                    } else {
                        lean_dec_ref(v_s_1415_);
                        lean_dec_ref(v_inst_1408_);
                        lean_dec_ref(v_inst_1407_);
                        lean_dec_ref(v_ictx_1401_);
                        v_toPure_1472_ = lean_ctor_get(v_toApplicative_1409_, 1);
                        lean_inc(v_toPure_1472_);
                        lean_dec_ref(v_toApplicative_1409_);
                        v___x_1473_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1463_);
                        lean_dec_ref(v_stxStack_1463_);
                        v___x_1474_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_1403_, v_pos_1404_, v_str_1405_, v___x_1473_);
                        v___x_1475_ = lean_apply_2(v_toPure_1472_, lean_box(0), v___x_1474_);
                        return v___x_1475_;
                    }
                }
            }
            1 => {
                lean_inc(v_pos_1404_);
                v___x_1429_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_1403_, v_pos_1404_, v_str_1405_, v_pos_1422_);
                if lean_obj_tag(v_errorMsg_1424_) == 0 {
                    lean_dec(v_pos_1404_);
                    v___y_1431_ = v_errorMsg_1424_;
                    state = 2;
                    continue;
                } else {
                    v_val_1443_ = lean_ctor_get(v_errorMsg_1424_, 0);
                    v_isSharedCheck_1461_ = (!lean_is_exclusive(v_errorMsg_1424_)) as u8;
                    if v_isSharedCheck_1461_ == 0 {
                        v___x_1445_ = v_errorMsg_1424_;
                        v_isShared_1446_ = v_isSharedCheck_1461_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_1443_);
                        lean_dec(v_errorMsg_1424_);
                        v___x_1445_ = lean_box(0);
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
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_1432_,
                    v___f_1406_,
                    v_sz_1433_,
                    v___x_1434_,
                    v_recoveredErrors_1425_,
                );
                if v_isShared_1428_ == 0 {
                    lean_ctor_set(v___x_1427_, 5, v___x_1435_);
                    lean_ctor_set(v___x_1427_, 4, v___y_1431_);
                    lean_ctor_set(v___x_1427_, 2, v___x_1429_);
                    v_s_1437_ = v___x_1427_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_stxStack_1420_);
                    lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_lhsPrec_1421_);
                    lean_ctor_set(v_reuseFailAlloc_1442_, 2, v___x_1429_);
                    lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_cache_1423_);
                    lean_ctor_set(v_reuseFailAlloc_1442_, 4, v___y_1431_);
                    lean_ctor_set(v_reuseFailAlloc_1442_, 5, v___x_1435_);
                    v_s_1437_ = v_reuseFailAlloc_1442_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1438_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1401_, v_s_1437_);
                v___x_1439_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1439_, 0, v___x_1438_);
                v___x_1440_ = l_Lean_MessageData_ofFormat(v___x_1439_);
                v___x_1441_ = l_Lean_throwError___redArg(v_inst_1407_, v_inst_1408_, v___x_1440_);
                return v___x_1441_;
            }
            4 => {
                v_unexpectedTk_1447_ = lean_ctor_get(v_val_1443_, 0);
                v_unexpected_1448_ = lean_ctor_get(v_val_1443_, 1);
                v_expected_1449_ = lean_ctor_get(v_val_1443_, 2);
                v_isSharedCheck_1460_ = (!lean_is_exclusive(v_val_1443_)) as u8;
                if v_isSharedCheck_1460_ == 0 {
                    v___x_1451_ = v_val_1443_;
                    v_isShared_1452_ = v_isSharedCheck_1460_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_expected_1449_);
                    lean_inc(v_unexpected_1448_);
                    lean_inc(v_unexpectedTk_1447_);
                    lean_dec(v_val_1443_);
                    v___x_1451_ = lean_box(0);
                    v_isShared_1452_ = v_isSharedCheck_1460_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1453_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_1403_, v_pos_1404_, v_str_1405_, v_unexpectedTk_1447_);
                if v_isShared_1452_ == 0 {
                    lean_ctor_set(v___x_1451_, 0, v___x_1453_);
                    v___x_1455_ = v___x_1451_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1453_);
                    lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_unexpected_1448_);
                    lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_expected_1449_);
                    v___x_1455_ = v_reuseFailAlloc_1459_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1446_ == 0 {
                    lean_ctor_set(v___x_1445_, 0, v___x_1455_);
                    v___x_1457_ = v___x_1445_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
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
    mut v_env_1476_: *mut LeanObject,
    mut v_p_1477_: *mut LeanObject,
    mut v_ictx_1478_: *mut LeanObject,
    mut v_s_1479_: *mut LeanObject,
    mut v_text_1480_: *mut LeanObject,
    mut v_pos_1481_: *mut LeanObject,
    mut v_str_1482_: *mut LeanObject,
    mut v___f_1483_: *mut LeanObject,
    mut v_inst_1484_: *mut LeanObject,
    mut v_inst_1485_: *mut LeanObject,
    mut v_toApplicative_1486_: *mut LeanObject,
    mut v_____do__lift_1487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1488_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_str_1482_);
    lean_dec_ref(v_text_1480_);
    return v_res_1488_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(
    mut v_str_1489_: *mut LeanObject,
    mut v_env_1490_: *mut LeanObject,
    mut v_p_1491_: *mut LeanObject,
    mut v_text_1492_: *mut LeanObject,
    mut v_pos_1493_: *mut LeanObject,
    mut v___f_1494_: *mut LeanObject,
    mut v_inst_1495_: *mut LeanObject,
    mut v_inst_1496_: *mut LeanObject,
    mut v_toApplicative_1497_: *mut LeanObject,
    mut v_toBind_1498_: *mut LeanObject,
    mut v_inst_1499_: *mut LeanObject,
    mut v_____do__lift_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1501_: u8 = 0;
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ictx_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    v___x_1501_ = 1;
    v___x_1502_ = lean_string_utf8_byte_size(v_str_1489_);
    lean_inc_ref(v_str_1489_);
    v_ictx_1503_ = l_Lean_Parser_mkInputContext___redArg(
        v_str_1489_,
        v_____do__lift_1500_,
        v___x_1501_,
        v___x_1502_,
    );
    v_s_1504_ = l_Lean_Parser_mkParserState(v_str_1489_);
    v___f_1505_ = lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    lean_closure_set(v___f_1505_, 0, v_env_1490_);
    lean_closure_set(v___f_1505_, 1, v_p_1491_);
    lean_closure_set(v___f_1505_, 2, v_ictx_1503_);
    lean_closure_set(v___f_1505_, 3, v_s_1504_);
    lean_closure_set(v___f_1505_, 4, v_text_1492_);
    lean_closure_set(v___f_1505_, 5, v_pos_1493_);
    lean_closure_set(v___f_1505_, 6, v_str_1489_);
    lean_closure_set(v___f_1505_, 7, v___f_1494_);
    lean_closure_set(v___f_1505_, 8, v_inst_1495_);
    lean_closure_set(v___f_1505_, 9, v_inst_1496_);
    lean_closure_set(v___f_1505_, 10, v_toApplicative_1497_);
    v___x_1506_ = lean_apply_4(
        v_toBind_1498_,
        lean_box(0),
        lean_box(0),
        v_inst_1499_,
        v___f_1505_,
    );
    return v___x_1506_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(
    mut v_inst_1507_: *mut LeanObject,
    mut v_strLit_1508_: *mut LeanObject,
    mut v_text_1509_: *mut LeanObject,
    mut v_env_1510_: *mut LeanObject,
    mut v_p_1511_: *mut LeanObject,
    mut v_inst_1512_: *mut LeanObject,
    mut v_inst_1513_: *mut LeanObject,
    mut v_toApplicative_1514_: *mut LeanObject,
    mut v_toBind_1515_: *mut LeanObject,
    mut v_inst_1516_: *mut LeanObject,
    mut v_pos_1517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getFileName_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    v_getFileName_1518_ = lean_ctor_get(v_inst_1507_, 2);
    lean_inc(v_getFileName_1518_);
    lean_dec_ref(v_inst_1507_);
    v_str_1519_ = l_Lean_TSyntax_getString(v_strLit_1508_);
    lean_inc_ref(v_str_1519_);
    lean_inc(v_pos_1517_);
    lean_inc_ref(v_text_1509_);
    v___f_1520_ = lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1520_, 0, v_text_1509_);
    lean_closure_set(v___f_1520_, 1, v_pos_1517_);
    lean_closure_set(v___f_1520_, 2, v_str_1519_);
    lean_inc(v_toBind_1515_);
    v___f_1521_ = lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__2 as *mut core::ffi::c_void,
        12,
        11,
    );
    lean_closure_set(v___f_1521_, 0, v_str_1519_);
    lean_closure_set(v___f_1521_, 1, v_env_1510_);
    lean_closure_set(v___f_1521_, 2, v_p_1511_);
    lean_closure_set(v___f_1521_, 3, v_text_1509_);
    lean_closure_set(v___f_1521_, 4, v_pos_1517_);
    lean_closure_set(v___f_1521_, 5, v___f_1520_);
    lean_closure_set(v___f_1521_, 6, v_inst_1512_);
    lean_closure_set(v___f_1521_, 7, v_inst_1513_);
    lean_closure_set(v___f_1521_, 8, v_toApplicative_1514_);
    lean_closure_set(v___f_1521_, 9, v_toBind_1515_);
    lean_closure_set(v___f_1521_, 10, v_inst_1516_);
    v___x_1522_ = lean_apply_4(
        v_toBind_1515_,
        lean_box(0),
        lean_box(0),
        v_getFileName_1518_,
        v___f_1521_,
    );
    return v___x_1522_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(
    mut v_inst_1523_: *mut LeanObject,
    mut v_strLit_1524_: *mut LeanObject,
    mut v_text_1525_: *mut LeanObject,
    mut v_env_1526_: *mut LeanObject,
    mut v_p_1527_: *mut LeanObject,
    mut v_inst_1528_: *mut LeanObject,
    mut v_inst_1529_: *mut LeanObject,
    mut v_toApplicative_1530_: *mut LeanObject,
    mut v_toBind_1531_: *mut LeanObject,
    mut v_inst_1532_: *mut LeanObject,
    mut v_pos_1533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1534_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_strLit_1524_);
    return v_res_1534_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(
    mut v___f_1535_: *mut LeanObject,
    mut v_pos_1536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    v___x_1537_ = lean_apply_1(v___f_1535_, v_pos_1536_);
    return v___x_1537_;
}
pub unsafe fn _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1() -> *mut LeanObject
{
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    v___x_1539_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0;
    v___x_1540_ = l_Lean_stringToMessageData(v___x_1539_);
    return v___x_1540_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(
    mut v_text_1541_: *mut LeanObject,
    mut v_inst_1542_: *mut LeanObject,
    mut v_inst_1543_: *mut LeanObject,
    mut v_strLit_1544_: *mut LeanObject,
    mut v_toBind_1545_: *mut LeanObject,
    mut v___f_1546_: *mut LeanObject,
    mut v_toApplicative_1547_: *mut LeanObject,
    mut v___f_1548_: *mut LeanObject,
    mut v_____r_1549_: *mut LeanObject,
    mut v_pos_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_source_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u32 = 0;
    let mut v___x_1553_: u32 = 0;
    let mut v___x_1554_: u8 = 0;
    v_source_1551_ = lean_ctor_get(v_text_1541_, 0);
    v___x_1552_ = lean_string_utf8_get(v_source_1551_, v_pos_1550_);
    v___x_1553_ = 34;
    v___x_1554_ = lean_uint32_dec_eq(v___x_1552_, v___x_1553_);
    if v___x_1554_ == 0 {
        let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_1548_);
        lean_dec_ref(v_toApplicative_1547_);
        v___x_1555_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once
            ),
            _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1,
        );
        v___x_1556_ =
            l_Lean_throwErrorAt___redArg(v_inst_1542_, v_inst_1543_, v_strLit_1544_, v___x_1555_);
        v___x_1557_ = lean_apply_4(
            v_toBind_1545_,
            lean_box(0),
            lean_box(0),
            v___x_1556_,
            v___f_1546_,
        );
        return v___x_1557_;
    } else {
        let mut v_toPure_1558_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_1546_);
        lean_dec(v_strLit_1544_);
        lean_dec_ref(v_inst_1543_);
        lean_dec_ref(v_inst_1542_);
        v_toPure_1558_ = lean_ctor_get(v_toApplicative_1547_, 1);
        lean_inc(v_toPure_1558_);
        lean_dec_ref(v_toApplicative_1547_);
        v___x_1559_ = lean_string_utf8_next(v_source_1551_, v_pos_1550_);
        v___x_1560_ = lean_apply_2(v_toPure_1558_, lean_box(0), v___x_1559_);
        v___x_1561_ = lean_apply_4(
            v_toBind_1545_,
            lean_box(0),
            lean_box(0),
            v___x_1560_,
            v___f_1548_,
        );
        return v___x_1561_;
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed(
    mut v_text_1562_: *mut LeanObject,
    mut v_inst_1563_: *mut LeanObject,
    mut v_inst_1564_: *mut LeanObject,
    mut v_strLit_1565_: *mut LeanObject,
    mut v_toBind_1566_: *mut LeanObject,
    mut v___f_1567_: *mut LeanObject,
    mut v_toApplicative_1568_: *mut LeanObject,
    mut v___f_1569_: *mut LeanObject,
    mut v_____r_1570_: *mut LeanObject,
    mut v_pos_1571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1572_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_pos_1571_);
    lean_dec_ref(v_text_1562_);
    return v_res_1572_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(
    mut v___f_1573_: *mut LeanObject,
    mut v_____s_1574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    v___x_1575_ = lean_box(0);
    v___x_1576_ = lean_apply_2(v___f_1573_, v___x_1575_, v_____s_1574_);
    return v___x_1576_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(
    mut v_toPure_1577_: *mut LeanObject,
    mut v_____do__lift_1578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_a_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1596_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_1578_) == 0 {
                    v_a_1579_ = lean_ctor_get(v_____do__lift_1578_, 0);
                    v_isSharedCheck_1587_ = (!lean_is_exclusive(v_____do__lift_1578_)) as u8;
                    if v_isSharedCheck_1587_ == 0 {
                        v___x_1581_ = v_____do__lift_1578_;
                        v_isShared_1582_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1579_);
                        lean_dec(v_____do__lift_1578_);
                        v___x_1581_ = lean_box(0);
                        v_isShared_1582_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1588_ = lean_ctor_get(v_____do__lift_1578_, 0);
                    v_isSharedCheck_1596_ = (!lean_is_exclusive(v_____do__lift_1578_)) as u8;
                    if v_isSharedCheck_1596_ == 0 {
                        v___x_1590_ = v_____do__lift_1578_;
                        v_isShared_1591_ = v_isSharedCheck_1596_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1588_);
                        lean_dec(v_____do__lift_1578_);
                        v___x_1590_ = lean_box(0);
                        v_isShared_1591_ = v_isSharedCheck_1596_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1582_ == 0 {
                    lean_ctor_set_tag(v___x_1581_, 1);
                    v___x_1584_ = v___x_1581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1579_);
                    v___x_1584_ = v_reuseFailAlloc_1586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1585_ = lean_apply_2(v_toPure_1577_, lean_box(0), v___x_1584_);
                return v___x_1585_;
            }
            3 => {
                if v_isShared_1591_ == 0 {
                    lean_ctor_set_tag(v___x_1590_, 0);
                    v___x_1593_ = v___x_1590_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1588_);
                    v___x_1593_ = v_reuseFailAlloc_1595_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1594_ = lean_apply_2(v_toPure_1577_, lean_box(0), v___x_1593_);
                return v___x_1594_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(
    mut v_source_1597_: *mut LeanObject,
    mut v_toPure_1598_: *mut LeanObject,
    mut v_toBind_1599_: *mut LeanObject,
    mut v___f_1600_: *mut LeanObject,
    mut v_b_1601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1602_: u32 = 0;
    let mut v___x_1603_: u32 = 0;
    let mut v___x_1604_: u8 = 0;
    v___x_1602_ = lean_string_utf8_get(v_source_1597_, v_b_1601_);
    v___x_1603_ = 35;
    v___x_1604_ = lean_uint32_dec_eq(v___x_1602_, v___x_1603_);
    if v___x_1604_ == 0 {
        let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
        v___x_1605_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1605_, 0, v_b_1601_);
        v___x_1606_ = lean_apply_2(v_toPure_1598_, lean_box(0), v___x_1605_);
        v___x_1607_ = lean_apply_4(
            v_toBind_1599_,
            lean_box(0),
            lean_box(0),
            v___x_1606_,
            v___f_1600_,
        );
        return v___x_1607_;
    } else {
        let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
        v___x_1608_ = lean_string_utf8_next(v_source_1597_, v_b_1601_);
        lean_dec(v_b_1601_);
        v___x_1609_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1609_, 0, v___x_1608_);
        v___x_1610_ = lean_apply_2(v_toPure_1598_, lean_box(0), v___x_1609_);
        v___x_1611_ = lean_apply_4(
            v_toBind_1599_,
            lean_box(0),
            lean_box(0),
            v___x_1610_,
            v___f_1600_,
        );
        return v___x_1611_;
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(
    mut v_source_1612_: *mut LeanObject,
    mut v_toPure_1613_: *mut LeanObject,
    mut v_toBind_1614_: *mut LeanObject,
    mut v___f_1615_: *mut LeanObject,
    mut v_b_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1617_: *mut LeanObject = core::ptr::null_mut();
    v_res_1617_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(
        v_source_1612_,
        v_toPure_1613_,
        v_toBind_1614_,
        v___f_1615_,
        v_b_1616_,
    );
    lean_dec_ref(v_source_1612_);
    return v_res_1617_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(
    mut v_text_1618_: *mut LeanObject,
    mut v___f_1619_: *mut LeanObject,
    mut v_toApplicative_1620_: *mut LeanObject,
    mut v_toBind_1621_: *mut LeanObject,
    mut v_inst_1622_: *mut LeanObject,
    mut v___f_1623_: *mut LeanObject,
    mut v_____x_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u32 = 0;
    let mut v___x_1628_: u32 = 0;
    let mut v___x_1629_: u8 = 0;
    v_start_1625_ = lean_ctor_get(v_____x_1624_, 0);
    lean_inc(v_start_1625_);
    lean_dec_ref(v_____x_1624_);
    v_source_1626_ = lean_ctor_get(v_text_1618_, 0);
    lean_inc_ref(v_source_1626_);
    lean_dec_ref(v_text_1618_);
    v___x_1627_ = lean_string_utf8_get(v_source_1626_, v_start_1625_);
    v___x_1628_ = 114;
    v___x_1629_ = lean_uint32_dec_eq(v___x_1627_, v___x_1628_);
    if v___x_1629_ == 0 {
        let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_source_1626_);
        lean_dec(v___f_1623_);
        lean_dec_ref(v_inst_1622_);
        lean_dec(v_toBind_1621_);
        lean_dec_ref(v_toApplicative_1620_);
        v___x_1630_ = lean_box(0);
        v___x_1631_ = lean_apply_2(v___f_1619_, v___x_1630_, v_start_1625_);
        return v___x_1631_;
    } else {
        let mut v_toPure_1632_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pos_1633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1635_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_1619_);
        v_toPure_1632_ = lean_ctor_get(v_toApplicative_1620_, 1);
        lean_inc_n(v_toPure_1632_, 2);
        lean_dec_ref(v_toApplicative_1620_);
        v_pos_1633_ = lean_string_utf8_next(v_source_1626_, v_start_1625_);
        lean_dec(v_start_1625_);
        v___f_1634_ = lean_alloc_closure(
            l_Lean_Doc_parseQuotedStrLit___redArg___lam__7 as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_1634_, 0, v_toPure_1632_);
        lean_inc(v_toBind_1621_);
        v___f_1635_ = lean_alloc_closure(
            l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1635_, 0, v_source_1626_);
        lean_closure_set(v___f_1635_, 1, v_toPure_1632_);
        lean_closure_set(v___f_1635_, 2, v_toBind_1621_);
        lean_closure_set(v___f_1635_, 3, v___f_1634_);
        v___x_1636_ = l___private_Init_While_0__whileM_erased___redArg(
            v_inst_1622_,
            v___f_1635_,
            v_pos_1633_,
        );
        v___x_1637_ = lean_apply_4(
            v_toBind_1621_,
            lean_box(0),
            lean_box(0),
            v___x_1636_,
            v___f_1623_,
        );
        return v___x_1637_;
    }
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(
    mut v_inst_1638_: *mut LeanObject,
    mut v_strLit_1639_: *mut LeanObject,
    mut v_text_1640_: *mut LeanObject,
    mut v_p_1641_: *mut LeanObject,
    mut v_inst_1642_: *mut LeanObject,
    mut v_inst_1643_: *mut LeanObject,
    mut v_toApplicative_1644_: *mut LeanObject,
    mut v_toBind_1645_: *mut LeanObject,
    mut v_inst_1646_: *mut LeanObject,
    mut v_env_1647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_toBind_1645_, 3);
    lean_inc_ref_n(v_toApplicative_1644_, 2);
    lean_inc_ref(v_inst_1643_);
    lean_inc_ref_n(v_inst_1642_, 3);
    lean_inc_ref_n(v_text_1640_, 2);
    lean_inc_n(v_strLit_1639_, 2);
    v___f_1648_ = lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed as *mut core::ffi::c_void,
        11,
        10,
    );
    lean_closure_set(v___f_1648_, 0, v_inst_1638_);
    lean_closure_set(v___f_1648_, 1, v_strLit_1639_);
    lean_closure_set(v___f_1648_, 2, v_text_1640_);
    lean_closure_set(v___f_1648_, 3, v_env_1647_);
    lean_closure_set(v___f_1648_, 4, v_p_1641_);
    lean_closure_set(v___f_1648_, 5, v_inst_1642_);
    lean_closure_set(v___f_1648_, 6, v_inst_1643_);
    lean_closure_set(v___f_1648_, 7, v_toApplicative_1644_);
    lean_closure_set(v___f_1648_, 8, v_toBind_1645_);
    lean_closure_set(v___f_1648_, 9, v_inst_1646_);
    v___f_1649_ = lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__4 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1649_, 0, v___f_1648_);
    lean_inc_ref(v___f_1649_);
    v___f_1650_ = lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    lean_closure_set(v___f_1650_, 0, v_text_1640_);
    lean_closure_set(v___f_1650_, 1, v_inst_1642_);
    lean_closure_set(v___f_1650_, 2, v_inst_1643_);
    lean_closure_set(v___f_1650_, 3, v_strLit_1639_);
    lean_closure_set(v___f_1650_, 4, v_toBind_1645_);
    lean_closure_set(v___f_1650_, 5, v___f_1649_);
    lean_closure_set(v___f_1650_, 6, v_toApplicative_1644_);
    lean_closure_set(v___f_1650_, 7, v___f_1649_);
    lean_inc_ref(v___f_1650_);
    v___f_1651_ = lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1651_, 0, v___f_1650_);
    v___f_1652_ = lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__9 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_1652_, 0, v_text_1640_);
    lean_closure_set(v___f_1652_, 1, v___f_1650_);
    lean_closure_set(v___f_1652_, 2, v_toApplicative_1644_);
    lean_closure_set(v___f_1652_, 3, v_toBind_1645_);
    lean_closure_set(v___f_1652_, 4, v_inst_1642_);
    lean_closure_set(v___f_1652_, 5, v___f_1651_);
    v___x_1653_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(
        v_inst_1642_,
        v_strLit_1639_,
    );
    lean_dec(v_strLit_1639_);
    v___x_1654_ = lean_apply_4(
        v_toBind_1645_,
        lean_box(0),
        lean_box(0),
        v___x_1653_,
        v___f_1652_,
    );
    return v___x_1654_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(
    mut v_inst_1655_: *mut LeanObject,
    mut v_inst_1656_: *mut LeanObject,
    mut v_strLit_1657_: *mut LeanObject,
    mut v_p_1658_: *mut LeanObject,
    mut v_inst_1659_: *mut LeanObject,
    mut v_inst_1660_: *mut LeanObject,
    mut v_toApplicative_1661_: *mut LeanObject,
    mut v_toBind_1662_: *mut LeanObject,
    mut v_inst_1663_: *mut LeanObject,
    mut v_text_1664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getEnv_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    v_getEnv_1665_ = lean_ctor_get(v_inst_1655_, 0);
    lean_inc(v_getEnv_1665_);
    lean_dec_ref(v_inst_1655_);
    lean_inc(v_toBind_1662_);
    v___f_1666_ = lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__10 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_1666_, 0, v_inst_1656_);
    lean_closure_set(v___f_1666_, 1, v_strLit_1657_);
    lean_closure_set(v___f_1666_, 2, v_text_1664_);
    lean_closure_set(v___f_1666_, 3, v_p_1658_);
    lean_closure_set(v___f_1666_, 4, v_inst_1659_);
    lean_closure_set(v___f_1666_, 5, v_inst_1660_);
    lean_closure_set(v___f_1666_, 6, v_toApplicative_1661_);
    lean_closure_set(v___f_1666_, 7, v_toBind_1662_);
    lean_closure_set(v___f_1666_, 8, v_inst_1663_);
    v___x_1667_ = lean_apply_4(
        v_toBind_1662_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1665_,
        v___f_1666_,
    );
    return v___x_1667_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit___redArg(
    mut v_inst_1668_: *mut LeanObject,
    mut v_inst_1669_: *mut LeanObject,
    mut v_inst_1670_: *mut LeanObject,
    mut v_inst_1671_: *mut LeanObject,
    mut v_inst_1672_: *mut LeanObject,
    mut v_inst_1673_: *mut LeanObject,
    mut v_p_1674_: *mut LeanObject,
    mut v_strLit_1675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1676_ = lean_ctor_get(v_inst_1668_, 0);
    lean_inc_ref(v_toApplicative_1676_);
    v_toBind_1677_ = lean_ctor_get(v_inst_1668_, 1);
    lean_inc_n(v_toBind_1677_, 2);
    v___f_1678_ = lean_alloc_closure(
        l_Lean_Doc_parseQuotedStrLit___redArg___lam__11 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_1678_, 0, v_inst_1670_);
    lean_closure_set(v___f_1678_, 1, v_inst_1672_);
    lean_closure_set(v___f_1678_, 2, v_strLit_1675_);
    lean_closure_set(v___f_1678_, 3, v_p_1674_);
    lean_closure_set(v___f_1678_, 4, v_inst_1668_);
    lean_closure_set(v___f_1678_, 5, v_inst_1671_);
    lean_closure_set(v___f_1678_, 6, v_toApplicative_1676_);
    lean_closure_set(v___f_1678_, 7, v_toBind_1677_);
    lean_closure_set(v___f_1678_, 8, v_inst_1673_);
    v___x_1679_ = lean_apply_4(
        v_toBind_1677_,
        lean_box(0),
        lean_box(0),
        v_inst_1669_,
        v___f_1678_,
    );
    return v___x_1679_;
}
pub unsafe fn l_Lean_Doc_parseQuotedStrLit(
    mut v_m_1680_: *mut LeanObject,
    mut v_inst_1681_: *mut LeanObject,
    mut v_inst_1682_: *mut LeanObject,
    mut v_inst_1683_: *mut LeanObject,
    mut v_inst_1684_: *mut LeanObject,
    mut v_inst_1685_: *mut LeanObject,
    mut v_inst_1686_: *mut LeanObject,
    mut v_p_1687_: *mut LeanObject,
    mut v_strLit_1688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_s_1690_: *mut LeanObject,
    mut v_toPure_1691_: *mut LeanObject,
    mut v_err_1692_: u8,
) -> *mut LeanObject {
    let mut v_stxStack_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    v_stxStack_1693_ = lean_ctor_get(v_s_1690_, 0);
    v___x_1694_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1693_);
    v___x_1695_ = lean_box((v_err_1692_) as usize);
    v___x_1696_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1696_, 0, v___x_1694_);
    lean_ctor_set(v___x_1696_, 1, v___x_1695_);
    v___x_1697_ = lean_apply_2(v_toPure_1691_, lean_box(0), v___x_1696_);
    return v___x_1697_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed(
    mut v_s_1698_: *mut LeanObject,
    mut v_toPure_1699_: *mut LeanObject,
    mut v_err_1700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_err_boxed_1701_: u8 = 0;
    let mut v_res_1702_: *mut LeanObject = core::ptr::null_mut();
    v_err_boxed_1701_ = (lean_unbox(v_err_1700_) as u8);
    v_res_1702_ =
        l_Lean_Doc_parseStrLit_x27___redArg___lam__0(v_s_1698_, v_toPure_1699_, v_err_boxed_1701_);
    lean_dec_ref(v_s_1698_);
    return v_res_1702_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__1(
    mut v___f_1703_: *mut LeanObject,
    mut v_err_1704_: u8,
) -> *mut LeanObject {
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    v___x_1705_ = lean_box((v_err_1704_) as usize);
    v___x_1706_ = lean_apply_1(v___f_1703_, v___x_1705_);
    return v___x_1706_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed(
    mut v___f_1707_: *mut LeanObject,
    mut v_err_1708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_err_boxed_1709_: u8 = 0;
    let mut v_res_1710_: *mut LeanObject = core::ptr::null_mut();
    v_err_boxed_1709_ = (lean_unbox(v_err_1708_) as u8);
    v_res_1710_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__1(v___f_1707_, v_err_boxed_1709_);
    return v_res_1710_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__2(
    mut v_toPure_1711_: *mut LeanObject,
    mut v___x_1712_: u8,
    mut v_toBind_1713_: *mut LeanObject,
    mut v___f_1714_: *mut LeanObject,
    mut v_____r_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = lean_box((v___x_1712_) as usize);
    v___x_1717_ = lean_apply_2(v_toPure_1711_, lean_box(0), v___x_1716_);
    v___x_1718_ = lean_apply_4(
        v_toBind_1713_,
        lean_box(0),
        lean_box(0),
        v___x_1717_,
        v___f_1714_,
    );
    return v___x_1718_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(
    mut v_toPure_1719_: *mut LeanObject,
    mut v___x_1720_: *mut LeanObject,
    mut v_toBind_1721_: *mut LeanObject,
    mut v___f_1722_: *mut LeanObject,
    mut v_____r_1723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_559__boxed_1724_: u8 = 0;
    let mut v_res_1725_: *mut LeanObject = core::ptr::null_mut();
    v___x_559__boxed_1724_ = (lean_unbox(v___x_1720_) as u8);
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
    mut v_env_1726_: *mut LeanObject,
    mut v_p_1727_: *mut LeanObject,
    mut v_ictx_1728_: *mut LeanObject,
    mut v_s_1729_: *mut LeanObject,
    mut v_toPure_1730_: *mut LeanObject,
    mut v___x_1731_: u8,
    mut v_toBind_1732_: *mut LeanObject,
    mut v_inst_1733_: *mut LeanObject,
    mut v_inst_1734_: *mut LeanObject,
    mut v_inst_1735_: *mut LeanObject,
    mut v_inst_1736_: *mut LeanObject,
    mut v_____do__lift_1737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: u8 = 0;
    v___x_1738_ = lean_box(0);
    v___x_1739_ = lean_box(0);
    lean_inc_ref(v_env_1726_);
    v___x_1740_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1740_, 0, v_env_1726_);
    lean_ctor_set(v___x_1740_, 1, v_____do__lift_1737_);
    lean_ctor_set(v___x_1740_, 2, v___x_1738_);
    lean_ctor_set(v___x_1740_, 3, v___x_1739_);
    v___x_1741_ = l_Lean_Parser_getTokenTable(v_env_1726_);
    lean_inc_ref(v_ictx_1728_);
    v_s_1742_ =
        l_Lean_Parser_ParserFn_run(v_p_1727_, v_ictx_1728_, v___x_1740_, v___x_1741_, v_s_1729_);
    lean_inc(v_toPure_1730_);
    lean_inc_ref_n(v_s_1742_, 2);
    v___f_1743_ = lean_alloc_closure(
        l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1743_, 0, v_s_1742_);
    lean_closure_set(v___f_1743_, 1, v_toPure_1730_);
    v___x_1744_ = l_Lean_Parser_ParserState_allErrors(v_s_1742_);
    v___x_1745_ = lean_array_get_size(v___x_1744_);
    lean_dec_ref(v___x_1744_);
    v___x_1746_ = lean_unsigned_to_nat(0);
    v___x_1747_ = lean_nat_dec_eq(v___x_1745_, v___x_1746_);
    if v___x_1747_ == 0 {
        let mut v___f_1748_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
        v___f_1748_ = lean_alloc_closure(
            l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_1748_, 0, v___f_1743_);
        v___x_1749_ = lean_box((v___x_1731_) as usize);
        lean_inc(v_toBind_1732_);
        v___f_1750_ = lean_alloc_closure(
            l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1750_, 0, v_toPure_1730_);
        lean_closure_set(v___f_1750_, 1, v___x_1749_);
        lean_closure_set(v___f_1750_, 2, v_toBind_1732_);
        lean_closure_set(v___f_1750_, 3, v___f_1748_);
        v___x_1751_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1728_, v_s_1742_);
        v___x_1752_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_1752_, 0, v___x_1751_);
        v___x_1753_ = l_Lean_MessageData_ofFormat(v___x_1752_);
        v___x_1754_ = l_Lean_logError___redArg(
            v_inst_1733_,
            v_inst_1734_,
            v_inst_1735_,
            v_inst_1736_,
            v___x_1753_,
        );
        v___x_1755_ = lean_apply_4(
            v_toBind_1732_,
            lean_box(0),
            lean_box(0),
            v___x_1754_,
            v___f_1750_,
        );
        return v___x_1755_;
    } else {
        let mut v_pos_1756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: u8 = 0;
        v_pos_1756_ = lean_ctor_get(v_s_1742_, 2);
        lean_inc(v_pos_1756_);
        v___x_1757_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1728_, v_pos_1756_);
        lean_dec(v_pos_1756_);
        if v___x_1757_ == 0 {
            let mut v___f_1758_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1760_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
            v___f_1758_ = lean_alloc_closure(
                l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_1758_, 0, v___f_1743_);
            v___x_1759_ = lean_box((v___x_1731_) as usize);
            lean_inc(v_toBind_1732_);
            v___f_1760_ = lean_alloc_closure(
                l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_1760_, 0, v_toPure_1730_);
            lean_closure_set(v___f_1760_, 1, v___x_1759_);
            lean_closure_set(v___f_1760_, 2, v_toBind_1732_);
            lean_closure_set(v___f_1760_, 3, v___f_1758_);
            v___x_1761_ = l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0;
            v___x_1762_ = l_Lean_Parser_ParserState_mkError(v_s_1742_, v___x_1761_);
            v___x_1763_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1728_, v___x_1762_);
            v___x_1764_ = lean_alloc_ctor(3, 1, (0) as u32);
            lean_ctor_set(v___x_1764_, 0, v___x_1763_);
            v___x_1765_ = l_Lean_MessageData_ofFormat(v___x_1764_);
            v___x_1766_ = l_Lean_logError___redArg(
                v_inst_1733_,
                v_inst_1734_,
                v_inst_1735_,
                v_inst_1736_,
                v___x_1765_,
            );
            v___x_1767_ = lean_apply_4(
                v_toBind_1732_,
                lean_box(0),
                lean_box(0),
                v___x_1766_,
                v___f_1760_,
            );
            return v___x_1767_;
        } else {
            let mut v___f_1768_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1769_: u8 = 0;
            let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_s_1742_);
            lean_dec(v_inst_1736_);
            lean_dec(v_inst_1735_);
            lean_dec_ref(v_inst_1734_);
            lean_dec_ref(v_inst_1733_);
            lean_dec_ref(v_ictx_1728_);
            v___f_1768_ = lean_alloc_closure(
                l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_1768_, 0, v___f_1743_);
            v___x_1769_ = 0;
            v___x_1770_ = lean_box((v___x_1769_) as usize);
            v___x_1771_ = lean_apply_2(v_toPure_1730_, lean_box(0), v___x_1770_);
            v___x_1772_ = lean_apply_4(
                v_toBind_1732_,
                lean_box(0),
                lean_box(0),
                v___x_1771_,
                v___f_1768_,
            );
            return v___x_1772_;
        }
    }
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(
    mut v_env_1773_: *mut LeanObject,
    mut v_p_1774_: *mut LeanObject,
    mut v_ictx_1775_: *mut LeanObject,
    mut v_s_1776_: *mut LeanObject,
    mut v_toPure_1777_: *mut LeanObject,
    mut v___x_1778_: *mut LeanObject,
    mut v_toBind_1779_: *mut LeanObject,
    mut v_inst_1780_: *mut LeanObject,
    mut v_inst_1781_: *mut LeanObject,
    mut v_inst_1782_: *mut LeanObject,
    mut v_inst_1783_: *mut LeanObject,
    mut v_____do__lift_1784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_575__boxed_1785_: u8 = 0;
    let mut v_res_1786_: *mut LeanObject = core::ptr::null_mut();
    v___x_575__boxed_1785_ = (lean_unbox(v___x_1778_) as u8);
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
    mut v_source_1787_: *mut LeanObject,
    mut v___x_1788_: u8,
    mut v___y_1789_: *mut LeanObject,
    mut v_env_1790_: *mut LeanObject,
    mut v_p_1791_: *mut LeanObject,
    mut v_toPure_1792_: *mut LeanObject,
    mut v_toBind_1793_: *mut LeanObject,
    mut v_inst_1794_: *mut LeanObject,
    mut v_inst_1795_: *mut LeanObject,
    mut v_inst_1796_: *mut LeanObject,
    mut v_inst_1797_: *mut LeanObject,
    mut v_s_1798_: *mut LeanObject,
    mut v___x_1799_: *mut LeanObject,
    mut v_____do__lift_1800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ictx_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_source_1787_);
                v_ictx_1801_ = l_Lean_Parser_mkInputContext___redArg(
                    v_source_1787_,
                    v_____do__lift_1800_,
                    v___x_1788_,
                    v___y_1789_,
                );
                v___x_1802_ = l_Lean_Parser_mkParserState(v_source_1787_);
                lean_dec_ref(v_source_1787_);
                v___x_1809_ = l_Lean_Syntax_getPos_x3f(v_s_1798_, v___x_1788_);
                if lean_obj_tag(v___x_1809_) == 0 {
                    v___x_1810_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_1811_ = l_panic___redArg(v___x_1799_, v___x_1810_);
                    v___y_1804_ = v___x_1811_;
                    state = 1;
                    continue;
                } else {
                    v_val_1812_ = lean_ctor_get(v___x_1809_, 0);
                    lean_inc(v_val_1812_);
                    lean_dec_ref_known(v___x_1809_, 1);
                    v___y_1804_ = v_val_1812_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_s_1805_ = l_Lean_Parser_ParserState_setPos(v___x_1802_, v___y_1804_);
                v___x_1806_ = lean_box((v___x_1788_) as usize);
                lean_inc(v_inst_1797_);
                lean_inc(v_toBind_1793_);
                v___f_1807_ = lean_alloc_closure(
                    l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed as *mut core::ffi::c_void,
                    12,
                    11,
                );
                lean_closure_set(v___f_1807_, 0, v_env_1790_);
                lean_closure_set(v___f_1807_, 1, v_p_1791_);
                lean_closure_set(v___f_1807_, 2, v_ictx_1801_);
                lean_closure_set(v___f_1807_, 3, v_s_1805_);
                lean_closure_set(v___f_1807_, 4, v_toPure_1792_);
                lean_closure_set(v___f_1807_, 5, v___x_1806_);
                lean_closure_set(v___f_1807_, 6, v_toBind_1793_);
                lean_closure_set(v___f_1807_, 7, v_inst_1794_);
                lean_closure_set(v___f_1807_, 8, v_inst_1795_);
                lean_closure_set(v___f_1807_, 9, v_inst_1796_);
                lean_closure_set(v___f_1807_, 10, v_inst_1797_);
                v___x_1808_ = lean_apply_4(
                    v_toBind_1793_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_source_1813_: *mut LeanObject,
    mut v___x_1814_: *mut LeanObject,
    mut v___y_1815_: *mut LeanObject,
    mut v_env_1816_: *mut LeanObject,
    mut v_p_1817_: *mut LeanObject,
    mut v_toPure_1818_: *mut LeanObject,
    mut v_toBind_1819_: *mut LeanObject,
    mut v_inst_1820_: *mut LeanObject,
    mut v_inst_1821_: *mut LeanObject,
    mut v_inst_1822_: *mut LeanObject,
    mut v_inst_1823_: *mut LeanObject,
    mut v_s_1824_: *mut LeanObject,
    mut v___x_1825_: *mut LeanObject,
    mut v_____do__lift_1826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_668__boxed_1827_: u8 = 0;
    let mut v_res_1828_: *mut LeanObject = core::ptr::null_mut();
    v___x_668__boxed_1827_ = (lean_unbox(v___x_1814_) as u8);
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
    lean_dec(v___x_1825_);
    lean_dec(v_s_1824_);
    return v_res_1828_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg___lam__4(
    mut v_text_1829_: *mut LeanObject,
    mut v_inst_1830_: *mut LeanObject,
    mut v_p_1831_: *mut LeanObject,
    mut v_toPure_1832_: *mut LeanObject,
    mut v_toBind_1833_: *mut LeanObject,
    mut v_inst_1834_: *mut LeanObject,
    mut v_inst_1835_: *mut LeanObject,
    mut v_inst_1836_: *mut LeanObject,
    mut v_s_1837_: *mut LeanObject,
    mut v___x_1838_: *mut LeanObject,
    mut v_env_1839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1840_: u8 = 0;
    let mut v___y_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getFileName_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: u8 = 0;
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1840_ = 1;
                v___x_1853_ = l_Lean_Syntax_getTailPos_x3f(v_s_1837_, v___x_1840_);
                if lean_obj_tag(v___x_1853_) == 0 {
                    v___x_1854_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once), _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
                    v___x_1855_ = l_panic___redArg(v___x_1838_, v___x_1854_);
                    v___y_1849_ = v___x_1855_;
                    state = 2;
                    continue;
                } else {
                    v_val_1856_ = lean_ctor_get(v___x_1853_, 0);
                    lean_inc(v_val_1856_);
                    lean_dec_ref_known(v___x_1853_, 1);
                    v___y_1849_ = v_val_1856_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v_getFileName_1844_ = lean_ctor_get(v_inst_1830_, 2);
                lean_inc(v_getFileName_1844_);
                v___x_1845_ = lean_box((v___x_1840_) as usize);
                lean_inc(v_toBind_1833_);
                v___f_1846_ = lean_alloc_closure(
                    l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed as *mut core::ffi::c_void,
                    14,
                    13,
                );
                lean_closure_set(v___f_1846_, 0, v___y_1842_);
                lean_closure_set(v___f_1846_, 1, v___x_1845_);
                lean_closure_set(v___f_1846_, 2, v___y_1843_);
                lean_closure_set(v___f_1846_, 3, v_env_1839_);
                lean_closure_set(v___f_1846_, 4, v_p_1831_);
                lean_closure_set(v___f_1846_, 5, v_toPure_1832_);
                lean_closure_set(v___f_1846_, 6, v_toBind_1833_);
                lean_closure_set(v___f_1846_, 7, v_inst_1834_);
                lean_closure_set(v___f_1846_, 8, v_inst_1830_);
                lean_closure_set(v___f_1846_, 9, v_inst_1835_);
                lean_closure_set(v___f_1846_, 10, v_inst_1836_);
                lean_closure_set(v___f_1846_, 11, v_s_1837_);
                lean_closure_set(v___f_1846_, 12, v___x_1838_);
                v___x_1847_ = lean_apply_4(
                    v_toBind_1833_,
                    lean_box(0),
                    lean_box(0),
                    v_getFileName_1844_,
                    v___f_1846_,
                );
                return v___x_1847_;
            }
            2 => {
                v_source_1850_ = lean_ctor_get(v_text_1829_, 0);
                lean_inc_ref(v_source_1850_);
                lean_dec_ref(v_text_1829_);
                v___x_1851_ = lean_string_utf8_byte_size(v_source_1850_);
                v___x_1852_ = lean_nat_dec_le(v___y_1849_, v___x_1851_);
                if v___x_1852_ == 0 {
                    lean_dec(v___y_1849_);
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
    mut v_inst_1857_: *mut LeanObject,
    mut v_inst_1858_: *mut LeanObject,
    mut v_p_1859_: *mut LeanObject,
    mut v_toPure_1860_: *mut LeanObject,
    mut v_toBind_1861_: *mut LeanObject,
    mut v_inst_1862_: *mut LeanObject,
    mut v_inst_1863_: *mut LeanObject,
    mut v_inst_1864_: *mut LeanObject,
    mut v_s_1865_: *mut LeanObject,
    mut v___x_1866_: *mut LeanObject,
    mut v_text_1867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getEnv_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    v_getEnv_1868_ = lean_ctor_get(v_inst_1857_, 0);
    lean_inc(v_getEnv_1868_);
    lean_dec_ref(v_inst_1857_);
    lean_inc(v_toBind_1861_);
    v___f_1869_ = lean_alloc_closure(
        l_Lean_Doc_parseStrLit_x27___redArg___lam__4 as *mut core::ffi::c_void,
        11,
        10,
    );
    lean_closure_set(v___f_1869_, 0, v_text_1867_);
    lean_closure_set(v___f_1869_, 1, v_inst_1858_);
    lean_closure_set(v___f_1869_, 2, v_p_1859_);
    lean_closure_set(v___f_1869_, 3, v_toPure_1860_);
    lean_closure_set(v___f_1869_, 4, v_toBind_1861_);
    lean_closure_set(v___f_1869_, 5, v_inst_1862_);
    lean_closure_set(v___f_1869_, 6, v_inst_1863_);
    lean_closure_set(v___f_1869_, 7, v_inst_1864_);
    lean_closure_set(v___f_1869_, 8, v_s_1865_);
    lean_closure_set(v___f_1869_, 9, v___x_1866_);
    v___x_1870_ = lean_apply_4(
        v_toBind_1861_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1868_,
        v___f_1869_,
    );
    return v___x_1870_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27___redArg(
    mut v_inst_1871_: *mut LeanObject,
    mut v_inst_1872_: *mut LeanObject,
    mut v_inst_1873_: *mut LeanObject,
    mut v_inst_1874_: *mut LeanObject,
    mut v_inst_1875_: *mut LeanObject,
    mut v_inst_1876_: *mut LeanObject,
    mut v_p_1877_: *mut LeanObject,
    mut v_s_1878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1879_ = lean_ctor_get(v_inst_1871_, 0);
    v_toBind_1880_ = lean_ctor_get(v_inst_1871_, 1);
    lean_inc_n(v_toBind_1880_, 2);
    v_toPure_1881_ = lean_ctor_get(v_toApplicative_1879_, 1);
    lean_inc(v_toPure_1881_);
    v___x_1882_ = lean_unsigned_to_nat(0);
    v___f_1883_ = lean_alloc_closure(
        l_Lean_Doc_parseStrLit_x27___redArg___lam__5 as *mut core::ffi::c_void,
        11,
        10,
    );
    lean_closure_set(v___f_1883_, 0, v_inst_1873_);
    lean_closure_set(v___f_1883_, 1, v_inst_1875_);
    lean_closure_set(v___f_1883_, 2, v_p_1877_);
    lean_closure_set(v___f_1883_, 3, v_toPure_1881_);
    lean_closure_set(v___f_1883_, 4, v_toBind_1880_);
    lean_closure_set(v___f_1883_, 5, v_inst_1871_);
    lean_closure_set(v___f_1883_, 6, v_inst_1874_);
    lean_closure_set(v___f_1883_, 7, v_inst_1876_);
    lean_closure_set(v___f_1883_, 8, v_s_1878_);
    lean_closure_set(v___f_1883_, 9, v___x_1882_);
    v___x_1884_ = lean_apply_4(
        v_toBind_1880_,
        lean_box(0),
        lean_box(0),
        v_inst_1872_,
        v___f_1883_,
    );
    return v___x_1884_;
}
pub unsafe fn l_Lean_Doc_parseStrLit_x27(
    mut v_m_1885_: *mut LeanObject,
    mut v_inst_1886_: *mut LeanObject,
    mut v_inst_1887_: *mut LeanObject,
    mut v_inst_1888_: *mut LeanObject,
    mut v_inst_1889_: *mut LeanObject,
    mut v_inst_1890_: *mut LeanObject,
    mut v_inst_1891_: *mut LeanObject,
    mut v_p_1892_: *mut LeanObject,
    mut v_s_1893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
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
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Mem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_DocString_Builtin_Parsing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Mem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
}
